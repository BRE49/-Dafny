class Queue<T> {
  var q : seq<T>; // contents of q.
  constructor ()
	{
    q := [];
	}

  // Returns the top element of the q, without removing it.
  method Enqueue(elem: T)
  modifies this;
  ensures q == old(q) + [elem];
  ensures q[|q|-1] == elem;
  {
    q := q + [elem];
  }

  method Dequeue() returns (r: T)
  modifies this;
  requires q != [];
  ensures q == old(q)[0..|old(q)|-1];
  ensures r == old(q)[|old(q)|-1];
  {    
    r := q[|q|-1];
    q := q[0..|q|-1];
  } 

  method Peek() returns (r: T)
  requires q != [];
  ensures q == old(q)
  ensures r == old(q)[|old(q)|-1];
  {    
    r := q[|q|-1];
  } 
}
