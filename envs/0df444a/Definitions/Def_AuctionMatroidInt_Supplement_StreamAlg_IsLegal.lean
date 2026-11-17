-- Prove2me | Definitions.Def_AuctionMatroidInt_Supplement_StreamAlg_IsLegal
-- name    : AuctionMatroidInt_Supplement_StreamAlg_IsLegal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:22:09.060538+00:00
-- url     : https://prove2.me/theorems/37256c00-1c5b-43b2-bd06-78ffa0de5cf0
-- title:
--   Legal semi-streaming algorithms: opaque elements, queries only on stored elements
-- statement:
--   A stream algorithm $A$ on $[n]$ is **legal** when
--
--   1. (*opacity*) it commutes with every renaming $\tau$ of $[n]$: its initial memory contains no element name that $\tau$ could move, and renaming the elements in the memory and in the arriving element renames the action it chooses (the queried set, the new memories and the output);
--   2. (*access*) every queried set is contained in the set of elements stored in the memory together with the arriving element.
--
--   Clause 2 is the paper's access rule: the oracles "can be queried only on subsets of the elements stored in memory", and the paper's algorithm also queries with the element just arriving. Clause 1 says that elements are objects delivered by the stream rather than names the algorithm can compute: without it, an algorithm on the ground set $[n]$ could enumerate element names with a counter, never read the stream, and make the pass bound meaningless. A legal algorithm may still test elements for equality and order them by their position in memory, which is all the paper's algorithms use.
--
--   **Formalization Note** Both clauses are required on all memories, not only on reachable ones; an implementation that halts with output $\emptyset$ on memories it never writes meets this.
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), §6.1, p.30 (PDF p.32); §6.2, pp.31–32 (PDF pp.33–34)

import Mathlib
import Definitions.Def_AuctionMatroidInt_Supplement_StreamAlg

namespace AuctionMatroidInt.Supplement

/-- **Legal semi-streaming algorithms: elements are opaque and queries touch only stored
elements.**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), §6.1, p.30: "The algorithm has
access to independence oracles for M1 and M2, which can be queried only on subsets of the
elements stored in memory"; §6.2, p.32: "the oracles are queried only for subsets of the stored
elements and e" (the arriving element).

`A.IsLegal` holds when
1. (*opacity*) `A` commutes with every renaming `τ` of the ground set: the initial memory is
   unchanged by `τ`, and renaming the memory and the arriving element renames the chosen action;
2. (*access*) every query is on a subset of the stored elements and the arriving element.

**Formalization Note.** In the streaming model an element is an object delivered by the stream,
not a name the algorithm can compute. Since the ground set is `Fin n`, an algorithm could
otherwise manufacture element names from a counter, read no stream at all, and make the pass bound
empty. Clause 1 rules this out: a renaming-invariant algorithm cannot encode an element's name in
a number, and cannot create a cell for an element it did not receive while two or more elements
are absent from its memory and input. It still compares elements for
equality and orders them by their position in memory, which is all the paper's algorithms
(Algorithm 4, Lemma 6.1, the greedy pass) need. Both clauses are required for all memories, not
only reachable ones; an implementation that halts with output `∅` on every memory it never writes
(an action unchanged by renaming, with no query) meets this. -/
def StreamAlg.IsLegal {n : ℕ} (A : StreamAlg n) : Prop :=
  (∀ τ : Equiv.Perm (Fin n),
      A.init.map (Cell.relabel τ) = A.init ∧
      ∀ (m : List (Cell n)) (x : Option (Fin n)),
        A.step (m.map (Cell.relabel τ)) (x.map τ) = (A.step m x).relabel τ) ∧
  ∀ (m : List (Cell n)) (x : Option (Fin n)) (i : Fin 2) (S : Finset (Fin n))
    (k : Bool → List (Cell n)),
    A.step m x = .query i S k → S ⊆ storedElems m ∪ x.toFinset

end AuctionMatroidInt.Supplement


