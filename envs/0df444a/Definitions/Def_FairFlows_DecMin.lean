-- Prove2me | Definitions.Def_FairFlows_DecMin
-- name    : FairFlows_DecMin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:21.158981+00:00
-- url     : https://prove2.me/theorems/630ac4aa-f157-4c3c-a8e4-5bb6117c926c
-- title:
--   Decreasing minimality on an edge set $F$
-- statement:
--   For $z\in\mathbb Z^A$ and a finite edge set $F$, let $\mathrm{dec}_F(z)$ be the list of the values $z(e)$, $e\in F$, arranged in non-increasing order (with multiplicity). A vector $y$ is **decreasingly smaller** than $z$ on $F$ if $\mathrm{dec}_F(y)$ is lexicographically strictly smaller than $\mathrm{dec}_F(z)$. For a set $S\subseteq\mathbb Z^A$, $z$ is **decreasingly minimal on $F$** ($F$-dec-min) in $S$ if $z\in S$ and no $y\in S$ is decreasingly smaller than $z$ on $F$: the largest component of $z$ on $F$ is as small as possible, within this the next largest, and so on.
--
--   This is the fairness notion of the paper; with $S=$ Q⃛$(f,g;m)$ it is the paper's $F$-dec-min integral feasible flow, and the same predicate serves the tightened sets of §5.
--
--   **Formalization Note** The sort uses $\ge$, giving the non-increasing order; an ascending sort would give increasing maximality, a different notion for flows (Remark 2.2). Both lists have length $|F|$ and `List.Lex (· < ·)` is the strict lexicographic order.
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, §1 p.3 (dec-min), §2.1 p.6 (decreasingly minimal on F), p.14 (decreasingly smaller), p.15 (arranged in a decreasing order)

import Mathlib

set_option autoImplicit false

namespace FairFlows

variable {A : Type}

/-- The values of `z` on the edge set `F`, arranged in non-increasing order (with
multiplicity) (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.3 and p.15:
"when both arranged in a decreasing order").

**Formalization Note** `F.val.map z` is the multiset of values of `z` on `F`; sorting it with
`≥` gives the non-increasing list, of length `|F|`. -/
def decSorted (F : Finset A) (z : A → ℤ) : List ℤ :=
  (F.val.map z).sort (· ≥ ·)

/-- `y` is decreasingly smaller than `z` on `F`: the non-increasingly sorted value list of `y`
on `F` is lexicographically strictly smaller than that of `z` (arXiv:1907.02673v5, p.14).

**Formalization Note** Both lists have length `|F|`; `List.Lex (· < ·)` is the strict
lexicographic order. Comparing the non-increasingly sorted lists is decreasing minimality;
an ascending sort would give increasing maximality instead (Remark 2.2). -/
def DecSmaller (F : Finset A) (y z : A → ℤ) : Prop :=
  List.Lex (· < ·) (decSorted F y) (decSorted F z)

/-- `z` is decreasingly minimal on `F` (`F`-dec-min) in the set `S ⊆ ℤ^A`: `z ∈ S` and no
member of `S` is decreasingly smaller than `z` on `F`, i.e. the largest component of `z` on `F`
is as small as possible, within this the next largest, and so on (arXiv:1907.02673v5, p.3 and
p.6).

**Formalization Note** `S` is a parameter so that the same predicate serves
`Q⃛(f, g; m)`, `Q⃛′ = Q⃛(f′, g′; m)` and any edge subset `F` (Lemma 5.2, Theorem 5.3). The
paper's `F`-dec-min element of `Q⃛(f, g; m)` is `IsDecMinOn (intFlows D f g m) F z`. -/
def IsDecMinOn (S : Set (A → ℤ)) (F : Finset A) (z : A → ℤ) : Prop :=
  z ∈ S ∧ ∀ y ∈ S, ¬ DecSmaller F y z

end FairFlows


