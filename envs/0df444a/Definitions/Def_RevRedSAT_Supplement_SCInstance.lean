-- Prove2me | Definitions.Def_RevRedSAT_Supplement_SCInstance
-- name    : RevRedSAT_Supplement_SCInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:57:31.870421+00:00
-- url     : https://prove2.me/theorems/96975e4c-6b49-40a8-bb3a-34d20d8843f2
-- title:
--   Set Cover instances and the number of bounded covers
-- statement:
--   An instance of counting **Set Cover** (App. C.1) is a universe $U=\{0,\dots,p-1\}$, an indexed family $S_0,\dots,S_{q-1}\subseteq U$ and an integer budget $b$. Its code lists $p$, the sets in index order, and then $b$ (a sign bit and $|b|$).
--
--   The quantity computed by Theorem 8.1 is
--
--   $$\#\Bigl\{X\subseteq[q] : |X|\le b,\ \textstyle\bigcup_{i\in X}S_i=U\Bigr\}.$$
--
--   Equal sets at different indices are different choices, nonminimal covers are counted, and the count is $0$ for $b<0$.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.1, p.92 (Set Cover); Theorem 8.1, p.56

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RevRedSAT_SearchWithin

set_option autoImplicit false

namespace RevRedSAT.Supplement

open RSListDecodingCapacity.AllRates

/-- **An instance of (counting) Set Cover.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.1, p.92: "Set Cover. Given a finite universe U, an indexed family S1, . . . , Sq ⊆ U, and
a budget b, find an index set A ⊆ {1, . . . , q} with |A| ≤ b and ⋃_{i∈A} Si = U. In the
exact-counting version, count these index sets A. Equal sets at different indices remain distinct
choices"; Theorem 8.1, p.56: "For any integer budget b".

**Formalization Note** The universe is `Fin p` and the indices are `Fin q` (relabelling); the
budget is an integer, as Theorem 8.1 allows. -/
structure SCInstance where
  /-- the number of universe elements -/
  p : ℕ
  /-- the number of indexed sets -/
  q : ℕ
  /-- the indexed family -/
  S : Fin q → Finset (Fin p)
  /-- the integer budget -/
  b : ℤ

/-- The code of an integer: its sign bit (`true` for negative) followed by its absolute value in
self-delimiting binary. -/
def encInt (b : ℤ) : List Bool := decide (b < 0) :: encNat b.natAbs

/-- The codes of a Set Cover instance: `p`, then the list of the sets `S_0, …, S_{q−1}` in index
order, each listed without repetition in any order, then the budget `b` last. -/
def IsSCCode (I : SCInstance) (w : List Bool) : Prop :=
  ∃ Ls : Fin I.q → List (Fin I.p), (∀ i, (Ls i).Nodup ∧ (Ls i).toFinset = I.S i) ∧
    w = encNat I.p ++ encList encSet (List.ofFn Ls) ++ encInt I.b

/-- The number of index sets `X ⊆ [q]` with `|X| ≤ b` and `⋃_{i∈X} S_i = U` (App. C, p.92: "counting
solutions of size at most a budget includes nonminimal solutions"); `0` when `b < 0`. -/
def coverCount (I : SCInstance) : ℕ :=
  (Finset.univ.filter fun X : Finset (Fin I.q) =>
    (X.card : ℤ) ≤ I.b ∧ X.biUnion I.S = Finset.univ).card

end RevRedSAT.Supplement


