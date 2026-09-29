-- Prove2me | Definitions.Def_SetCoverThreshold_MaxCover_Instance
-- name    : SetCoverThreshold_MaxCover_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:01:43.662488+00:00
-- url     : https://prove2.me/theorems/d0fb825a-3b40-44d0-86d5-0b61bc4d00bf
-- title:
--   Max k-cover instances, their encoding, opt, (non-constructive) approximation within δ, and greedy runs
-- statement:
--   This file defines max $k$-cover and the notions of approximation Feige uses for it (J. ACM 45(4), 1998, p. 634 and §5, pp. 647–648).
--
--   1. **Instances.** "Let $S$ be a set of $n$ points and $\mathcal F=\{S_1,\dots,S_s\}$ a collection of subsets of $S$ … *Max k-cover* is the problem of selecting $k$ subsets from $\mathcal F$ such that their union contains as many points as possible" (p. 634). An instance consists of $n$, a list of subsets of $\{0,\dots,n-1\}$, and $k$.
--   2. **Encoding.** An instance is written over the alphabet $\{0,1,\#\}$: $n$ in unary and a separator, then each set as its characteristic bit-vector of length $n$ followed by a separator, then $k$ in unary. Its length is $\Theta(ns+n+k)$.
--   3. **Optimum.** $\mathrm{opt}$ is the largest number of points covered by at most $k$ of the sets:
--   $$\mathrm{opt}=\max\Big\{\Big|\bigcup_{i\in T}S_i\Big| : T\subseteq\{1,\dots,s\},\ |T|\le k\Big\}.$$
--   4. **Approximation within $\delta$ (p. 648).** "We say that a polynomial time algorithm *approximates* max $k$-cover within a ratio of $0 < \delta < 1$ if on any input, the algorithm outputs a number that is between opt and $\delta\cdot$opt, where opt denotes number of points covered by the optimal solution." `MaxCoverApproximable δ` holds if some polynomial-time computable function (Cook's one-tape machines) maps the encoding of every instance to a unary number $v$ with $\delta\cdot\mathrm{opt}\le v\le\mathrm{opt}$.
--   5. **Greedy runs (p. 647).** The greedy algorithm iteratively selects "the sets that cover the largest number of yet uncovered points". A greedy run is a sequence of $k$ set indices such that each selected set covers at least as many points outside the union of the previously selected sets as any other set; ties are arbitrary.
--
--   The non-constructive notion 4 is the hypothesis of Theorem 5.3; any algorithm that outputs $k$ sets whose union is large yields one (the size of a union is computable), so it is the weaker assumption.
--
--   **Formalization Note** The optimum is over at most $k$ sets; it equals the paper's "exactly $k$" optimum whenever $k\le s$ and also covers $k>s$. The maximum is a finite supremum over a nonempty family (it contains $T=\emptyset$), so it has no junk value. Points are 0-based.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 634 (max k-cover), p. 647 (greedy, Proposition 5.1), p. 648 (definition of approximating max k-cover)

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace SetCoverThreshold.MaxCover

open CookPvsNP

/-- An instance of **max k-cover** (p. 634): `n` points `Fin n`, a list of subsets of the points,
and the number `k` of subsets to be selected. -/
structure Instance where
  /-- The number of points. -/
  n : ℕ
  /-- The collection of subsets. -/
  sets : List (Finset (Fin n))
  /-- The number of subsets to select. -/
  k : ℕ

/-- The alphabet used to write instances. -/
inductive Sym where
  | zero
  | one
  | sep
  deriving DecidableEq

instance : Fintype Sym where
  elems := {Sym.zero, Sym.one, Sym.sep}
  complete := by intro x; cases x <;> simp

/-- The characteristic bit-vector of a set of points. -/
def encodeSet {n : ℕ} (S : Finset (Fin n)) : List Sym :=
  List.ofFn (fun p : Fin n => if p ∈ S then Sym.one else Sym.zero)

/-- Encoding of an instance: `n` in unary and a separator, then each set as its characteristic
bit-vector followed by a separator, then `k` in unary. -/
def encode (I : Instance) : List Sym :=
  List.replicate I.n Sym.one ++ (Sym.sep :: I.sets.flatMap (fun S => encodeSet S ++ [Sym.sep])) ++
    List.replicate I.k Sym.one

/-- The points covered by the sub-collection of sets with indices in `T`. -/
def coverOf (I : Instance) (T : Finset (Fin I.sets.length)) : Finset (Fin I.n) :=
  T.biUnion (fun i => I.sets.get i)

/-- `opt`: the largest number of points covered by at most `k` of the sets. -/
def opt (I : Instance) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin I.sets.length))).filter (fun T => T.card ≤ I.k)).sup
    (fun T => (coverOf I T).card)

/-- **Approximating max k-cover within a ratio `δ`** (p. 648, non-constructive): a
polynomial-time algorithm that on every input outputs (in unary) a number between `δ · opt`
and `opt`. -/
def MaxCoverApproximable (δ : ℝ) : Prop :=
  ∃ A : List Sym → List Unit, PolyTimeComputable A ∧
    ∀ I : Instance, δ * (opt I : ℝ) ≤ (A (encode I)).length ∧ (A (encode I)).length ≤ opt I

/-- A **greedy run** (p. 647): a sequence of `k` set indices, each covering the largest number of
points not covered by the sets selected before it (ties broken arbitrarily). -/
def IsGreedyRun (I : Instance) (run : Fin I.k → Fin I.sets.length) : Prop :=
  ∀ t : Fin I.k, ∀ j : Fin I.sets.length,
    (I.sets.get j \ coverOf I ((Finset.univ.filter (· < t)).image run)).card ≤
      (I.sets.get (run t) \ coverOf I ((Finset.univ.filter (· < t)).image run)).card

end SetCoverThreshold.MaxCover


