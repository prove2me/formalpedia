-- Prove2me | Definitions.Def_Disjunctive_CutCorrespondence_Rank_v2
-- name    : Disjunctive_CutCorrespondence_Rank_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T22:02:37.68445+00:00
-- url     : https://prove2.me/theorems/208e8727-ad85-49eb-acbd-3d31e94e9c3f
-- title:
--   Rank of a polyhedron w.r.t. four cut families (re-issued on the corrected Ch. 8 definitions)
-- statement:
--   Rank of $P$ with respect to a cut-generating procedure applied along an enumeration of the 0-1 variables, and the elementary closures of a polyhedron w.r.t. simple disjunctive cuts, strengthened lift-and-project cuts (Theorem 6.4's $\gamma$) and mixed integer Gomory cuts, lifted from a representation $\{x:Ax\ge b\}$ to a set by intersecting over all representations. Content unchanged except that it is built on the corrected `Cglp_v2`/`Tableau_v2` modules (corrected $\gamma$ and $\bar\pi$).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §8.4

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Basic
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau_v2

namespace Disjunctive.CutCorrespondence

/-- One round of a cut-generating procedure applied to a coordinate: takes the current
polyhedron (as a bare `Set`) and a disjunction coordinate to the new, tightened set (Balas §8.4,
p. 104: "a certain cut generating procedure"). -/
def CutStep (n : ℕ) := Set (Fin n → ℝ) → Fin n → Set (Fin n → ℝ)

/-- Folding a `CutStep` left to right over an explicit coordinate sequence. -/
def IterateCutStep {n : ℕ} (Phi : CutStep n) (P : Set (Fin n → ℝ)) (l : List (Fin n)) :
    Set (Fin n → ℝ) :=
  l.foldl Phi P

/-- `P` has rank at most `r` with respect to the cut-generating procedure `Φ` and the 0-1 index
set `N'` (Balas §8.4, p. 104): there is a length-`r` enumeration of `N'` after which recursively
applying `Φ` reaches the convex hull of `N'`-integral points of `P`. Since the book's own proof of
Theorem 8.7 exhibits such a sequence of length exactly `|N'|` for each cut family rather than
searching for the minimal such length, "rank at most `r`" (existence of a witness of length `r`)
is what is needed and stated, rather than the exact minimal rank. -/
def HasRankAtMost {n : ℕ} (Phi : CutStep n) (P : Set (Fin n → ℝ)) (Nprime : Finset (Fin n))
    (r : ℕ) : Prop :=
  ∃ l : List (Fin n), l.Nodup ∧ l.toFinset = Nprime ∧ l.length = r ∧
    IterateCutStep Phi P l = convexHull ℝ (P ∩ ⋂ j ∈ Nprime, ZeroOneSet j)

/-- The elementary closure of a *represented* polyhedron `{x : Ax≥b}` with respect to simple
disjunctive cuts from the disjunction `x_k≤0 ∨ x_k≥1` (Balas §8.3, p. 102-103): intersect with
every simple disjunctive cut arising from a valid basis `ι` (nonsingular, `0<ā_k0<1`, matching
Lemma 8.1/8.3's basicness and dominance conditions). -/
def SimpleDisjClosure {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Fin n) :
    Set (Fin n → ℝ) :=
  Poly A b ∩
    ⋂ (ι : Fin n → Fin m) (_ : Function.Injective ι) (_ : IsUnit (Ahat A ι).det)
      (_ : 0 < Abar0 A b ι k) (_ : Abar0 A b ι k < 1), SimpleDisjCutSet A b ι k

/-- The elementary closure of a *represented* polyhedron with respect to strengthened
lift-and-project cuts from the disjunction on `k` (Balas §8.2, Theorem 6.4/8.5): intersect with
every strengthened cut `γx≥β` (Theorem 6.4's `γ`, strengthening only the coefficients of 0-1
variables `j ∈ N'`, with the multipliers of the rows `x_j ≥ 0` removed from `uÃ_j, vÃ_j`) arising
from a feasible solution of `(CGLP)_k` with `u0, v0 > 0`. -/
def StrengthenedLPClosure {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Fin n)
    (Nprime : Finset (Fin n)) : Set (Fin n → ℝ) :=
  Poly A b ∩
    ⋂ (α : Fin n → ℝ) (u : Fin m → ℝ) (u0 : ℝ) (v : Fin m → ℝ) (v0 : ℝ) (β : ℝ)
      (_ : IsCGLPKFeasible A b k α u u0 v v0 β) (_ : 0 < u0) (_ : 0 < v0),
      {x | β ≤ dotProduct (Gamma A b u u0 v v0 Nprime α) x}

/-- The elementary closure of a *represented* polyhedron with respect to mixed integer Gomory
cuts (equivalently, strengthened simple disjunctive cuts, eq. (8.10)) from the disjunction on
`k` (Balas §8.2-8.3). -/
def MIGClosure {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Fin n)
    (Nprime : Finset (Fin n)) : Set (Fin n → ℝ) :=
  Poly A b ∩
    ⋂ (ι : Fin n → Fin m) (_ : Function.Injective ι) (_ : IsUnit (Ahat A ι).det)
      (_ : 0 < Abar0 A b ι k) (_ : Abar0 A b ι k < 1),
      StrengthenedSimpleDisjCutSet A b ι k Nprime

/-- Lifting `SimpleDisjClosure` from a specific representation to a bare `Set`, by intersecting
over every valid linear representation of the current set (well-defined for the genuine
polyhedra this procedure is ever applied to; see `MODERATION_NOTES.md`). -/
def SimpleDisjClosureOfSet {n : ℕ} (S : Set (Fin n → ℝ)) (k : Fin n) : Set (Fin n → ℝ) :=
  ⋂ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (_ : Poly A b = S),
    SimpleDisjClosure A b k

/-- Lifting `StrengthenedLPClosure` from a specific representation to a bare `Set`. -/
def StrengthenedLPClosureOfSet {n : ℕ} (S : Set (Fin n → ℝ)) (k : Fin n)
    (Nprime : Finset (Fin n)) : Set (Fin n → ℝ) :=
  ⋂ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (_ : Poly A b = S),
    StrengthenedLPClosure A b k Nprime

/-- Lifting `MIGClosure` from a specific representation to a bare `Set`. -/
def MIGClosureOfSet {n : ℕ} (S : Set (Fin n → ℝ)) (k : Fin n) (Nprime : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  ⋂ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (_ : Poly A b = S),
    MIGClosure A b k Nprime

end Disjunctive.CutCorrespondence


