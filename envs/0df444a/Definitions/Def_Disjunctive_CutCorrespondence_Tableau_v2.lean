-- Prove2me | Definitions.Def_Disjunctive_CutCorrespondence_Tableau_v2
-- name    : Disjunctive_CutCorrespondence_Tableau_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T22:01:46.548286+00:00
-- url     : https://prove2.me/theorems/c42fc2ca-8bcb-4fa7-8226-b524da307599
-- title:
--   Tableau of Ch. 8 and the mixed integer Gomory coefficients $\bar\pi_j$ (corrected)
-- statement:
--   The simplex tableau quantities of Chapter 8 for a nonsingular $\hat A=\tilde A_J$ (rows enumerated by $\iota$): $\bar a_{k0}=e_k\hat A^{-1}\hat b$, $\bar a_{kj}=-(\hat A^{-1})_{kj}$, the simple disjunctive cut coefficients $\pi_j=\max\{\bar a_{kj}(1-\bar a_{k0}),-\bar a_{kj}\bar a_{k0}\}$, $\pi_0=\bar a_{k0}(1-\bar a_{k0})$, the surplus $s_j(x)=(\tilde Ax-\tilde b)_{\iota j}$, and the strengthened (mixed integer Gomory) coefficients of eq. (8.10): $\bar\pi_j=\min\{f_{kj}(1-\bar a_{k0}),(1-f_{kj})\bar a_{k0}\}$ for $j\in J\cap N'$ and $\bar\pi_j=\pi_j$ otherwise.
--
--   **Correction.** "$j\in J\cap N'$" means: the nonbasic row $\iota j$ is the bound $x_l\ge 0$ of a 0-1 variable $l\in N'$ (its surplus is the integer variable $x_l$). The retired `PiBar` strengthened position $j$ whenever $j\in N'$ as a *row position*, i.e. it applied the Gomory strengthening to arbitrary (non-integer) surplus variables, producing invalid cuts.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §8.1-8.2, eqs. (8.4)-(8.10)

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp_v2

namespace Disjunctive.CutCorrespondence

/-- `Â`, the `n×n` submatrix of `Ã` whose rows are `ι 0, …, ι (n-1)` (Balas §8.1, p. 98-99): an
explicit enumeration `ι : Fin n → M` of the row index set `J`, rather than a bare `Finset M`, so
that the submatrix and its inverse are genuine square `Matrix (Fin n) (Fin n) ℝ` objects. -/
def Ahat {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (ι : Fin n → M) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Atil (ι i) j

/-- `b̂`, the subvector of `b̃` corresponding to `Â` (Balas §8.1, p. 99). -/
def Bhat {n : ℕ} {M : Type*} (btil : M → ℝ) (ι : Fin n → M) : Fin n → ℝ :=
  fun i => btil (ι i)

/-- `ā_k0 := e_k Â⁻¹ b̂` (Balas §8.1, eq. (8.6), p. 100): the value of `x_k` at the basic solution
determined by `ι`. -/
noncomputable def Abar0 {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (k : Fin n) : ℝ :=
  (Ahat Atil ι)⁻¹.mulVec (Bhat btil ι) k

/-- `ā_kj := -(Â⁻¹)_{kj}`, indexed by row-position `i` (Balas §8.1, p. 99, following eq. (8.5)). -/
noncomputable def Abar {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (ι : Fin n → M) (k i : Fin n) : ℝ :=
  -((Ahat Atil ι)⁻¹) k i

/-- `π¹_j := ā_kj(1-ā_k0)` (Balas §8.1, eq. (8.8), p. 100). -/
noncomputable def Pi1 {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (k i : Fin n) : ℝ :=
  Abar Atil ι k i * (1 - Abar0 Atil btil ι k)

/-- `π²_j := -ā_kj·ā_k0` (Balas §8.1, eq. (8.8), p. 100). -/
noncomputable def Pi2 {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (k i : Fin n) : ℝ :=
  -(Abar Atil ι k i) * Abar0 Atil btil ι k

/-- `π0 := ā_k0(1-ā_k0)` (Balas §8.1, eq. (8.7), p. 100). -/
noncomputable def Pi0 {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (k : Fin n) : ℝ :=
  Abar0 Atil btil ι k * (1 - Abar0 Atil btil ι k)

/-- `π_j := max{π¹_j,π²_j}` (Balas §8.1, eq. (8.8), p. 100). -/
noncomputable def PiCoef {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (k i : Fin n) : ℝ :=
  max (Pi1 Atil btil ι k i) (Pi2 Atil btil ι k i)

/-- The surplus (slack) value `s_j := (Ãx)_j - b̃_j` at row `ι i`, a genuine affine function of
`x` for every row of `Ã` (bound or original), matching Balas's own identification of a bound
row's surplus with the corresponding variable (Balas §8.1, p. 99, eq. (8.4)-(8.5)): see
`MODERATION_NOTES.md`. -/
def Surplus {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M)
    (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  (dotProduct (Atil (ι i)) x) - btil (ι i)

/-- The simple disjunctive cut `π^s_J x_J ≥ π0` (Balas §8.1, eq. (8.7)-(8.8)), viewed as a
subset of the original `x`-space via the surplus substitution (8.4)-(8.5). -/
def SimpleDisjCutSet {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (k : Fin n) : Set (Fin n → ℝ) :=
  {x | Pi0 Atil btil ι k ≤ ∑ i, PiCoef Atil btil ι k i * Surplus Atil btil ι i x}

/-- `f_kj`, the fractional part of `ā_kj` (standard mixed-integer-Gomory-cut notation, used
without restatement by Balas §8.2; see `MODERATION_NOTES.md`). -/
noncomputable def FracAbar {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (ι : Fin n → M) (k i : Fin n) : ℝ :=
  Int.fract (Abar Atil ι k i)

open Classical in
/-- `π̄_j`, the strengthened cut coefficients of eq. (8.10) (Balas §8.2, p. 103):
`min{f_kj(1-ā_k0), (1-f_kj)ā_k0}` for `j ∈ J ∩ N'`, `π_j` otherwise. In the book `J` is a set of
rows of `Ã` and "`j ∈ J ∩ N'`" identifies the nonnegativity row `x_j ≥ 0` of a 0-1 variable
`j ∈ N'` with that variable: the nonbasic surplus at such a row *is* the integer-constrained
`x_j`, which is what makes the mixed-integer-Gomory strengthening valid. Accordingly the
coefficient at row-position `i` is strengthened exactly when the row `ι i` is the nonnegativity
row `x_j ≥ 0` (`IsNonnegRow`) of some `j ∈ N'`; the surplus of any other row (an original row of
`Ax ≥ b`, an upper-bound row, or the bound row of a continuous variable) is not
integer-constrained and keeps `π_j`. (The retired version strengthened whenever `i ∈ N'` as a
*row position*, which strengthens non-integer surplus variables.) -/
noncomputable def PiBar {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (k : Fin n) (Nprime : Finset (Fin n)) (i : Fin n) : ℝ :=
  if ∃ j ∈ Nprime, IsNonnegRow Atil btil (ι i) j then
    min (FracAbar Atil ι k i * (1 - Abar0 Atil btil ι k))
      ((1 - FracAbar Atil ι k i) * Abar0 Atil btil ι k)
  else PiCoef Atil btil ι k i

/-- The strengthened simple disjunctive cut (mixed integer Gomory cut) `π̄^s_J x_J ≥ π0`
(Balas §8.2, eq. (8.10)), viewed as a subset of `x`-space via the same surplus substitution as
`SimpleDisjCutSet`. -/
def StrengthenedSimpleDisjCutSet {n : ℕ} {M : Type*} [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k : Fin n)
    (Nprime : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {x | Pi0 Atil btil ι k ≤ ∑ i, PiBar Atil btil ι k Nprime i * Surplus Atil btil ι i x}

/-- The submatrix of `Ã` indexed by the row set `J` is nonsingular (Balas §8.1, Lemma 8.2, p. 98):
formalized via the existence of *some* enumeration `ι` of `J` whose associated `Â` has nonzero
determinant, which is independent of the choice of enumeration (a row permutation cannot turn a
nonsingular matrix singular). -/
def IsNonsingularSubmatrix {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (J : Finset M) : Prop :=
  ∃ ι : Fin n → M, Function.Injective ι ∧ Finset.image ι Finset.univ = J ∧
    IsUnit (Ahat Atil ι).det

end Disjunctive.CutCorrespondence


