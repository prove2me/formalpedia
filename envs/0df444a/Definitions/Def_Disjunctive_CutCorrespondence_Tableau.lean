-- Prove2me | Definitions.Def_Disjunctive_CutCorrespondence_Tableau
-- name    : Disjunctive_CutCorrespondence_Tableau
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:44:46.568263+00:00
-- url     : https://prove2.me/theorems/572ee1f8-8927-4c14-8948-a7e677cae11f
-- title:
--   The basis Â, ā_k0, the simple disjunctive cut, and its strengthening
-- statement:
--   This definition fixes the tableau/basis apparatus of Section 8.1 — the nonsingular
--   submatrix `Â`, the resulting cut coefficients `π¹,π²,π,π0`, and the simple disjunctive cut itself
--   — and its strengthening from Section 8.2.
--
--   Given an explicit enumeration `ι : Fin n → M` of an `n`-element row set `J ⊆ M` (rather than a
--   bare `Finset M`, so that `Â := (i,j) ↦ Ã_{ι i, j}` is a genuine square `Matrix (Fin n) (Fin n) ℝ`),
--   `Abar0`/`Abar` are `ā_k0 := e_kÂ⁻¹b̂` and `ā_kj := -(Â⁻¹)_{kj}` (eq. (8.5)-(8.6)); `Pi1`/`Pi2`/`Pi0`/
--   `PiCoef` are `π¹_j,π²_j,π0,π_j:=max{π¹_j,π²_j}` (eq. (8.7)-(8.8)). `Surplus` is the slack value
--   `s_j := (Ãx)_j - b̃_j` at row `ι i`, a genuine affine function of `x` for *every* row (bound or
--   original) — see `MODERATION_NOTES.md` for why this, not a literal `x_j` substitution, is used to
--   view `SimpleDisjCutSet` (the cut `π^s_Jx_J≥π0`) as a subset of the original `x`-space. `FracAbar`
--   is the fractional part `f_kj` used, without restatement, by the book's own strengthened-cut
--   formula (8.10); `PiBar`/`StrengthenedSimpleDisjCutSet` implement that formula. `IsNonsingularSubmatrix`
--   states nonsingularity of the submatrix indexed by a bare `Finset M`, via the existence of some
--   enumeration witnessing it (Lemma 8.2's conclusion).
--
--   **Formalization Note (see `MODERATION_NOTES.md` for the full account).** `PiBar`'s `Nprime`
--   parameter is a `Finset` of row-*positions* (`Fin n`), not of variables, since the book's own
--   "`j∈J∩N'`" test relies on an identification between certain rows and certain variables that this
--   mission's abstract row type `M` does not track; this is stated explicitly as a judgment call.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 98-103, Section 8.1-8.2

import Mathlib

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

/-- `π̄_j`, the strengthened cut coefficients of eq. (8.10) (Balas §8.2, p. 103): `min{f_kj(1-ā_k0),
(1-f_kj)ā_k0}` for row-position `i` (via `ι`) in the 0-1 row-position set `Nprime`, `π_j`
otherwise. **`Nprime` here is a `Finset` of row-*positions*, not of variables**: see
`MODERATION_NOTES.md` for why "j ∈ J∩N'" (a row-vs-variable identification specific to the
book's own m+p+n-row augmented matrix, which this mission's abstract row type does not track) is
formalized this way. -/
noncomputable def PiBar {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (k : Fin n) (Nprime : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ Nprime then
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


