-- Prove2me | Definitions.Def_Disjunctive_RayCGLP_Tableau
-- name    : Disjunctive_RayCGLP_Tableau
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:54:50.093984+00:00
-- url     : https://prove2.me/theorems/1972c1f6-5cfc-4857-8709-ae3f87da72c4
-- title:
--   Â, γ, the sign-flip step, and the combined-row cut
-- statement:
--   This definition restates the tableau/basis apparatus of `08-cut-correspondence`
--   and `09-simplex-tableau` (`Ahat`, `Bhat`, `Abar0`, `Abar`, `SurplusM`, `GammaOf`) and adds this
--   chapter's own combined-row cut and sign-flip-step notions, needed for Theorem 10.1.
--
--   `IsSignFlipStep k jh jh'` captures rule (b) of Theorem 10.1: the sign of `ā_{k,·}` flips between
--   two consecutive indices of the exchange chain (`ā_{k,jh}>0, ā_{k,jh'}<0`, matching (b1), or the
--   reverse, matching (b2)). `CombinedCutSet k i J γ` is the simple disjunctive cut from `z≤0∨z≥1`
--   (`z:=x_k+γx_i`) applied to the combined source row `(10.1)_γ` (eq. (10.1), p. 122): coefficients
--   `(āk0+γāi0)(1-(āk0+γāi0))` and `max{(1-(āk0+γāi0))(ākj+γāij), -(āk0+γāi0)(ākj+γāij)}`, matching
--   the pattern of `09-simplex-tableau`'s `f⁺,f⁻` construction (the same combined-row device, before
--   scaling by the sum of multipliers) applied at a single fixed `γ` rather than optimized over it.
--
--   **Formalization Note.** `IsSignFlipStep` is the substantive content of rule (b)'s two cases
--   (b1)/(b2) combined via the flip they jointly describe, rather than two separate hypotheses, since
--   the book's own text presents them as the two directions of the same phenomenon ("switches its
--   sign from positive to negative"/"from negative to positive").
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 108, 113, 122, Section 9.1, 9.2, 10.1

import Mathlib

namespace Disjunctive.RayCGLP

/-- `Â`, the `n×n` submatrix of `Ã` whose rows are `ι 0, …, ι (n-1)` (restated locally from
`08-cut-correspondence`/`09-simplex-tableau`). -/
def Ahat {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (ι : Fin n → M) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Atil (ι i) j

/-- `b̂`, the subvector of `b̃` corresponding to `Â` (restated locally). -/
def Bhat {n : ℕ} {M : Type*} (btil : M → ℝ) (ι : Fin n → M) : Fin n → ℝ :=
  fun i => btil (ι i)

/-- `ā_k0 := e_k Â⁻¹ b̂` (restated locally). -/
noncomputable def Abar0 {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (k : Fin n) : ℝ :=
  (Ahat Atil ι)⁻¹.mulVec (Bhat btil ι) k

/-- `ā_kj := -(Â⁻¹)_{kj}` (restated locally). -/
noncomputable def Abar {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (ι : Fin n → M) (k j : Fin n) : ℝ :=
  -((Ahat Atil ι)⁻¹) k j

/-- The surplus (slack) value at an arbitrary row `i : M` (restated locally from
`09-simplex-tableau`'s `SurplusM`). -/
def SurplusM {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (i : M)
    (x : Fin n → ℝ) : ℝ :=
  dotProduct (Atil i) x - btil i

/-- `γ_l := -ā_kl/ā_il` (restated locally from `09-simplex-tableau`'s `GammaOf`). -/
noncomputable def GammaOf {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (ι : Fin n → M) (k i l : Fin n) : ℝ :=
  -(Abar Atil ι k l) / Abar Atil ι i l

/-- One step of rule (b) of Theorem 10.1: the sign of `ā_{k,·}` flips between two consecutive
indices of the exchange chain, matching (b1) (positive to negative) or (b2) (negative to
positive) combined via the flip itself (Balas §10.1, p. 122). -/
def IsSignFlipStep {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (ι : Fin n → M) (k jh jh' : Fin n) : Prop :=
  (0 < Abar Atil ι k jh ∧ Abar Atil ι k jh' < 0) ∨ (Abar Atil ι k jh < 0 ∧ 0 < Abar Atil ι k jh')

/-- The simple disjunctive cut from the disjunction `z ≤ 0 ∨ z ≥ 1` applied to the *combined*
source row `(10.1)_γ` (Balas §10.1, p. 122, eq. (10.1)): `z := x_k + γx_i`, row coefficients
`ā_{kj}+γā_{ij}`, right-hand side `ā_{k0}+γā_{i0}`. -/
def CombinedCutSet {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k i : Fin n)
    (J : Finset (Fin n)) (γ : ℝ) : Set (Fin n → ℝ) :=
  {x | (Abar0 Atil btil ι k + γ * Abar0 Atil btil ι i) *
        (1 - (Abar0 Atil btil ι k + γ * Abar0 Atil btil ι i)) ≤
      ∑ j ∈ J, max ((1 - (Abar0 Atil btil ι k + γ * Abar0 Atil btil ι i)) *
            (Abar Atil ι k j + γ * Abar Atil ι i j))
          (-(Abar0 Atil btil ι k + γ * Abar0 Atil btil ι i) *
            (Abar Atil ι k j + γ * Abar Atil ι i j)) *
        SurplusM Atil btil (ι j) x}

end Disjunctive.RayCGLP


