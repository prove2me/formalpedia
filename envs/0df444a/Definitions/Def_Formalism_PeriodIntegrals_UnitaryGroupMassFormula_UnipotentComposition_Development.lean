-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:13:52.189155+00:00
-- url     : https://prove2.me/theorems/fd3c09b5-cfde-425d-85dd-2831a46a4466
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_hsVec_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def DegDP : Prop := ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (q : MvPolynomial (Vr N) ℂ),
  (dP X q).totalDegree ≤ q.totalDegree
def DegD : Prop := ∀ k j ρ : ℕ, (qD k j ρ).totalDegree ≤ j ∧ (qDb k j ρ).totalDegree ≤ j
def Expand : Prop := ∀ (k j ρ : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ)
    (F : Mat k (j + ρ) → E), CkOn (m : ℕ∞) (GV k (j + ρ)) F →
    ∀ (w : List (Mat k (j + ρ))) (L : FS k (j + ρ)), (∀ X ∈ w, inLie k (j + ρ) X) →
    (∀ e ∈ L, ∀ X ∈ e.2, inLie k (j + ρ) X) → (∀ e ∈ L, e.2.length + w.length ≤ m) →
    ∀ g ∈ GV k (j + ρ), DjU k j ρ g ≠ 0 →
      Rw w (shape k j ρ F L) g = shape k j ρ F (steps k j ρ w L) g
def Bd (k j ρ κ ℓ : ℕ) (L : FS k (j + ρ)) : Prop :=
  ∀ e ∈ L, e.1.1.totalDegree ≤ κ ∧ e.2.length ≤ ℓ ∧ ∀ X ∈ e.2, inLie k (j + ρ) X
section ops
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : hsVec (c • A) = c • hsVec A := by
  unfold hsVec
  ext i
  simp
open Classical in

def mkTerm (k j ρ : ℕ) (e : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ))) : DTerm k (j + ρ) Wp Wq where
  coef g := sv k j ρ e.1 g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  coefAdj g := (starRingEnd ℂ) (sv k j ρ e.1 g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  word := if ∀ X ∈ e.2, inLie k (j + ρ) X then e.2 else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := by
    intro x A B
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hsInner, hsVec_smul,
      inner_smul_right, inner_smul_left, Complex.conj_conj]
end ops
section sums
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end sums
end PI.UnitaryGroupMassFormula.UsCompose


