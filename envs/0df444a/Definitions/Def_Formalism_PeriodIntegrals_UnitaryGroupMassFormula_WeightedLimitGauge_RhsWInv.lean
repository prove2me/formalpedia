-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:15.023692+00:00
-- url     : https://prove2.me/theorems/81e70cde-f4f6-54c6-93d5-34dceb2696be
-- title:
--   Rhs WInv
-- statement:
--   Definitions and structural lemmas for Rhs WInv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsWInv.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_HU_lmulM_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
def orbV (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (x : Mt k r) : Fin (2 * r + k + 1) → ℂ := Matrix.of x *ᵥ z'
def rmulM (b : Mat k r) (x : Mt k r) : Mt k r := fun i j => (Matrix.of x * b) i j
def DescUniq : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (μW' : Measure (Mt k r)), IsHaarOn (UWset k r z') μW' →
    μW' Set.univ ≠ ⊤ → ∀ ν₁ ν₂ : Measure (Mt k r), SigmaFinite ν₁ → SigmaFinite ν₂ →
    ν₁ {x | Matrix.of x ∉ UWb k r} = 0 → ν₂ {x | Matrix.of x ∉ UWb k r} = 0 →
    (∀ b ∈ UWset k r z', ν₁.map (rmulM b) = ν₁) → (∀ b ∈ UWset k r z', ν₂.map (rmulM b) = ν₂) →
    ν₁.map (orbV k r z') = ν₂.map (orbV k r z') → ν₁ = ν₂
def RInvNu : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ b ∈ UWset k r z',
      (nuR k r z z' μW μW' μsec).map (rmulM b) = nuR k r z z' μW μW' μsec
def OrbInv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ s ∈ UWb k r, ∀ F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞, Measurable F →
      rhsW k r z z' μW μW' μsec (fun x => F (s *ᵥ orbV k r z' x)) =
        rhsW k r z z' μW μW' μsec (fun x => F (orbV k r z' x))
def lmulE (s : Mat k r) (hs : IsUnit s.det) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM s
  invFun := lmulM s⁻¹
  left_inv x := Matrix.nonsing_inv_mul_cancel_left (A := s) (Matrix.of x) hs
  right_inv x := Matrix.mul_nonsing_inv_cancel_left (A := s) (Matrix.of x) hs
  measurable_toFun := (HU.lmulM_cont s).measurable
  measurable_invFun := (HU.lmulM_cont s⁻¹).measurable
end PI.RhsWLim.W.RI


