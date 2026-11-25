-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DecSmoothAtGapOfDecSmooth
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_DecSmoothAtGapOfDecSmooth
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:10:18.013529+00:00
-- url     : https://prove2.me/theorems/1f41ae8e-9f31-4d58-bb12-065753abbdbe
-- title:
--   Dec Smooth At Gap Of Dec Smooth
-- statement:
--   Definitions and structural lemmas for Dec Smooth At Gap Of Dec Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DecSmoothAtGapOfDecSmooth.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SideNormalisedGap
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_LieMatrixVectors
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_KFinDecayOfDecInf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SigmaFiniteOfPosLintegralNeTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SideCompare
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)
open PI.BesselPeriodGGP (IsHaarOn IsQuotMeas)
open Formalism.FourierDecayAlt GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap (Mat decExp decConst dimV dimN thrG thrS thrSS propExp DecGap Size Thresholds muS mulP IsSide
  IsSideNormalised KFinDecay wordSeminorm DecKFin DecSmooth)
section Side
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
  (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
  (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r))
end Side
section Decay
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def LowDecay (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ w₁ w₂ : H, IsLowUnitH k r ε lam σ w₁ → IsLowUnitH k r ε lam σ w₂ →
    ∃ C : ℝ, ∀ x ∈ UH (Hpk k r), ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ C * gN x ^ (-a)
def SmoothDecay (k r : ℕ) (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ v₀ : H, IsKFinHpk (k := k) (r := r) σ v₀ →
    ∃ (C : ℝ) (Ws : List (List (Mat k r))), (∀ D ∈ Ws, ∀ X ∈ D, InLieHpk k r X) ∧
      ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ x ∈ UH (Hpk k r),
        ‖⟪v₀, σ x w⟫_ℂ‖ ≤ C * wordSeminorm σ Ws w * gN x ^ (1 - a)
end Decay
def DecLowWeak : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    1 ≤ k → IsHCParam lam → IsDSHpk k r ε lam σ → GapAtLeast ε lam h → 120 * dimV k r ^ 3 ≤ h →
    LowDecay k r ε lam σ (decExp r h)
def DecSmoothAtGap : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    IsHCParam lam → IsDSHpk k r ε lam σ → GapAtLeast ε lam h → ThreeDimData.GapOK k r h →
    KFinDecay k r σ (decExp r h) → SmoothDecay k r σ (decExp r h)
end GlobalTheory.SideCompare


