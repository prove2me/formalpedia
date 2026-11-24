-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Development
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:23:51.969298+00:00
-- url     : https://prove2.me/theorems/f5d8867a-9583-4f72-9864-fc66c6d91ba7
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/Development.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section
namespace QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def SmoothOnSet {n : ℕ} (G : Set (Matrix (Fin n) (Fin n) ℂ)) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ g₀ ∈ G, ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ G → f g = F g
def StepGroup : Prop :=
  ∀ (k r : ℕ) (i : Fin (r + 1)) (X : Mx k r), inLieLev k r i X →
    IsClosed (Glev k r i) ∧ (∀ g ∈ Glev k r i, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i) ∧
      ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i
def StepAnalytic : Prop :=
  ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)) (μ : Measure (Fin n → Fin n → ℂ)) (X : Matrix (Fin n) (Fin n) ℂ)
    (f₁ f₂ : Matrix (Fin n) (Fin n) ℂ → ℂ),
    IsClosed G → (∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G) → μ Gᶜ = 0 →
    (∀ t : ℝ, μ.map (B.rmulF (NormedSpace.exp ((t : ℂ) • X))) = μ) →
    (∀ K : Set (Fin n → Fin n → ℂ), IsCompact K → μ K < ⊤) →
    SmoothOnSet G f₁ → SmoothOnSet G f₂ →
    (∃ K : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact K ∧ ∀ g ∈ G, g ∉ K → f₁ g = 0) →
    (∃ K : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact K ∧ ∀ g ∈ G, g ∉ K → f₂ g = 0) →
    (∫ x, RdV X f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
      -∫ x, f₁ (Matrix.of x) * star (RdV X f₂ (Matrix.of x)) ∂μ
end QnRdSkewW


