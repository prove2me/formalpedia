-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:28:28.812568+00:00
-- url     : https://prove2.me/theorems/e750242c-e661-4963-bfd0-6505141dd584
-- title:
--   Schur Hpk Alt
-- statement:
--   Definitions and structural lemmas for Schur Hpk Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselSquareIntegrable/SchurHpkAlt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselL2FixAtZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SigmaMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.BesselL2FixAtZero
open MeasureTheory Matrix
open scoped InnerProductSpace
open PI.UpqRep PI.BesselL2FixAtZero
def EIntVec : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
  ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
    Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • σ (x * Matrix.of g) w) μG
def SchurHpk : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
  ∃ d : ℝ, 0 < d ∧ ∀ v₁ w₁ v₂ w₂ : H,
    Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
      ⟪w₁, σ (Matrix.of g) v₁⟫_ℂ * star ⟪w₂, σ (Matrix.of g) v₂⟫_ℂ) μG ∧
    ∫ g, ⟪w₁, σ (Matrix.of g) v₁⟫_ℂ * star ⟪w₂, σ (Matrix.of g) v₂⟫_ℂ ∂μG =
      ⟪v₂, v₁⟫_ℂ * ⟪w₁, w₂⟫_ℂ / (d : ℂ)
end PI.UnitaryGroupMassFormula.BesselL2FixAtZero


