-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SigmaMul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SigmaMul
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:23:34.767128+00:00
-- url     : https://prove2.me/theorems/af76aadb-ebc6-4c6f-a79d-d91e81a07844
-- title:
--   Sigma Mul
-- statement:
--   Definitions and structural lemmas for Sigma Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselSquareIntegrable/SigmaMul.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselL2FixAtZero
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
def SchurVec : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
  ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
    Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • σ (x * Matrix.of g) w) μG ∧
    ∫ g, eFun μG σ w (Matrix.of g) • σ (x * Matrix.of g) w ∂μG = σ x w
def BesselFun : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b → GapC 0 k r b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r),
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS →
    IsQuotMeas μG μS ν →
  ∃ ℓ : H →ₗ[ℂ] Vp,
    (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      ℓ (σ h (σ m (σ g w))) = psiGen k r z c m • π h (ℓ (σ g w))) ∧
    AEStronglyMeasurable (fun x => ℓ (σ (Matrix.of x) w)) μG ∧
    AEStronglyMeasurable (fun x => ℓ (σ (Matrix.of x) w)) ν ∧
    l2SG ν (fun g => ℓ (σ g w)) < ⊤ ∧ l2SG ν (fun g => ℓ (σ g w)) ≠ 0 ∧
    ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      ∫ g, eFun μG σ w (Matrix.of g) • ℓ (σ (x * Matrix.of g) w) ∂μG =
        ℓ (∫ g, eFun μG σ w (Matrix.of g) • σ (x * Matrix.of g) w ∂μG)
end PI.UnitaryGroupMassFormula.BesselL2FixAtZero


