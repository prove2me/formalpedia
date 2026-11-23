-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:13.121699+00:00
-- url     : https://prove2.me/theorems/44093c88-3516-43b9-bf8c-a26f353fb108
-- title:
--   Unitary Model Of Multiplicity Garding Density
-- statement:
--   Definitions and structural lemmas for Unitary Model Of Multiplicity Garding Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/UnitaryModelOfMultiplicityGardingDensity.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_HCMult
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff
noncomputable section
namespace PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Defs
variable {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def gv (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (x : H) : H :=
  ∫ h, Φ (umat h) • τ (umat h) x ∂(muG ε)
def SmoothJ (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H) : Prop :=
  SmoothOnH (Jm ε) (fun g => τ g y)
end Defs
def StepGarding : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ →
    ∀ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
      ∀ x : H, SmoothJ ε τ (gv ε τ Φ x)
def StepDense : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ →
    ∀ (u : H) (δ : ℝ), 0 < δ →
      ∃ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ ‖gv ε τ Φ u - u‖ < δ
def StepKAvg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ →
    ∀ (ν : Measure (UJ ε)), IsFiniteMeasure ν → ν ((KG ε : Set (UJ ε))ᶜ) = 0 →
    ∀ c : UJ ε → ℂ, Continuous c →
    ∀ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ → ∀ x : H,
      ∃ Φ' : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ' ∧ HasCompactSupport Φ' ∧
        ∫ g, c g • τ (umat g) (gv ε τ Φ x) ∂ν = gv ε τ Φ' x
def StepKHaar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ ν : Measure (UJ ε), IsFiniteMeasure ν ∧ ν Set.univ ≠ 0 ∧
    ν ((KG ε : Set (UJ ε))ᶜ) = 0 ∧ ∀ a ∈ KG ε, ν.map (fun g => a * g) = ν
def StepJModel : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ → IsIrredOn (UJset ε) τ →
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε τ S → ∀ v ∈ S, SmoothJ ε τ v
def StepTopJ : Prop :=
  PI.HCMult → StepGarding → StepDense → StepKAvg → StepKHaar → StepJModel
def StepTransport : Prop := StepJModel → PI.KFinSmooth
def StepConjInv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∀ a ∈ KG ε, (muG ε).map (fun g => a * g * a⁻¹) = muG ε
def StepDenseW : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ →
    ∀ W : Submodule ℂ H, FiniteDimensional ℂ W →
      ∃ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
        (∀ a ∈ Kset ε, ∀ m, Φ (a * m * aᴴ) = Φ m) ∧
        ∀ w ∈ W, ‖gv ε τ Φ w - w‖ ≤ ‖w‖ / 2
def UnitaryModelOfMultiplicityGardingDensity : Prop :=
  PI.HCMult → StepGarding → StepConjInv → StepDenseW → StepJModel
end PI.KFinSmoothW


