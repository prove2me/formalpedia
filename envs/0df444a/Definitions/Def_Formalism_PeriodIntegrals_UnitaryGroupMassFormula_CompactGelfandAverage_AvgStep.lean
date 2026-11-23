-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:55.967569+00:00
-- url     : https://prove2.me/theorems/7263dad8-8756-4208-8b77-a99b89f9d397
-- title:
--   Avg Step
-- statement:
--   Definitions and structural lemmas for Avg Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/AvgStep.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.GelfCpt
open MeasureTheory Matrix
def intMat {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) {N : ℕ}
    (ρ : G →* GL (Fin N) ℂ) (f : G → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => ∫ g, f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ
def AvgStep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (N : ℕ) (ρ : G →* GL (Fin N) ℂ), PI.UMultOne.Cont ρ →
    ∀ f : G → ℂ, Continuous f →
      (∀ h ∈ H, ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * intMat μ ρ f =
        intMat μ ρ f * ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) →
      ∃ f' : G → ℂ, Continuous f' ∧ (∀ h ∈ H, ∀ x, f' (h * x * h⁻¹) = f' x) ∧
        intMat μ ρ f' = intMat μ ρ f
def MulStep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (N : ℕ) (ρ : G →* GL (Fin N) ℂ), PI.UMultOne.Cont ρ →
    ∀ f₁ f₂ : G → ℂ, Continuous f₁ → Continuous f₂ →
      intMat μ ρ f₁ * intMat μ ρ f₂ = intMat μ ρ (fun z => ∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ)
end PI.UnitaryGroupMassFormula.GelfCpt


