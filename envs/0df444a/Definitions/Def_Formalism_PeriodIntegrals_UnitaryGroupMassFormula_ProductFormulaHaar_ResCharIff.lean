-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:21:10.298387+00:00
-- url     : https://prove2.me/theorems/27c45b15-706b-4071-931e-7f5f318da3ba
-- title:
--   Res Char Iff
-- statement:
--   Definitions and structural lemmas for Res Char Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ResCharIff.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField MeasureTheory ValuativeRel Formalism.MainNotions.S.Loc
namespace PI.ProdFormulaE.St
def HaarAlg : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [Module.Free K A] [Module.Finite K A] [IsModuleTopology K A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (y : A), IsUnit y → ∀ S : Set A,
      μ ((fun z => y * z) '' S) = ENNReal.ofReal (modF K (Algebra.norm K y)) * μ S
def NormLoc : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ι : F →+* K), DenseRange ι →
    (∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) →
    ∀ z : F, modF K (ι z) = FinitePlace.mk p z
def TrInt : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (K : Type) [Field K] [Algebra ℚ_[ℓ] K] [FiniteDimensional ℚ_[ℓ] K]
    (w : K), IsIntegral ℤ w → ‖Algebra.trace ℚ_[ℓ] K w‖ ≤ 1
def ResCharIff : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) (ℓ : ℕ), ℓ.Prime →
    (resChar p = ℓ ↔ ((ℓ : 𝓞 F) ∈ p.asIdeal))
end PI.ProdFormulaE.St
end


