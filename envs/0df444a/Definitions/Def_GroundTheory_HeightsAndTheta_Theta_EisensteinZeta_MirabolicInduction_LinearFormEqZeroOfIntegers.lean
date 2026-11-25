-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:58:32.16866+00:00
-- url     : https://prove2.me/theorems/e7e12bf3-9fbc-5807-bab9-edbab2557a79
-- title:
--   Linear Form Eq Zero Of Integers
-- statement:
--   Definitions and structural lemmas for Linear Form Eq Zero Of Integers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Theta
namespace UnitaryReduction
namespace DualHomPf
open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace NumberField.InfinitePlace
open scoped InnerProductSpace nonZeroDivisors ComplexConjugate
section NumberFieldFacts
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
open Classical
end NumberFieldFacts
section DualLattice
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
end DualLattice
section DualBasis
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
end DualBasis
section DualBasis2
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
end DualBasis2
section Fibres
variable {E : Type} [Field E] [NumberField E]
variable (S : MetSpace E) (τ : InfinitePlace E)
def fibFun (σ : S.V →ₗ[E] E) : S.FibSp τ →ₗ[ℂ] ℂ :=
  (S.dualFunctional τ ((1 : CAt τ.embedding) ⊗ₜ[E] σ) : S.FibSp τ →L[ℂ] ℂ)
end Fibres
section Adjoints
variable {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [FiniteDimensional ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]
end Adjoints
section IdealMaps
variable {E : Type} [Field E] [NumberField E]
variable {V V' : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']
end IdealMaps
section FibMaps
variable {E : Type} [Field E] [NumberField E]
end FibMaps
end DualHomPf
open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace DualHomPf
open scoped InnerProductSpace nonZeroDivisors
end UnitaryReduction
end GroundTheory.Heights₂.Theta


