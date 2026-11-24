-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGenSESStep
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGenSESStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:08.775071+00:00
-- url     : https://prove2.me/theorems/123601f8-ed53-44f1-9c28-f9a76b7ae47a
-- title:
--   PGen SESStep
-- statement:
--   Definitions and structural lemmas for PGen SESStep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGenSESStep.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
namespace GenSESStep
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
section Loc
variable {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M}
abbrev locMap {N : Type*} [AddCommGroup N] [Module (MRingOver S ι) N] (T : Submonoid (MRingOver S ι))
    (f : M →ₗ[MRingOver S ι] N) : LocalizedModule T M →ₗ[MRingOver S ι] LocalizedModule T N :=
  IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N) f
end Loc
end GenSESStep
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


