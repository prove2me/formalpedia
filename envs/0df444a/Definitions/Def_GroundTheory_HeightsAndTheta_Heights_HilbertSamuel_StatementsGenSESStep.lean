-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:06.542458+00:00
-- url     : https://prove2.me/theorems/688e07a0-fe1d-4e93-9df8-af83fa3713d6
-- title:
--   Statements Gen SESStep
-- statement:
--   Definitions and structural lemmas for Statements Gen SESStep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsGenSESStep.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
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
def GenSESStep.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M' : Type) [AddCommGroup M'] [Module (MRingOver S ι) M'] [Module S M']
    [IsScalarTower S (MRingOver S ι) M'] (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (M'' : Type) [AddCommGroup M''] [Module (MRingOver S ι) M''] [Module S M'']
    [IsScalarTower S (MRingOver S ι) M'']
    (𝓜' : (K → ℤ) → Submodule S M') (𝓜 : (K → ℤ) → Submodule S M) (𝓜'' : (K → ℤ) → Submodule S M'')
    (g : M' →ₗ[MRingOver S ι] M) (h : M →ₗ[MRingOver S ι] M''),
    KH.IsMGraded S ι 𝓜' → KH.IsMGraded S ι 𝓜 → KH.IsMGraded S ι 𝓜'' →
    KH.IsMGradedMap S ι 𝓜' 𝓜 g → KH.IsMGradedMap S ι 𝓜 𝓜'' h →
    Function.Injective g → Function.Surjective h → LinearMap.range g = LinearMap.ker h →
    ∀ d : K → ℤ, Subsingleton (KH.cechHc ι 𝓜' d 1) → GeneratedMod S ι 𝓜' d → GeneratedMod S ι 𝓜'' d →
      GeneratedMod S ι 𝓜 d
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


