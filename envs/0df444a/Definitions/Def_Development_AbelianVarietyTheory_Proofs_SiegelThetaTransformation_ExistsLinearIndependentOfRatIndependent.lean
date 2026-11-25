-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:01.082864+00:00
-- url     : https://prove2.me/theorems/b6fb5e78-a88b-49b4-b27d-21ecbf701c2f
-- title:
--   Exists Linear Independent Of Rat Independent
-- statement:
--   Definitions and structural lemmas for Exists Linear Independent Of Rat Independent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot


set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW
noncomputable def rowEmb {E m n : Type} [Field E] [Fintype n] (W : Matrix n m E) :
    (n → E) →ₗ[ℤ] EuclideanSpace ℂ ((E →+* ℂ) × m) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun t => WithLp.toLp 2 fun p => p.1 ((t ᵥ* W) p.2)
      map_zero' := by ext p; simp
      map_add' := fun s t => by ext p; simp [add_vecMul] }
end GlobalTheory.SW


