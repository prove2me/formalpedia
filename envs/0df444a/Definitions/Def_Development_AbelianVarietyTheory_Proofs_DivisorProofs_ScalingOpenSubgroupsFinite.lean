-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScalingOpenSubgroupsFinite
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScalingOpenSubgroupsFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:57.053805+00:00
-- url     : https://prove2.me/theorems/4be5b2d5-3f9f-47e6-8ccc-7e4cb15dbaed
-- title:
--   Scaling Open Subgroups Finite
-- statement:
--   Definitions and structural lemmas for Scaling Open Subgroups Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScalingOpenSubgroupsFinite.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.BoxCosetSum
variable {F : Type} [Field F] [NumberField F]
def boxSub (κ : Type) (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)) :
    AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {u | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v}
  add_mem' := by
    intro a b ha hb i v
    simp only [Pi.add_apply, map_add]
    exact (B v).add_mem (ha i v) (hb i v)
  zero_mem' := by
    intro i v
    simp only [Pi.zero_apply, map_zero]
    exact (B v).zero_mem
  neg_mem' := by
    intro a ha i v
    simp only [Pi.neg_apply, map_neg]
    exact (B v).neg_mem (ha i v)
end GlobalTheory.BoxCosetSum
end


