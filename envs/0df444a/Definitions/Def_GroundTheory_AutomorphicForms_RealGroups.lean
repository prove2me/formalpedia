-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_RealGroups
-- name    : GroundTheory_AutomorphicForms_RealGroups
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:31.834972+00:00
-- url     : https://prove2.me/theorems/4355f29f-0326-48b0-bd21-a4e927194365
-- title:
--   Real Groups
-- statement:
--   Definitions and structural lemmas for Real Groups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroups.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsKAK
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawaHaar
import Theorems.Thm_GroundTheory_Automorphic_coe_iwasawaHomeomorph_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply


set_option autoImplicit false
namespace GroundTheory.Automorphic
open Matrix Set
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {n : Type*} [Fintype n] [LinearOrder n]
section HaarKBComplex
open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator
instance : SecondCountableTopology (Matrix n n ℂ) :=
  inferInstanceAs (SecondCountableTopology (n → n → ℂ))
instance : SecondCountableTopology (GL n ℂ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℂ)).isEmbedding.secondCountableTopology
instance : LocallyCompactSpace (GL n ℂ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℂ)).locallyCompactSpace
instance : SecondCountableTopology (upperPosSubgroup n ℂ) :=
  TopologicalSpace.Subtype.secondCountableTopology _
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
theorem isClosed_upperPosSubgroupC : IsClosed (upperPosSubgroup n ℂ : Set (GL n ℂ)) := by
  have e : (upperPosSubgroup n ℂ : Set (GL n ℂ)) =
      (⋂ i, ⋂ j, {g : GL n ℂ | j < i → (g : Matrix n n ℂ) i j = 0}) ∩
        ⋂ i, {g : GL n ℂ | 0 ≤ (g : Matrix n n ℂ) i i} := by
    ext g
    simp only [SetLike.mem_coe, mem_upperPosSubgroup, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro ⟨hU, hpos⟩; exact ⟨fun i j h => hU h, fun i => (hpos i).le⟩
    · rintro ⟨hU, hnn⟩
      have hU' : (g : Matrix n n ℂ).IsUpperTriangular := fun i j h => hU i j h
      refine ⟨hU', fun i => lt_of_le_of_ne (hnn i) (Ne.symm ?_)⟩
      have hdet := ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
      rw [det_of_isUpperTriangular hU'] at hdet
      exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
    (isClosed_iInter fun i => ?_)
  · by_cases h : j < i
    · simp only [h, forall_const]
      exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
    · simp only [h, IsEmpty.forall_iff, ofPred_true, isClosed_univ]
  · exact isClosed_le continuous_const (Units.continuous_val.matrix_elem i i)
instance : LocallyCompactSpace (upperPosSubgroup n ℂ) :=
  isClosed_upperPosSubgroupC.locallyCompactSpace
noncomputable def kbInvHomeomorphC : GL n ℂ ≃ₜ unitaryGroup n ℂ × upperPosSubgroup n ℂ :=
  kbHomeomorph.symm.trans ((Homeomorph.refl _).prodCongr (Homeomorph.inv _))
end HaarKBComplex
end GroundTheory.Automorphic


