-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:33:06.856808+00:00
-- url     : https://prove2.me/theorems/6ac4a529-f6ce-4bc4-8779-5c98ec9a1803
-- title:
--   Idele Action
-- statement:
--   Definitions and structural lemmas for Idele Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
def localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) (v : HeightOneSpectrum (𝓞 K)) :
    Submodule (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  Submodule.span _ ((fun x : K ↦ (x : v.adicCompletion K)) '' (I : Set K))
namespace IdeleGroup
local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ
instance : MulAction (IdeleGroup K) 𝓘 where
  smul s I := toFractionalIdeal s * I
  one_smul I := by
    change toFractionalIdeal 1 * I = I
    rw [map_one, one_mul]
  mul_smul s t I := by
    change toFractionalIdeal (s * t) * I = toFractionalIdeal s * (toFractionalIdeal t * I)
    rw [map_mul, mul_assoc]
theorem smul_def (s : IdeleGroup K) (I : 𝓘) : s • I = toFractionalIdeal s * I :=
  rfl
instance : IsScalarTower (IdeleGroup K) 𝓘 𝓘 :=
  ⟨fun s I J ↦ by simp only [smul_def, smul_eq_mul, mul_assoc]⟩
instance : SMulCommClass (IdeleGroup K) 𝓘 𝓘 :=
  ⟨fun s I J ↦ by simp only [smul_def, smul_eq_mul, mul_left_comm]⟩
instance : MulAction.IsPretransitive (IdeleGroup K) 𝓘 :=
  ⟨fun I J ↦ by
    obtain ⟨s, hs⟩ := toFractionalIdeal_surjective (J * I⁻¹)
    exact ⟨s, by rw [smul_def, hs, inv_mul_cancel_right]⟩⟩
end IdeleGroup
end
end GroundTheory.Global


