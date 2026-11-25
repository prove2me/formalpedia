-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_NonvanishingDivisorSum
-- name    : GroundTheory_GlobalFields_TateThesis_NonvanishingDivisorSum
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:56.828659+00:00
-- url     : https://prove2.me/theorems/55a8f11f-004a-5aef-952a-f9715f7df94d
-- title:
--   Nonvanishing Divisor Sum
-- statement:
--   Definitions and structural lemmas for Nonvanishing Divisor Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_coeffTerm_bot
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.HeckeCharacter.coeffTerm_bot
attribute [local simp] GroundTheory.Global.HeckeCharacter.toIdele_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply


set_option autoImplicit false
open NumberField Ideal Complex Filter Topology
namespace GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
theorem finite_setOf_le_of_ne_bot {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    {J : Ideal (𝓞 K) | I ≤ J}.Finite := by
  have hN : absNorm I ≠ 0 := fun h ↦ hI (absNorm_eq_zero_iff.1 h)
  refine (Set.Finite.biUnion (Finset.finite_toSet (Finset.range (absNorm I + 1)))
    fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) k).subset fun J hJ ↦ ?_
  simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio]
  exact ⟨absNorm J, Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hN)
    (absNorm_dvd_absNorm_of_le hJ)), rfl⟩
def idealDivisors (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  if hI : I = ⊥ then ∅ else (finite_setOf_le_of_ne_bot hI).toFinset
def divisorSum (ψ : Ideal (𝓞 K) → ℝ) (I : Ideal (𝓞 K)) : ℝ :=
  ∑ J ∈ idealDivisors I, ψ J
def divisorSumCoeff (ψ : Ideal (𝓞 K) → ℝ) (n : ℕ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, (divisorSum ψ I : ℂ)
end
end GroundTheory.Global


