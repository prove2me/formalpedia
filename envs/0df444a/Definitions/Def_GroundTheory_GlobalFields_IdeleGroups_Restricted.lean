-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
-- name    : GroundTheory_GlobalFields_IdeleGroups_Restricted
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:40.568276+00:00
-- url     : https://prove2.me/theorems/a0401818-6d97-469b-a0cf-7d10e90dfc1e
-- title:
--   Restricted
-- statement:
--   Definitions and structural lemmas for Restricted, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Restricted.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
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
namespace GroundTheory.Global
open Filter Topology NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
noncomputable section
namespace RestrictedProduct
variable {ι : Type*} {R : ι → Type*} [∀ i, Monoid (R i)] [∀ i, TopologicalSpace (R i)]
  {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)] {B : Π i, S i}
theorem continuous_unitsEquiv_symm :
    Continuous (_root_.RestrictedProduct.unitsEquiv R (B := B) (𝓕 := cofinite)).symm := by
  rw [Units.continuous_iff]
  constructor
  · exact _root_.RestrictedProduct.mapAlong_continuous (fun i ↦ (R i)ˣ) R id tendsto_id
      (A₁ := fun i ↦ ((Submonoid.ofClass (B i)).units : Set (R i)ˣ))
      (A₂ := fun i ↦ (B i : Set (R i)))
      (fun i (u : (R i)ˣ) ↦ (u : R i)) (.of_forall fun _ _ hu ↦ hu.1)
      (fun _ ↦ Units.continuous_val)
  · exact _root_.RestrictedProduct.mapAlong_continuous (fun i ↦ (R i)ˣ) R id tendsto_id
      (A₁ := fun i ↦ ((Submonoid.ofClass (B i)).units : Set (R i)ˣ))
      (A₂ := fun i ↦ (B i : Set (R i)))
      (fun i (u : (R i)ˣ) ↦ ((u⁻¹ : (R i)ˣ) : R i)) (.of_forall fun _ _ hu ↦ hu.2)
      (fun _ ↦ Units.continuous_coe_inv)
theorem continuous_unitsEquiv (hBopen : ∀ i, IsOpen (B i : Set (R i))) :
    Continuous (_root_.RestrictedProduct.unitsEquiv R (B := B) (𝓕 := cofinite)) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  set T : Set ι :=
    {i | _root_.RestrictedProduct.unitsEquiv R x i ∈ (Submonoid.ofClass (B i)).units} with hTdef
  have hT : cofinite ≤ 𝓟 T := le_principal_iff.2 (_root_.RestrictedProduct.unitsEquiv R x).2
  let U : Set (Πʳ i, [R i, B i])ˣ :=
    {y | ∀ i ∈ T, (y : Πʳ i, [R i, B i]) i ∈ B i ∧
      ((y⁻¹ : (Πʳ i, [R i, B i])ˣ) : Πʳ i, [R i, B i]) i ∈ B i}
  have hUo : IsOpen U := by
    have h1 := _root_.RestrictedProduct.isOpen_forall_imp_mem hBopen (p := (· ∈ T))
    have h2 := (h1.preimage Units.continuous_val).inter (h1.preimage Units.continuous_coe_inv)
    convert h2 using 1
    ext y
    simp only [U, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, ← forall_and]
    exact forall_congr' fun i ↦ ⟨fun h hi ↦ h hi, fun h hi ↦ h hi⟩
  have hxU : x ∈ U := fun i hi ↦ hi
  let G : U → Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓟 T] :=
    fun y ↦ ⟨fun i ↦ _root_.RestrictedProduct.unitsEquiv R y.1 i,
      eventually_principal.2 fun i hi ↦ y.2 i hi⟩
  have hG : Continuous G := by
    rw [_root_.RestrictedProduct.continuous_rng_of_principal]
    refine continuous_pi fun i ↦ ?_
    exact (Units.continuous_map (f := _root_.RestrictedProduct.evalMonoidHom R i)
      (_root_.RestrictedProduct.continuous_eval i)).comp continuous_subtype_val
  have hFU : ContinuousOn (_root_.RestrictedProduct.unitsEquiv R (B := B) (𝓕 := cofinite)) U := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (_root_.RestrictedProduct.continuous_inclusion hT).comp hG
  exact hFU.continuousAt (hUo.mem_nhds hxU)
def continuousUnitsEquiv (hBopen : ∀ i, IsOpen (B i : Set (R i))) :
    (Πʳ i, [R i, B i])ˣ ≃ₜ* Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units] where
  toMulEquiv := _root_.RestrictedProduct.unitsEquiv R
  continuous_toFun := continuous_unitsEquiv hBopen
  continuous_invFun := continuous_unitsEquiv_symm
end RestrictedProduct
namespace IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
def finiteUnitsEquiv :
    (FiniteAdeleRing (𝓞 K) K)ˣ ≃ₜ* Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units] :=
  RestrictedProduct.continuousUnitsEquiv (R := fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (B := fun v ↦ v.adicCompletionIntegers K)
    (fun v ↦ Valued.isOpen_valuationSubring (v.adicCompletion K))
def prodRestrictedEquiv :
    IdeleGroup K ≃ₜ* (InfiniteAdeleRing K)ˣ × Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units] :=
  (prodEquiv K).trans
    { toMulEquiv := MulEquiv.prodCongr (MulEquiv.refl _) (finiteUnitsEquiv K).toMulEquiv
      continuous_toFun :=
        continuous_fst.prodMk ((finiteUnitsEquiv K).continuous.comp continuous_snd)
      continuous_invFun :=
        continuous_fst.prodMk ((finiteUnitsEquiv K).symm.continuous.comp continuous_snd) }
end IdeleGroup
end
end GroundTheory.Global


