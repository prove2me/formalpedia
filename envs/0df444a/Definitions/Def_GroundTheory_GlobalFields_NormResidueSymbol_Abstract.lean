-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_Abstract
-- name    : GroundTheory_GlobalFields_NormResidueSymbol_Abstract
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:31:06.275061+00:00
-- url     : https://prove2.me/theorems/37a71b85-8067-419a-bf23-0802c80736c2
-- title:
--   Abstract
-- statement:
--   Definitions and structural lemmas for Abstract, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/Abstract.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_Adele_IdeleBasis
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_eq
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding_of_ne
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding_of_ne
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_units_adicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isTopologicalBasis
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_isTopologicalBasis
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
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
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
namespace GroundTheory.Global
open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
noncomputable section
namespace IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
theorem eventually_finiteProj_mem_units (x : IdeleGroup K) :
    ∀ᶠ v in cofinite, finiteProj v x ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  filter_upwards [(prodRestrictedEquiv K x).2.2] with v hv
  rw [finiteProj_eq]
  exact hv
end IdeleGroup
namespace IdeleMap
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)
theorem hasFiniteMulSupport
    (hφ : ∀ᶠ v in cofinite, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)
    (x : IdeleGroup K) :
    Function.HasFiniteMulSupport fun v ↦ φ v (finiteProj v x) := by
  have h : ∀ᶠ v in cofinite, φ v (finiteProj v x) = 1 := by
    filter_upwards [hφ, eventually_finiteProj_mem_units x] with v hv hx
    exact hv hx
  exact eventually_cofinite.1 h
def ideleMap
    (hφ : ∀ᶠ v in cofinite, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker) :
    IdeleGroup K →* G where
  toFun x := (∏ᶠ v, φ v (finiteProj v x)) * ∏ w, φinf w (infiniteProj w x)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    rw [finprod_mul_distrib (hasFiniteMulSupport φ hφ x) (hasFiniteMulSupport φ hφ y),
      Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _
variable (hφ : ∀ᶠ v in cofinite,
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)
theorem ideleMap_apply (x : IdeleGroup K) :
    ideleMap φ φinf hφ x = (∏ᶠ v, φ v (finiteProj v x)) * ∏ w, φinf w (infiniteProj w x) :=
  rfl
@[simp]
theorem ideleMap_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ideleMap φ φinf hφ (finiteEmbedding v a) = φ v a := by
  rw [ideleMap_apply, finprod_eq_single _ v fun u hu ↦ by
    rw [finiteProj_finiteEmbedding_of_ne hu, map_one]]
  have h : ∀ w, infiniteProj w (finiteEmbedding v a) = 1 := fun w ↦ Units.ext rfl
  simp [h]
@[simp]
theorem ideleMap_infiniteEmbedding (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ideleMap φ φinf hφ (infiniteEmbedding w a) = φinf w a := by
  rw [ideleMap_apply, Finset.prod_eq_single w (fun u _ hu ↦ by
    rw [infiniteProj_infiniteEmbedding_of_ne hu, map_one]) (fun h ↦ (h (Finset.mem_univ w)).elim)]
  have h : ∀ v, finiteProj v (infiniteEmbedding w a) = 1 := fun v ↦ Units.ext rfl
  simp [h]
theorem ideleMap_eq_one_of_forall_mem
    (N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
    (Ninf : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)
    (hN : ∀ v, N v ≤ (φ v).ker) (hNinf : ∀ w, Ninf w ≤ (φinf w).ker) {x : IdeleGroup K}
    (hx : ∀ v, finiteProj v x ∈ N v) (hxinf : ∀ w, infiniteProj w x ∈ Ninf w) :
    ideleMap φ φinf hφ x = 1 := by
  rw [ideleMap_apply, finprod_eq_one_of_forall_eq_one fun v ↦ hN v (hx v),
    Finset.prod_eq_one fun w _ ↦ hNinf w (hxinf w), mul_one]
variable [TopologicalSpace G] [DiscreteTopology G]
theorem continuous_ideleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w)) :
    Continuous (ideleMap φ φinf hφ) := by
  have hker : ∀ {X : Type _} [TopologicalSpace X] [Group X] (f : X →* G), Continuous f →
      IsOpen (f.ker : Set X) := fun f hf ↦ by
    rw [MonoidHom.coe_ker]
    exact (isOpen_discrete ({1} : Set G)).preimage hf
  set V : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)ˣ := fun v ↦
    ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) ∩
      ((φ v).ker : Set (v.adicCompletion K)ˣ) with hVdef
  set W : Set (IdeleGroup K) :=
    {x | (∀ w, infiniteProj w x ∈ ((φinf w).ker : Set (w.Completion)ˣ)) ∧
      ∀ v, finiteProj v x ∈ V v} with hWdef
  have hWo : IsOpen W := (isTopologicalBasis K).isOpen
    ⟨fun w ↦ ((φinf w).ker : Set (w.Completion)ˣ), V, fun w ↦ hker _ (hφinfc w),
      fun v ↦ (isOpen_units_adicCompletionIntegers K v).inter (hker _ (hφc v)),
      hφ.mono fun v hv ↦ Set.inter_eq_left.2 (SetLike.coe_subset_coe.2 hv), rfl⟩
  have h1W : (1 : IdeleGroup K) ∈ W :=
    ⟨fun w ↦ by simp, fun v ↦ by simp [V]⟩
  have hψW : ∀ x ∈ W, ideleMap φ φinf hφ x = 1 := fun x hx ↦
    ideleMap_eq_one_of_forall_mem φ φinf hφ (fun v ↦ (φ v).ker) (fun w ↦ (φinf w).ker)
      (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) (fun v ↦ (hx.2 v).2) hx.1
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one, nhds_discrete G, tendsto_pure]
  exact eventually_of_mem (hWo.mem_nhds h1W) hψW
def continuousIdeleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w)) :
    IdeleGroup K →ₜ* G where
  toMonoidHom := ideleMap φ φinf hφ
  continuous_toFun := continuous_ideleMap φ φinf hφ hφc hφinfc
end IdeleMap
end
end GroundTheory.Global


