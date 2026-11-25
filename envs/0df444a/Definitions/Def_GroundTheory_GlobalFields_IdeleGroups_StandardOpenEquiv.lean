-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
-- name    : GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:54.018898+00:00
-- url     : https://prove2.me/theorems/74af756f-1424-4ef2-aa21-a50a850320d9
-- title:
--   Standard Open Equiv
-- statement:
--   Definitions and structural lemmas for Standard Open Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/StandardOpenEquiv.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_continuous_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_toInfinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup
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
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing
noncomputable section
def unitsContinuousMulEquiv {A B : Type*} [Monoid A] [Monoid B] [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃* B) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    Aˣ ≃ₜ* Bˣ where
  toMulEquiv := Units.mapEquiv e
  continuous_toFun := Units.continuous_map (f := e.toMonoidHom) h₁
  continuous_invFun := Units.continuous_map (f := e.symm.toMonoidHom) h₂
def continuousMulEquivProdCongr {A B C D : Type*} [Monoid A] [Monoid B] [Monoid C] [Monoid D]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    (e₁ : A ≃ₜ* B) (e₂ : C ≃ₜ* D) : A × C ≃ₜ* B × D where
  toMulEquiv := MulEquiv.prodCongr e₁.toMulEquiv e₂.toMulEquiv
  continuous_toFun := by
    exact (e₁.continuous.comp continuous_fst).prodMk (e₂.continuous.comp continuous_snd)
  continuous_invFun := by
    exact (e₁.symm.continuous.comp continuous_fst).prodMk (e₂.symm.continuous.comp continuous_snd)
def openSubgroupEquivQuotient {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H N : Subgroup G) (hH : IsOpen (H : Set G)) (hinf : H ⊓ N = ⊥)
    (hsup : H ⊔ N = ⊤) : H ≃ₜ* G ⧸ N :=
  let f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have h2 : (h : G) ∈ H ⊓ N := ⟨h.2, (QuotientGroup.eq_one_iff _).1 hh⟩
    rw [hinf, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hg : g ∈ H ⊔ N := hsup ▸ Subgroup.mem_top g
    obtain ⟨h, hh, n, hn, rfl⟩ := Subgroup.mem_sup.1 hg
    refine ⟨⟨h, hh⟩, ?_⟩
    show ((h : G) : G ⧸ N) = ((h * n : G) : G ⧸ N)
    exact QuotientGroup.eq.2 (by rwa [inv_mul_cancel_left])
  let e : H ≃* G ⧸ N := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have hc : Continuous e := QuotientGroup.continuous_mk.comp continuous_subtype_val
  have ho : IsOpenMap e := QuotientGroup.isOpenMap_coe.comp hH.isOpenMap_subtype_val
  { toMulEquiv := e
    continuous_toFun := hc
    continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous }
@[simp]
theorem openSubgroupEquivQuotient_apply {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H N : Subgroup G) (hH : IsOpen (H : Set G)) (hinf : H ⊓ N = ⊥)
    (hsup : H ⊔ N = ⊤) (h : H) :
    openSubgroupEquivQuotient H N hH hinf hsup h = ((h : G) : G ⧸ N) :=
  rfl
namespace IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
def localIntegerUnit (v : HeightOneSpectrum (𝓞 K)) (x : standardOpenSubgroup K) :
    (v.adicCompletionIntegers K)ˣ where
  val := ⟨((x : IdeleGroup K) : 𝔸[K]).2 v, ((mem_standardOpenSubgroup K).1 x.2 v).1⟩
  inv := ⟨(((x : IdeleGroup K)⁻¹ : IdeleGroup K) : 𝔸[K]).2 v,
    ((mem_standardOpenSubgroup K).1 x.2 v).2⟩
  val_inv := Subtype.ext (congrArg (fun y : 𝔸[K] ↦ y.2 v) (x : IdeleGroup K).mul_inv)
  inv_val := Subtype.ext (congrArg (fun y : 𝔸[K] ↦ y.2 v) (x : IdeleGroup K).inv_mul)
@[simp]
theorem coe_localIntegerUnit (v : HeightOneSpectrum (𝓞 K)) (x : standardOpenSubgroup K) :
    (((localIntegerUnit v x : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
      v.adicCompletion K) = ((x : IdeleGroup K) : 𝔸[K]).2 v :=
  rfl
theorem continuous_localIntegerUnit (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (localIntegerUnit (K := K) v) := by
  rw [Units.continuous_iff]
  constructor
  · exact ((Units.continuous_val.comp (continuous_finiteProj v)).comp
      continuous_subtype_val).subtype_mk _
  · exact ((Units.continuous_coe_inv.comp (continuous_finiteProj v)).comp
      continuous_subtype_val).subtype_mk _
def ofIntegerUnits (a : (InfiniteAdeleRing K)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) : IdeleGroup K where
  val := ((a : InfiniteAdeleRing K),
    _root_.RestrictedProduct.structureMap _ _ _ fun v ↦ (u v : v.adicCompletionIntegers K))
  inv := (((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
    _root_.RestrictedProduct.structureMap _ _ _ fun v ↦ ((u v)⁻¹ : (v.adicCompletionIntegers K)ˣ))
  val_inv := Prod.ext a.mul_inv (Subtype.ext (funext fun v ↦ congrArg Subtype.val (u v).mul_inv))
  inv_val := Prod.ext a.inv_mul (Subtype.ext (funext fun v ↦ congrArg Subtype.val (u v).inv_mul))
@[simp]
theorem coe_ofIntegerUnits_fst (a : (InfiniteAdeleRing K)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) :
    ((ofIntegerUnits a u : IdeleGroup K) : 𝔸[K]).1 = a :=
  rfl
@[simp]
theorem coe_ofIntegerUnits_snd (a : (InfiniteAdeleRing K)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    ((ofIntegerUnits a u : IdeleGroup K) : 𝔸[K]).2 v =
      ((u v : v.adicCompletionIntegers K) : v.adicCompletion K) :=
  rfl
theorem ofIntegerUnits_mem (a : (InfiniteAdeleRing K)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) :
    ofIntegerUnits a u ∈ standardOpenSubgroup K :=
  (mem_standardOpenSubgroup K).2 fun v ↦
    ⟨(u v : v.adicCompletionIntegers K).2, (((u v)⁻¹ : (v.adicCompletionIntegers K)ˣ) :
      v.adicCompletionIntegers K).2⟩
theorem continuous_ofIntegerUnits :
    Continuous (fun p : (InfiniteAdeleRing K)ˣ ×
        (Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) ↦
      ofIntegerUnits p.1 p.2) := by
  rw [Units.continuous_iff]
  constructor
  · exact (Units.continuous_val.comp continuous_fst).prodMk
      (_root_.RestrictedProduct.isEmbedding_structureMap.continuous.comp
        (continuous_pi fun v ↦ Units.continuous_val.comp ((continuous_apply v).comp continuous_snd)))
  · exact (Units.continuous_coe_inv.comp continuous_fst).prodMk
      (_root_.RestrictedProduct.isEmbedding_structureMap.continuous.comp
        (continuous_pi fun v ↦
          Units.continuous_coe_inv.comp ((continuous_apply v).comp continuous_snd)))
variable (K) in

def standardOpenSubgroupEquiv :
    standardOpenSubgroup K ≃ₜ* (InfiniteAdeleRing K)ˣ ×
      Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ where
  toFun x := (toInfinite K (x : IdeleGroup K), fun v ↦ localIntegerUnit v x)
  invFun p := ⟨ofIntegerUnits p.1 p.2, ofIntegerUnits_mem p.1 p.2⟩
  left_inv _ := Subtype.ext (Units.ext (Prod.ext rfl (Subtype.ext (funext fun _ ↦ rfl))))
  right_inv _ := Prod.ext (Units.ext rfl) (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  map_mul' x y := Prod.ext (map_mul (toInfinite K) (x : IdeleGroup K) y)
    (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  continuous_toFun := ((continuous_toInfinite K).comp continuous_subtype_val).prodMk
    (continuous_pi fun v ↦ continuous_localIntegerUnit v)
  continuous_invFun := continuous_ofIntegerUnits.subtype_mk _
end IdeleGroup
end
end GroundTheory.Global


