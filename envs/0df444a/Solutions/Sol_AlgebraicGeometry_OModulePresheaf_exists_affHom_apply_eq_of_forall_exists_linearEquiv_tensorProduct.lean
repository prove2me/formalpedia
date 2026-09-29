-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2d9d9f97-e64c-5dfa-96eb-57982c2bfd98

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent
import Theorems.Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace P2Sol

variable {A : Type u} [CommRing A] {P V' : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} {p : V' ⟶ P}

theorem sep (G' : OModulePresheaf (p ≫ q)) (hq : G'.IsQuasicoherent) (V : V'.affineOpens)
    (s : Set Γ(V', V.1)) (hs : Ideal.span s = ⊤) (y : G'.obj V.1)
    (hy : ∀ r : s, G'.res (V'.basicOpen_le r.1) y = 0) : y = 0 := by
  letI : ∀ r : s, Module Γ(V', V.1) (G'.obj (V'.basicOpen r.1)) := fun r => G'.moduleRestrict (V'.basicOpen_le r.1)
  haveI : ∀ r : s, IsLocalizedModule.Away r.1 (G'.resₗ (V'.basicOpen_le r.1)) :=
    fun r => G'.isLocalizedModule_res_of_isQuasicoherent hq V r.1
  exact Module.eq_zero_of_isLocalized_span s hs (fun r : s => G'.obj (V'.basicOpen r.1))
    (fun r => G'.resₗ (V'.basicOpen_le r.1)) y hy

theorem sep_eq (G' : OModulePresheaf (p ≫ q)) (hq : G'.IsQuasicoherent) (V : V'.affineOpens)
    (s : Set Γ(V', V.1)) (hs : Ideal.span s = ⊤) (y y' : G'.obj V.1)
    (hy : ∀ r : s, G'.res (V'.basicOpen_le r.1) y = G'.res (V'.basicOpen_le r.1) y') : y = y' := by
  rw [← sub_eq_zero]
  exact sep G' hq V s hs _ fun r => by rw [map_sub, hy r, sub_self]

section Chart

variable (G₁ G₂ : OModulePresheaf q) (G'₁ G'₂ : OModulePresheaf (p ≫ q))
  (η₁ : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (G₁.obj U.1 →ₗ[A] G'₁.obj V.1))
  (η₂ : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (G₂.obj U.1 →ₗ[A] G'₂.obj V.1))
  (ψ : OModulePresheaf.AffHom G₁ G₂)

def ψlin (U : P.affineOpens) : G₁.obj U.1 →ₗ[Γ(P, U.1)] G₂.obj U.1 :=
  { toFun := ψ.app U, map_add' := (ψ.app U).map_add, map_smul' := ψ.app_smul U }

@[scoped simp] theorem ψlin_apply (U : P.affineOpens) (x : G₁.obj U.1) : ψlin G₁ G₂ ψ U x = ψ.app U x := rfl

theorem chart_ext (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1)
    (hβ₁ : letI := (p.appLE U.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] G₁.obj U.1 ≃ₗ[Γ(V', V.1)] G'₁.obj V.1, ∀ x : G₁.obj U.1, β (1 ⊗ₜ x) = η₁ U V h x)
    {S N : Type u} [CommRing S] [AddCommGroup N] [Module S N] (σ : Γ(V', V.1) →+* S)
    (f g : G'₁.obj V.1 →+ N)
    (hf : ∀ (b : Γ(V', V.1)) (z : G'₁.obj V.1), f (b • z) = σ b • f z)
    (hg : ∀ (b : Γ(V', V.1)) (z : G'₁.obj V.1), g (b • z) = σ b • g z)
    (hfg : ∀ x : G₁.obj U.1, f (η₁ U V h x) = g (η₁ U V h x)) : f = g := by
  letI := (p.appLE U.1 V.1 h).hom.toAlgebra
  obtain ⟨β, hβ⟩ := hβ₁
  ext z
  obtain ⟨t, rfl⟩ := β.surjective z
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    have hbx : β (b ⊗ₜ x) = b • η₁ U V h x := by
      rw [← hβ x, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hbx, hf, hg, hfg]
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]

end Chart

section Main

variable (G₁ G₂ : OModulePresheaf q) (hq₁ : G₁.IsQuasicoherent) (hq₂ : G₂.IsQuasicoherent)
  (G'₁ : OModulePresheaf (p ≫ q)) (hq'₁ : G'₁.IsQuasicoherent)
  (η₁ : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (G₁.obj U.1 →ₗ[A] G'₁.obj V.1))
  (hη₁s : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : G₁.obj U.1),
    η₁ U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η₁ U V h x)
  (hη₁V : ∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
    (hV : V₁.1 ≤ V₂.1) (x : G₁.obj U.1), G'₁.res hV (η₁ U V₂ h₂ x) = η₁ U V₁ h₁ x)
  (hη₁U : ∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
    (hU : U₁.1 ≤ U₂.1) (x : G₁.obj U₂.1), η₁ U₂ V h₂ x = η₁ U₁ V h₁ (G₁.res hU x))
  (hβ₁ : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1),
    letI := (p.appLE U.1 V.1 h).hom.toAlgebra
    ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] G₁.obj U.1 ≃ₗ[Γ(V', V.1)] G'₁.obj V.1,
      ∀ x : G₁.obj U.1, β (1 ⊗ₜ x) = η₁ U V h x)
  (G'₂ : OModulePresheaf (p ≫ q)) (hq'₂ : G'₂.IsQuasicoherent)
  (η₂ : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (G₂.obj U.1 →ₗ[A] G'₂.obj V.1))
  (hη₂s : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : G₂.obj U.1),
    η₂ U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η₂ U V h x)
  (hη₂V : ∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
    (hV : V₁.1 ≤ V₂.1) (x : G₂.obj U.1), G'₂.res hV (η₂ U V₂ h₂ x) = η₂ U V₁ h₁ x)
  (hη₂U : ∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
    (hU : U₁.1 ≤ U₂.1) (x : G₂.obj U₂.1), η₂ U₂ V h₂ x = η₂ U₁ V h₁ (G₂.res hU x))
  (hβ₂ : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1),
    letI := (p.appLE U.1 V.1 h).hom.toAlgebra
    ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] G₂.obj U.1 ≃ₗ[Γ(V', V.1)] G'₂.obj V.1,
      ∀ x : G₂.obj U.1, β (1 ⊗ₜ x) = η₂ U V h x)
  (ψ : OModulePresheaf.AffHom G₁ G₂)

def θ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) : G'₁.obj V.1 →ₗ[Γ(V', V.1)] G'₂.obj V.1 :=
  letI := (p.appLE U.1 V.1 h).hom.toAlgebra
  (Classical.choose (hβ₂ U V h)).toLinearMap ∘ₗ ((ψlin G₁ G₂ ψ U).baseChange Γ(V', V.1)) ∘ₗ
    (Classical.choose (hβ₁ U V h)).symm.toLinearMap

theorem θ_eta (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (x : G₁.obj U.1) :
    θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U V h (η₁ U V h x) = η₂ U V h (ψ.app U x) := by
  letI := (p.appLE U.1 V.1 h).hom.toAlgebra
  have h1 : (Classical.choose (hβ₁ U V h)).symm (η₁ U V h x) = 1 ⊗ₜ x :=
    (Classical.choose (hβ₁ U V h)).symm_apply_eq.mpr (Classical.choose_spec (hβ₁ U V h) x).symm
  simp only [θ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [h1, LinearMap.baseChange_tmul, ψlin_apply, Classical.choose_spec (hβ₂ U V h)]

include hη₁V hη₂V in
theorem res_θ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
    (hV : V₁.1 ≤ V₂.1) (z : G'₁.obj V₂.1) :
    G'₂.res hV (θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U V₂ h₂ z) =
      θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U V₁ h₁ (G'₁.res hV z) := by
  have key := chart_ext G₁ G'₁ η₁ U V₂ h₂ (hβ₁ U V₂ h₂) (V'.presheaf.map (homOfLE hV).op).hom
    ((G'₂.res hV).toAddMonoidHom.comp (θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U V₂ h₂).toAddMonoidHom)
    ((θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U V₁ h₁).toAddMonoidHom.comp (G'₁.res hV).toAddMonoidHom)
    (fun b z => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, map_smul, G'₂.res_smul])
    (fun b z => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, G'₁.res_smul, map_smul])
    (fun x => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe]
      rw [θ_eta, hη₂V U V₁ V₂ h₁ h₂ hV, hη₁V U V₁ V₂ h₁ h₂ hV, θ_eta])
  exact congrArg (fun φ => φ z) (congrArg DFunLike.coe key)

include hη₁U hη₂U in

theorem θ_eq_of_le (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
    (hU : U₁.1 ≤ U₂.1) :
    θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U₁ V h₁ = θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U₂ V h₂ := by
  have key := chart_ext G₁ G'₁ η₁ U₂ V h₂ (hβ₁ U₂ V h₂) (RingHom.id _)
    (θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U₁ V h₁).toAddMonoidHom (θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U₂ V h₂).toAddMonoidHom
    (fun b z => by simp) (fun b z => by simp)
    (fun x => by
      simp only [LinearMap.toAddMonoidHom_coe]
      rw [θ_eta, hη₁U U₁ U₂ V h₁ h₂ hU, θ_eta, hη₂U U₁ U₂ V h₁ h₂ hU]
      congr 1
      exact LinearMap.congr_fun (ψ.naturality hU) x)
  exact LinearMap.toAddMonoidHom_injective key

theorem span_eq_top_of_cover (V : V'.affineOpens) (𝒰 : Set P.affineOpens)
    (hcov : ∀ v ∈ V.1, ∃ U ∈ 𝒰, p.base v ∈ U.1) :
    Ideal.span {g : Γ(V', V.1) | ∃ U ∈ 𝒰, V'.basicOpen g ≤ p ⁻¹ᵁ U.1} = ⊤ := by
  set s : Set Γ(V', V.1) := {g : Γ(V', V.1) | ∃ U ∈ 𝒰, V'.basicOpen g ≤ p ⁻¹ᵁ U.1} with hsdef
  have hle : (⨆ f : s, V'.basicOpen (f : Γ(V', V.1))) ≤ V.1 := iSup_le fun g => V'.basicOpen_le (g : Γ(V', V.1))
  have hge : V.1 ≤ ⨆ f : s, V'.basicOpen (f : Γ(V', V.1)) := by
    intro v hv
    obtain ⟨U, hU𝒰, hvU⟩ := hcov v hv
    have hv' : v ∈ (V.1 ⊓ p ⁻¹ᵁ U.1 : V'.Opens) := ⟨hv, hvU⟩
    obtain ⟨g, hg, hvg⟩ := V.2.exists_basicOpen_le (V := V.1 ⊓ p ⁻¹ᵁ U.1) ⟨v, hv'⟩ hv
    have hgs : g ∈ s := ⟨U, hU𝒰, hg.trans inf_le_right⟩
    exact Opens.mem_iSup.mpr ⟨⟨g, hgs⟩, hvg⟩
  exact V.2.iSup_basicOpen_eq_self_iff.mp (le_antisymm hle hge)

abbrev bo (V : V'.affineOpens) (g : Γ(V', V.1)) : V'.affineOpens := ⟨V'.basicOpen g, V.2.basicOpen g⟩

include hη₁V hη₂V hη₁U hη₂U hq'₂ in

theorem θ_eq (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1) :
    θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U₁ V h₁ = θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U₂ V h₂ := by

  let 𝒰 : Set P.affineOpens := {U | U.1 ≤ U₁.1 ⊓ U₂.1}
  have hcov : ∀ v ∈ V.1, ∃ U ∈ 𝒰, p.base v ∈ U.1 := by
    intro v hv
    have hv₁₂ : p.base v ∈ U₁.1 ⊓ U₂.1 := ⟨h₁ hv, h₂ hv⟩
    obtain ⟨r, hr, hvr⟩ := U₁.2.exists_basicOpen_le ⟨p.base v, hv₁₂⟩ (h₁ hv)
    exact ⟨⟨P.basicOpen r, U₁.2.basicOpen r⟩, hr, hvr⟩
  have hs := span_eq_top_of_cover V 𝒰 hcov
  ext z
  apply sep_eq G'₂ hq'₂ V _ hs
  rintro ⟨g, U₃, hU₃, hg⟩
  have hg₁ : (bo V g).1 ≤ p ⁻¹ᵁ U₁.1 := hg.trans (p.preimage_mono (hU₃.trans inf_le_left))
  have hg₂ : (bo V g).1 ≤ p ⁻¹ᵁ U₂.1 := hg.trans (p.preimage_mono (hU₃.trans inf_le_right))
  show G'₂.res (V'.basicOpen_le g) _ = G'₂.res (V'.basicOpen_le g) _
  rw [res_θ G₁ G₂ G'₁ η₁ hη₁V hβ₁ G'₂ η₂ hη₂V hβ₂ ψ U₁ (bo V g) V hg₁ h₁,
    res_θ G₁ G₂ G'₁ η₁ hη₁V hβ₁ G'₂ η₂ hη₂V hβ₂ ψ U₂ (bo V g) V hg₂ h₂,
    ← θ_eq_of_le G₁ G₂ G'₁ η₁ hη₁U hβ₁ G'₂ η₂ hη₂U hβ₂ ψ U₃ U₁ (bo V g) hg hg₁ (hU₃.trans inf_le_left),
    ← θ_eq_of_le G₁ G₂ G'₁ η₁ hη₁U hβ₁ G'₂ η₂ hη₂U hβ₂ ψ U₃ U₂ (bo V g) hg hg₂ (hU₃.trans inf_le_right)]

abbrev rf {W₁ W₂ : V'.Opens} (h : W₂ ≤ W₁) : Γ(V', W₁) →+* Γ(V', W₂) := (V'.presheaf.map (homOfLE h).op).hom

theorem rf_rf {W₁ W₂ W₃ : V'.Opens} (h₁₂ : W₂ ≤ W₁) (h₂₃ : W₃ ≤ W₂) (a : Γ(V', W₁)) :
    rf h₂₃ (rf h₁₂ a) = rf (h₂₃.trans h₁₂) a := by
  change (V'.presheaf.map (homOfLE h₁₂).op ≫ V'.presheaf.map (homOfLE h₂₃).op).hom a = _
  rw [← Functor.map_comp]; rfl

def resV (G' : OModulePresheaf (p ≫ q)) {V W₁ W₂ : V'.Opens} (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V) (h : W₂ ≤ W₁) :
    letI := G'.moduleRestrict h₁; letI := G'.moduleRestrict h₂
    G'.obj W₁ →ₗ[Γ(V', V)] G'.obj W₂ :=
  letI := G'.moduleRestrict h₁; letI := G'.moduleRestrict h₂
  { toFun := G'.res h
    map_add' := map_add _
    map_smul' := fun a x => by
      show G'.res h (rf h₁ a • x) = rf h₂ a • G'.res h x
      rw [G'.res_smul, rf_rf] }

theorem resV_apply (G' : OModulePresheaf (p ≫ q)) {V W₁ W₂ : V'.Opens} (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V) (h : W₂ ≤ W₁)
    (x : G'.obj W₁) :
    letI := G'.moduleRestrict h₁; letI := G'.moduleRestrict h₂
    resV G' h₁ h₂ h x = G'.res h x := rfl

theorem basicOpen_mul_le_left (V : V'.affineOpens) (g₁ g₂ : Γ(V', V.1)) :
    V'.basicOpen (g₁ * g₂) ≤ V'.basicOpen g₁ := by rw [Scheme.basicOpen_mul]; exact inf_le_left
theorem basicOpen_mul_le_right (V : V'.affineOpens) (g₁ g₂ : Γ(V', V.1)) :
    V'.basicOpen (g₁ * g₂) ≤ V'.basicOpen g₂ := by rw [Scheme.basicOpen_mul]; exact inf_le_right

theorem isLocalizedModule_resV (G' : OModulePresheaf (p ≫ q)) (hq' : G'.IsQuasicoherent) (V : V'.affineOpens)
    (g₁ g₂ : Γ(V', V.1)) :
    letI := G'.moduleRestrict (V'.basicOpen_le g₁)
    letI := G'.moduleRestrict ((V'.basicOpen_le (rf (V'.basicOpen_le g₁) g₂)).trans (V'.basicOpen_le g₁))
    IsLocalizedModule (Submonoid.powers g₂)
      (resV G' (V := V.1) (V'.basicOpen_le g₁) ((V'.basicOpen_le (rf (V'.basicOpen_le g₁) g₂)).trans (V'.basicOpen_le g₁))
        (V'.basicOpen_le (rf (V'.basicOpen_le g₁) g₂))) := by
  have h₁ : V'.basicOpen g₁ ≤ V.1 := V'.basicOpen_le g₁
  have hb : V'.basicOpen (rf h₁ g₂) ≤ V'.basicOpen g₁ := V'.basicOpen_le _
  have hbV : V'.basicOpen (rf h₁ g₂) ≤ V.1 := hb.trans h₁
  letI i₀ : Module Γ(V', (bo V g₁).1) (G'.obj (V'.basicOpen (rf h₁ g₂))) := G'.moduleRestrict hb
  have H : IsLocalizedModule (Submonoid.powers (rf h₁ g₂)) (G'.resₗ hb) :=
    G'.isLocalizedModule_res_of_isQuasicoherent hq' (bo V g₁) (rf h₁ g₂)
  letI i₁ : Module Γ(V', V.1) (G'.obj (V'.basicOpen g₁)) := G'.moduleRestrict h₁
  letI i₂ : Module Γ(V', V.1) (G'.obj (V'.basicOpen (rf h₁ g₂))) := G'.moduleRestrict hbV
  have hpow : ∀ n : ℕ, rf h₁ (g₂ ^ n) = (rf h₁ g₂) ^ n := fun n => map_pow _ _ _

  have hact : ∀ (n : ℕ) (a : G'.obj (V'.basicOpen (rf h₁ g₂))),
      (haveI := i₂; (g₂ ^ n : Γ(V', V.1)) • a) = (haveI := i₀; ((rf h₁ g₂) ^ n : Γ(V', (bo V g₁).1)) • a) := by
    intro n a
    show rf hbV (g₂ ^ n) • a = rf hb ((rf h₁ g₂) ^ n) • a
    rw [← hpow, rf_rf]
  show IsLocalizedModule (Submonoid.powers g₂) (resV G' (V := V.1) h₁ hbV hb)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have hu := H.map_units ⟨(rf h₁ g₂) ^ n, n, rfl⟩
    rw [Module.End.isUnit_iff] at hu ⊢
    convert hu using 1
    funext a
    simp only [Module.algebraMap_end_apply]
    exact hact n a
  · intro y
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, e⟩ := H.surj y
    refine ⟨⟨x, ⟨g₂ ^ n, n, rfl⟩⟩, ?_⟩
    change (haveI := i₂; (g₂ ^ n : Γ(V', V.1)) • y) = G'.res hb x
    change (haveI := i₀; ((rf h₁ g₂) ^ n : Γ(V', (bo V g₁).1)) • y) = G'.res hb x at e
    rw [hact n y]
    exact e
  · intro x₁ x₂ e
    obtain ⟨⟨_, n, rfl⟩, hc⟩ := H.exists_of_eq (x₁ := x₁) (x₂ := x₂) e
    refine ⟨⟨g₂ ^ n, n, rfl⟩, ?_⟩
    change (haveI := i₁; (g₂ ^ n : Γ(V', V.1)) • x₁) = (haveI := i₁; (g₂ ^ n : Γ(V', V.1)) • x₂)
    change ((rf h₁ g₂) ^ n) • x₁ = ((rf h₁ g₂) ^ n) • x₂ at hc
    show rf h₁ (g₂ ^ n) • x₁ = rf h₁ (g₂ ^ n) • x₂
    rw [hpow]; exact hc

include hη₁V hη₂V hη₁U hη₂U hq'₂ in

theorem exists_glue (V : V'.affineOpens) {ι : Type u} [Fintype ι] (g : ι → Γ(V', V.1)) (hg : Ideal.span (Set.range g) = ⊤)
    (U : ι → P.affineOpens) (hU : ∀ i, V'.basicOpen (g i) ≤ p ⁻¹ᵁ (U i).1) (z : G'₁.obj V.1) :
    ∃! w : G'₂.obj V.1, ∀ i, G'₂.res (V'.basicOpen_le (g i)) w =
      θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ (U i) (bo V (g i)) (hU i) (G'₁.res (V'.basicOpen_le (g i)) z) := by
  letI : ∀ i, Module Γ(V', V.1) (G'₂.obj (V'.basicOpen (g i))) := fun i => G'₂.moduleRestrict (V'.basicOpen_le (g i))
  haveI : ∀ i, IsLocalizedModule (Submonoid.powers (g i)) (G'₂.resₗ (V'.basicOpen_le (g i))) :=
    fun i => G'₂.isLocalizedModule_res_of_isQuasicoherent hq'₂ V (g i)

  have huniq : ∀ w₁ w₂ : G'₂.obj V.1,
      (∀ i, G'₂.res (V'.basicOpen_le (g i)) w₁ = θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ (U i) (bo V (g i)) (hU i) (G'₁.res (V'.basicOpen_le (g i)) z)) →
      (∀ i, G'₂.res (V'.basicOpen_le (g i)) w₂ = θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ (U i) (bo V (g i)) (hU i) (G'₁.res (V'.basicOpen_le (g i)) z)) →
      w₁ = w₂ := fun w₁ w₂ h₁ h₂ =>
    sep_eq G'₂ hq'₂ V (Set.range g) hg w₁ w₂ (by rintro ⟨_, i, rfl⟩; exact (h₁ i).trans (h₂ i).symm)

  have hle : ∀ i j, V'.basicOpen (rf (V'.basicOpen_le (g i)) (g j)) ≤ V.1 :=
    fun i j => (V'.basicOpen_le _).trans (V'.basicOpen_le (g i))
  have hle' : ∀ i j, V'.basicOpen (rf (V'.basicOpen_le (g i)) (g j)) ≤ V'.basicOpen (g j) := fun i j => by
    rw [Scheme.basicOpen_res]; exact inf_le_right
  letI : ∀ i j, Module Γ(V', V.1) (G'₂.obj (V'.basicOpen (rf (V'.basicOpen_le (g i)) (g j)))) :=
    fun i j => G'₂.moduleRestrict (hle i j)
  haveI : ∀ i j, IsLocalizedModule (Submonoid.powers (g j))
      (resV G'₂ (V := V.1) (V'.basicOpen_le (g i)) (hle i j) (V'.basicOpen_le (rf (V'.basicOpen_le (g i)) (g j)))) :=
    fun i j => isLocalizedModule_resV G'₂ hq'₂ V (g i) (g j)

  have hx : ∀ i j,
      resV G'₂ (V := V.1) (V'.basicOpen_le (g i)) (hle i j) (V'.basicOpen_le (rf (V'.basicOpen_le (g i)) (g j)))
          (θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ (U i) (bo V (g i)) (hU i) (G'₁.res (V'.basicOpen_le (g i)) z)) =
        resV G'₂ (V := V.1) (V'.basicOpen_le (g j)) (hle i j) (hle' i j)
          (θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ (U j) (bo V (g j)) (hU j) (G'₁.res (V'.basicOpen_le (g j)) z)) := by
    intro i j
    let W : V'.affineOpens := bo (bo V (g i)) (rf (V'.basicOpen_le (g i)) (g j))
    have hWi : W.1 ≤ p ⁻¹ᵁ (U i).1 := (V'.basicOpen_le _).trans (hU i)
    have hWj : W.1 ≤ p ⁻¹ᵁ (U j).1 := (hle' i j).trans (hU j)
    show G'₂.res _ _ = G'₂.res _ _
    rw [res_θ G₁ G₂ G'₁ η₁ hη₁V hβ₁ G'₂ η₂ hη₂V hβ₂ ψ (U i) W (bo V (g i)) hWi (hU i),
      res_θ G₁ G₂ G'₁ η₁ hη₁V hβ₁ G'₂ η₂ hη₂V hβ₂ ψ (U j) W (bo V (g j)) hWj (hU j),
      G'₁.res_res, G'₁.res_res,
      θ_eq G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ (U i) (U j) W hWi hWj]
  obtain ⟨w, hw⟩ := IsLocalizedModule.exists_forall_apply_eq_of_span_range_eq_top g hg
    (fun i => G'₂.resₗ (V'.basicOpen_le (g i)))
    (fun i j => resV G'₂ (V := V.1) (V'.basicOpen_le (g i)) (hle i j) (V'.basicOpen_le (rf (V'.basicOpen_le (g i)) (g j))))
    (fun i j => resV G'₂ (V := V.1) (V'.basicOpen_le (g j)) (hle i j) (hle' i j))
    (fun i j => by ext x; exact (G'₂.res_res _ _ x).trans (G'₂.res_res _ _ x).symm)
    (fun i => θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ (U i) (bo V (g i)) (hU i) (G'₁.res (V'.basicOpen_le (g i)) z)) hx
  exact ⟨w, hw, fun y hy => huniq y w hy hw⟩

theorem exists_cover (V : V'.affineOpens) :
    ∃ (ι : Type u) (_ : Fintype ι) (g : ι → Γ(V', V.1)) (U : ι → P.affineOpens),
      Ideal.span (Set.range g) = ⊤ ∧ ∀ i, V'.basicOpen (g i) ≤ p ⁻¹ᵁ (U i).1 := by
  classical
  have hcov : ∀ v ∈ V.1, ∃ U ∈ (Set.univ : Set P.affineOpens), p.base v ∈ U.1 := by
    intro v _
    obtain ⟨_, ⟨W, hW, rfl⟩, hvW, -⟩ :=
      P.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (p.base v)) isOpen_univ
    exact ⟨⟨W, hW⟩, Set.mem_univ _, hvW⟩
  have hs := span_eq_top_of_cover V Set.univ hcov
  obtain ⟨T, hTs, hT1⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp hs)
  have hT : Ideal.span (T : Set Γ(V', V.1)) = ⊤ := (Ideal.eq_top_iff_one _).mpr hT1
  have hmem : ∀ t : T, ∃ U : P.affineOpens, V'.basicOpen (t : Γ(V', V.1)) ≤ p ⁻¹ᵁ U.1 := fun t => by
    obtain ⟨U, -, hU⟩ := hTs t.2; exact ⟨U, hU⟩
  choose U hU using hmem
  refine ⟨T, inferInstance, Subtype.val, U, ?_, hU⟩
  rwa [Subtype.range_coe_subtype, Finset.setOf_mem]

include hη₁V hη₂V hη₁U hη₂U hq'₂ in

theorem exists_app (V : V'.affineOpens) :
    ∃ φ : G'₁.obj V.1 → G'₂.obj V.1,
      ∀ (U : P.affineOpens) (W : V'.affineOpens) (hWV : W.1 ≤ V.1) (hW : W.1 ≤ p ⁻¹ᵁ U.1) (z : G'₁.obj V.1),
        G'₂.res hWV (φ z) = θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U W hW (G'₁.res hWV z) := by
  obtain ⟨ι, _, g, U, hg, hU⟩ := exists_cover (p := p) V
  refine ⟨fun z => (exists_glue G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V g hg U hU z).exists.choose,
    fun U₀ W hWV hW z => ?_⟩
  have P := (exists_glue G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V g hg U hU z).exists.choose_spec
  set w := (exists_glue G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V g hg U hU z).exists.choose

  have hsW : Ideal.span (Set.range (⇑(rf hWV) ∘ g)) = ⊤ := by
    rw [Set.range_comp, ← Ideal.map_span, hg, Ideal.map_top]
  apply sep_eq G'₂ hq'₂ W _ hsW
  rintro ⟨_, i, rfl⟩
  have hDW : V'.basicOpen (rf hWV (g i)) ≤ W.1 := V'.basicOpen_le _
  have hDi : V'.basicOpen (rf hWV (g i)) ≤ V'.basicOpen (g i) := by rw [Scheme.basicOpen_res]; exact inf_le_right
  have hDU₀ : (bo W (rf hWV (g i))).1 ≤ p ⁻¹ᵁ U₀.1 := hDW.trans hW
  have hDUi : (bo W (rf hWV (g i))).1 ≤ p ⁻¹ᵁ (U i).1 := hDi.trans (hU i)
  show G'₂.res hDW (G'₂.res hWV w) = G'₂.res hDW _
  rw [G'₂.res_res, show G'₂.res (hDW.trans hWV) w = G'₂.res hDi (G'₂.res (V'.basicOpen_le (g i)) w) from
    (G'₂.res_res _ _ w).symm, P i,
    res_θ G₁ G₂ G'₁ η₁ hη₁V hβ₁ G'₂ η₂ hη₂V hβ₂ ψ (U i) (bo W (rf hWV (g i))) (bo V (g i)) hDUi (hU i) hDi,
    res_θ G₁ G₂ G'₁ η₁ hη₁V hβ₁ G'₂ η₂ hη₂V hβ₂ ψ U₀ (bo W (rf hWV (g i))) W hDU₀ hW hDW,
    G'₁.res_res, G'₁.res_res,
    θ_eq G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ (U i) U₀ (bo W (rf hWV (g i))) hDUi hDU₀]

theorem θ_smulA (U : P.affineOpens) (W : V'.affineOpens) (h : W.1 ≤ p ⁻¹ᵁ U.1) (a : A) (y : G'₁.obj W.1) :
    θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U W h (a • y) = a • θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U W h y := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) W.1
  rw [← algebraMap_smul (Γ(V', W.1)) a y, map_smul, algebraMap_smul]

include hq'₂ in

theorem eq_of_forall_chart (V : V'.affineOpens) (y y' : G'₂.obj V.1)
    (h : ∀ (U : P.affineOpens) (W : V'.affineOpens) (hWV : W.1 ≤ V.1) (_ : W.1 ≤ p ⁻¹ᵁ U.1),
      G'₂.res hWV y = G'₂.res hWV y') : y = y' := by
  obtain ⟨ι, _, g, U, hg, hU⟩ := exists_cover (p := p) V
  exact sep_eq G'₂ hq'₂ V _ hg y y' (by rintro ⟨_, i, rfl⟩; exact h (U i) (bo V (g i)) (V'.basicOpen_le _) (hU i))

theorem θ_surjective (U : P.affineOpens) (W : V'.affineOpens) (h : W.1 ≤ p ⁻¹ᵁ U.1)
    (hsU : Function.Surjective (ψ.app U)) :
    Function.Surjective (θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U W h) := by
  letI := (p.appLE U.1 W.1 h).hom.toAlgebra
  have hψU : Function.Surjective (ψlin G₁ G₂ ψ U) := hsU
  have hbc : Function.Surjective ((ψlin G₁ G₂ ψ U).baseChange Γ(V', W.1)) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ hψU
  show Function.Surjective (fun y => _)
  simp only [θ, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (Classical.choose (hβ₂ U W h)).surjective.comp (hbc.comp (Classical.choose (hβ₁ U W h)).symm.surjective)

def JΓ (G' : OModulePresheaf (p ≫ q)) (J : Ideal A) (W : V'.Opens) : Submodule Γ(V', W) (G'.obj W) where
  carrier := (J • (⊤ : Submodule A (G'.obj W)) : Submodule A (G'.obj W))
  add_mem' := fun ha hb => add_mem ha hb
  zero_mem' := zero_mem _
  smul_mem' := fun b z hz => by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) W
    show b • z ∈ J • (⊤ : Submodule A (G'.obj W))
    refine Submodule.smul_induction_on (p := fun z => b • z ∈ J • (⊤ : Submodule A (G'.obj W))) hz ?_ ?_
    · intro j hj n _; rw [smul_algebra_smul_comm]; exact Submodule.smul_mem_smul hj trivial
    · intro x y hx hy; rw [smul_add]; exact add_mem hx hy

theorem mem_JΓ (G' : OModulePresheaf (p ≫ q)) (J : Ideal A) (W : V'.Opens) (z : G'.obj W) :
    z ∈ JΓ G' J W ↔ z ∈ J • (⊤ : Submodule A (G'.obj W)) := Iff.rfl

include hβ₂ in

theorem smul_eq_zero_chart (J : Ideal A) (U : P.affineOpens) (W : V'.affineOpens) (h : W.1 ≤ p ⁻¹ᵁ U.1)
    (hsU : Function.Surjective (ψ.app U)) (hkU : LinearMap.ker (ψ.app U) = J • (⊤ : Submodule A (G₁.obj U.1)))
    (j : A) (hj : j ∈ J) (w : G'₂.obj W.1) : j • w = 0 := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) W.1
  have key := chart_ext G₂ G'₂ η₂ U W h (hβ₂ U W h) (RingHom.id _)
    (DistribMulAction.toAddMonoidHom (G'₂.obj W.1) j) 0
    (fun b z => by simp only [DistribMulAction.toAddMonoidHom_apply, RingHom.id_apply]; exact (smul_algebra_smul_comm j b z).symm)
    (fun b z => by simp)
    (fun y => by
      obtain ⟨x, rfl⟩ := hsU y
      have hx : j • x ∈ LinearMap.ker (ψ.app U) := by rw [hkU]; exact Submodule.smul_mem_smul hj trivial
      simp only [DistribMulAction.toAddMonoidHom_apply, AddMonoidHom.zero_apply]
      rw [← map_smul, ← map_smul, LinearMap.mem_ker.mp hx, map_zero])
  exact congrArg (fun φ => φ w) (congrArg DFunLike.coe key)

theorem θ_ker_le (J : Ideal A) (U : P.affineOpens) (W : V'.affineOpens) (h : W.1 ≤ p ⁻¹ᵁ U.1)
    (hsU : Function.Surjective (ψ.app U)) (hkU : LinearMap.ker (ψ.app U) = J • (⊤ : Submodule A (G₁.obj U.1)))
    (y : G'₁.obj W.1) (hy : θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U W h y = 0) : y ∈ JΓ G'₁ J W.1 := by
  letI := (p.appLE U.1 W.1 h).hom.toAlgebra
  have hβ₁spec : ∀ x, (Classical.choose (hβ₁ U W h)) (1 ⊗ₜ x) = η₁ U W h x := Classical.choose_spec (hβ₁ U W h)
  obtain ⟨t, rfl⟩ := (Classical.choose (hβ₁ U W h)).surjective y
  have ht : (ψlin G₁ G₂ ψ U).baseChange Γ(V', W.1) t = 0 := by
    have : (Classical.choose (hβ₂ U W h)) (((ψlin G₁ G₂ ψ U).baseChange Γ(V', W.1))
        ((Classical.choose (hβ₁ U W h)).symm ((Classical.choose (hβ₁ U W h)) t))) = 0 := hy
    rwa [LinearEquiv.symm_apply_apply, LinearEquiv.map_eq_zero_iff] at this
  have hex := lTensor_exact Γ(V', W.1) (LinearMap.exact_subtype_ker_map (ψlin G₁ G₂ ψ U)) hsU
  have ht' : t ∈ LinearMap.range (LinearMap.lTensor Γ(V', W.1) (LinearMap.ker (ψlin G₁ G₂ ψ U)).subtype) := by
    rw [(LinearMap.exact_iff.mp hex).symm, LinearMap.mem_ker]
    rw [congrFun (LinearMap.baseChange_eq_ltensor (A := Γ(V', W.1)) (ψlin G₁ G₂ ψ U)) t] at ht
    exact ht
  obtain ⟨t₀, rfl⟩ := ht'
  clear ht hy
  induction t₀ using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact zero_mem _
  | tmul b k =>
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply,
      show (Classical.choose (hβ₁ U W h)) (b ⊗ₜ (k : G₁.obj U.1)) = b • η₁ U W h k by
        rw [← hβ₁spec, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    refine Submodule.smul_mem _ b ?_
    have hk : (k : G₁.obj U.1) ∈ J • (⊤ : Submodule A (G₁.obj U.1)) := by rw [← hkU]; exact k.2
    show η₁ U W h k ∈ J • (⊤ : Submodule A (G'₁.obj W.1))
    refine Submodule.smul_induction_on (p := fun x => η₁ U W h x ∈ J • (⊤ : Submodule A (G'₁.obj W.1))) hk ?_ ?_
    · intro j hj n _; rw [map_smul]; exact Submodule.smul_mem_smul hj trivial
    · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add]; exact add_mem h₁ h₂

include hq'₁ in

theorem exists_num (J : Ideal A) (V : V'.affineOpens) (g : Γ(V', V.1)) (y : G'₁.obj (V'.basicOpen g))
    (hy : y ∈ J • (⊤ : Submodule A (G'₁.obj (V'.basicOpen g)))) :
    ∃ m : G'₁.obj V.1, m ∈ J • (⊤ : Submodule A (G'₁.obj V.1)) ∧
      ∃ n : ℕ, G'₁.res (V'.basicOpen_le g) m = rf (V'.basicOpen_le g) (g ^ n) • y := by
  letI i₁ : Module Γ(V', V.1) (G'₁.obj (V'.basicOpen g)) := G'₁.moduleRestrict (V'.basicOpen_le g)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) (V'.basicOpen g)
  have H₁ : IsLocalizedModule (Submonoid.powers g) (G'₁.resₗ (V'.basicOpen_le g)) :=
    G'₁.isLocalizedModule_res_of_isQuasicoherent hq'₁ V g
  refine Submodule.smul_induction_on
    (p := fun y => ∃ m : G'₁.obj V.1, m ∈ J • (⊤ : Submodule A (G'₁.obj V.1)) ∧
      ∃ n : ℕ, G'₁.res (V'.basicOpen_le g) m = rf (V'.basicOpen_le g) (g ^ n) • y) hy ?_ ?_
  · intro j hj n _
    obtain ⟨⟨u, ⟨_, a, rfl⟩⟩, e⟩ := H₁.surj n
    change rf (V'.basicOpen_le g) (g ^ a) • n = G'₁.res (V'.basicOpen_le g) u at e
    refine ⟨j • u, Submodule.smul_mem_smul hj trivial, a, ?_⟩
    rw [map_smul, ← e]
    exact (smul_algebra_smul_comm _ _ _).symm
  · intro x y hx hy
    obtain ⟨m₁, hm₁, n₁, e₁⟩ := hx
    obtain ⟨m₂, hm₂, n₂, e₂⟩ := hy
    refine ⟨g ^ n₂ • m₁ + g ^ n₁ • m₂, add_mem ((JΓ G'₁ J V.1).smul_mem _ hm₁) ((JΓ G'₁ J V.1).smul_mem _ hm₂),
      n₁ + n₂, ?_⟩
    rw [map_add, G'₁.res_smul, G'₁.res_smul, e₁, e₂, smul_add, smul_smul, smul_smul, ← map_mul, ← map_mul, ← pow_add,
      ← pow_add, add_comm n₂ n₁]

include hη₁V hη₂V hη₁U hη₂U hq'₂

private def _root_.P2Sol.app (V : V'.affineOpens) : G'₁.obj V.1 → G'₂.obj V.1 :=
  (exists_app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V).choose

p2m_export "P2Sol" "app"
theorem app_spec (V : V'.affineOpens) (U : P.affineOpens) (W : V'.affineOpens) (hWV : W.1 ≤ V.1) (hW : W.1 ≤ p ⁻¹ᵁ U.1)
    (z : G'₁.obj V.1) :
    G'₂.res hWV (app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V z) =
      θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U W hW (G'₁.res hWV z) :=
  (exists_app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V).choose_spec U W hWV hW z

theorem app_add (V : V'.affineOpens) (z z' : G'₁.obj V.1) :
    app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V (z + z') =
      app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V z +
        app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V z' := by
  apply eq_of_forall_chart G'₂ hq'₂ V
  intro U W hWV hW
  rw [map_add, app_spec (U := U) (hWV := hWV) (hW := hW), app_spec (U := U) (hWV := hWV) (hW := hW),
    app_spec (U := U) (hWV := hWV) (hW := hW), map_add, map_add]

theorem app_smulA (V : V'.affineOpens) (a : A) (z : G'₁.obj V.1) :
    app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V (a • z) =
      a • app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V z := by
  apply eq_of_forall_chart G'₂ hq'₂ V
  intro U W hWV hW
  rw [map_smul, app_spec (U := U) (hWV := hWV) (hW := hW), app_spec (U := U) (hWV := hWV) (hW := hW), map_smul, θ_smulA]

private theorem _root_.P2Sol.app_smul (V : V'.affineOpens) (b : Γ(V', V.1)) (z : G'₁.obj V.1) :
    app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V (b • z) =
      b • app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V z := by
  apply eq_of_forall_chart G'₂ hq'₂ V
  intro U W hWV hW
  rw [G'₂.res_smul, app_spec (U := U) (hWV := hWV) (hW := hW), app_spec (U := U) (hWV := hWV) (hW := hW), G'₁.res_smul,
    map_smul]

p2m_export "P2Sol" "app_smul"

def appLin (V : V'.affineOpens) : G'₁.obj V.1 →ₗ[A] G'₂.obj V.1 :=
  { toFun := app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V
    map_add' := app_add G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V
    map_smul' := app_smulA G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V }

@[scoped simp] theorem appLin_apply (V : V'.affineOpens) (z : G'₁.obj V.1) :
    appLin G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V z =
      app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V z := rfl

theorem res_app (V₁ V₂ : V'.affineOpens) (hV : V₁.1 ≤ V₂.1) (z : G'₁.obj V₂.1) :
    G'₂.res hV (app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V₂ z) =
      app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V₁ (G'₁.res hV z) := by
  apply eq_of_forall_chart G'₂ hq'₂ V₁
  intro U W hWV hW
  rw [G'₂.res_res, app_spec (V := V₂) (U := U) (W := W) (hWV := hWV.trans hV) (hW := hW),
    app_spec (V := V₁) (U := U) (W := W) (hWV := hWV) (hW := hW), G'₁.res_res]

def ψ' : OModulePresheaf.AffHom G'₁ G'₂ where
  app := appLin G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ
  app_smul V b z := app_smul G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V b z
  naturality h := by
    ext z
    exact (res_app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ _ _ h z).symm

theorem app_eta (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (x : G₁.obj U.1) :
    app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V (η₁ U V h x) = η₂ U V h (ψ.app U x) := by
  have := app_spec G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V U V le_rfl h (η₁ U V h x)
  rw [G'₂.res_refl_apply, G'₁.res_refl_apply, θ_eta] at this
  exact this

theorem app_eq_θ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (z : G'₁.obj V.1) :
    app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V z = θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ U V h z := by
  have := app_spec G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V U V le_rfl h z
  rw [G'₂.res_refl_apply, G'₁.res_refl_apply] at this
  exact this

include hq'₁ in

theorem app_surjective (hsU : ∀ U : P.affineOpens, Function.Surjective (ψ.app U)) (V : V'.affineOpens) :
    Function.Surjective (app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V) := by
  obtain ⟨ι, _, g, U, hg, hU⟩ := exists_cover (p := p) V

  let F : G'₁.obj V.1 →ₗ[Γ(V', V.1)] G'₂.obj V.1 :=
    { toFun := app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V
      map_add' := app_add G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V
      map_smul' := app_smul G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V }
  suffices h : LinearMap.range F = ⊤ from LinearMap.range_eq_top.mp h
  letI : ∀ r : Set.range g, Module Γ(V', V.1) (G'₂.obj (V'.basicOpen r.1)) := fun r => G'₂.moduleRestrict (V'.basicOpen_le r.1)
  haveI : ∀ r : Set.range g, IsLocalizedModule.Away r.1 (G'₂.resₗ (V'.basicOpen_le r.1)) :=
    fun r => G'₂.isLocalizedModule_res_of_isQuasicoherent hq'₂ V r.1
  apply Submodule.eq_top_of_isLocalized₀_span (Set.range g) hg (fun r : Set.range g => G'₂.obj (V'.basicOpen r.1))
    (fun r => G'₂.resₗ (V'.basicOpen_le r.1))
  rintro ⟨_, i, rfl⟩
  rw [eq_top_iff]
  rintro y -

  obtain ⟨z', rfl⟩ := θ_surjective G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ (U i) (bo V (g i)) (hU i) (hsU (U i)) y
  letI i₁ : Module Γ(V', V.1) (G'₁.obj (V'.basicOpen (g i))) := G'₁.moduleRestrict (V'.basicOpen_le (g i))
  have H₁ : IsLocalizedModule (Submonoid.powers (g i)) (G'₁.resₗ (V'.basicOpen_le (g i))) :=
    G'₁.isLocalizedModule_res_of_isQuasicoherent hq'₁ V (g i)
  obtain ⟨⟨z, ⟨_, n, rfl⟩⟩, e⟩ := H₁.surj z'
  refine ⟨app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V z, ⟨z, rfl⟩, ⟨g i ^ n, n, rfl⟩, ?_⟩
  rw [IsLocalizedModule.mk'_eq_iff]
  change G'₂.res (V'.basicOpen_le (g i)) (app G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V z) =
    rf (V'.basicOpen_le (g i)) (g i ^ n) • θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ (U i) (bo V (g i)) (hU i) z'
  change rf (V'.basicOpen_le (g i)) (g i ^ n) • z' = G'₁.res (V'.basicOpen_le (g i)) z at e
  rw [app_spec (U := U i) (W := bo V (g i)) (hWV := V'.basicOpen_le (g i)) (hW := hU i), ← e, map_smul]

include hβ₂ in

theorem smul_eq_zero (J : Ideal A) (hsU : ∀ U : P.affineOpens, Function.Surjective (ψ.app U))
    (hkU : ∀ U : P.affineOpens, LinearMap.ker (ψ.app U) = J • (⊤ : Submodule A (G₁.obj U.1)))
    (V : V'.affineOpens) (j : A) (hj : j ∈ J) (w : G'₂.obj V.1) : j • w = 0 := by
  apply eq_of_forall_chart G'₂ hq'₂ V
  intro U W hWV hW
  rw [map_smul, map_zero,
    smul_eq_zero_chart (G₁ := G₁) (G₂ := G₂) (G'₂ := G'₂) (η₂ := η₂) (hβ₂ := hβ₂) (ψ := ψ) J U W hW (hsU U) (hkU U) j hj]

include hq'₁ in

theorem app_ker (J : Ideal A) (hsU : ∀ U : P.affineOpens, Function.Surjective (ψ.app U))
    (hkU : ∀ U : P.affineOpens, LinearMap.ker (ψ.app U) = J • (⊤ : Submodule A (G₁.obj U.1)))
    (V : V'.affineOpens) :
    LinearMap.ker (appLin G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V) =
      J • (⊤ : Submodule A (G'₁.obj V.1)) := by
  apply le_antisymm
  · intro z hz
    rw [LinearMap.mem_ker, appLin_apply] at hz
    obtain ⟨ι, _, g, U, hg, hU⟩ := exists_cover (p := p) V
    letI : ∀ r : Set.range g, Module Γ(V', V.1) (G'₁.obj (V'.basicOpen r.1)) :=
      fun r => G'₁.moduleRestrict (V'.basicOpen_le r.1)
    haveI : ∀ r : Set.range g, IsLocalizedModule.Away r.1 (G'₁.resₗ (V'.basicOpen_le r.1)) :=
      fun r => G'₁.isLocalizedModule_res_of_isQuasicoherent hq'₁ V r.1
    rw [← mem_JΓ]
    apply Submodule.mem_of_isLocalized_span (Set.range g) hg (fun r : Set.range g => G'₁.obj (V'.basicOpen r.1))
      (fun r => G'₁.resₗ (V'.basicOpen_le r.1))
    rintro ⟨_, i, rfl⟩

    have hzi : θ G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ (U i) (bo V (g i)) (hU i) (G'₁.res (V'.basicOpen_le (g i)) z) = 0 := by
      have := app_spec G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ V (U i) (bo V (g i))
        (V'.basicOpen_le (g i)) (hU i) z
      rw [hz, map_zero] at this
      exact this.symm
    have hmem := θ_ker_le G₁ G₂ G'₁ η₁ hβ₁ G'₂ η₂ hβ₂ ψ J (U i) (bo V (g i)) (hU i) (hsU (U i)) (hkU (U i)) _ hzi
    obtain ⟨m, hm, n, e⟩ := exists_num (G'₁ := G'₁) hq'₁ J V (g i) _ ((mem_JΓ _ _ _ _).mp hmem)
    refine ⟨m, (mem_JΓ _ _ _ _).mpr hm, ⟨g i ^ n, n, rfl⟩, ?_⟩
    rw [IsLocalizedModule.mk'_eq_iff]
    exact e
  · refine Submodule.smul_le.mpr fun j hj z _ => ?_
    rw [LinearMap.mem_ker, map_smul, appLin_apply]
    exact smul_eq_zero G₁ G₂ G'₁ η₁ hη₁V hη₁U G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ J hsU hkU V j hj _

end Main

end P2Sol
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol"

theorem solution
    {A : Type u} [CommRing A]
    {P V' : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) (p : V' ⟶ P)
    (G₁ G₂ : OModulePresheaf q) (hq₁ : G₁.IsQuasicoherent) (hq₂ : G₂.IsQuasicoherent)
    (G'₁ : OModulePresheaf (p ≫ q)) (hq'₁ : G'₁.IsQuasicoherent)
    (η₁ : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (G₁.obj U.1 →ₗ[A] G'₁.obj V.1))
    (hη₁s : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : G₁.obj U.1),
      η₁ U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η₁ U V h x)
    (hη₁V : ∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
      (hV : V₁.1 ≤ V₂.1) (x : G₁.obj U.1), G'₁.res hV (η₁ U V₂ h₂ x) = η₁ U V₁ h₁ x)
    (hη₁U : ∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
      (hU : U₁.1 ≤ U₂.1) (x : G₁.obj U₂.1), η₁ U₂ V h₂ x = η₁ U₁ V h₁ (G₁.res hU x))
    (hβ₁ : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1),
      letI := (p.appLE U.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] G₁.obj U.1 ≃ₗ[Γ(V', V.1)] G'₁.obj V.1,
        ∀ x : G₁.obj U.1, β (1 ⊗ₜ x) = η₁ U V h x)
    (G'₂ : OModulePresheaf (p ≫ q)) (hq'₂ : G'₂.IsQuasicoherent)
    (η₂ : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (G₂.obj U.1 →ₗ[A] G'₂.obj V.1))
    (hη₂s : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : G₂.obj U.1),
      η₂ U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η₂ U V h x)
    (hη₂V : ∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
      (hV : V₁.1 ≤ V₂.1) (x : G₂.obj U.1), G'₂.res hV (η₂ U V₂ h₂ x) = η₂ U V₁ h₁ x)
    (hη₂U : ∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
      (hU : U₁.1 ≤ U₂.1) (x : G₂.obj U₂.1), η₂ U₂ V h₂ x = η₂ U₁ V h₁ (G₂.res hU x))
    (hβ₂ : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1),
      letI := (p.appLE U.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] G₂.obj U.1 ≃ₗ[Γ(V', V.1)] G'₂.obj V.1,
        ∀ x : G₂.obj U.1, β (1 ⊗ₜ x) = η₂ U V h x)
    (ψ : OModulePresheaf.AffHom G₁ G₂) :
    ∃ ψ' : OModulePresheaf.AffHom G'₁ G'₂,
      (∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (x : G₁.obj U.1),
        ψ'.app V (η₁ U V h x) = η₂ U V h (ψ.app U x)) ∧
      ((∀ U : P.affineOpens, Function.Surjective (ψ.app U)) →
        ∀ V : V'.affineOpens, Function.Surjective (ψ'.app V)) ∧
      (∀ J : Ideal A, (∀ U : P.affineOpens, Function.Surjective (ψ.app U)) →
        (∀ U : P.affineOpens, LinearMap.ker (ψ.app U) = J • (⊤ : Submodule A (G₁.obj U.1))) →
        ∀ V : V'.affineOpens, LinearMap.ker (ψ'.app V) = J • (⊤ : Submodule A (G'₁.obj V.1))) := by
  refine ⟨P2Sol.ψ' G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ, ?_, ?_, ?_⟩
  · intro U V h x
    exact P2Sol.app_eta G₁ G₂ G'₁ η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ U V h x
  · intro hsU V
    exact P2Sol.app_surjective G₁ G₂ G'₁ (hq'₁ := hq'₁) η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ hsU V
  · intro J hsU hkU V
    exact P2Sol.app_ker G₁ G₂ G'₁ (hq'₁ := hq'₁) η₁ hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂V hη₂U hβ₂ ψ J hsU hkU V

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol"

end S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct (solution)
