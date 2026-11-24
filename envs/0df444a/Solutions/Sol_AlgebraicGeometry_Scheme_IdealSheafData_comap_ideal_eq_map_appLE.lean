-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:05.782028+00:00
-- url     : https://prove2.me/submissions/bd62628a-f73e-44ac-9148-0afea33f09c9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}
private theorem comap_ideal_eq_ker_pullbackFst (I : Y.IdealSheafData) (f : X ⟶ Y)
    (V : X.affineOpens) :
    (I.comap f).ideal V
      = RingHom.ker ((Limits.pullback.fst f I.subschemeι).app (V : X.Opens)).hom := by
  have hc : I.comap f = Scheme.Hom.ker (Limits.pullback.fst f I.subschemeι) := rfl
  rw [hc, ← map_bot, ideal_map_of_isAffineHom,
    show ((⊥ : (Limits.pullback f I.subschemeι).IdealSheafData).ideal) = ⊥ from ideal_bot]
  exact (RingHom.ker_eq_comap_bot _).symm
private theorem appLE_congr_hom {Z W : Scheme.{u}} {g₁ g₂ : Z ⟶ W} (h : g₁ = g₂)
    (U : W.Opens) (V : Z.Opens) (e₁ : V ≤ g₁ ⁻¹ᵁ U) :
    g₁.appLE U V e₁ = g₂.appLE U V (h ▸ e₁) := by
  subst h; rfl
private theorem map_appLE_le_ker_pullbackFst (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens) (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) :
    Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U) ≤
      RingHom.ker ((Limits.pullback.fst f I.subschemeι).app (V : X.Opens)).hom := by
  have hcond : Limits.pullback.fst f I.subschemeι ≫ f
      = Limits.pullback.snd f I.subschemeι ≫ I.subschemeι := Limits.pullback.condition
  have h2 : (Limits.pullback.fst f I.subschemeι) ⁻¹ᵁ (f ⁻¹ᵁ (U : Y.Opens))
      = (Limits.pullback.snd f I.subschemeι) ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ (U : Y.Opens)) := by
    have h3 := congrArg
      (fun g : (Limits.pullback f I.subschemeι) ⟶ Y => g ⁻¹ᵁ (U : Y.Opens)) hcond
    simpa using h3
  have hle : (Limits.pullback.fst f I.subschemeι) ⁻¹ᵁ (V : X.Opens)
      ≤ (Limits.pullback.snd f I.subschemeι) ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ (U : Y.Opens)) := by
    rw [← h2]
    intro x hx
    exact e hx
  have happ : f.appLE (U : Y.Opens) (V : X.Opens) e
        ≫ (Limits.pullback.fst f I.subschemeι).app (V : X.Opens)
      = I.subschemeι.app (U : Y.Opens)
        ≫ (Limits.pullback.snd f I.subschemeι).appLE (I.subschemeι ⁻¹ᵁ (U : Y.Opens))
            ((Limits.pullback.fst f I.subschemeι) ⁻¹ᵁ (V : X.Opens)) hle := by
    rw [← Scheme.Hom.appLE_eq_app (Limits.pullback.fst f I.subschemeι),
      ← Scheme.Hom.appLE_eq_app I.subschemeι, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hcond]
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  have hker : (I.subschemeι.app (U : Y.Opens)).hom a = 0 := by
    have hd := I.ker_subschemeι_app U
    rw [← RingHom.mem_ker, hd]
    exact ha
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, happ, CommRingCat.hom_comp,
    RingHom.comp_apply, hker, map_zero]
private theorem appLE_top_eq_appTop (f : X ⟶ Y) (e0 : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE (⊤ : Y.Opens) (⊤ : X.Opens) e0 = f.appTop := by
  have h1 : X.presheaf.map (homOfLE e0).op = 𝟙 Γ(X, ⊤) := X.presheaf.map_id (op (⊤ : X.Opens))
  calc f.appLE (⊤ : Y.Opens) (⊤ : X.Opens) e0
      = f.app (⊤ : Y.Opens) ≫ X.presheaf.map (homOfLE e0).op := rfl
    _ = f.app (⊤ : Y.Opens) ≫ 𝟙 Γ(X, ⊤) := by rw [h1]
    _ = f.appTop := Category.comp_id _
private theorem exists_hom_comp_eq_appLE_comp (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens) (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens))
    (C : CommRingCat.{u}) (q : Γ(X, (V : X.Opens)) ⟶ C)
    (hq : Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U)
      ≤ RingHom.ker q.hom) :
    ∃ ψ : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ (U : Y.Opens)) ⟶ C,
      I.subschemeι.app (U : Y.Opens) ≫ ψ = f.appLE (U : Y.Opens) (V : X.Opens) e ≫ q := by
  refine ⟨(I.subschemeObjIso U).hom ≫ CommRingCat.ofHom
      (Ideal.Quotient.lift (I.ideal U)
        (q.hom.comp (f.appLE (U : Y.Opens) (V : X.Opens) e).hom) ?_), ?_⟩
  · intro a ha
    have h := hq (Ideal.mem_map_of_mem _ ha)
    rw [RingHom.mem_ker] at h
    exact h
  · rw [subschemeι_app, Category.assoc, Iso.inv_hom_id_assoc]
    ext a
    rfl
private theorem exists_hom_pullbackFst_app_comp_eq (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens) (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens))
    (C : CommRingCat.{u}) (q : Γ(X, (V : X.Opens)) ⟶ C)
    (ψ : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ (U : Y.Opens)) ⟶ C)
    (hring : I.subschemeι.app (U : Y.Opens) ≫ ψ
      = f.appLE (U : Y.Opens) (V : X.Opens) e ≫ q) :
    ∃ θ : Γ(Limits.pullback f I.subschemeι,
        Limits.pullback.fst f I.subschemeι ⁻¹ᵁ (V : X.Opens)) ⟶ C,
      (Limits.pullback.fst f I.subschemeι).app (V : X.Opens) ≫ θ = q := by
  have hV : IsAffineOpen (V : X.Opens) := V.2
  have hU : IsAffineOpen (U : Y.Opens) := U.2
  have hf := IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e
  have hι := IsAffineOpen.SpecMap_appLE_fromSpec I.subschemeι hU
      (hU.preimage I.subschemeι) (le_refl (I.subschemeι ⁻¹ᵁ (U : Y.Opens)))
  have hsq : (Spec.map q ≫ hV.fromSpec) ≫ f
      = (Spec.map ψ ≫ (hU.preimage I.subschemeι).fromSpec) ≫ I.subschemeι := by
    rw [Category.assoc, Category.assoc, ← hf, ← hι, ← Category.assoc, ← Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp, Scheme.Hom.appLE_eq_app, hring]
  obtain ⟨g, hlift⟩ : ∃ g : Spec C ⟶ Limits.pullback f I.subschemeι,
      g ≫ Limits.pullback.fst f I.subschemeι = Spec.map q ≫ hV.fromSpec :=
    ⟨Limits.pullback.lift _ _ hsq, Limits.pullback.lift_fst _ _ _⟩
  have hpre : (⊤ : (Spec C).Opens)
      ≤ g ⁻¹ᵁ (Limits.pullback.fst f I.subschemeι ⁻¹ᵁ (V : X.Opens)) := by
    have h3 := congrArg (fun h : Spec C ⟶ X => h ⁻¹ᵁ (V : X.Opens)) hlift
    have h4 : g ⁻¹ᵁ (Limits.pullback.fst f I.subschemeι ⁻¹ᵁ (V : X.Opens))
        = Spec.map q ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ (V : X.Opens)) := by simpa using h3
    rw [h4, hV.fromSpec_preimage_self]
    simp
  have e₁ : (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) ≤ hV.fromSpec ⁻¹ᵁ (V : X.Opens) :=
    le_of_eq (hV.fromSpec_preimage_self).symm
  have e₂ : (⊤ : (Spec C).Opens)
      ≤ Spec.map q ⁻¹ᵁ (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) := by simp
  have hsplit := Scheme.Hom.appLE_comp_appLE (Spec.map q) hV.fromSpec (V : X.Opens)
      (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) (⊤ : (Spec C).Opens) e₁ e₂
  have h0 : ∀ i : (op (⊤ : (Spec Γ(X, (V : X.Opens))).Opens))
      ⟶ op (⊤ : (Spec Γ(X, (V : X.Opens))).Opens),
      (Spec Γ(X, (V : X.Opens))).presheaf.map i = 𝟙 _ := by
    intro i
    have hi : i = 𝟙 _ := rfl
    rw [hi, CategoryTheory.Functor.map_id]
  have hdef : hV.fromSpec.appLE (V : X.Opens) (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) e₁
      = hV.fromSpec.app (V : X.Opens)
        ≫ (Spec Γ(X, (V : X.Opens))).presheaf.map (homOfLE e₁).op := rfl
  have ha : hV.fromSpec.appLE (V : X.Opens) (⊤ : (Spec Γ(X, (V : X.Opens))).Opens) e₁
      = (Scheme.ΓSpecIso Γ(X, (V : X.Opens))).inv := by
    rw [hdef, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp, ← op_comp,
      h0, Category.comp_id]
  have hb : (Spec.map q).appTop
      = (Scheme.ΓSpecIso Γ(X, (V : X.Opens))).hom ≫ q ≫ (Scheme.ΓSpecIso C).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  refine ⟨g.appLE (Limits.pullback.fst f I.subschemeι ⁻¹ᵁ (V : X.Opens))
      (⊤ : (Spec C).Opens) hpre ≫ (Scheme.ΓSpecIso C).hom, ?_⟩
  rw [← Category.assoc, ← Scheme.Hom.appLE_eq_app (Limits.pullback.fst f I.subschemeι),
    Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hlift, ← hsplit, ha, appLE_top_eq_appTop, hb]
  simp
private theorem ker_pullbackFst_le_map_appLE (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens) (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) :
    RingHom.ker ((Limits.pullback.fst f I.subschemeι).app (V : X.Opens)).hom ≤
      Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U) := by
  obtain ⟨C, q, hq⟩ : ∃ (C : CommRingCat.{u}) (q : Γ(X, (V : X.Opens)) ⟶ C),
      RingHom.ker q.hom = Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U) :=
    ⟨_, CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom (I.ideal U))), Ideal.mk_ker⟩
  obtain ⟨ψ, hψ⟩ := exists_hom_comp_eq_appLE_comp I f U V e C q (le_of_eq hq.symm)
  obtain ⟨θ, hθ⟩ := exists_hom_pullbackFst_app_comp_eq I f U V e C q ψ hψ
  rw [← hq]
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  rw [← hθ, CommRingCat.hom_comp, RingHom.comp_apply, hx, map_zero]
end AlgebraicGeometry.Scheme.IdealSheafData
namespace FunctorialResolution.Blowup
end FunctorialResolution.Blowup
namespace AlgebraicGeometry.Scheme.IdealSheafData
end AlgebraicGeometry.Scheme.IdealSheafData
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}
namespace AlgebraicGeometry.Scheme.IdealSheafData
theorem _root_.solution (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens)
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE (U : Y.Opens) (V : X.Opens) e).hom := by
  rw [comap_ideal_eq_ker_pullbackFst I f V]
  exact le_antisymm (ker_pullbackFst_le_map_appLE I f U V e)
    (map_appLE_le_ker_pullbackFst I f U V e)
end AlgebraicGeometry.Scheme.IdealSheafData
