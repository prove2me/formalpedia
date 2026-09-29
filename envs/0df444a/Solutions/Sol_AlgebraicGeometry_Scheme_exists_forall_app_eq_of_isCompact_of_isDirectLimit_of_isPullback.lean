-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0a74fdb1-e074-5ab7-a766-618b9ee4a13d

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_app_eq_of_isCompact_of_isDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FunFamilySpread

theorem exists_ge_forall {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)] {κ : Type u} [Finite κ]
    (j : ι) (f : κ → ι) : ∃ m, j ≤ m ∧ ∀ k, f k ≤ m := by
  classical
  haveI := Fintype.ofFinite κ
  obtain ⟨m, hm⟩ := Finset.exists_le (insert j (Finset.univ.image f))
  exact ⟨m, hm _ (Finset.mem_insert_self _ _), fun k => hm _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ k)))⟩

lemma res_res {X : Scheme.{u}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op s) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl

lemma res_injective_of_eq {Y : Scheme.{u}} {U U' : Y.Opens} (h : U' = U) :
    Function.Injective (Y.presheaf.map (homOfLE h.le).op) := by
  intro a b hab
  have e := congrArg (Y.presheaf.map (homOfLE h.ge).op) hab
  rw [res_res, res_res] at e
  have ha : Y.presheaf.map (homOfLE (h.ge.trans h.le)).op a = a := by
    have : homOfLE (h.ge.trans h.le) = 𝟙 U := rfl
    rw [this, op_id, Y.presheaf.map_id]; rfl
  have hb : Y.presheaf.map (homOfLE (h.ge.trans h.le)).op b = b := by
    have : homOfLE (h.ge.trans h.le) = 𝟙 U := rfl
    rw [this, op_id, Y.presheaf.map_id]; rfl
  rwa [ha, hb] at e

lemma appLE_injective_of_isIso {Y Y' : Scheme.{u}} (c : Y' ⟶ Y) [IsIso c] (U : Y.Opens) (V : Y'.Opens)
    (h : V = c ⁻¹ᵁ U) : Function.Injective (c.appLE U V h.le) := by
  intro a b hab
  rw [Scheme.Hom.appLE, CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hab
  exact (ConcreteCategory.bijective_of_isIso (c.app U)).1 (res_injective_of_eq h hab)

lemma appLE_appLE_of_comp_eq {Z Y Y' : Scheme.{u}} (c : Y' ⟶ Y) (s : Y ⟶ Z) (d : Y' ⟶ Z) (hc : c ≫ s = d)
    (U : Z.Opens) (V : Y.Opens) (W : Y'.Opens) (e₁ : V ≤ s ⁻¹ᵁ U) (e₂ : W ≤ c ⁻¹ᵁ V) (e₃ : W ≤ d ⁻¹ᵁ U) (z : Γ(Z, U)) :
    c.appLE V W e₂ (s.appLE U V e₁ z) = d.appLE U W e₃ z := by
  subst hc
  rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE]

end FunFamilySpread

open FunFamilySpread in
theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    {XR : Scheme.{u}} (p : XR ⟶ X) (q : XR ⟶ Spec (CommRingCat.of R))
    (hp : IsPullback p q fX (Spec.map (CommRingCat.ofHom (g i))))
    {κ : Type u} [Finite κ] (W : κ → X.Opens) (hW : ∀ k, IsCompact (W k : Set X))
    (a : ∀ k, Γ(XR, p ⁻¹ᵁ W k)) :
    ∃ (j : ι) (hij : i ≤ j)
      (b : ∀ k, Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij))),
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k)),
      ∀ (c : XR ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = p →
        c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = q ≫ Spec.map (CommRingCat.ofHom (g j)) →
        ∀ (k : κ) (e : p ⁻¹ᵁ W k = c ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k)),
          XR.presheaf.map (eqToHom e).op
            (c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) (b k)) = a k := by
  classical

  have epre : ∀ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W k = hp.isoPullback.inv ⁻¹ᵁ (p ⁻¹ᵁ W k) := fun k => by
    rw [← Scheme.Hom.comp_preimage, hp.isoPullback_inv_fst]
  let s : ∀ k, Γ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))), (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W k) := fun k => hp.isoPullback.inv.appLE (p ⁻¹ᵁ W k) _ (epre k).le (a k)

  have step := fun k => AlgebraicGeometry.Scheme.exists_app_eq_of_isCompact_of_isDirectLimit φ g hR i fX (W k) (hW k) (s k)
  choose jk hjk tk htk using step
  obtain ⟨j, hij, hk⟩ := exists_ge_forall i jk

  have ecomp : ∀ k, (φ (jk k) j (hk k)).comp (φ i (jk k) (hjk k)) = φ i j hij := fun k =>
    RingHom.ext fun x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) (hjk k) (hk k) x
  let d : ∀ k, Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij))) ⟶
      Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i (jk k) (hjk k)))) := fun k =>
    Limits.pullback.lift (Limits.pullback.fst fX _)
      (Limits.pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom (φ (jk k) j (hk k))))
      (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ecomp])
  have hd1 : ∀ k, d k ≫ Limits.pullback.fst fX _ = Limits.pullback.fst fX _ := fun k => Limits.pullback.lift_fst _ _ _
  have hd2 : ∀ k, d k ≫ Limits.pullback.snd fX _ = Limits.pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom (φ (jk k) j (hk k))) :=
    fun k => Limits.pullback.lift_snd _ _ _
  have ed : ∀ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k ≤
      d k ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i (jk k) (hjk k))))) ⁻¹ᵁ W k) := fun k => by
    rw [← Scheme.Hom.comp_preimage, hd1]
  refine ⟨j, hij, fun k => (d k).appLE _ _ (ed k) (tk k), fun c hc1 hc2 k e => ?_⟩

  have egj : ∀ k, (g j).comp (φ (jk k) j (hk k)) = g (jk k) := fun k => RingHom.ext fun x => hR.compatibility (jk k) j (hk k) x

  let c₀ : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))) ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i (jk k) (hjk k)))) := hp.isoPullback.inv ≫ c ≫ d k
  have hc₀1 : c₀ ≫ Limits.pullback.fst fX _ = (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) := by
    simp only [c₀, Category.assoc, hd1, hc1, IsPullback.isoPullback_inv_fst]
  have hc₀2 : c₀ ≫ Limits.pullback.snd fX _ = Limits.pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom (g (jk k))) := by
    simp only [c₀, Category.assoc, hd2]
    rw [← Category.assoc c, hc2, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, egj,
      IsPullback.isoPullback_inv_snd_assoc]
  have e₀ : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W k = c₀ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i (jk k) (hjk k))))) ⁻¹ᵁ W k) := by
    rw [← Scheme.Hom.comp_preimage, hc₀1]
  have H := htk k c₀ hc₀1 hc₀2 e₀

  rw [← CategoryTheory.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map] at H ⊢
  have H' : hp.isoPullback.inv.appLE (p ⁻¹ᵁ W k) _ (epre k).le
      ((c ≫ d k).appLE _ (p ⁻¹ᵁ W k) (by rw [← Scheme.Hom.comp_preimage, Category.assoc, hd1, hc1]) (tk k)) = s k := by
    rw [appLE_appLE_of_comp_eq hp.isoPullback.inv (c ≫ d k) c₀ rfl]
    exact H
  have H'' := appLE_injective_of_isIso hp.isoPullback.inv (p ⁻¹ᵁ W k) _ (epre k) H'
  rw [← H'']
  exact (appLE_appLE_of_comp_eq c (d k) (c ≫ d k) rfl _ _ _ (ed k) _ _ (tk k))

end S_AlgebraicGeometry_Scheme_exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback (solution)
