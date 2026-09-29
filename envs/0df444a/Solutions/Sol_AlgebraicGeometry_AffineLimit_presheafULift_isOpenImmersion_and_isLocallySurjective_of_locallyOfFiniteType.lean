-- Prove2me | solution 1 for AlgebraicGeometry.AffineLimit.presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4d396eb4-b4d1-5e69-9926-7fc547313f1b

import Mathlib
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_AffineLimit_presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_AffineLimit_presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage IsOpenImmersion.lift Scheme.openCoverOfIsOpenCover_X Scheme.zariskiTopology morphismRestrict_ι Scheme.Opens.range_ι Scheme.Hom IsAffine LocallyOfFiniteType Spec Spec.map Scheme IsOpenImmersion Scheme.openCoverOfIsOpenCover_f Scheme.Hom.isoImage_inv_ι Spec.preimage HasRingHomProperty.Spec_iff Scheme.Cover.glueMorphisms Scheme.Opens.ι_apply Scheme.isBasis_affineOpens IsAffineOpen Scheme.Opens Scheme.homOfLE_ι Scheme.Hom.coe_image Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.Opens.iSupOpenCover HasRingHomProperty IsOpenImmersion.lift_fac Scheme.Hom.comp_apply Scheme.Cover"
namespace AffineLimit
p2m_export "AlgebraicGeometry.AffineLimit" "specOver IsLFPSurj IsLFPInj HomIsLFP"
p2m_open "AlgebraicGeometry.AffineLimit AlgebraicGeometry"

namespace LFPExtend

variable {R : Type u} [CommRing R] {G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1)}
  {ι : Type u} {X : ι → Scheme.{u}} (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶ G.overTotal)

structure Hyps : Prop where
  sheaf : Presieve.IsSheaf Scheme.zariskiTopology G.overTotal
  surj : IsLFPSurj G
  inj : IsLFPInj G
  homLFP : ∀ i, HomIsLFP (uliftYonedaEquiv (f i)).1
  charts : ∀ ⦃T : Scheme.{u}⦄ (x : uliftYoneda.{u + 1}.obj T ⟶ G.overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv x).1 →
      ∃ (U : ι → T.Opens) (φ : ∀ i, (↑(U i) : Scheme.{u}) ⟶ X i),
        (⨆ i, U i) = ⊤ ∧
        ∀ i, uliftYoneda.{u + 1}.map (φ i) ≫ f i = uliftYoneda.{u + 1}.map (U i).ι ≫ x ∧
          ∀ ⦃T' : Scheme.{u}⦄ (ψ : T' ⟶ T) (φ' : T' ⟶ X i),
            LocallyOfFiniteType (ψ ≫ (uliftYonedaEquiv x).1) →
            uliftYoneda.{u + 1}.map φ' ≫ f i = uliftYoneda.{u + 1}.map ψ ≫ x →
            ∃ χ : T' ⟶ ↑(U i), χ ≫ (U i).ι = ψ ∧ χ ≫ φ i = φ'

section general

variable {F : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)}

lemma uliftYonedaEquiv_map_comp {W W' : Scheme.{u}} (g : W' ⟶ W) (a : uliftYoneda.{u + 1}.obj W ⟶ F) :
    uliftYonedaEquiv (uliftYoneda.{u + 1}.map g ≫ a) = F.map g.op (uliftYonedaEquiv a) :=
  (uliftYonedaEquiv_naturality (X := op W) a g.op).symm

lemma app_up {W W' : Scheme.{u}} (g : W' ⟶ W) (a : uliftYoneda.{u + 1}.obj W ⟶ F) :
    a.app (op W') ⟨g⟩ = uliftYonedaEquiv (uliftYoneda.{u + 1}.map g ≫ a) := by
  rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]

lemma hom_ext_of_openCover (hF : Presieve.IsSheaf Scheme.zariskiTopology F) {W : Scheme.{u}}
    (𝒰 : W.OpenCover) {a b : uliftYoneda.{u + 1}.obj W ⟶ F}
    (h : ∀ j, uliftYoneda.{u + 1}.map (𝒰.f j) ≫ a = uliftYoneda.{u + 1}.map (𝒰.f j) ≫ b) : a = b := by
  apply uliftYonedaEquiv.injective
  refine (hF.isSheafFor _ 𝒰.mem_grothendieckTopology).isSeparatedFor.ext ?_
  rintro Y g ⟨j⟩
  rw [← uliftYonedaEquiv_map_comp, ← uliftYonedaEquiv_map_comp, h j]

lemma exists_isAffineOpen_mem_le {W : Scheme.{u}} {U : W.Opens} {p : W} (hp : p ∈ U) :
    ∃ W₀ : W.Opens, IsAffineOpen W₀ ∧ p ∈ W₀ ∧ W₀ ≤ U := by
  obtain ⟨W₀, hW₀, hpW₀, hle⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens W)) hp
  exact ⟨W₀, hW₀, hpW₀, hle⟩

lemma locallyOfFiniteType_Spec_algebraMap (A₀ : Type u) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom]
  exact RingHom.finiteType_algebraMap.mpr ‹_›

lemma Spec_map_algHom_comp {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (g : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]

lemma Spec_map_val_comp_inclusion {A : Type u} [CommRing A] [Algebra R A] {S S' : Subalgebra R A} (hle : S ≤ S') :
    Spec.map (CommRingCat.ofHom S'.val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom) =
      Spec.map (CommRingCat.ofHom S.val.toRingHom) := by
  rw [← Spec.map_comp]; rfl

lemma Spec_map_val_comp_algebraMap {A : Type u} [CommRing A] [Algebra R A] (S : Subalgebra R A) :
    Spec.map (CommRingCat.ofHom S.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥S)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [← Spec.map_comp]; rfl

end general

lemma fst_uliftYonedaEquiv_map_comp {W W' : Scheme.{u}} (g : W' ⟶ W)
    (a : uliftYoneda.{u + 1}.obj W ⟶ G.overTotal) :
    (uliftYonedaEquiv (uliftYoneda.{u + 1}.map g ≫ a)).1 = g ≫ (uliftYonedaEquiv a).1 := by
  rw [uliftYonedaEquiv_map_comp]; rfl

variable {f} in
lemma fst_eq_of_comp_eq {W W' : Scheme.{u}} {i : ι} {a : W ⟶ X i} {y : uliftYoneda.{u + 1}.obj W' ⟶ G.overTotal}
    {g : W ⟶ W'} (h : uliftYoneda.{u + 1}.map a ≫ f i = uliftYoneda.{u + 1}.map g ≫ y) :
    a ≫ (uliftYonedaEquiv (f i)).1 = g ≫ (uliftYonedaEquiv y).1 := by
  rw [← fst_uliftYonedaEquiv_map_comp, ← fst_uliftYonedaEquiv_map_comp, h]

lemma hom_ext_overTotal {W : Scheme.{u}} {a b : uliftYoneda.{u + 1}.obj W ⟶ G.overTotal}
    (t : W ⟶ Spec (CommRingCat.of R)) (ha : (uliftYonedaEquiv a).1 = t) (hb : (uliftYonedaEquiv b).1 = t)
    (h : Functor.OverTotal.toFibre (Over.mk t) (uliftYonedaEquiv a) ha =
      Functor.OverTotal.toFibre (Over.mk t) (uliftYonedaEquiv b) hb) : a = b := by
  apply uliftYonedaEquiv.injective
  rw [← Functor.OverTotal.ofFibre_toFibre (Over.mk t) (uliftYonedaEquiv a) ha, h,
    Functor.OverTotal.ofFibre_toFibre]

lemma toFibre_map_comp {W W' : Scheme.{u}} {t : W ⟶ Spec (CommRingCat.of R)} {t' : W' ⟶ Spec (CommRingCat.of R)}
    (g : W' ⟶ W) (hg : g ≫ t = t') (a : uliftYoneda.{u + 1}.obj W ⟶ G.overTotal)
    (ha : (uliftYonedaEquiv a).1 = t) (ha' : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map g ≫ a)).1 = t') :
    Functor.OverTotal.toFibre (Over.mk t') (uliftYonedaEquiv (uliftYoneda.{u + 1}.map g ≫ a)) ha' =
      G.map (Over.homMk g hg : Over.mk t' ⟶ Over.mk t).op
        (Functor.OverTotal.toFibre (Over.mk t) (uliftYonedaEquiv a) ha) := by
  have hb' : (G.overTotal.map (Over.homMk g hg : Over.mk t' ⟶ Over.mk t).left.op (uliftYonedaEquiv a)).1 =
      (Over.mk t').hom := (congrArg (g ≫ ·) ha).trans hg
  exact (Functor.OverTotal.toFibre_congr _ (uliftYonedaEquiv_map_comp g a) ha' hb').trans
    (Functor.OverTotal.toFibre_naturality (Over.homMk g hg : Over.mk t' ⟶ Over.mk t) _ ha hb')

lemma eq_of_comp_eq_of_locallyOfFiniteType (h : Hyps f) {i : ι} {T : Scheme.{u}} (a b : T ⟶ X i)
    [LocallyOfFiniteType (a ≫ (uliftYonedaEquiv (f i)).1)]
    (hab : uliftYoneda.{u + 1}.map a ≫ f i = uliftYoneda.{u + 1}.map b ≫ f i) : a = b := by
  have hy1 : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map a ≫ f i)).1 = a ≫ (uliftYonedaEquiv (f i)).1 :=
    fst_uliftYonedaEquiv_map_comp a (f i)
  obtain ⟨U, φ, -, hU⟩ := h.charts (uliftYoneda.{u + 1}.map a ≫ f i) (by rw [hy1]; infer_instance)
  obtain ⟨-, cart⟩ := hU i
  have hl : LocallyOfFiniteType (𝟙 T ≫ (uliftYonedaEquiv (uliftYoneda.{u + 1}.map a ≫ f i)).1) := by
    rw [Category.id_comp, hy1]; infer_instance
  obtain ⟨χa, ha1, ha2⟩ := cart (𝟙 T) a hl (by rw [CategoryTheory.Functor.map_id, Category.id_comp])
  obtain ⟨χb, hb1, hb2⟩ := cart (𝟙 T) b hl (by rw [CategoryTheory.Functor.map_id, Category.id_comp]; exact hab.symm)
  have : χa = χb := by rw [← cancel_mono (U i).ι, ha1, hb1]
  rw [← ha2, ← hb2, this]

lemma eq_of_comp_eq_Spec (h : Hyps f) {i : ι} (B : Type u) [CommRing B] [Algebra R B]
    (a b : Spec (CommRingCat.of B) ⟶ X i)
    (ha : a ≫ (uliftYonedaEquiv (f i)).1 = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hab : uliftYoneda.{u + 1}.map a ≫ f i = uliftYoneda.{u + 1}.map b ≫ f i) : a = b := by
  have hb : b ≫ (uliftYonedaEquiv (f i)).1 = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [← ha, ← fst_uliftYonedaEquiv_map_comp, ← fst_uliftYonedaEquiv_map_comp, hab]
  obtain ⟨A₀, hA₀, a₀, ha₀, haa₀⟩ := (h.homLFP i).1 B a ha
  obtain ⟨A₀', hA₀', b₀, hb₀, hbb₀⟩ := (h.homLFP i).1 B b hb

  obtain ⟨A₁, hA₁, a₁, b₁, ha₁, haa₁, hb₁, hbb₁⟩ : ∃ (A₁ : Subalgebra R B) (_ : A₁.FG)
      (a₁ b₁ : Spec (CommRingCat.of ↥A₁) ⟶ X i),
      a₁ ≫ (uliftYonedaEquiv (f i)).1 = Spec.map (CommRingCat.ofHom (algebraMap R ↥A₁)) ∧
      Spec.map (CommRingCat.ofHom A₁.val.toRingHom) ≫ a₁ = a ∧
      b₁ ≫ (uliftYonedaEquiv (f i)).1 = Spec.map (CommRingCat.ofHom (algebraMap R ↥A₁)) ∧
      Spec.map (CommRingCat.ofHom A₁.val.toRingHom) ≫ b₁ = b :=
    ⟨A₀ ⊔ A₀', hA₀.sup hA₀',
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_sup_left : A₀ ≤ A₀ ⊔ A₀')).toRingHom) ≫ a₀,
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_sup_right : A₀' ≤ A₀ ⊔ A₀')).toRingHom) ≫ b₀,
      by rw [Category.assoc, ha₀, Spec_map_algHom_comp],
      by rw [← Category.assoc, Spec_map_val_comp_inclusion]; exact haa₀,
      by rw [Category.assoc, hb₀, Spec_map_algHom_comp],
      by rw [← Category.assoc, Spec_map_val_comp_inclusion]; exact hbb₀⟩
  have e1 : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map a₁ ≫ f i)).1 =
      Spec.map (CommRingCat.ofHom (algebraMap R ↥A₁)) := by
    rw [fst_uliftYonedaEquiv_map_comp]; exact ha₁
  have e2 : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map b₁ ≫ f i)).1 =
      Spec.map (CommRingCat.ofHom (algebraMap R ↥A₁)) := by
    rw [fst_uliftYonedaEquiv_map_comp]; exact hb₁
  have E1 : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map (Spec.map (CommRingCat.ofHom A₁.val.toRingHom)) ≫
      uliftYoneda.{u + 1}.map a₁ ≫ f i)).1 = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [← Functor.map_comp_assoc, haa₁, fst_uliftYonedaEquiv_map_comp]; exact ha
  have E2 : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map (Spec.map (CommRingCat.ofHom A₁.val.toRingHom)) ≫
      uliftYoneda.{u + 1}.map b₁ ≫ f i)).1 = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [← Functor.map_comp_assoc, hbb₁, fst_uliftYonedaEquiv_map_comp]; exact hb

  obtain ⟨A₂, hA₂, hle, hA₂eq⟩ := h.inj B A₁ hA₁
    (Functor.OverTotal.toFibre (specOver R ↥A₁) (uliftYonedaEquiv (uliftYoneda.{u + 1}.map a₁ ≫ f i)) e1)
    (Functor.OverTotal.toFibre (specOver R ↥A₁) (uliftYonedaEquiv (uliftYoneda.{u + 1}.map b₁ ≫ f i)) e2)
    ((toFibre_map_comp (Spec.map (CommRingCat.ofHom A₁.val.toRingHom)) (Spec_map_val_comp_algebraMap A₁)
        _ e1 E1).symm.trans
      ((Functor.OverTotal.toFibre_congr _
        (by rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, haa₁, hbb₁, hab]) E1 E2).trans
      (toFibre_map_comp (Spec.map (CommRingCat.ofHom A₁.val.toRingHom)) (Spec_map_val_comp_algebraMap A₁)
        _ e2 E2)))
  have ha₂ : (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom) ≫ a₁) ≫
      (uliftYonedaEquiv (f i)).1 = Spec.map (CommRingCat.ofHom (algebraMap R ↥A₂)) := by
    rw [Category.assoc, ha₁, Spec_map_algHom_comp]
  have hb₂ : (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom) ≫ b₁) ≫
      (uliftYonedaEquiv (f i)).1 = Spec.map (CommRingCat.ofHom (algebraMap R ↥A₂)) := by
    rw [Category.assoc, hb₁, Spec_map_algHom_comp]
  have E1' : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) ≫ uliftYoneda.{u + 1}.map a₁ ≫ f i)).1 =
      Spec.map (CommRingCat.ofHom (algebraMap R ↥A₂)) := by
    rw [← Functor.map_comp_assoc, fst_uliftYonedaEquiv_map_comp]; exact ha₂
  have E2' : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) ≫ uliftYoneda.{u + 1}.map b₁ ≫ f i)).1 =
      Spec.map (CommRingCat.ofHom (algebraMap R ↥A₂)) := by
    rw [← Functor.map_comp_assoc, fst_uliftYonedaEquiv_map_comp]; exact hb₂
  have hab₂ : uliftYoneda.{u + 1}.map (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom) ≫ a₁) ≫
      f i = uliftYoneda.{u + 1}.map (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom) ≫ b₁) ≫
      f i := by
    rw [Functor.map_comp_assoc, Functor.map_comp_assoc]
    refine hom_ext_overTotal (Spec.map (CommRingCat.ofHom (algebraMap R ↥A₂))) E1' E2' ?_
    exact (toFibre_map_comp _ (Spec_map_algHom_comp _) _ e1 E1').trans
      (hA₂eq.trans (toFibre_map_comp _ (Spec_map_algHom_comp _) _ e2 E2').symm)
  haveI : Algebra.FiniteType R ↥A₂ := (Subalgebra.fg_iff_finiteType A₂).mp hA₂
  haveI : LocallyOfFiniteType ((Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom) ≫ a₁) ≫
      (uliftYonedaEquiv (f i)).1) := by
    rw [ha₂]; exact locallyOfFiniteType_Spec_algebraMap ↥A₂
  have h₂ := eq_of_comp_eq_of_locallyOfFiniteType f h _ _ hab₂
  rw [← haa₁, ← hbb₁, ← Spec_map_val_comp_inclusion hle, Category.assoc, Category.assoc, h₂]

lemma eq_of_comp_eq (h : Hyps f) {i : ι} {W : Scheme.{u}} (a b : W ⟶ X i)
    (hab : uliftYoneda.{u + 1}.map a ≫ f i = uliftYoneda.{u + 1}.map b ≫ f i) : a = b := by
  refine Scheme.Cover.hom_ext W.affineCover _ _ fun j => ?_

  set e := (W.affineCover.X j).isoSpec
  suffices e.inv ≫ W.affineCover.f j ≫ a = e.inv ≫ W.affineCover.f j ≫ b by
    simpa using congrArg (e.hom ≫ ·) this
  set t := (e.inv ≫ W.affineCover.f j ≫ a) ≫ (uliftYonedaEquiv (f i)).1 with ht
  letI : Algebra R Γ(W.affineCover.X j, ⊤) := (Spec.preimage t).hom.toAlgebra
  refine eq_of_comp_eq_Spec f h Γ(W.affineCover.X j, ⊤) _ _ ?_ (by simp only [Functor.map_comp, Category.assoc, hab])
  rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]

structure LocalLift {T : Scheme.{u}} (x : uliftYoneda.{u + 1}.obj T ⟶ G.overTotal) (i : ι) where

  V : T.Opens

  φ : (↑V : Scheme.{u}) ⟶ X i
  w : uliftYoneda.{u + 1}.map φ ≫ f i = uliftYoneda.{u + 1}.map V.ι ≫ x

variable {T : Scheme.{u}} (x : uliftYoneda.{u + 1}.obj T ⟶ G.overTotal)

abbrev chartOpen (i : ι) : T.Opens := ⨆ s : LocalLift f x i, s.V

lemma le_chartOpen {i : ι} (s : LocalLift f x i) : s.V ≤ chartOpen f x i :=
  le_iSup (fun s : LocalLift f x i => s.V) s

noncomputable abbrev chartCover (i : ι) : (↑(chartOpen f x i) : Scheme.{u}).OpenCover :=
  Scheme.Opens.iSupOpenCover (fun s : LocalLift f x i => s.V)

lemma chartCover_f_ι {i : ι} (s : LocalLift f x i) : (chartCover f x i).f s ≫ (chartOpen f x i).ι = s.V.ι :=
  T.homOfLE_ι (le_chartOpen f x s)

noncomputable def chartMap (h : Hyps f) (i : ι) : (↑(chartOpen f x i) : Scheme.{u}) ⟶ X i :=
  Scheme.Cover.glueMorphisms (chartCover f x i)
    (fun s => s.φ) (fun s t => eq_of_comp_eq f h _ _ (by

      have hw : ∀ r : LocalLift f x i,
          uliftYoneda.{u + 1}.map (show (chartCover f x i).X r ⟶ X i from r.φ) ≫ f i =
            uliftYoneda.{u + 1}.map ((chartCover f x i).f r) ≫ uliftYoneda.{u + 1}.map (chartOpen f x i).ι ≫ x := by
        intro r
        rw [← uliftYoneda.{u + 1}.map_comp_assoc, chartCover_f_ι]
        exact r.w
      rw [uliftYoneda.{u + 1}.map_comp_assoc, uliftYoneda.{u + 1}.map_comp_assoc, hw s, hw t,
        ← uliftYoneda.{u + 1}.map_comp_assoc, pullback.condition, uliftYoneda.{u + 1}.map_comp_assoc]))

lemma chartCover_f_chartMap (h : Hyps f) {i : ι} (s : LocalLift f x i) :
    (chartCover f x i).f s ≫ chartMap f x h i = s.φ :=
  Scheme.Cover.ι_glueMorphisms (chartCover f x i) _ _ s

lemma chartMap_w (h : Hyps f) (i : ι) :
    uliftYoneda.{u + 1}.map (chartMap f x h i) ≫ f i = uliftYoneda.{u + 1}.map (chartOpen f x i).ι ≫ x := by
  refine hom_ext_of_openCover h.sheaf (chartCover f x i) fun s => ?_
  rw [← uliftYoneda.{u + 1}.map_comp_assoc, ← uliftYoneda.{u + 1}.map_comp_assoc, chartCover_f_chartMap,
    chartCover_f_ι]
  exact s.w

lemma image_preimage_le_chartOpen (V : T.Opens) {T₀ : Scheme.{u}}
    (x₀ : uliftYoneda.{u + 1}.obj T₀ ⟶ G.overTotal) (π : (↑V : Scheme.{u}) ⟶ T₀)
    (hπ : uliftYoneda.{u + 1}.map π ≫ x₀ = uliftYoneda.{u + 1}.map V.ι ≫ x)
    {i : ι} (U₀ : T₀.Opens) (φ₀ : (↑U₀ : Scheme.{u}) ⟶ X i)
    (h₀ : uliftYoneda.{u + 1}.map φ₀ ≫ f i = uliftYoneda.{u + 1}.map U₀.ι ≫ x₀) :
    V.ι ''ᵁ (π ⁻¹ᵁ U₀) ≤ chartOpen f x i :=
  le_chartOpen f x
    { V := V.ι ''ᵁ (π ⁻¹ᵁ U₀)
      φ := (V.ι.isoImage (π ⁻¹ᵁ U₀)).inv ≫ (π ∣_ U₀) ≫ φ₀
      w := by
        rw [uliftYoneda.{u + 1}.map_comp_assoc, uliftYoneda.{u + 1}.map_comp_assoc, h₀,
          ← uliftYoneda.{u + 1}.map_comp_assoc (π ∣_ U₀), morphismRestrict_ι, uliftYoneda.{u + 1}.map_comp_assoc,
          hπ, ← uliftYoneda.{u + 1}.map_comp_assoc, ← uliftYoneda.{u + 1}.map_comp_assoc, Category.assoc,
          Scheme.Hom.isoImage_inv_ι] }

lemma exists_descent (h : Hyps f) (V : T.Opens) (hV : IsAffineOpen V) :
    ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra R A₀) (_ : Algebra.FiniteType R A₀)
      (x₀ : uliftYoneda.{u + 1}.obj (Spec (CommRingCat.of A₀)) ⟶ G.overTotal)
      (π : (↑V : Scheme.{u}) ⟶ Spec (CommRingCat.of A₀)),
      (uliftYonedaEquiv x₀).1 = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) ∧
      uliftYoneda.{u + 1}.map π ≫ x₀ = uliftYoneda.{u + 1}.map V.ι ≫ x := by
  haveI : IsAffine (↑V : Scheme.{u}) := hV
  set e := (↑V : Scheme.{u}).isoSpec with he
  set xA := uliftYoneda.{u + 1}.map (e.inv ≫ V.ι) ≫ x with hxA
  letI : Algebra R Γ(↑V, ⊤) := (Spec.preimage (uliftYonedaEquiv xA).1).hom.toAlgebra
  have hr : (uliftYonedaEquiv xA).1 = Spec.map (CommRingCat.ofHom (algebraMap R Γ(↑V, ⊤))) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨A₀, hA₀, g₀, hg₀⟩ := h.surj Γ(↑V, ⊤) (Functor.OverTotal.toFibre (specOver R Γ(↑V, ⊤)) (uliftYonedaEquiv xA) hr)
  haveI : Algebra.FiniteType R ↥A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  set x₀ : uliftYoneda.{u + 1}.obj (Spec (CommRingCat.of ↥A₀)) ⟶ G.overTotal :=
    uliftYonedaEquiv.symm (Functor.OverTotal.ofFibre (specOver R ↥A₀) g₀) with hx₀def
  have hx₀ : uliftYonedaEquiv x₀ = Functor.OverTotal.ofFibre (specOver R ↥A₀) g₀ := Equiv.apply_symm_apply _ _
  have hx₀1 : (uliftYonedaEquiv x₀).1 = Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀)) := by rw [hx₀]; rfl
  have E : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map (Spec.map (CommRingCat.ofHom A₀.val.toRingHom)) ≫ x₀)).1 =
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(↑V, ⊤))) := by
    rw [fst_uliftYonedaEquiv_map_comp, hx₀1, Spec_map_val_comp_algebraMap]
  refine ⟨↥A₀, inferInstance, inferInstance, inferInstance, x₀, e.hom ≫ Spec.map (CommRingCat.ofHom A₀.val.toRingHom),
    hx₀1, ?_⟩
  suffices uliftYoneda.{u + 1}.map (Spec.map (CommRingCat.ofHom A₀.val.toRingHom)) ≫ x₀ = xA from
    (uliftYoneda.{u + 1}.map_comp_assoc _ _ _).trans (((congrArg (uliftYoneda.{u + 1}.map e.hom ≫ ·) this)).trans
      (by rw [hxA, ← uliftYoneda.{u + 1}.map_comp_assoc, e.hom_inv_id_assoc]))
  refine hom_ext_overTotal _ E hr ?_
  rw [toFibre_map_comp _ (Spec_map_val_comp_algebraMap A₀) x₀ hx₀1 E, ← hg₀]
  congr 1
  exact (Functor.OverTotal.toFibre_congr _ hx₀ hx₀1 rfl).trans (Functor.OverTotal.toFibre_ofFibre _ g₀)

variable {x} in

lemma mem_of_comp_eq (h : Hyps f) {i : ι} (A₀ : Type u) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
    (x₀ : uliftYoneda.{u + 1}.obj (Spec (CommRingCat.of A₀)) ⟶ G.overTotal)
    (hx₀ : (uliftYonedaEquiv x₀).1 = Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
    (U₀ : (Spec (CommRingCat.of A₀)).Opens) (φ₀ : (↑U₀ : Scheme.{u}) ⟶ X i)
    (cart₀ : ∀ ⦃T' : Scheme.{u}⦄ (ψ : T' ⟶ Spec (CommRingCat.of A₀)) (φ' : T' ⟶ X i),
      LocallyOfFiniteType (ψ ≫ (uliftYonedaEquiv x₀).1) →
      uliftYoneda.{u + 1}.map φ' ≫ f i = uliftYoneda.{u + 1}.map ψ ≫ x₀ →
      ∃ χ : T' ⟶ ↑U₀, χ ≫ U₀.ι = ψ ∧ χ ≫ φ₀ = φ')
    (B : Type u) [CommRing B] (k : A₀ →+* B) (b : Spec (CommRingCat.of B) ⟶ X i)
    (hb : uliftYoneda.{u + 1}.map b ≫ f i = uliftYoneda.{u + 1}.map (Spec.map (CommRingCat.ofHom k)) ≫ x₀)
    (q : Spec (CommRingCat.of B)) : Spec.map (CommRingCat.ofHom k) q ∈ U₀ := by
  letI : Algebra R B := (k.comp (algebraMap R A₀)).toAlgebra
  let kₐ : A₀ →ₐ[R] B := { k with commutes' := fun _ => rfl }
  have hkR : Spec.map (CommRingCat.ofHom k) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := Spec_map_algHom_comp kₐ
  have hbR : b ≫ (uliftYonedaEquiv (f i)).1 = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [fst_eq_of_comp_eq hb, hx₀, hkR]
  obtain ⟨B₀, hB₀, b₀, hb₀R, hbb₀⟩ := (h.homLFP i).1 B b hbR

  obtain ⟨B₁, hB₁, h01, κ, hκ⟩ : ∃ (B₁ : Subalgebra R B) (_ : B₁.FG) (_ : B₀ ≤ B₁) (κ : A₀ →ₐ[R] ↥B₁),
      B₁.val.comp κ = kₐ :=
    ⟨B₀ ⊔ kₐ.range, hB₀.sup (by rw [← Algebra.map_top]; exact Algebra.FiniteType.out.map kₐ), le_sup_left,
      kₐ.codRestrict (B₀ ⊔ kₐ.range) fun a => (le_sup_right : kₐ.range ≤ B₀ ⊔ kₐ.range) (kₐ.mem_range_self a),
      by ext; rfl⟩
  have hκk : Spec.map (CommRingCat.ofHom B₁.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom κ.toRingHom) =
      Spec.map (CommRingCat.ofHom k) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun g : A₀ →ₐ[R] B => Spec.map (CommRingCat.ofHom g.toRingHom)) hκ

  set b₁ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h01).toRingHom) ≫ b₀ with hb₁def
  set σ₁ := Spec.map (CommRingCat.ofHom κ.toRingHom) with hσ₁def
  have hbb₁ : Spec.map (CommRingCat.ofHom B₁.val.toRingHom) ≫ b₁ = b := by
    rw [hb₁def, ← Category.assoc, Spec_map_val_comp_inclusion]; exact hbb₀
  have e1 : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map b₁ ≫ f i)).1 =
      Spec.map (CommRingCat.ofHom (algebraMap R ↥B₁)) := by
    rw [fst_uliftYonedaEquiv_map_comp, hb₁def, Category.assoc, hb₀R, Spec_map_algHom_comp]
  have e2 : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map σ₁ ≫ x₀)).1 =
      Spec.map (CommRingCat.ofHom (algebraMap R ↥B₁)) := by
    rw [fst_uliftYonedaEquiv_map_comp, hx₀, hσ₁def, Spec_map_algHom_comp]
  have E1 : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map (Spec.map (CommRingCat.ofHom B₁.val.toRingHom)) ≫
      uliftYoneda.{u + 1}.map b₁ ≫ f i)).1 = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [← Functor.map_comp_assoc, hbb₁, fst_uliftYonedaEquiv_map_comp, hbR]
  have E2 : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map (Spec.map (CommRingCat.ofHom B₁.val.toRingHom)) ≫
      uliftYoneda.{u + 1}.map σ₁ ≫ x₀)).1 = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [← Functor.map_comp_assoc, hσ₁def, hκk, fst_uliftYonedaEquiv_map_comp, hx₀, hkR]
  obtain ⟨B₂, hB₂, hle, hB₂eq⟩ := h.inj B B₁ hB₁
    (Functor.OverTotal.toFibre (specOver R ↥B₁) (uliftYonedaEquiv (uliftYoneda.{u + 1}.map b₁ ≫ f i)) e1)
    (Functor.OverTotal.toFibre (specOver R ↥B₁) (uliftYonedaEquiv (uliftYoneda.{u + 1}.map σ₁ ≫ x₀)) e2)
    ((toFibre_map_comp (Spec.map (CommRingCat.ofHom B₁.val.toRingHom)) (Spec_map_val_comp_algebraMap B₁)
        _ e1 E1).symm.trans
      ((Functor.OverTotal.toFibre_congr _
        (by rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hbb₁, hσ₁def, hκk, hb]) E1 E2).trans
      (toFibre_map_comp (Spec.map (CommRingCat.ofHom B₁.val.toRingHom)) (Spec_map_val_comp_algebraMap B₁)
        _ e2 E2)))

  set j₂ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom) with hj₂
  have E1' : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map j₂ ≫ uliftYoneda.{u + 1}.map b₁ ≫ f i)).1 =
      Spec.map (CommRingCat.ofHom (algebraMap R ↥B₂)) := by
    rw [fst_uliftYonedaEquiv_map_comp, e1, hj₂, Spec_map_algHom_comp]
  have E2' : (uliftYonedaEquiv (uliftYoneda.{u + 1}.map j₂ ≫ uliftYoneda.{u + 1}.map σ₁ ≫ x₀)).1 =
      Spec.map (CommRingCat.ofHom (algebraMap R ↥B₂)) := by
    rw [fst_uliftYonedaEquiv_map_comp, e2, hj₂, Spec_map_algHom_comp]
  have heq : uliftYoneda.{u + 1}.map (j₂ ≫ b₁) ≫ f i = uliftYoneda.{u + 1}.map (j₂ ≫ σ₁) ≫ x₀ := by
    rw [Functor.map_comp_assoc, Functor.map_comp_assoc]
    refine hom_ext_overTotal (Spec.map (CommRingCat.ofHom (algebraMap R ↥B₂))) E1' E2' ?_
    exact (toFibre_map_comp _ (Spec_map_algHom_comp _) _ e1 E1').trans
      (hB₂eq.trans (toFibre_map_comp _ (Spec_map_algHom_comp _) _ e2 E2').symm)
  haveI : Algebra.FiniteType R ↥B₂ := (Subalgebra.fg_iff_finiteType B₂).mp hB₂
  have hlft : LocallyOfFiniteType ((j₂ ≫ σ₁) ≫ (uliftYonedaEquiv x₀).1) := by
    rw [hx₀, Category.assoc, hσ₁def, Spec_map_algHom_comp, hj₂, Spec_map_algHom_comp]
    exact locallyOfFiniteType_Spec_algebraMap ↥B₂
  obtain ⟨χ, hχ, -⟩ := cart₀ (j₂ ≫ σ₁) (j₂ ≫ b₁) hlft heq

  have hk' : Spec.map (CommRingCat.ofHom k) = Spec.map (CommRingCat.ofHom B₂.val.toRingHom) ≫ χ ≫ U₀.ι := by
    rw [hχ, ← Category.assoc, hj₂, Spec_map_val_comp_inclusion hle, hσ₁def, hκk]
  rw [hk', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  simp

lemma mem_chartOpen (h : Hyps f) {i : ι} {W : Scheme.{u}} (ψ : W ⟶ T) (φ' : W ⟶ X i)
    (hφ' : uliftYoneda.{u + 1}.map φ' ≫ f i = uliftYoneda.{u + 1}.map ψ ≫ x) (p : W) :
    ψ p ∈ chartOpen f x i := by

  obtain ⟨V, hV, hpV, -⟩ := exists_isAffineOpen_mem_le (show ψ p ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨A₀, _, _, _, x₀, π, hx₀, hπ⟩ := exists_descent f x h V hV
  haveI hl : LocallyOfFiniteType (uliftYonedaEquiv x₀).1 := by rw [hx₀]; exact locallyOfFiniteType_Spec_algebraMap A₀
  obtain ⟨U₀, φ₀, -, hU₀⟩ := h.charts x₀ hl
  obtain ⟨h₀, cart₀⟩ := hU₀ i

  obtain ⟨W₀, hW₀, hpW₀, hle⟩ := exists_isAffineOpen_mem_le (show p ∈ ψ ⁻¹ᵁ V from hpV)
  haveI : IsAffine (↑W₀ : Scheme.{u}) := hW₀
  set e := (↑W₀ : Scheme.{u}).isoSpec with he
  set ψV : (↑W₀ : Scheme.{u}) ⟶ ↑V := W.homOfLE hle ≫ ψ ∣_ V with hψV
  have hψV_ι : ψV ≫ V.ι = W₀.ι ≫ ψ := by
    rw [hψV, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  set τ := e.inv ≫ ψV ≫ π with hτ
  set k := (Spec.preimage τ).hom with hk
  have hkτ : Spec.map (CommRingCat.ofHom k) = τ := by rw [hk, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hb : uliftYoneda.{u + 1}.map (e.inv ≫ W₀.ι ≫ φ') ≫ f i =
      uliftYoneda.{u + 1}.map (Spec.map (CommRingCat.ofHom k)) ≫ x₀ := by
    rw [hkτ, hτ, uliftYoneda.{u + 1}.map_comp_assoc, uliftYoneda.{u + 1}.map_comp_assoc, hφ',
      uliftYoneda.{u + 1}.map_comp_assoc, uliftYoneda.{u + 1}.map_comp_assoc, hπ,
      ← uliftYoneda.{u + 1}.map_comp_assoc ψV, hψV_ι, uliftYoneda.{u + 1}.map_comp_assoc]
  have hq := mem_of_comp_eq f h A₀ x₀ hx₀ (U₀ i) (φ₀ i) cart₀ _ k (e.inv ≫ W₀.ι ≫ φ') hb (e.hom ⟨p, hpW₀⟩)
  apply image_preimage_le_chartOpen f x V x₀ π hπ (U₀ i) (φ₀ i) h₀
  show ψ p ∈ ((V.ι ''ᵁ (π ⁻¹ᵁ U₀ i) : T.Opens) : Set T)
  rw [Scheme.Hom.coe_image]
  refine ⟨ψV ⟨p, hpW₀⟩, ?_, ?_⟩
  · show π (ψV ⟨p, hpW₀⟩) ∈ U₀ i
    rw [hkτ, hτ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hq
    simpa using hq
  · rw [← Scheme.Hom.comp_apply, hψV_ι, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]

lemma exists_mem_chartOpen (h : Hyps f) (p : T) : ∃ i, p ∈ chartOpen f x i := by
  obtain ⟨V, hV, hpV, -⟩ := exists_isAffineOpen_mem_le (show p ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨A₀, _, _, _, x₀, π, hx₀, hπ⟩ := exists_descent f x h V hV
  haveI hl : LocallyOfFiniteType (uliftYonedaEquiv x₀).1 := by rw [hx₀]; exact locallyOfFiniteType_Spec_algebraMap A₀
  obtain ⟨U₀, φ₀, hcov, hU₀⟩ := h.charts x₀ hl
  have : π ⟨p, hpV⟩ ∈ (⊤ : (Spec (CommRingCat.of A₀)).Opens) := trivial
  rw [← hcov, Opens.mem_iSup] at this
  obtain ⟨i, hi⟩ := this
  refine ⟨i, image_preimage_le_chartOpen f x V x₀ π hπ (U₀ i) (φ₀ i) (hU₀ i).1 ?_⟩
  show p ∈ ((V.ι ''ᵁ (π ⁻¹ᵁ U₀ i) : T.Opens) : Set T)
  rw [Scheme.Hom.coe_image]
  exact ⟨⟨p, hpV⟩, hi, by simp⟩

lemma iSup_chartOpen (h : Hyps f) : ⨆ i, chartOpen f x i = ⊤ :=
  top_le_iff.mp fun p _ => Opens.mem_iSup.mpr (exists_mem_chartOpen f x h p)

lemma exists_fac (h : Hyps f) (i : ι) {W : Scheme.{u}} (ψ : W ⟶ T) (φ' : W ⟶ X i)
    (hφ' : uliftYoneda.{u + 1}.map φ' ≫ f i = uliftYoneda.{u + 1}.map ψ ≫ x) :
    ∃ χ : W ⟶ ↑(chartOpen f x i), χ ≫ (chartOpen f x i).ι = ψ ∧ χ ≫ chartMap f x h i = φ' := by
  have hrange : Set.range ⇑ψ ⊆ Set.range ⇑(chartOpen f x i).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact mem_chartOpen f x h ψ φ' hφ' p
  refine ⟨IsOpenImmersion.lift _ ψ hrange, IsOpenImmersion.lift_fac _ _ _, eq_of_comp_eq f h _ _ ?_⟩
  rw [Functor.map_comp_assoc, chartMap_w, ← Functor.map_comp_assoc, IsOpenImmersion.lift_fac, hφ']

lemma isPullback_chart (h : Hyps f) (i : ι) :
    IsPullback (uliftYoneda.{u + 1}.map (chartMap f x h i)) (uliftYoneda.{u + 1}.map (chartOpen f x i).ι)
      (f i) x := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [← NatTrans.comp_app, ← NatTrans.comp_app, chartMap_w]
  · rintro ⟨a⟩ ⟨b⟩ ⟨-, h2⟩
    have h2' : a ≫ (chartOpen f x i).ι = b ≫ (chartOpen f x i).ι := congrArg ULift.down h2
    rw [cancel_mono] at h2'
    rw [h2']
  · rintro ⟨φ'⟩ ⟨ψ⟩ hc
    obtain ⟨χ, h1, h2⟩ := exists_fac f x h i ψ φ' (by
      apply uliftYonedaEquiv.injective
      rw [← app_up, ← app_up]
      exact hc)
    exact ⟨⟨χ⟩, congrArg ULift.up h2, congrArg ULift.up h1⟩

variable {x}

lemma presheafULift_isOpenImmersion (h : Hyps f) (i : ι) :
    MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i) :=
  MorphismProperty.relative.of_exists fun _ x =>
    ⟨_, uliftYoneda.{u + 1}.map (chartMap f x h i), (chartOpen f x i).ι, isPullback_chart f x h i, inferInstance⟩

lemma isLocallySurjective (h : Hyps f) : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) where
  imageSieve_mem {T} s := by
    obtain ⟨x, rfl⟩ := uliftYonedaEquiv.{u + 1}.surjective s
    refine GrothendieckTopology.superset_covering _ ?_
      ((T.openCoverOfIsOpenCover (chartOpen f x) (iSup_chartOpen f x h)).mem_grothendieckTopology)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    refine ⟨(Sigma.ι (fun i => uliftYoneda.{u + 1}.obj (X i)) i).app _ ⟨chartMap f x h i⟩, ?_⟩
    rw [← types_comp_apply ((Sigma.ι (fun i => uliftYoneda.{u + 1}.obj (X i)) i).app _) ((Sigma.desc f).app _),
      ← NatTrans.comp_app, Sigma.ι_desc, app_up]
    erw [chartMap_w.{u} f x h i]
    erw [uliftYonedaEquiv_map_comp]
    rfl

end LFPExtend

end AlgebraicGeometry.AffineLimit

p2m_open "AlgebraicGeometry.AffineLimit P2MW.S_AlgebraicGeometry_AffineLimit_presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType.AlgebraicGeometry.AffineLimit"

theorem solution (R : Type u) [CommRing R] (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1))
    (hG : Presieve.IsSheaf Scheme.zariskiTopology G.overTotal)
    (hsurj : IsLFPSurj G) (hinj : IsLFPInj G)
    {ι : Type u} (X : ι → Scheme.{u}) (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶ G.overTotal)
    (hX : ∀ i, HomIsLFP (uliftYonedaEquiv (f i)).1)
    (H : ∀ ⦃T : Scheme.{u}⦄ (x : uliftYoneda.{u + 1}.obj T ⟶ G.overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv x).1 →
      ∃ (U : ι → T.Opens) (φ : ∀ i, (↑(U i) : Scheme.{u}) ⟶ X i),
        (⨆ i, U i) = ⊤ ∧
        ∀ i, uliftYoneda.{u + 1}.map (φ i) ≫ f i = uliftYoneda.{u + 1}.map (U i).ι ≫ x ∧
          ∀ ⦃T' : Scheme.{u}⦄ (ψ : T' ⟶ T) (φ' : T' ⟶ X i),
            LocallyOfFiniteType (ψ ≫ (uliftYonedaEquiv x).1) →
            uliftYoneda.{u + 1}.map φ' ≫ f i = uliftYoneda.{u + 1}.map ψ ≫ x →
            ∃ χ : T' ⟶ ↑(U i), χ ≫ (U i).ι = ψ ∧ χ ≫ φ i = φ') :
    (∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i)) ∧
      Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f) :=
  have h : AlgebraicGeometry.AffineLimit.LFPExtend.Hyps f := ⟨hG, hsurj, hinj, hX, H⟩
  ⟨AlgebraicGeometry.AffineLimit.LFPExtend.presheafULift_isOpenImmersion f h,
    AlgebraicGeometry.AffineLimit.LFPExtend.isLocallySurjective f h⟩

end S_AlgebraicGeometry_AffineLimit_presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType
end P2MW
export P2MW.S_AlgebraicGeometry_AffineLimit_presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType (solution)
