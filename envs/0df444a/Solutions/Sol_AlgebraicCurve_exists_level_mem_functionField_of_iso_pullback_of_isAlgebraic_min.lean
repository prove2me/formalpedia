-- Prove2me | solution 1 for AlgebraicCurve.exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c93f8eab-b7e2-5cce-a2d4-909640508d59

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u u'

namespace P2mGenEngine

section fieldSpec

theorem exists_germ_top_eq_of_field (T : Type u) [Field T] (x : Spec (CommRingCat.of T))
    (t : (Spec (CommRingCat.of T)).presheaf.stalk x) :
    ∃ s : Γ(Spec (CommRingCat.of T), ⊤), (Spec (CommRingCat.of T)).presheaf.germ ⊤ x trivial s = t := by
  obtain ⟨U, hxU, s, hs⟩ := (Spec (CommRingCat.of T)).presheaf.exists_germ_eq t
  have hle : (⊤ : (Spec (CommRingCat.of T)).Opens) ≤ U := by
    intro y _
    have : y = x := Subsingleton.elim (α := PrimeSpectrum T) y x
    rw [this]; exact hxU
  refine ⟨(Spec (CommRingCat.of T)).presheaf.map (homOfLE hle).op s, ?_⟩
  rw [TopCat.Presheaf.germ_res_apply]
  exact hs

theorem eq_of_specMap_comp_eq {R : CommRingCat.{u}} {S K : Type u} [CommRing S] [CommRing K]
    (incl : S →+* K) (hincl : Function.Injective incl)
    (v₁ v₂ : Spec (CommRingCat.of S) ⟶ Spec R)
    (h : Spec.map (CommRingCat.ofHom incl) ≫ v₁ = Spec.map (CommRingCat.ofHom incl) ≫ v₂) :
    v₁ = v₂ := by
  rw [← Spec.map_preimage v₁, ← Spec.map_preimage v₂] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  haveI : Mono (CommRingCat.ofHom incl) := ConcreteCategory.mono_of_injective _ hincl
  rw [cancel_mono] at h'
  rw [h']

end fieldSpec

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] (ι : A₀ →+* A)
  {X X₀ : Scheme.{u}} [IsIntegral X] [IsIntegral X₀]
  (p : X ⟶ X₀) (b : X ⟶ Spec (CommRingCat.of A)) (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀))

noncomputable def ffMap (hgen : p.base (genericPoint X) = genericPoint X₀) :
    X₀.functionField →+* X.functionField :=
  (p.stalkMap (genericPoint X)).hom.comp
    (X₀.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom

theorem fromSpecStalk_comp_eq (hgen : p.base (genericPoint X) = genericPoint X₀) :
    X.fromSpecStalk (genericPoint X) ≫ p =
      Spec.map (CommRingCat.ofHom (ffMap p hgen)) ≫ X₀.fromSpecStalk (genericPoint X₀) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk p,
    ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq hgen),
    ← Category.assoc, ← Spec.map_comp]
  rfl

theorem fromSpecStalk_comp_base_eq :
    X.fromSpecStalk (genericPoint X) ≫ b =
      Spec.map (CommRingCat.ofHom (AlgebraicCurve.SemistableModel.baseToFunctionField b)) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk b, Spec.fromSpecStalk_eq, ← Spec.map_comp,
    Category.assoc, Scheme.Hom.germ_stalkMap b ⊤ (genericPoint X) trivial]
  rfl

theorem closure_range_ffMap_union_range_baseToFunctionField_eq_top
    (H : IsPullback p b f₀ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : p.base (genericPoint X) = genericPoint X₀) :
    Subfield.closure (Set.range (ffMap p hgen) ∪
      Set.range (AlgebraicCurve.SemistableModel.baseToFunctionField b)) = ⊤ := by
  classical
  set θ := ffMap p hgen with hθ
  set β := AlgebraicCurve.SemistableModel.baseToFunctionField b with hβ
  set T₀ : Subfield X.functionField := Subfield.closure (Set.range θ ∪ Set.range β) with hT₀

  have hθmem : ∀ w, θ w ∈ T₀ := fun w => Subfield.subset_closure (Or.inl ⟨w, rfl⟩)
  have hβmem : ∀ a, β a ∈ T₀ := fun a => Subfield.subset_closure (Or.inr ⟨a, rfl⟩)
  let θ' : X₀.functionField →+* T₀ := θ.codRestrict T₀ hθmem
  let β' : A →+* T₀ := β.codRestrict T₀ hβmem
  let incl : T₀ →+* X.functionField := T₀.subtype
  have hinclθ : incl.comp θ' = θ := RingHom.ext fun _ => rfl
  have hinclβ : incl.comp β' = β := RingHom.ext fun _ => rfl
  have hincl : Function.Injective incl := Subtype.coe_injective

  let η : Spec (X.presheaf.stalk (genericPoint X)) ⟶ X := X.fromSpecStalk (genericPoint X)
  let j : Spec (CommRingCat.of X.functionField) ⟶ Spec (CommRingCat.of T₀) :=
    Spec.map (CommRingCat.ofHom incl)
  let u₁ : Spec (CommRingCat.of T₀) ⟶ X₀ :=
    Spec.map (CommRingCat.ofHom θ') ≫ X₀.fromSpecStalk (genericPoint X₀)
  let u₂ : Spec (CommRingCat.of T₀) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom β')
  have hA : η ≫ p = Spec.map (CommRingCat.ofHom θ) ≫ X₀.fromSpecStalk (genericPoint X₀) :=
    fromSpecStalk_comp_eq p hgen
  have hB : η ≫ b = Spec.map (CommRingCat.ofHom β) := fromSpecStalk_comp_base_eq b
  have hju₁ : j ≫ u₁ = η ≫ p := by
    rw [hA]
    change Spec.map (CommRingCat.ofHom incl) ≫ Spec.map (CommRingCat.ofHom θ') ≫ _ = _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hinclθ]
  have hju₂ : j ≫ u₂ = η ≫ b := by
    rw [hB]
    change Spec.map (CommRingCat.ofHom incl) ≫ Spec.map (CommRingCat.ofHom β') = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hinclβ]

  have w : u₁ ≫ f₀ = u₂ ≫ Spec.map (CommRingCat.ofHom ι) := by
    refine eq_of_specMap_comp_eq incl hincl _ _ ?_
    change j ≫ u₁ ≫ f₀ = j ≫ u₂ ≫ Spec.map (CommRingCat.ofHom ι)
    rw [← Category.assoc, hju₁, ← Category.assoc, hju₂, Category.assoc, Category.assoc, H.w]

  let lam : Spec (CommRingCat.of T₀) ⟶ X := H.lift u₁ u₂ w
  have hfac : η = j ≫ lam := by
    refine H.hom_ext ?_ ?_
    · rw [Category.assoc, H.lift_fst, hju₁]
    · rw [Category.assoc, H.lift_snd, hju₂]

  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo η).hom := by
    intro y
    refine ⟨(X.presheaf.stalkCongr (by rw [Scheme.fromSpecStalk_closedPoint]; rfl)).inv y, ?_⟩
    change (Scheme.stalkClosedPointTo (X.fromSpecStalk (genericPoint X))).hom _ = y
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    exact CategoryTheory.Iso.inv_hom_id_apply _ _
  rw [hfac] at hsurj
  have key : ∀ z', (Scheme.stalkClosedPointTo j).hom z' ∈ Set.range incl := by
    intro z'
    obtain ⟨s, rfl⟩ := exists_germ_top_eq_of_field T₀ _ z'
    change ((Spec (CommRingCat.of T₀)).presheaf.germ ⊤ _ trivial ≫
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom incl))).hom s ∈ Set.range incl
    rw [Scheme.germ_stalkClosedPointTo_Spec]
    exact ⟨_, rfl⟩
  have hrange : ∀ z, (Scheme.stalkClosedPointTo (j ≫ lam)).hom z ∈ Set.range incl := by
    intro z
    rw [Scheme.stalkClosedPointTo_comp]
    exact key _

  rw [eq_top_iff]
  intro t _
  obtain ⟨z, hz⟩ := hsurj t
  obtain ⟨t', ht'⟩ := hrange z
  rw [hz] at ht'
  rw [← ht']
  exact t'.2

end P2mGenEngine

namespace P2mGenEngine

theorem exists_finset_mem_closure_union_image {L E : Type*} [Field L] [Field E] [Algebra L E]
    (S : Set E) {x : E} (hx : x ∈ Subfield.closure (S ∪ Set.range (algebraMap L E))) :
    ∃ T : Finset L, x ∈ Subfield.closure (S ∪ algebraMap L E '' (T : Set L)) := by
  classical

  have mono : ∀ (T T' : Finset L), T ⊆ T' →
      Subfield.closure (S ∪ algebraMap L E '' (T : Set L)) ≤
        Subfield.closure (S ∪ algebraMap L E '' (T' : Set L)) := by
    intro T T' h
    apply Subfield.closure_mono
    apply Set.union_subset_union_right
    exact Set.image_mono (Finset.coe_subset.mpr h)
  refine Subfield.closure_induction
    (p := fun y _ => ∃ T : Finset L, y ∈ Subfield.closure (S ∪ algebraMap L E '' (T : Set L)))
    ?_ ?_ ?_ ?_ ?_ ?_ hx
  · rintro y (hyS | ⟨l, rfl⟩)
    · exact ⟨∅, Subfield.subset_closure (Or.inl hyS)⟩
    · refine ⟨{l}, Subfield.subset_closure (Or.inr ⟨l, ?_, rfl⟩)⟩
      simp
  · exact ⟨∅, Subfield.one_mem _⟩
  · rintro y z - - ⟨T₁, h₁⟩ ⟨T₂, h₂⟩
    exact ⟨T₁ ∪ T₂, Subfield.add_mem _ (mono T₁ _ Finset.subset_union_left h₁)
      (mono T₂ _ Finset.subset_union_right h₂)⟩
  · rintro y - ⟨T, h⟩
    exact ⟨T, Subfield.neg_mem _ h⟩
  · rintro y - ⟨T, h⟩
    exact ⟨T, Subfield.inv_mem _ h⟩
  · rintro y z - - ⟨T₁, h₁⟩ ⟨T₂, h₂⟩
    exact ⟨T₁ ∪ T₂, Subfield.mul_mem _ (mono T₁ _ Finset.subset_union_left h₁)
      (mono T₂ _ Finset.subset_union_right h₂)⟩

end P2mGenEngine

namespace P2mGenEngine

theorem exists_finset_mem_closure_union_image' {R E : Type*} [CommRing R] [Field E] (β : R →+* E)
    (S : Set E) {x : E} (hx : x ∈ Subfield.closure (S ∪ Set.range β)) :
    ∃ T : Finset R, x ∈ Subfield.closure (S ∪ β '' (T : Set R)) := by
  classical
  have mono : ∀ (T T' : Finset R), T ⊆ T' →
      Subfield.closure (S ∪ β '' (T : Set R)) ≤ Subfield.closure (S ∪ β '' (T' : Set R)) := by
    intro T T' h
    apply Subfield.closure_mono
    apply Set.union_subset_union_right
    exact Set.image_mono (Finset.coe_subset.mpr h)
  refine Subfield.closure_induction
    (p := fun y _ => ∃ T : Finset R, y ∈ Subfield.closure (S ∪ β '' (T : Set R)))
    ?_ ?_ ?_ ?_ ?_ ?_ hx
  · rintro y (hyS | ⟨l, rfl⟩)
    · exact ⟨∅, Subfield.subset_closure (Or.inl hyS)⟩
    · refine ⟨{l}, Subfield.subset_closure (Or.inr ⟨l, ?_, rfl⟩)⟩
      simp
  · exact ⟨∅, Subfield.one_mem _⟩
  · rintro y z - - ⟨T₁, h₁⟩ ⟨T₂, h₂⟩
    exact ⟨T₁ ∪ T₂, Subfield.add_mem _ (mono T₁ _ Finset.subset_union_left h₁)
      (mono T₂ _ Finset.subset_union_right h₂)⟩
  · rintro y - ⟨T, h⟩
    exact ⟨T, Subfield.neg_mem _ h⟩
  · rintro y - ⟨T, h⟩
    exact ⟨T, Subfield.inv_mem _ h⟩
  · rintro y z - - ⟨T₁, h₁⟩ ⟨T₂, h₂⟩
    exact ⟨T₁ ∪ T₂, Subfield.mul_mem _ (mono T₁ _ Finset.subset_union_left h₁)
      (mono T₂ _ Finset.subset_union_right h₂)⟩

end P2mGenEngine

open AlgebraicCurve

namespace LevelExistsE133

theorem alg_tower {F : Type*} [Field F] (F₀ F₁ : Subfield F) (h : F₀ ≤ F₁) [Algebra.IsAlgebraic F₀ F] :
    Algebra.IsAlgebraic F₁ F := by
  letI : Algebra F₀ F₁ := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower F₀ F₁ F := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  exact Algebra.IsAlgebraic.tower_top (K := F₀) (L := F₁) (A := F)

theorem base_genericPoint_eq {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : X ⟶ Y) [Surjective g] :
    g.base (genericPoint X) = genericPoint Y := by
  have hX := genericPoint_spec X
  have hY := genericPoint_spec Y
  have h1 : IsGenericPoint (g.base (genericPoint X)) (⊤ : Set Y) := by
    rw [isGenericPoint_def]
    apply Set.eq_univ_of_univ_subset
    have h2 : g.base '' closure ({genericPoint X} : Set X) ⊆ closure (g.base '' {genericPoint X}) :=
      image_closure_subset_closure_image g.base.hom.continuous
    rw [hX.def, Set.image_singleton] at h2
    intro y _
    obtain ⟨x, rfl⟩ := g.surjective y
    exact h2 ⟨x, trivial, rfl⟩
  exact h1.eq hY

section Ring
variable {L : Type u} [Field L] (A : ValuationSubring L) {A₁ : Type u} [CommRing A₁] (ι₁ : A₁ →+* A)

theorem valuationRing_of_range_eq_inter (hι₁ : Function.Injective ι₁) (K₁ : Subfield L)
    (range_ι₁ : Set.range (fun a : A₁ => ((ι₁ a : A) : L)) = (A : Set L) ∩ (K₁ : Set L)) :
    haveI := Function.Injective.isDomain ι₁ hι₁; ValuationRing A₁ := by
  haveI := Function.Injective.isDomain ι₁ hι₁
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  have ha : ((ι₁ a : A) : L) ∈ (A : Set L) ∩ (K₁ : Set L) := range_ι₁ ▸ ⟨a, rfl⟩
  have hb : ((ι₁ b : A) : L) ∈ (A : Set L) ∩ (K₁ : Set L) := range_ι₁ ▸ ⟨b, rfl⟩
  by_cases hb0 : b = 0
  · exact ⟨0, Or.inl (by simp [hb0])⟩
  by_cases ha0 : a = 0
  · exact ⟨0, Or.inr (by simp [ha0])⟩
  have hbL : ((ι₁ b : A) : L) ≠ 0 := by
    intro h; apply hb0; apply hι₁; simpa using h
  have haL : ((ι₁ a : A) : L) ≠ 0 := by
    intro h; apply ha0; apply hι₁; simpa using h
  rcases A.mem_or_inv_mem (((ι₁ b : A) : L) / ((ι₁ a : A) : L)) with h | h
  ·
    have hK : ((ι₁ b : A) : L) / ((ι₁ a : A) : L) ∈ (K₁ : Set L) := K₁.div_mem hb.2 ha.2
    obtain ⟨c, hc⟩ : ((ι₁ b : A) : L) / ((ι₁ a : A) : L) ∈ Set.range (fun a : A₁ => ((ι₁ a : A) : L)) :=
      range_ι₁ ▸ ⟨h, hK⟩
    refine ⟨c, Or.inl ?_⟩
    apply hι₁; ext
    simp only [map_mul]
    push_cast
    simp only at hc
    rw [hc]; field_simp
  · rw [inv_div] at h
    have hK : ((ι₁ a : A) : L) / ((ι₁ b : A) : L) ∈ (K₁ : Set L) := K₁.div_mem ha.2 hb.2
    obtain ⟨c, hc⟩ : ((ι₁ a : A) : L) / ((ι₁ b : A) : L) ∈ Set.range (fun a : A₁ => ((ι₁ a : A) : L)) :=
      range_ι₁ ▸ ⟨h, hK⟩
    refine ⟨c, Or.inr ?_⟩
    apply hι₁; ext
    simp only [map_mul]
    push_cast
    simp only at hc
    rw [hc]; field_simp

theorem faithfullyFlat_of_range_eq_inter [IsLocalHom ι₁] (hι₁ : Function.Injective ι₁) (K₁ : Subfield L)
    (range_ι₁ : Set.range (fun a : A₁ => ((ι₁ a : A) : L)) = (A : Set L) ∩ (K₁ : Set L)) :
    ι₁.FaithfullyFlat := by
  haveI := Function.Injective.isDomain ι₁ hι₁
  haveI : ValuationRing A₁ := valuationRing_of_range_eq_inter A ι₁ hι₁ K₁ range_ι₁
  letI : Algebra A₁ A := ι₁.toAlgebra
  have halg : algebraMap A₁ A = ι₁ := rfl
  haveI : IsLocalHom (algebraMap A₁ A) := halg ▸ inferInstance
  haveI : Module.IsTorsionFree A₁ A := ⟨fun r hr x y hxy => by
    have hr0 : r ≠ 0 := hr.ne_zero
    have h' : ι₁ r * x = ι₁ r * y := by simp [Algebra.smul_def] at hxy ⊢; exact hxy
    exact mul_left_cancel₀ (fun h => hr0 (hι₁ (by simpa using h))) h'⟩
  haveI : Module.Flat A₁ A :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  have : Module.FaithfullyFlat A₁ A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (RingHom.faithfullyFlat_algebraMap_iff.mpr this)

theorem flat_and_surjective_specMap [IsLocalHom ι₁] (hι₁ : Function.Injective ι₁) (K₁ : Subfield L)
    (range_ι₁ : Set.range (fun a : A₁ => ((ι₁ a : A) : L)) = (A : Set L) ∩ (K₁ : Set L)) :
    Flat (Spec.map (CommRingCat.ofHom ι₁)) ∧ Surjective (Spec.map (CommRingCat.ofHom ι₁)) :=
  (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom ι₁)).mpr
    (by simpa using faithfullyFlat_of_range_eq_inter A ι₁ hι₁ K₁ range_ι₁)

end Ring

theorem isIntegral_of_flat_of_surjective {X Y : Scheme.{u}} [IsIntegral X] (g : X ⟶ Y) [Flat g] [Surjective g] :
    IsIntegral Y := by
  haveI : IrreducibleSpace Y := by
    have h := (IrreducibleSpace.isIrreducible_univ X).image g.base g.base.hom.continuous.continuousOn
    rw [Set.image_univ, g.surjective.range_eq] at h
    exact { isPreirreducible_univ := h.2, toNonempty := Set.nonempty_iff_univ_nonempty.mpr h.1 }
  haveI : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    obtain ⟨x, rfl⟩ := g.surjective y
    algebraize [(g.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ (Flat.stalkMap g x) (g.toLRSHom.prop x)
    exact isReduced_of_injective (g.stalkMap x).hom ‹RingHom.FaithfullyFlat _›.injective
  haveI : IsReduced Y := isReduced_of_isReduced_stalk Y
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

theorem stalkMap_stalkSpecializes_chain {X Y Z : Scheme.{u}} (g : X ⟶ Y) (π : Y ⟶ Z) (x : X) {y : Y} {z : Z}
    (hy : g.base x = y) (hz : π.base y = z) (q : X ⟶ Z) (hq : q = g ≫ π) (hxz : q.base x = z)
    (t : Z.presheaf.stalk z) :
    (q.stalkMap x).hom ((Z.presheaf.stalkSpecializes (specializes_of_eq hxz)).hom t) =
    (g.stalkMap x).hom ((Y.presheaf.stalkSpecializes (specializes_of_eq hy)).hom
      ((π.stalkMap y).hom ((Z.presheaf.stalkSpecializes (specializes_of_eq hz)).hom t))) := by
  subst hy hz hq
  change ((g ≫ π).stalkMap x).hom ((Z.presheaf.stalkSpecializes (specializes_refl (π.base (g.base x)))).hom t) =
    (g.stalkMap x).hom ((Y.presheaf.stalkSpecializes (specializes_refl (g.base x))).hom
      ((π.stalkMap (g.base x)).hom ((Z.presheaf.stalkSpecializes (specializes_refl (π.base (g.base x)))).hom t)))
  simp only [TopCat.Presheaf.stalkSpecializes_refl, Scheme.Hom.stalkMap_comp]
  rfl

theorem stalkMap_baseToFunctionField {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (g : X ⟶ Y) (fY : Y ⟶ Spec (CommRingCat.of R)) (fX : X ⟶ Spec (CommRingCat.of S))
    (hsq : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (hgen : g.base (genericPoint X) = genericPoint Y) (r : R) :
    (g.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom
      (SemistableModel.baseToFunctionField fY r)) = SemistableModel.baseToFunctionField fX (φ r) := by
  have hnat : (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (φ r) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ : CommRingCat.of R ⟶ CommRingCat.of S)
    have h2 := congrArg (fun k => CommRingCat.Hom.hom k r) h
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] using h2
  have hsq' : fY.appTop ≫ g.appTop = (Spec.map (CommRingCat.ofHom φ)).appTop ≫ fX.appTop := by
    rw [← Scheme.Hom.comp_appTop, hsq, Scheme.Hom.comp_appTop]
  have hsq'' := congrArg (fun k => CommRingCat.Hom.hom k ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) hsq'
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hsq''
  simp only [SemistableModel.baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  rw [hnat, ← hsq'']
  rw [← CommRingCat.comp_apply (Y.presheaf.germ ⊤ _ _), TopCat.Presheaf.germ_stalkSpecializes]
  erw [Scheme.Hom.germ_stalkMap_apply]
  rfl

end LevelExistsE133

open LevelExistsE133 AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι₀.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) = toBase)

    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)

    (x₀ : X₀) (hx₀ : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).base x = x₀)
    (w : ℕ) (hw : 1 ≤ w)
    (e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
    (he : ∀ a : A₀,
      e (algebraMap (X₀.presheaf.stalk x₀) (AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀))
          ((X₀.presheaf.germ ⊤ x₀ trivial).hom
            (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
          (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))
    {n : ℕ} (f : Fin n → X.functionField) :
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (ι₁' : A₀ →+* A₁) (_ : IsLocalHom ι₁') (ι₁ : A₁ →+* ↥A) (_ : IsLocalHom ι₁) (_ : Function.Injective ι₁)
      (_ : ι₁.comp ι₁' = ι₀) (ϖ₁ : A₁) (_ : maximalIdeal A₁ = Ideal.span {ϖ₁})
      (X₁ : Scheme.{0}) (_ : IsIntegral X₁) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁)) (g₁ : X₁ ⟶ X₀)
      (_ : IsPullback g₁ f₁ toBase₀ (Spec.map (CommRingCat.ofHom ι₁')))
      (e₁ : X ≅ Limits.pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
      (_ : e₁.hom ≫ Limits.pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = toBase)
      (_ : (e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) ≫ g₁ =
        iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
      (hgen : (e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint X) = genericPoint X₁)
      (u : Fin n → X₁.functionField),
      ∀ i : Fin n, f i = ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint X)).hom
        ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (u i)) := by
  classical

  let p₀ : X ⟶ X₀ := iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))
  have hsq₀ : IsPullback p₀ toBase toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ iso rfl hiso
    change (iso.hom ≫ pullback.fst _ _) ≫ toBase₀ = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, hiso]
  haveI hsurj₀ : Surjective (Spec.map (CommRingCat.ofHom ι₀)) := by
    refine ⟨fun q => ?_⟩
    by_cases hq : q.asIdeal = ⊥
    · refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
      show Ideal.comap ι₀ ⊥ = q.asIdeal
      rw [hq, Ideal.comap_bot_of_injective ι₀ hι₀]
    · refine ⟨closedPoint ↥A, ?_⟩
      rw [Spec_closedPoint]
      apply PrimeSpectrum.ext
      haveI := q.isPrime
      exact (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hq q.isPrime)).symm
  haveI : Surjective p₀ := inferInstance
  have hgen₀ : p₀.base (genericPoint X) = genericPoint X₀ := base_genericPoint_eq p₀

  have htop := P2mGenEngine.closure_range_ffMap_union_range_baseToFunctionField_eq_top ι₀ p₀ toBase toBase₀ hsq₀ hgen₀
  have hΛi : ∀ i : Fin n, ∃ Λ : Finset ↥A, f i ∈ Subfield.closure (Set.range (P2mGenEngine.ffMap p₀ hgen₀) ∪
      (SemistableModel.baseToFunctionField toBase) '' (Λ : Set ↥A)) := fun i =>
    P2mGenEngine.exists_finset_mem_closure_union_image' _ _ (by rw [htop]; exact Subfield.mem_top _)
  choose Λf hΛf using hΛi
  let Λ : Finset ↥A := Finset.univ.biUnion Λf
  have hΛ : ∀ i : Fin n, f i ∈ Subfield.closure (Set.range (P2mGenEngine.ffMap p₀ hgen₀) ∪
      (SemistableModel.baseToFunctionField toBase) '' (Λ : Set ↥A)) := by
    intro i
    refine Subfield.closure_mono ?_ (hΛf i)
    apply Set.union_subset_union_right
    apply Set.image_mono
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ha⟩

  let ι₀L : A₀ →+* L := A.subtype.comp ι₀
  have hι₀L : Function.Injective ι₀L := Subtype.coe_injective.comp hι₀
  let K := FractionRing A₀
  letI algA₀L : Algebra A₀ L := ι₀L.toAlgebra
  letI algKL : Algebra K L := (IsFractionRing.lift hι₀L : K →+* L).toAlgebra
  haveI hST : IsScalarTower A₀ K L := IsScalarTower.of_algebraMap_eq (fun a => by
    show ι₀L a = (IsFractionRing.lift hι₀L : K →+* L) (algebraMap A₀ K a)
    rw [IsFractionRing.lift_algebraMap])
  let S : Set L := (fun a : ↥A => (a : L)) '' (Λ : Set ↥A)
  let K₁ : IntermediateField K L := IntermediateField.adjoin K S
  have hSint : ∀ s ∈ S, IsIntegral K s := by
    rintro s ⟨lam, hlam, rfl⟩
    letI algA₀A : Algebra A₀ ↥A := ι₀.toAlgebra

    obtain ⟨p, hp0, hp⟩ := halg lam
    obtain ⟨q, hq⟩ := Polynomial.map_surjective (ι₀.rangeRestrict) ι₀.rangeRestrict_surjective p
    have hq0 : q ≠ 0 := by rintro rfl; exact hp0 (by rw [← hq, Polynomial.map_zero])
    have halgA : IsAlgebraic A₀ (lam : ↥A) := by
      refine ⟨q, hq0, ?_⟩
      rw [Polynomial.aeval_def, show algebraMap A₀ ↥A = (ι₀.range.subtype).comp ι₀.rangeRestrict from rfl,
        ← Polynomial.eval₂_map, hq]
      exact hp

    let toL : ↥A →ₐ[A₀] L := { A.subtype with commutes' := fun _ => rfl }
    have halgL : IsAlgebraic A₀ ((lam : ↥A) : L) := halgA.algHom toL
    have halgK : IsAlgebraic K ((lam : ↥A) : L) := halgL.extendScalars (IsFractionRing.injective A₀ K)
    exact halgK.isIntegral
  haveI : FiniteDimensional K ↥K₁ := IntermediateField.finiteDimensional_adjoin hSint
  letI algA₀K₁ : Algebra A₀ ↥K₁ := ((algebraMap K ↥K₁).comp (algebraMap A₀ K)).toAlgebra
  haveI : IsScalarTower A₀ K ↥K₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let O : ValuationSubring ↥K₁ := A.comap (algebraMap ↥K₁ L)
  have hAO : ∀ a : A₀, algebraMap A₀ ↥K₁ a ∈ O := by
    intro a
    show algebraMap ↥K₁ L (algebraMap K ↥K₁ (algebraMap A₀ K a)) ∈ A
    rw [show algebraMap ↥K₁ L (algebraMap K ↥K₁ (algebraMap A₀ K a)) = algebraMap K L (algebraMap A₀ K a) from rfl,
      ← IsScalarTower.algebraMap_apply]
    exact (ι₀ a).2
  have hO : O ≠ ⊤ := by
    intro hO
    have hϖ0 : ϖ₀ ≠ 0 := by
      intro h0
      apply IsDiscreteValuationRing.not_a_field A₀
      rw [hϖ₀, h0, Ideal.span_singleton_eq_bot]
    have hm : ι₀ ϖ₀ ∈ maximalIdeal ↥A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have : ϖ₀ ∈ maximalIdeal A₀ := by rw [hϖ₀]; exact Ideal.mem_span_singleton_self ϖ₀
      exact ((IsLocalRing.mem_maximalIdeal _).mp this) (isUnit_of_map_unit ι₀ ϖ₀ hu)
    have hk0 : (algebraMap A₀ ↥K₁ ϖ₀ : ↥K₁) ≠ 0 := by
      intro h0
      apply hϖ0
      have : algebraMap ↥K₁ L (algebraMap A₀ ↥K₁ ϖ₀) = 0 := by rw [h0, map_zero]
      have h2 : ι₀L ϖ₀ = 0 := by
        rw [show ι₀L ϖ₀ = algebraMap K L (algebraMap A₀ K ϖ₀) from (IsScalarTower.algebraMap_apply A₀ K L ϖ₀)]
        exact this
      exact hι₀L (by rw [h2, map_zero])
    have hinv : (algebraMap A₀ ↥K₁ ϖ₀)⁻¹ ∈ O := by rw [hO]; exact ValuationSubring.mem_top _
    have hinvA : ((ι₀ ϖ₀ : ↥A) : L)⁻¹ ∈ A := by
      have : algebraMap ↥K₁ L (algebraMap A₀ ↥K₁ ϖ₀)⁻¹ ∈ A := hinv
      rw [map_inv₀] at this
      rwa [show algebraMap ↥K₁ L (algebraMap A₀ ↥K₁ ϖ₀) = ((ι₀ ϖ₀ : ↥A) : L) from
        (IsScalarTower.algebraMap_apply A₀ K L ϖ₀).symm] at this
    have hu : IsUnit (ι₀ ϖ₀) := by
      have hne : ((ι₀ ϖ₀ : ↥A) : L) ≠ 0 := fun h => hϖ0 (hι₀ (Subtype.ext (by simpa using h)))
      exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvA⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩
    exact (IsLocalRing.mem_maximalIdeal _).mp hm hu
  haveI hDVR : IsDiscreteValuationRing ↥O :=
    ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite (A := A₀) (K := K) O hAO hO

  let ι₁ : ↥O →+* ↥A := (algebraMap ↥K₁ L).restrict O.toSubring A.toSubring (fun x hx => hx)
  have hι₁v : ∀ a : ↥O, ((ι₁ a : ↥A) : L) = algebraMap ↥K₁ L (a : ↥K₁) := fun a => rfl
  have hι₁ : Function.Injective ι₁ := by
    intro a b h
    have : ((ι₁ a : ↥A) : L) = ((ι₁ b : ↥A) : L) := by rw [h]
    rw [hι₁v, hι₁v] at this
    exact Subtype.ext ((algebraMap ↥K₁ L).injective this)
  haveI hι₁loc : IsLocalHom ι₁ := by
    constructor
    intro a ha
    have ha0 : (a : ↥K₁) ≠ 0 := by
      intro h0
      apply ha.ne_zero
      apply Subtype.ext
      show ((ι₁ a : ↥A) : L) = 0
      rw [hι₁v, h0, map_zero]
    have hinvA : (algebraMap ↥K₁ L (a : ↥K₁))⁻¹ ∈ A := by
      obtain ⟨w, hw⟩ := ha
      have h1 : ((w : ↥A) : L) * (((w⁻¹ : (↥A)ˣ) : ↥A) : L) = 1 := by
        rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
      rw [hw, hι₁v] at h1
      rw [← eq_inv_of_mul_eq_one_right h1]
      exact ((w⁻¹ : (↥A)ˣ) : ↥A).2
    have hinvO : (a : ↥K₁)⁻¹ ∈ O := by
      show algebraMap ↥K₁ L (a : ↥K₁)⁻¹ ∈ A
      rw [map_inv₀]; exact hinvA
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvO⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
  let ι₁' : A₀ →+* ↥O := (algebraMap A₀ ↥K₁).codRestrict O.toSubring hAO
  have hcomp : ι₁.comp ι₁' = ι₀ := by
    ext a
    show algebraMap ↥K₁ L (algebraMap K ↥K₁ (algebraMap A₀ K a)) = ((ι₀ a : ↥A) : L)
    exact (IsScalarTower.algebraMap_apply A₀ K L a).symm
  haveI hι₁'loc : IsLocalHom ι₁' := by
    constructor
    intro a ha
    have : IsUnit (ι₁ (ι₁' a)) := ha.map ι₁
    rw [← RingHom.comp_apply, hcomp] at this
    exact isUnit_of_map_unit ι₀ a this
  obtain ⟨ϖ₁, hϖ₁irr⟩ := IsDiscreteValuationRing.exists_irreducible ↥O
  have hϖ₁ : maximalIdeal ↥O = Ideal.span {ϖ₁} := hϖ₁irr.maximalIdeal_eq
  have range_ι₁ : Set.range (fun a : ↥O => ((ι₁ a : ↥A) : L)) = (A : Set L) ∩ (K₁.toSubfield : Set L) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨(ι₁ a).2, by show ((ι₁ a : ↥A) : L) ∈ K₁.toSubfield; rw [hι₁v]; exact (a : ↥K₁).2⟩
    · rintro ⟨hyA, hyK⟩
      exact ⟨⟨⟨y, hyK⟩, hyA⟩, rfl⟩

  let Sι := Spec.map (CommRingCat.ofHom ι₁)
  let Sj := Spec.map (CommRingCat.ofHom ι₁')
  have hSpec : Spec.map (CommRingCat.ofHom ι₀) = Sι ≫ Sj := by
    rw [← hcomp, CommRingCat.ofHom_comp, Spec.map_comp]
  let X₁ := pullback toBase₀ Sj
  let f₁ : X₁ ⟶ Spec (CommRingCat.of ↥O) := pullback.snd toBase₀ Sj
  let g₁ : X₁ ⟶ X₀ := pullback.fst toBase₀ Sj
  have hsq₁ : IsPullback g₁ f₁ toBase₀ Sj := IsPullback.of_hasPullback toBase₀ Sj
  let e₁ : X ≅ pullback f₁ Sι :=
    iso ≪≫ pullback.congrHom rfl hSpec ≪≫ (pullbackLeftPullbackSndIso toBase₀ Sj Sι).symm
  have he₁ : e₁.hom ≫ pullback.snd f₁ Sι = toBase := by
    simp only [e₁, f₁, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd,
      pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
    exact hiso
  let π : X ⟶ X₁ := e₁.hom ≫ pullback.fst f₁ Sι
  have hπg : π ≫ g₁ = p₀ := by
    simp only [g₁, π, e₁, f₁, p₀, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
      pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  have hsqπ : π ≫ f₁ = toBase ≫ Sι := by
    rw [← he₁, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨hSιflat, hSιsurj⟩ := flat_and_surjective_specMap A ι₁ hι₁ K₁.toSubfield range_ι₁
  haveI := hSιflat
  haveI := hSιsurj
  haveI hπflat : Flat π := inferInstance
  haveI hπsurj : Surjective π := inferInstance
  haveI hX₁ : IsIntegral X₁ := isIntegral_of_flat_of_surjective π
  have hgen : π.base (genericPoint X) = genericPoint X₁ := base_genericPoint_eq π
  have hgen₁ : g₁.base (genericPoint X₁) = genericPoint X₀ := by
    rw [← hgen]
    change (π ≫ g₁).base (genericPoint X) = genericPoint X₀
    rw [hπg]
    exact hgen₀

  let ψ : X₁.functionField →+* X.functionField := P2mGenEngine.ffMap π hgen
  have hψ : ∀ v, ψ v = (π.stalkMap (genericPoint X)).hom ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom v) :=
    fun v => rfl
  have hle : Subfield.closure (Set.range (P2mGenEngine.ffMap p₀ hgen₀) ∪
      (SemistableModel.baseToFunctionField toBase) '' (Λ : Set ↥A)) ≤ ψ.fieldRange := by
    rw [Subfield.closure_le]
    rintro _ (⟨t, rfl⟩ | ⟨lam, hlam, rfl⟩)
    · refine ⟨P2mGenEngine.ffMap g₁ hgen₁ t, ?_⟩
      show ψ _ = _
      rw [hψ]
      exact (stalkMap_stalkSpecializes_chain π g₁ (genericPoint X) hgen hgen₁ p₀ hπg.symm hgen₀ t).symm
    · have hlamK : ((lam : ↥A) : L) ∈ K₁ := IntermediateField.subset_adjoin K S ⟨lam, hlam, rfl⟩
      let a₁ : ↥O := ⟨⟨(lam : L), hlamK⟩, lam.2⟩
      have ha₁ : ι₁ a₁ = lam := Subtype.ext rfl
      refine ⟨SemistableModel.baseToFunctionField f₁ a₁, ?_⟩
      show ψ _ = _
      rw [hψ, stalkMap_baseToFunctionField ι₁ π f₁ toBase hsqπ hgen a₁, ha₁]
  have hu : ∀ i : Fin n, ∃ u : X₁.functionField, ψ u = f i := fun i => hle (hΛ i)
  choose u hu using hu
  exact ⟨↥O, inferInstance, inferInstance, hDVR, ι₁', hι₁'loc, ι₁, hι₁loc, hι₁, hcomp, ϖ₁, hϖ₁, X₁, hX₁, f₁, g₁,
    hsq₁, e₁, he₁, hπg, hgen, u, fun i => (hu i).symm⟩

end S_AlgebraicCurve_exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min
end P2MW
export P2MW.S_AlgebraicCurve_exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min (solution)
