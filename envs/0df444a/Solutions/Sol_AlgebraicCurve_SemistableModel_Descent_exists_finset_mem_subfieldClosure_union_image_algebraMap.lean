-- Prove2me | solution 1 for AlgebraicCurve.SemistableModel.Descent.exists_finset_mem_subfieldClosure_union_image_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c849ad57-fd59-53c0-b9dd-491c38a132a6

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableModel_Descent_exists_finset_mem_subfieldClosure_union_image_algebraMap

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

open AlgebraicCurve in
theorem solution
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent) (s : F) :
    ∃ Λ : Finset L, s ∈ Subfield.closure ((D.F₀ : Set F) ∪ (algebraMap L F) '' (↑Λ : Set L)) := by
  classical

  let p : M.X ⟶ D.X₀ := D.iso.hom ≫ pullback.fst D.toBase₀ (Spec.map (CommRingCat.ofHom D.ι))
  have hsq : IsPullback p M.toBase D.toBase₀ (Spec.map (CommRingCat.ofHom D.ι)) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ D.iso rfl D.iso_snd
    change (D.iso.hom ≫ pullback.fst D.toBase₀ (Spec.map (CommRingCat.ofHom D.ι))) ≫ D.toBase₀ = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, D.iso_snd]
  have hgen : p.base (genericPoint M.X) = genericPoint D.X₀ := D.base_genericPoint
  have htop := P2mGenEngine.closure_range_ffMap_union_range_baseToFunctionField_eq_top
    D.ι p M.toBase D.toBase₀ hsq hgen

  set T : Subfield F := Subfield.closure ((D.F₀ : Set F) ∪ Set.range (algebraMap L F)) with hT
  have hle : Subfield.closure (Set.range (P2mGenEngine.ffMap p hgen) ∪
      Set.range (SemistableModel.baseToFunctionField M.toBase)) ≤ T.map M.ffEquiv.toRingHom := by
    rw [Subfield.closure_le]
    rintro _ (⟨w, rfl⟩ | ⟨a, rfl⟩)
    · rw [SetLike.mem_coe, Subfield.mem_map]
      refine ⟨((D.ffEquiv₀.symm w : D.F₀) : F), Subfield.subset_closure (Or.inl (D.ffEquiv₀.symm w).2), ?_⟩
      change M.ffEquiv _ = _
      rw [D.ffEquiv₀_ffEquiv, RingEquiv.apply_symm_apply]
      rfl
    · rw [SetLike.mem_coe, Subfield.mem_map]
      refine ⟨algebraMap L F (a : L), Subfield.subset_closure (Or.inr ⟨_, rfl⟩), ?_⟩
      exact M.ffEquiv_algebraMap a
  rw [htop, top_le_iff] at hle
  have hsT : s ∈ T := by
    have : M.ffEquiv s ∈ T.map M.ffEquiv.toRingHom := by rw [hle]; exact Subfield.mem_top _
    rw [Subfield.mem_map] at this
    obtain ⟨y, hy, hys⟩ := this
    have : y = s := M.ffEquiv.injective hys
    rw [← this]; exact hy
  exact P2mGenEngine.exists_finset_mem_closure_union_image (L := L) (D.F₀ : Set F) hsT

end S_AlgebraicCurve_SemistableModel_Descent_exists_finset_mem_subfieldClosure_union_image_algebraMap
end P2MW
export P2MW.S_AlgebraicCurve_SemistableModel_Descent_exists_finset_mem_subfieldClosure_union_image_algebraMap (solution)
