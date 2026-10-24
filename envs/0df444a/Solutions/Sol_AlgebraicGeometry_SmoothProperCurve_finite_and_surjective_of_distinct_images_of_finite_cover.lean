-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.finite_and_surjective_of_distinct_images_of_finite_cover
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T13:15:33.367378+00:00
-- url     : https://prove2.me/submissions/3732fe34-f00e-4167-97fa-9f331d74bcb9

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace PhilipponProperCurveMap

lemma closed_of_ne_generic {X : Type*} [TopologicalSpace X] [T0Space X]
    [QuasiSober X] [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 1)
    (x : X) (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  let Z : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hmin : IsMin Z := by
    rcases Order.krullDim_le_one_iff.mp hdim Z with h | h
    · exact h
    · have heq : Z = T := le_antisymm (fun _ _ => trivial) (h (fun _ _ => trivial))
      apply False.elim
      apply hx
      apply (isGenericPoint_closure (x := x)).eq
      rw [show closure {x} = Set.univ from congrArg
        (fun a : TopologicalSpace.IrreducibleCloseds X => (a : Set X)) heq]
      exact genericPoint_spec X
  have hcl : closure ({x} : Set X) = {x} := by
    apply Set.Subset.antisymm ?_ subset_closure
    intro y hy
    let Y : TopologicalSpace.IrreducibleCloseds X :=
      ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hYZ : Y ≤ Z := closure_minimal (Set.singleton_subset_iff.mpr hy) isClosed_closure
    have hZY : Z ≤ Y := hmin hYZ
    have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
    have hyx : y ⤳ x := specializes_iff_mem_closure.mpr
      (hZY (subset_closure (Set.mem_singleton x)))
    exact Set.mem_singleton_iff.mpr ((hxy.antisymm hyx).eq.symm)
  exact closure_eq_iff_isClosed.mp hcl

/-- Over any field, a rational section is determined by its image point. -/
lemma rational_point_ext {K : Type u} [Field K] {Y : Scheme.{u}}
    (y : Y ⟶ Spec (.of K)) (p q : Spec (.of K) ⟶ Y)
    (hp : p ≫ y = 𝟙 _) (hq : q ≫ y = 𝟙 _)
    (heq : p (IsLocalRing.closedPoint K) = q (IsLocalRing.closedPoint K)) : p = q := by
  let x := p (IsLocalRing.closedPoint K)
  let m : Y.residueField x ⟶ .of K :=
    Y.descResidueField (Scheme.stalkClosedPointTo p)
  let n : Y.residueField x ⟶ .of K :=
    (Y.residueFieldCongr heq).hom ≫ Y.descResidueField (Scheme.stalkClosedPointTo q)
  have hm : Spec.map m ≫ Y.fromSpecResidueField x = p :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y p
  have hn : Spec.map n ≫ Y.fromSpecResidueField x = q := by
    simp only [n, Spec.map_comp, Category.assoc]
    rw [Scheme.residueFieldCongr_fromSpecResidueField]
    exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y q
  let r : CommRingCat.of K ⟶ Y.residueField x :=
    Spec.preimage (Y.fromSpecResidueField x ≫ y)
  have hrm : r ≫ m = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc, hm, hp, Spec.map_id]
  have hrn : r ≫ n = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc, hn, hq, Spec.map_id]
  have hr : Function.Surjective r := by
    intro z
    refine ⟨m z, m.hom.injective ?_⟩
    exact congrArg (fun t : CommRingCat.of K ⟶ CommRingCat.of K => t (m z)) hrm
  have hmn : m = n := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    obtain ⟨a, rfl⟩ := hr z
    exact (congrArg (fun t : CommRingCat.of K ⟶ CommRingCat.of K => t a) hrm).trans
      (congrArg (fun t : CommRingCat.of K ⟶ CommRingCat.of K => t a) hrn).symm
  rw [← hm, ← hn, hmn]

lemma closed_off_generic_of_finite {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : X ⟶ Y) [IsFinite g] [Surjective g]
    (hY : ∀ y : Y, y ≠ genericPoint Y → IsClosed ({y} : Set Y)) :
    ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X) := by
  have hg : g (genericPoint X) = genericPoint Y := by
    apply IsGenericPoint.eq ?_ (genericPoint_spec Y)
    simpa [Set.image_univ, Set.range_eq_univ.mpr g.surjective] using
      (genericPoint_spec X).image g.continuous
  intro x hx
  have hgx : g x ≠ genericPoint Y := by
    intro heq
    have he := (g.isDiscrete_preimage_singleton (genericPoint Y)).eq_of_specializes
      (genericPoint_specializes x) (by change g (genericPoint X) = genericPoint Y; exact hg)
      (by change g x = genericPoint Y; exact heq)
    exact hx he.symm
  have hc := hY (g x) hgx
  have hcl : closure ({x} : Set X) = {x} := by
    apply Set.Subset.antisymm ?_ subset_closure
    intro z hz
    have hxz : x ⤳ z := specializes_iff_mem_closure.mpr hz
    have hgz : g z = g x := (hxz.map g.continuous).mem_closed hc (Set.mem_singleton _)
    have he := (g.isDiscrete_preimage_singleton (g x)).eq_of_specializes hxz
      (by change g x = g x; rfl) (by change g z = g x; exact hgz)
    exact Set.mem_singleton_iff.mpr he.symm
  exact closure_eq_iff_isClosed.mp hcl

lemma finite_of_nonconstant {K : Type u} [Field K] {D Y : Scheme.{u}}
    (d : D ⟶ Spec (.of K)) [IsIntegral D] [IsProper d]
    [SmoothOfRelativeDimension 1 d] (y : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType y] [IsSeparated y]
    (f : D ⟶ Y) (hf : f ≫ y = d) (hn : ¬ (Set.range f).Subsingleton) : IsFinite f := by
  let : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian d
  let : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace d
  let : AlgebraicGeometry.IsNoetherian D := ⟨⟩
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace y
  have : IsProper (f ≫ y) := by rw [hf]; infer_instance
  have : IsProper f := IsProper.of_comp f y
  have hdim := SmoothOfRelativeDimension.topologicalKrullDim_le d 1
  have hD := closed_of_ne_generic hdim
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsFinite)
  intro z
  obtain ⟨v, hvz, hv⟩ := nonempty_inter_closedPoints
    (Set.singleton_nonempty z |>.mono subset_closure) isClosed_closure.isLocallyClosed
  have hzv : z ⤳ v := specializes_iff_mem_closure.mpr hvz
  have hpre : IsClosed (f ⁻¹' {v}) := hv.preimage f.continuous
  have hne : f ⁻¹' {v} ≠ Set.univ := by
    intro heq
    apply hn
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have ha : f a = v := by
      have : a ∈ f ⁻¹' {v} := heq.symm ▸ Set.mem_univ a
      exact this
    have hb : f b = v := by
      have : b ∈ f ⁻¹' {v} := heq.symm ▸ Set.mem_univ b
      exact this
    exact ha.trans hb.symm
  have hfin := Scheme.finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton hD
    (f ⁻¹' {v}) hpre hne
  obtain ⟨V, hvV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f v hfin
  exact ⟨V, hzv.mem_open V.isOpen hvV, hV⟩

lemma surjective_of_nonconstant {D Y : Scheme.{u}} [IsIntegral D] [JacobsonSpace D]
    [IsIntegral Y] [NoetherianSpace Y] (f : D ⟶ Y) [IsProper f]
    (hY : ∀ y : Y, y ≠ genericPoint Y → IsClosed ({y} : Set Y))
    (hn : ¬ (Set.range f).Subsingleton) : Surjective f := by
  constructor
  apply Set.range_eq_univ.mp
  by_contra hne
  have hc : IsClosed (Set.range f) := by
    simpa only [Set.image_univ] using f.isClosedMap _ isClosed_univ
  have hfin := Scheme.finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton hY
    (Set.range f) hc hne
  have hsub := subsingleton_image_closure_of_finite_of_isPreirreducible
    (f := fun x => f x) isClosed_univ.isLocallyClosed
    (IrreducibleSpace.isIrreducible_univ D).isPreirreducible f.continuous f.isClosedMap
    (by simpa only [Set.image_univ] using hfin)
  exact hn (by simpa using hsub)

end PhilipponProperCurveMap

theorem solution
    (K : Type u) [Field K] {C W D : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (g : W ⟶ C)
    [IsIntegral W] [IsFinite g] [Surjective g]
    (d : D ⟶ Spec (.of K)) [IsIntegral D] [IsProper d]
    [SmoothOfRelativeDimension 1 d] (f : D ⟶ W) (hf : f ≫ (g ≫ c) = d)
    (a b : Spec (.of K) ⟶ D) (ha : a ≫ d = 𝟙 _) (hb : b ≫ d = 𝟙 _)
    (hne : a ≫ f ≠ b ≫ f) : IsFinite f ∧ Surjective f := by
  let w := g ≫ c
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian w
  let : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace w
  let : AlgebraicGeometry.IsNoetherian W := ⟨⟩
  let : JacobsonSpace D := LocallyOfFiniteType.jacobsonSpace d
  have hn : ¬ (Set.range f).Subsingleton := by
    intro hsub
    apply hne
    apply PhilipponProperCurveMap.rational_point_ext w (a ≫ f) (b ≫ f)
    · change (a ≫ f) ≫ (g ≫ c) = 𝟙 _
      rw [Category.assoc, hf]
      exact ha
    · change (b ≫ f) ≫ (g ≫ c) = 𝟙 _
      rw [Category.assoc, hf]
      exact hb
    · exact hsub ⟨a (IsLocalRing.closedPoint K), rfl⟩
        ⟨b (IsLocalRing.closedPoint K), rfl⟩
  have hfinite := PhilipponProperCurveMap.finite_of_nonconstant d w f hf hn
  let := hfinite
  have hC := PhilipponProperCurveMap.closed_of_ne_generic
    (SmoothOfRelativeDimension.topologicalKrullDim_le c 1)
  have hW := PhilipponProperCurveMap.closed_off_generic_of_finite g hC
  exact ⟨hfinite, PhilipponProperCurveMap.surjective_of_nonconstant f hW hn⟩
