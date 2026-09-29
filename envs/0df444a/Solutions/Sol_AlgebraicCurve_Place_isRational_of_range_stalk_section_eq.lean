-- Prove2me | solution 1 for AlgebraicCurve.Place.isRational_of_range_stalk_section_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/50d49bcd-4686-5803-8380-931eda8e7310

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Opposite

namespace RatPlaceAux

theorem residue_germ_surjective (k : Type u) [Field k] :
    Function.Surjective (fun t : Γ(Spec (CommRingCat.of k), ⊤) =>
      (Spec (CommRingCat.of k)).residue (closedPoint k)
        ((Spec (CommRingCat.of k)).presheaf.germ ⊤ (closedPoint k) trivial t)) := by
  intro z
  obtain ⟨s, rfl⟩ := (Spec (CommRingCat.of k)).residue_surjective (closedPoint k) z
  obtain ⟨U, hU, t, rfl⟩ := TopCat.Presheaf.germ_exist (Spec (CommRingCat.of k)).presheaf s
  have hUtop : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [Subsingleton.elim y (closedPoint k)]
    exact hU
  subst hUtop
  exact ⟨t, rfl⟩

end RatPlaceAux

open RatPlaceAux in
theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    (σ : Spec (CommRingCat.of k) ⟶ X) (hσ : σ ≫ c = 𝟙 _) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ (v : AlgebraicCurve.Place k X.functionField),
      (algebraMap (X.presheaf.stalk (σ.base (IsLocalRing.closedPoint k))) X.functionField).range =
        v.toValuationSubring.toSubring → v.IsRational := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  intro v hv

  set x : X := σ.base (closedPoint k) with hxdef
  let A : Type u := X.presheaf.stalk x
  let φ : A →+* X.functionField := algebraMap A X.functionField
  have hφinj : Function.Injective φ := IsFractionRing.injective A X.functionField

  let ι : k →+* Γ(Spec (CommRingCat.of k), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  let toA : k →+* A := (X.presheaf.germ ⊤ x trivial).hom.comp (c.appTop.hom.comp ι)
  have hcompat : ∀ a : k, φ (toA a) = algebraMap k X.functionField a := by
    intro a
    show φ ((X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom (ι a))) =
      (X.presheaf.germ ⊤ (genericPoint X) trivial).hom (c.appTop.hom (ι a))
    have := X.presheaf.germ_stalkSpecializes (U := ⊤) (y := x) trivial (x := genericPoint X)
      ((genericPoint_spec X).specializes (trivial : x ∈ (⊤ : Set X)))
    exact congrArg (fun f => f.hom (c.appTop.hom (ι a))) this

  let g : A →+* (Spec (CommRingCat.of k)).residueField (closedPoint k) :=
    ((Spec (CommRingCat.of k)).residue (closedPoint k)).hom.comp (σ.stalkMap (closedPoint k)).hom
  have hg : ∀ a : k, g (toA a) =
      (Spec (CommRingCat.of k)).residue (closedPoint k)
        ((Spec (CommRingCat.of k)).presheaf.germ ⊤ (closedPoint k) trivial (ι a)) := by
    intro a
    show (Spec (CommRingCat.of k)).residue (closedPoint k)
        ((X.presheaf.germ ⊤ x trivial ≫ σ.stalkMap (closedPoint k)).hom (c.appTop.hom (ι a))) = _
    rw [Scheme.Hom.germ_stalkMap σ ⊤ (closedPoint k) trivial]
    show (Spec (CommRingCat.of k)).residue (closedPoint k)
        (((Spec (CommRingCat.of k)).presheaf.germ ⊤ (closedPoint k) trivial).hom ((c.appTop ≫ σ.appTop).hom (ι a))) = _
    rw [← Scheme.Hom.comp_appTop, hσ, Scheme.Hom.id_appTop]
    rfl

  have hconst : ∀ s : A, ∃ a : k, s - toA a ∈ maximalIdeal A := by
    intro s
    obtain ⟨t, ht⟩ := residue_germ_surjective k (g s)
    obtain ⟨a, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective t
    refine ⟨a, ?_⟩
    have h0 : g (s - toA a) = 0 := by rw [map_sub, hg, sub_eq_zero]; exact ht.symm
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (hu.map g).ne_zero h0

  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hy : (y : X.functionField) ∈ φ.range := by rw [hv]; exact y.2
  obtain ⟨s, hs⟩ := hy
  obtain ⟨a, ha⟩ := hconst s
  refine ⟨a, ?_⟩

  show Ideal.Quotient.mk _ (⟨algebraMap k X.functionField a, v.algebraMap_mem' a⟩ : v.toValuationSubring) = Ideal.Quotient.mk _ y
  rw [Ideal.Quotient.eq, mem_maximalIdeal, mem_nonunits_iff]

  have hm : toA a - s ∈ maximalIdeal A := by simpa using neg_mem ha
  rintro ⟨w, hw⟩

  have hw1 := congrArg Subtype.val w.val_inv
  rw [hw] at hw1
  obtain ⟨t, ht⟩ : ((w⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring).1 ∈ φ.range := by
    rw [hv]; exact ((w⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring).2
  have hval : ((⟨algebraMap k X.functionField a, v.algebraMap_mem' a⟩ : v.toValuationSubring) - y).1 = φ (toA a - s) := by
    show algebraMap k X.functionField a - (y : X.functionField) = _
    rw [map_sub, hcompat, hs]
  have hprod : φ ((toA a - s) * t) = φ 1 := by
    rw [map_mul, map_one, ← hval, ht]
    exact hw1
  have hunit : IsUnit (toA a - s) := IsUnit.of_mul_eq_one t (hφinj hprod)
  exact (mem_maximalIdeal _ |>.mp hm) hunit

end S_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq
end P2MW
export P2MW.S_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq (solution)
