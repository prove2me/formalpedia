-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/438910d6-6e3f-52e9-9994-7bd7ba0eb471

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem solution
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) (x : closedPoints M.C) (hx : (M.placeOfPoint x).deg = 1) :
    ∃ pt : Spec (CommRingCat.of K) ⟶ M.C,
      pt ≫ M.toBase = 𝟙 _ ∧ pt.base (IsLocalRing.closedPoint K) = x.1 := by
  classical

  set v : Place K L := M.placeOfPoint x
  let A : ValuationSubring L := v.toValuationSubring
  let S : CommRingCat := M.C.presheaf.stalk x.1

  let ρ : CommRingCat.of K ⟶ M.C.residueField x.1 :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ M.toBase.appTop ≫ M.C.Γevaluation x.1

  have hA : M.C.fromSpecResidueField x.1 ≫ M.toBase = Spec.map ρ := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    simp only [← Spec.map_comp]
    congr 1
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of K) (M.toBase.base x.1)]
    simp only [ρ, Category.assoc, Scheme.residue_residueFieldMap, Scheme.Hom.germ_stalkMap_assoc]
    rfl

  let φ : S →+* L :=
    (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp (algebraMap S M.C.functionField)
  have hφrange : φ.range = A.toSubring := M.range_stalk_eq x
  have hφmem : ∀ s : S, φ s ∈ A := fun s => by
    have h : φ s ∈ φ.range := ⟨s, rfl⟩
    rw [hφrange] at h
    exact h
  let ψ : S →+* A := φ.codRestrict A hφmem
  have hψ : ∀ s : S, (ψ s : L) = φ s := fun _ => rfl

  let c : K → S := fun a =>
    M.C.presheaf.germ ⊤ x.1 trivial (M.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))
  have hρc : ∀ a : K, ρ.hom a = IsLocalRing.residue S (c a) := fun _ => rfl

  have hgerm : ∀ t : Γ(M.C, ⊤), algebraMap S M.C.functionField (M.C.presheaf.germ ⊤ x.1 trivial t)
      = M.C.presheaf.germ ⊤ (genericPoint M.C) trivial t := by
    intro t
    change (M.C.presheaf.germ ⊤ x.1 trivial ≫ M.C.presheaf.stalkSpecializes
      ((genericPoint_spec M.C).specializes trivial)) t = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]

  have hφc : ∀ a : K, φ (c a) = algebraMap K L a := by
    intro a
    have h1 : algebraMap S M.C.functionField (c a) = baseToFunctionField M.toBase a := hgerm _
    simp only [φ, RingHom.coe_comp, Function.comp_apply, h1, ← M.ffEquiv_algebraMap]
    exact M.ffEquiv.symm_apply_apply _
  have hψc : ∀ a : K, ψ (c a) = algebraMap K A a := fun a =>
    Subtype.ext (by rw [hψ, hφc]; rfl)

  have hx' : Module.finrank K v.ResidueField = 1 := hx
  have hsurjA : Function.Surjective (algebraMap K v.ResidueField) := by
    have hbt : (⊥ : Subalgebra K v.ResidueField) = ⊤ :=
      Subalgebra.bot_eq_top_of_finrank_eq_one hx'
    intro r
    have hr : r ∈ (⊤ : Subalgebra K v.ResidueField) := Algebra.mem_top
    rw [← hbt, Algebra.mem_bot] at hr
    exact hr

  have hρsurj : Function.Surjective ρ.hom := by
    intro r
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective (R := S) r
    obtain ⟨a, ha⟩ := hsurjA (IsLocalRing.residue A (ψ s))
    refine ⟨a, ?_⟩
    rw [hρc]
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) (c a)
      = Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) s
    rw [Ideal.Quotient.eq]

    by_contra hns
    have hu : IsUnit (c a - s) := by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hns
    have hu' : IsUnit (algebraMap K A a - ψ s) := by
      have := hu.map ψ
      rwa [map_sub, hψc] at this
    have hne : IsLocalRing.residue A (algebraMap K A a - ψ s) ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu'
    apply hne
    rw [map_sub, sub_eq_zero, ← ha]
    rfl

  haveI : IsIso ρ := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨ρ.hom.injective, hρsurj⟩
  refine ⟨Spec.map (inv ρ) ≫ M.C.fromSpecResidueField x.1, ?_, ?_⟩
  · rw [Category.assoc, hA, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]
  · simp

end S_AlgebraicCurve_CurveModel_exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one (solution)
