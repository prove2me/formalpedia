-- Prove2me | solution 1 for AlgebraicCurve.existsUnique_centre_place_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ebace3ab-a03e-5207-aa1e-2e8cba6624a0

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_existsUnique_centre_place_of_isProper

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace CentreL2

open WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_iff_adicValuation_le_one (v : Place K F) (x : F) :
    x ∈ v.toValuationSubring ↔ v.adicValuation x ≤ 1 := by
  refine ⟨fun h => v.adicValuation_le_one_of_mem h, fun h => ?_⟩
  by_contra hx
  have hx0 : x ≠ 0 := fun e => hx (e ▸ v.toValuationSubring.zero_mem)
  have hxi : x⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem x).resolve_left hx
  have hnu : ¬ IsUnit (⟨x⁻¹, hxi⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨w, hw⟩ := hu
    apply hx
    have : x = ((w⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) := by
      have h1 : ((w : v.toValuationSubring) : F) * ((w⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) = 1 := by
        rw [← MulMemClass.coe_mul, w.mul_inv]
        rfl
      rw [hw] at h1
      rw [eq_inv_of_mul_eq_one_right h1, inv_inv]
    rw [this]
    exact SetLike.coe_mem _
  have hlt : v.adicValuation x⁻¹ < 1 :=
    lt_of_le_of_ne (v.adicValuation_le_one_of_mem hxi)
      (fun e => hnu ((v.adicValuation_coe_eq_one_iff ⟨x⁻¹, hxi⟩).mp e))
  rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.mpr (v.adicValuation_ne_zero hx0))] at hlt
  exact not_le.mpr hlt h

theorem adicValuation_lt_one_of_not_isUnit (v : Place K F) {x : v.toValuationSubring}
    (hx : ¬ IsUnit x) : v.adicValuation (x : F) < 1 :=
  lt_of_le_of_ne (v.adicValuation_le_one_of_mem x.2)
    (fun e => hx ((v.adicValuation_coe_eq_one_iff x).mp e))

end CentreL2

open CentreL2 in

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ v : Place k C.functionField, ∃! z : C, (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1)) := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  intro v

  have hVC : ValuativeCriterion c := by
    have h : IsProper c := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1

  let R : Type u := ↥v.toValuationSubring
  have F1 : C.fromSpecStalk (genericPoint C) ≫ c =
      Spec.map (CommRingCat.ofHom (algebraMap R C.functionField)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
    rw [← Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq,
      ← Spec.map_comp, Category.assoc, Scheme.Hom.germ_stalkMap]
    congr 1
  let Sq : ValuativeCommSq c :=
    { R := R, K := C.functionField, i₁ := C.fromSpecStalk (genericPoint C),
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap k R)), commSq := ⟨F1⟩ }

  have mkLift : ∀ z : C, (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1)) →
      ∃ L : Sq.commSq.LiftStruct, L.l.base (IsLocalRing.closedPoint R) = z := by
    intro z hz
    have hmem : ∀ s, algebraMap (C.presheaf.stalk z) C.functionField s ∈ v.toValuationSubring :=
      fun s => (mem_iff_adicValuation_le_one v _).mpr (hz s).1
    let ψ : C.presheaf.stalk z →+* R :=
      (algebraMap (C.presheaf.stalk z) C.functionField).codRestrict v.toValuationSubring hmem
    haveI hloc : IsLocalHom ψ := by
      refine ⟨fun s hs => ?_⟩
      by_contra hns
      have h1 := (hz s).2 ((IsLocalRing.mem_maximalIdeal s).mpr hns)
      have h2 : v.adicValuation ((ψ s : R) : C.functionField) = 1 :=
        (v.adicValuation_coe_eq_one_iff _).mpr hs
      exact (lt_irrefl _) (h2 ▸ h1)
    haveI : IsLocalHom (CommRingCat.ofHom ψ).hom := hloc
    have hσ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap R C.functionField) =
        C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes (Set.mem_univ z)) := by
      ext s
      rfl
    refine ⟨⟨Spec.map (CommRingCat.ofHom ψ) ≫ C.fromSpecStalk z, ?_, ?_⟩, ?_⟩
    · show Spec.map (CommRingCat.ofHom (algebraMap R C.functionField)) ≫
        Spec.map (CommRingCat.ofHom ψ) ≫ C.fromSpecStalk z = C.fromSpecStalk (genericPoint C)
      rw [← Spec.map_comp_assoc, hσ, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    · show (Spec.map (CommRingCat.ofHom ψ) ≫ C.fromSpecStalk z) ≫ c =
        Spec.map (CommRingCat.ofHom (algebraMap k R))
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq,
        ← Spec.map_comp, ← Spec.map_comp]
      simp only [Category.assoc]
      rw [Scheme.Hom.germ_stalkMap_assoc]
      congr 1
      ext a
      show algebraMap (C.presheaf.stalk z) C.functionField
        (C.presheaf.germ (c ⁻¹ᵁ ⊤) z trivial (c.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a))) =
        baseToFunctionField c a
      show C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes (Set.mem_univ z))
        (C.presheaf.germ (c ⁻¹ᵁ ⊤) z trivial (c.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a))) = _
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
      rfl
    · show (Spec.map (CommRingCat.ofHom ψ) ≫ C.fromSpecStalk z).base (IsLocalRing.closedPoint R) = z
      rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  obtain ⟨Lu⟩ := hVC Sq
  let ℓ := Lu.default.l

  refine ⟨ℓ.base (IsLocalRing.closedPoint R), ?_, ?_⟩
  · intro s

    have F2 : Scheme.stalkClosedPointTo ℓ ≫ CommRingCat.ofHom (algebraMap R C.functionField) =
        C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes (Set.mem_univ _)) := by
      apply Spec.map_injective
      rw [← cancel_mono (C.fromSpecStalk _), Spec.map_comp, Category.assoc,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      exact Lu.default.fac_left
    have hs : algebraMap (C.presheaf.stalk (ℓ.base (IsLocalRing.closedPoint R))) C.functionField s =
        ((Scheme.stalkClosedPointTo ℓ).hom s : R) := by
      show (C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes (Set.mem_univ _))).hom s = _
      rw [← F2]
      rfl
    refine ⟨?_, fun hsm => ?_⟩
    · rw [hs]; exact v.adicValuation_le_one_of_mem (SetLike.coe_mem _)
    · rw [hs]
      apply adicValuation_lt_one_of_not_isUnit
      intro hu
      exact ((IsLocalRing.mem_maximalIdeal s).mp hsm) (IsLocalHom.map_nonunit _ hu)
  ·
    intro z₁ hz₁
    obtain ⟨L₁, hL₁⟩ := mkLift z₁ hz₁
    rw [← hL₁, Subsingleton.elim L₁ Lu.default]

#print axioms solution

end S_AlgebraicCurve_existsUnique_centre_place_of_isProper
end P2MW
export P2MW.S_AlgebraicCurve_existsUnique_centre_place_of_isProper (solution)
