-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/81bdac48-ae0d-594f-9237-6cd5d62e378b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {X : Scheme.{u}} [IsIntegral X] (x : X) (P : Ideal (X.presheaf.stalk x)) [hP : P.IsPrime] :
    ∃ hη : (X.fromSpecStalk x).base ⟨P, hP⟩ ⤳ x,
      (∀ b : X.presheaf.stalk x,
        b ∈ P ↔ X.residue ((X.fromSpecStalk x).base ⟨P, hP⟩) ((X.presheaf.stalkSpecializes hη).hom b) = 0) ∧
      ((X.fromSpecStalk x).base ⟨P, hP⟩ = genericPoint X ↔ P = ⊥) := by
  classical

  have hη : (X.fromSpecStalk x).base ⟨P, hP⟩ ⤳ x := by
    have : (X.fromSpecStalk x).base ⟨P, hP⟩ ∈ Set.range (X.fromSpecStalk x).base := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  refine ⟨hη, fun b => ?_, ?_⟩
  ·
    have hqc : (⟨P, hP⟩ : Spec (X.presheaf.stalk x)) ⤳ IsLocalRing.closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.specializes_closedPoint _
    have hins : Inseparable ((X.fromSpecStalk x).base (IsLocalRing.closedPoint (X.presheaf.stalk x))) x := by
      rw [Scheme.fromSpecStalk_closedPoint]

    have key : X.presheaf.stalkSpecializes hη ≫ (X.fromSpecStalk x).stalkMap ⟨P, hP⟩ =
        StructureSheaf.toStalk (X.presheaf.stalk x) ⟨P, hP⟩ := by
      have h1 := (X.fromSpecStalk x).stalkSpecializes_stalkMap _ _ hqc
      have h2 : X.presheaf.stalkSpecializes hη = (X.presheaf.stalkCongr hins).inv ≫
          X.presheaf.stalkSpecializes ((X.fromSpecStalk x).base.hom.map_specializes hqc) := by
        rw [TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.stalkSpecializes_comp]
      have h3 : (X.fromSpecStalk x).stalkMap (IsLocalRing.closedPoint (X.presheaf.stalk x)) =
          Scheme.stalkClosedPointTo (X.fromSpecStalk x) ≫ (stalkClosedPointIso (X.presheaf.stalk x)).inv := by
        rw [Scheme.stalkClosedPointTo, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [h2, Category.assoc, h1, h3, Scheme.stalkClosedPointTo_fromSpecStalk, stalkClosedPointIso_inv,
        Category.assoc, Iso.inv_hom_id_assoc]
      exact StructureSheaf.toStalk_stalkSpecializes hqc
    have keyb : ((X.fromSpecStalk x).stalkMap ⟨P, hP⟩).hom ((X.presheaf.stalkSpecializes hη).hom b) =
        (StructureSheaf.toStalk (X.presheaf.stalk x) ⟨P, hP⟩).hom b := by
      have := congrArg (fun φ => φ.hom b) key
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
      exact this

    letI : Algebra (X.presheaf.stalk x) ((Spec (X.presheaf.stalk x)).presheaf.stalk ⟨P, hP⟩) :=
      StructureSheaf.stalkAlgebra (R := X.presheaf.stalk x) ⟨P, hP⟩
    haveI : IsLocalization.AtPrime ((Spec (X.presheaf.stalk x)).presheaf.stalk ⟨P, hP⟩)
        (⟨P, hP⟩ : PrimeSpectrum (X.presheaf.stalk x)).asIdeal :=
      StructureSheaf.IsLocalization.to_stalk (X.presheaf.stalk x) ⟨P, hP⟩
    have hloc : b ∈ P ↔ (StructureSheaf.toStalk (X.presheaf.stalk x) ⟨P, hP⟩).hom b ∈
        IsLocalRing.maximalIdeal ((Spec (X.presheaf.stalk x)).presheaf.stalk ⟨P, hP⟩) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff ((Spec (X.presheaf.stalk x)).presheaf.stalk ⟨P, hP⟩)
        (⟨P, hP⟩ : PrimeSpectrum (X.presheaf.stalk x)).asIdeal b).symm
    rw [hloc, ← keyb]
    refine (IsLocalRing.mem_maximalIdeal (R := (Spec (X.presheaf.stalk x)).presheaf.stalk ⟨P, hP⟩) _).trans ?_
    refine mem_nonunits_iff.trans ?_
    refine (isUnit_map_iff ((X.fromSpecStalk x).stalkMap ⟨P, hP⟩).hom _).not.trans ?_
    refine mem_nonunits_iff.symm.trans ?_
    refine (IsLocalRing.mem_maximalIdeal _).symm.trans ?_
    exact (IsLocalRing.residue_eq_zero_iff _).symm
  ·
    have hgen : (X.fromSpecStalk x).base (⊥ : PrimeSpectrum (X.presheaf.stalk x)) = genericPoint X := by
      obtain ⟨q₀, hq₀⟩ : genericPoint X ∈ Set.range (X.fromSpecStalk x).base := by
        rw [Scheme.range_fromSpecStalk]; exact genericPoint_specializes x
      have hb : (⊥ : PrimeSpectrum (X.presheaf.stalk x)) ⤳ q₀ := by
        have := genericPoint_specializes q₀
        rwa [genericPoint_eq_bot_of_affine] at this
      have h1 : (X.fromSpecStalk x).base (⊥ : PrimeSpectrum (X.presheaf.stalk x)) ⤳ genericPoint X :=
        hq₀ ▸ hb.map (X.fromSpecStalk x).base.hom.continuous
      exact (h1.antisymm (genericPoint_specializes _)).eq
    constructor
    · intro h
      have := (X.fromSpecStalk x).isEmbedding.injective (h.trans hgen.symm)
      exact congrArg PrimeSpectrum.asIdeal this
    · intro h
      have : (⟨P, hP⟩ : PrimeSpectrum (X.presheaf.stalk x)) = ⊥ := PrimeSpectrum.ext h
      rw [this]
      exact hgen

end S_AlgebraicGeometry_Scheme_exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff (solution)
