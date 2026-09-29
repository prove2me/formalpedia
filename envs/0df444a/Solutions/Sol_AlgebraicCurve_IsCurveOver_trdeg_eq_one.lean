-- Prove2me | solution 1 for AlgebraicCurve.IsCurveOver.trdeg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/636e0221-c5c9-559d-ac6d-076cb24c0b8d

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_IsCurveOver_trdeg_eq_one

set_option autoImplicit false

open AlgebraicCurve IntermediateField

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem solution
    (K F : Type*) [Field K] [Field F] [Algebra K F] [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    Algebra.trdeg K F = 1 := by

  have hex : ∃ x : F, Transcendental K x := by
    by_contra h
    push_neg at h
    haveI : Algebra.IsAlgebraic K F := ⟨fun x => not_not.1 (h x)⟩
    haveI : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
    exact false_of_nontrivial_of_subsingleton Ω[F⁄K]
  obtain ⟨x, hx⟩ := hex
  have hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F :=
    AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType hx
  apply le_antisymm
  ·
    haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F := Algebra.IsAlgebraic.of_finite _ F
    haveI : Algebra.IsAlgebraic (Algebra.adjoin K ({x} : Set F)) F :=
      (IsFractionRing.comap_isAlgebraic_iff (A := Algebra.adjoin K ({x} : Set F))
        (K := IntermediateField.adjoin K ({x} : Set F)) (C := F)).2 inferInstance
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk K ({x} : Set F)
    rwa [Cardinal.mk_singleton] at h
  ·
    have hind : AlgebraicIndependent K ![x] := algebraicIndependent_iff_transcendental.2 hx
    have h := hind.lift_cardinalMk_le_trdeg
    rw [Cardinal.mk_fintype, Fintype.card_unique] at h
    simpa using h

end S_AlgebraicCurve_IsCurveOver_trdeg_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_IsCurveOver_trdeg_eq_one (solution)
