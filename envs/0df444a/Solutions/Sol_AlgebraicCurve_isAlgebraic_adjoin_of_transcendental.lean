-- Prove2me | solution 1 for AlgebraicCurve.isAlgebraic_adjoin_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4ad059e0-b94e-59d0-8eee-547b3ce24372

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental

open Set Cardinal

namespace AlgebraicCurve
namespace FF2KE3

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isAlgebraic_adjoin_of_transcendental' (x : F)
    [halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F := by

  have hx : Transcendental K x := by
    intro hxalg
    haveI : Algebra.IsAlgebraic K (IntermediateField.adjoin K ({x} : Set F)) :=
      IntermediateField.isAlgebraic_adjoin_simple hxalg.isIntegral
    haveI : Algebra.IsAlgebraic K F :=
      Algebra.IsAlgebraic.trans K (IntermediateField.adjoin K ({x} : Set F)) F
    exact ht (Algebra.IsAlgebraic.isAlgebraic t)

  have hbx : IsTranscendenceBasis K ![x] := by
    rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨algebraicIndependent_iff_transcendental.mpr hx, ?_⟩
    have : Set.range ![x] = {x} := by simp
    rw [this]
    exact (IntermediateField.isAlgebraic_adjoin_iff_top (F := K) (s := ({x} : Set F))).mp halg

  have hind : AlgebraicIndepOn K id ({t} : Set F) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using ht
  obtain ⟨S, htS, hS⟩ := exists_isTranscendenceBasis_superset hind

  have hcard := hS.lift_cardinalMk_eq hbx
  simp only [Cardinal.mk_fin, Nat.cast_one, Cardinal.lift_one, Cardinal.lift_eq_one] at hcard
  have hS_eq : S = {t} :=
    (Cardinal.mk_le_one_iff_set_subsingleton.mp hcard.le).eq_singleton_of_mem (htS rfl)
  subst hS_eq
  have h := hS.isAlgebraic_field
  rwa [Subtype.range_coe] at h

end AlgebraicCurve.FF2KE3

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F :=
  AlgebraicCurve.FF2KE3.isAlgebraic_adjoin_of_transcendental' x ht

end S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental
end P2MW
export P2MW.S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental (solution)
