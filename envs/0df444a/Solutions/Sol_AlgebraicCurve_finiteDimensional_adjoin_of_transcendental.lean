-- Prove2me | solution 1 for AlgebraicCurve.finiteDimensional_adjoin_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/bc4e1e56-5766-5df9-8200-673eaab4dc84

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental

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

theorem finiteDimensional_adjoin_of_transcendental' (x : F)
    [hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (ht : Transcendental K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := by
  haveI halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F :=
    isAlgebraic_adjoin_of_transcendental' x ht
  set E := IntermediateField.adjoin K ({t} : Set F)
  set Kx := IntermediateField.adjoin K ({x} : Set F)

  let b := Module.finBasis Kx F
  let S : Set F := insert x (Set.range b)
  haveI : Finite S := Set.Finite.insert x (Set.finite_range b) |>.to_subtype

  haveI hM : FiniteDimensional E (IntermediateField.adjoin E S) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (halg.isAlgebraic y).isIntegral

  have htop : IntermediateField.adjoin E S = ⊤ := by
    rw [eq_top_iff]
    intro y _

    have hKx : ∀ c : Kx, (c : F) ∈ IntermediateField.adjoin E S := by
      intro c
      have hle : Kx ≤ (IntermediateField.adjoin E S).restrictScalars K := by
        rw [IntermediateField.adjoin_le_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact IntermediateField.subset_adjoin E S (Set.mem_insert _ _)
      exact hle c.2

    rw [← b.sum_repr y]
    refine Subfield.sum_mem _ fun i _ => ?_
    rw [IntermediateField.smul_def]
    exact mul_mem (hKx _) (IntermediateField.subset_adjoin E S (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  rw [htop] at hM
  exact (IntermediateField.topEquiv (F := E) (E := F)).toLinearEquiv.finiteDimensional

end AlgebraicCurve.FF2KE3

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] {t : F} (ht : Transcendental K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F :=
  AlgebraicCurve.FF2KE3.finiteDimensional_adjoin_of_transcendental' x ht

end S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
end P2MW
export P2MW.S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental (solution)
