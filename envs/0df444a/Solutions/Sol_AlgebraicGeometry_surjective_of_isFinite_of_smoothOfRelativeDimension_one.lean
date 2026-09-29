-- Prove2me | solution 1 for AlgebraicGeometry.surjective_of_isFinite_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5b4c6772-757a-5d80-afde-1134cebc351a

import Mathlib
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_surjective_of_isFinite_of_smoothOfRelativeDimension_one

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {k : Type u} [Field k] {C U : Scheme.{u}}
    (πC : C ⟶ Spec (CommRingCat.of k)) (πU : U ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsIntegral U]
    [SmoothOfRelativeDimension 1 πC] [SmoothOfRelativeDimension 1 πU]
    (c : C ⟶ U) (hc : c ≫ πU = πC) [IsFinite c] :
    Function.Surjective c.base := by
  classical
  have hηCcl : closure ({genericPoint C} : Set C) = Set.univ := genericPoint_spec C
  have hηUcl : closure ({genericPoint U} : Set U) = Set.univ := genericPoint_spec U

  have hclosed : IsClosed (Set.range c.base) := c.isClosedMap.isClosed_range
  have hrange : Set.range c.base = closure {c.base (genericPoint C)} := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      have hy : c.base y ∈ c.base '' closure {genericPoint C} := ⟨y, by rw [hηCcl]; trivial, rfl⟩
      have := image_closure_subset_closure_image c.continuous hy
      rwa [Set.image_singleton] at this
    · exact closure_minimal (Set.singleton_subset_iff.mpr ⟨_, rfl⟩) hclosed

  suffices hgen : c.base (genericPoint C) = genericPoint U by
    intro z
    have hz : z ∈ closure ({c.base (genericPoint C)} : Set U) := by rw [hgen, hηUcl]; trivial
    rwa [← hrange] at hz
  by_contra hne

  have hηC : ¬ IsClosed ({genericPoint C} : Set C) := by
    intro hcl
    have hdvr := AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed
      πC (genericPoint C) hcl
    haveI := hdvr
    exact IsDiscreteValuationRing.not_isField (C.presheaf.stalk (genericPoint C))
      (Field.toIsField (R := C.functionField))

  haveI : Smooth πU := SmoothOfRelativeDimension.smooth (n := 1) (f := πU)
  haveI : Smooth πC := SmoothOfRelativeDimension.smooth (n := 1) (f := πC)
  haveI : JacobsonSpace U := LocallyOfFiniteType.jacobsonSpace πU
  obtain ⟨v, hvZ, hvcl⟩ := nonempty_inter_closedPoints (Z := closure {c.base (genericPoint C)})
    ⟨c.base (genericPoint C), subset_closure (Set.mem_singleton _)⟩ isClosed_closure.isLocallyClosed
  rw [mem_closedPoints_iff] at hvcl
  have huv : c.base (genericPoint C) ⤳ v := specializes_iff_mem_closure.mpr hvZ
  have hu_eq_v : c.base (genericPoint C) = v := by
    have hdvr := AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed
      πU v hvcl
    obtain ⟨P, hP⟩ : c.base (genericPoint C) ∈ Set.range (U.fromSpecStalk v).base := by
      rw [Scheme.range_fromSpecStalk]; exact huv
    rcases eq_or_ne P.asIdeal ⊥ with h0 | h0
    ·
      exfalso
      apply hne
      rw [← hP]
      have hPgen : P = genericPoint (Spec (U.presheaf.stalk v)) := by
        rw [genericPoint_eq_bot_of_affine]; apply PrimeSpectrum.ext; exact h0
      apply ((genericPoint_spec U).eq _).symm
      change closure {(U.fromSpecStalk v).base P} = Set.univ
      apply Set.eq_univ_of_univ_subset
      rw [← hηUcl]
      apply closure_minimal _ isClosed_closure
      rw [Set.singleton_subset_iff]

      obtain ⟨Q, hQ⟩ : genericPoint U ∈ Set.range (U.fromSpecStalk v).base := by
        rw [Scheme.range_fromSpecStalk]
        exact (genericPoint_spec U).specializes (Set.mem_univ v)
      rw [← hQ]
      have hQ' : Q ∈ closure {P} := by
        rw [hPgen, (show closure {genericPoint (Spec (U.presheaf.stalk v))} = Set.univ from
          genericPoint_spec (Spec (U.presheaf.stalk v)))]
        trivial
      have := image_closure_subset_closure_image (U.fromSpecStalk v).continuous ⟨Q, hQ', rfl⟩
      rwa [Set.image_singleton] at this
    ·
      haveI := hdvr
      have hPmax : P.asIdeal = IsLocalRing.maximalIdeal _ :=
        IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal P.isPrime h0)
      have hPc : P = IsLocalRing.closedPoint (U.presheaf.stalk v) := PrimeSpectrum.ext hPmax
      rw [hPc, Scheme.fromSpecStalk_closedPoint] at hP
      exact hP.symm

  have hu_cl : IsClosed ({c.base (genericPoint C)} : Set U) := hu_eq_v ▸ hvcl
  have hfib : c.base ⁻¹' {c.base (genericPoint C)} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    have hy : c.base y ∈ Set.range c.base := ⟨y, rfl⟩
    rw [hrange, hu_cl.closure_eq] at hy
    exact hy
  have hfin : Finite C := by
    have := c.finite_preimage_singleton (c.base (genericPoint C))
    rw [hfib] at this
    exact Set.finite_univ_iff.mp this
  haveI : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace πC
  haveI : DiscreteTopology C := inferInstance
  exact hηC (isClosed_discrete _)

end S_AlgebraicGeometry_surjective_of_isFinite_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_surjective_of_isFinite_of_smoothOfRelativeDimension_one (solution)
