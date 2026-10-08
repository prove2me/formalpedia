-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordStructuralReduction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordStructuralReduction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:06:03.82932+00:00
-- url     : https://prove2.me/theorems/ed2694d2-2ba0-4eef-9cea-4b941e3c1c41
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordStructuralReduction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordStructuralReduction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordStructuralReduction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordPrimitivePart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordCantorReduction_p0

set_option autoImplicit false




/-!
# Structural reduction of oriented sextic ideals

This file joins the two algebraic seams:

* polynomial-content division produces a primitive integral ideal;
* primitive integral ideals have semi-Mumford graph form.

It then packages the well-founded affine-degree step.  Infinity balancing
is deliberately a separate phase.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)

theorem IntegralOrientedRep.exists_semiMumford
    (R : IntegralOrientedRep M)
    (hprimitive : IdealIsPrimitive M R.ideal) :
    ∃ D : SemiMumford M,
      semiMumfordClass M O D = R.picClass M O ∧
      mumfordIdeal M D.u D.v = R.ideal := by
  obtain ⟨D, hIdeal, -, hn⟩ :=
    exists_semiMumford_of_primitive M R.ideal
      (R.ideal_ne_bot M) hprimitive (R.atInfinity + 1)
  have hunit : mumfordIdealUnit M D = R.unit := by
    apply Units.ext
    rw [coe_mumfordIdealUnit, hIdeal, ← R.coe_unit]
  have hraw : semiMumfordRaw M D = R.raw M := by
    apply Prod.ext
    · exact hunit
    · change
        Multiplicative.ofAdd (D.nInf - 1) =
          Multiplicative.ofAdd R.atInfinity
      congr 1
      rw [hn]
      omega
  refine ⟨D, ?_, hIdeal⟩
  change
    Additive.ofMul
        (QuotientGroup.mk' (principalOriented M O).range
          (semiMumfordRaw M D)) =
      Additive.ofMul
        (QuotientGroup.mk' (principalOriented M O).range
          (R.raw M))
  rw [hraw]

/-- Every oriented class has a semi-Mumford representative before any
degree reduction. -/
theorem exists_semiMumfordRepresentative
    (c : ConcretePic M O) :
    ∃ D : SemiMumford M, semiMumfordClass M O D = c := by
  obtain ⟨R, hprimitive, hR⟩ :=
    exists_primitiveIntegralRepresentative M O c
  obtain ⟨D, hD, -⟩ :=
    R.exists_semiMumford M O hprimitive
  exact ⟨D, hD.trans hR⟩

/-! ## A canonical affine-degree step -/

/-- The quotient already supplied by the divisibility field of a
semi-Mumford representative. -/
def semiFactor (D : SemiMumford M) : K[X] :=
  Classical.choose D.curve_dvd

theorem semiFactor_spec (D : SemiMumford M) :
    M.f - D.v ^ 2 = D.u * semiFactor M D :=
  Classical.choose_spec D.curve_dvd

/-- At degree three use the monic lift `v+u`; otherwise use the reduced
graph polynomial itself. -/
def degreeLift (D : SemiMumford M) : K[X] :=
  if D.u.natDegree = 3 then D.v + D.u else D.v

theorem degreeLift_congr (D : SemiMumford M) :
    D.u ∣ degreeLift M D - D.v := by
  unfold degreeLift
  split_ifs
  · refine ⟨1, ?_⟩
    ring
  · simp

theorem degreeLift_curve_dvd (D : SemiMumford M) :
    D.u ∣ M.f - (degreeLift M D) ^ 2 := by
  unfold degreeLift
  split_ifs
  · obtain ⟨w, hw⟩ := D.curve_dvd
    refine ⟨w - 2 * D.v - D.u, ?_⟩
    calc
      M.f - (D.v + D.u) ^ 2 =
          (M.f - D.v ^ 2) -
            2 * D.u * D.v - D.u ^ 2 := by ring
      _ = D.u * w - 2 * D.u * D.v - D.u ^ 2 := by
            rw [hw]
      _ = D.u * (w - 2 * D.v - D.u) := by ring
  · exact D.curve_dvd

def degreeStepFactor (D : SemiMumford M) : K[X] :=
  Classical.choose (degreeLift_curve_dvd M D)

theorem degreeStepFactor_spec (D : SemiMumford M) :
    M.f - (degreeLift M D) ^ 2 =
      D.u * degreeStepFactor M D :=
  Classical.choose_spec (degreeLift_curve_dvd M D)

theorem degreeStepFactor_ne_zero (D : SemiMumford M) :
    degreeStepFactor M D ≠ 0 :=
  cantorFactor_ne_zero M D.u (degreeLift M D)
    (degreeStepFactor M D) (degreeStepFactor_spec M D)

def degreeStep
    (D : SemiMumford M) :
    SemiMumford M :=
  cantorNextSemi M O D (degreeLift M D) (degreeStepFactor M D)
    (degreeStepFactor_spec M D) (degreeStepFactor_ne_zero M D)

theorem degreeStep_class
    (D : SemiMumford M) :
    semiMumfordClass M O (degreeStep M O D) =
      semiMumfordClass M O D := by
  unfold degreeStep
  apply cantorNextSemi_class M O D
    (degreeLift M D) (degreeStepFactor M D)
    (degreeStepFactor_spec M D) (degreeStepFactor_ne_zero M D)
    (degreeLift_congr M D)
  unfold degreeLift
  split_ifs with hdeg
  · simpa using
      cantorBezout_add_mul M D 1 (degreeStepFactor M D)
        (by
          simpa [degreeLift, hdeg] using
            degreeStepFactor_spec M D)
  · simpa using
      cantorBezout_of_semi_factor M D (degreeStepFactor M D)
        (by
          simpa [degreeLift, hdeg] using
            degreeStepFactor_spec M D)

theorem degreeStep_lt
    (D : SemiMumford M) (hlarge : 2 < D.u.natDegree) :
    (degreeStep M O D).u.natDegree < D.u.natDegree := by
  unfold degreeStep
  rw [cantorNextSemi_natDegree]
  by_cases hthree : D.u.natDegree = 3
  · have hspec :
        M.f - (D.v + D.u) ^ 2 =
          D.u * degreeStepFactor M D := by
      simpa [degreeLift, hthree] using degreeStepFactor_spec M D
    have hle :=
      (cubicCantorFactor M D (degreeStepFactor M D) hthree
        hspec).2
    omega
  · have hspec :
        M.f - D.v ^ 2 =
          D.u * degreeStepFactor M D := by
      simpa [degreeLift, hthree] using degreeStepFactor_spec M D
    apply cantorFactor_natDegree_lt M D
      (degreeStepFactor M D) hspec
    omega

/-- A semi-Mumford representative together with the terminal affine degree
bound.  This does not yet impose the independent infinity-balance bounds. -/
structure LowDegreeSemi where
  toSemi : SemiMumford M
  degree_le_two : toSemi.u.natDegree ≤ 2

def reduceDegree (D : SemiMumford M) : LowDegreeSemi M :=
  if hsmall : D.u.natDegree ≤ 2 then
    ⟨D, hsmall⟩
  else
    reduceDegree (degreeStep M O D)
termination_by D.u.natDegree
decreasing_by
  exact degreeStep_lt M O D (by omega)

@[simp] theorem reduceDegree_class
    (D : SemiMumford M) :
    semiMumfordClass M O (reduceDegree M O D).toSemi =
      semiMumfordClass M O D := by
  rw [reduceDegree]
  split_ifs with hsmall
  · rfl
  · rw [reduceDegree_class, degreeStep_class]
termination_by D.u.natDegree
decreasing_by
  exact degreeStep_lt M O D (by omega)

/-- Phase I of the structural reduction: every oriented class has a
representative of affine degree at most two.  No claim about the independent
`nInf` balance is made here. -/
theorem exists_lowDegreeSemiRepresentative
    (c : ConcretePic M O) :
    ∃ D : LowDegreeSemi M,
      semiMumfordClass M O D.toSemi = c := by
  obtain ⟨D, hD⟩ := exists_semiMumfordRepresentative M O c
  exact ⟨reduceDegree M O D, (reduceDegree_class M O D).trans hD⟩

end

end MazurProof.SexticMumford


