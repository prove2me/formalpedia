-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CandidateCollapse_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13CandidateCollapse_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:20:47.39429+00:00
-- url     : https://prove2.me/theorems/a46d1758-5bf6-450d-aebc-bf8ae66de137
-- title:
--   FLT.Assumptions.MazurProof.N13CandidateCollapse source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13CandidateCollapse

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13CandidateCollapse
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LocalDlogTwo_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SexticSquareclass_p0

set_option autoImplicit false




/-!
# Structural collapse of the N13 fake-descent candidates

The first ramified logarithm reduces the sixteen binary exponent vectors to
`(0,0,s,s)`.  The remaining nonzero vector represents
`e₂ * a * q`, which differs from the rational scalar `13` by a square.

This file joins those two facts without a sixteen-row table.  It does not
assert that every global fake-Selmer class belongs to the candidate
envelope, nor that every local image lies in the first-jet kernel; those are
the two remaining arithmetic semantic bridges.
-/

namespace MazurProof.N13CandidateCollapse

noncomputable section

open N13SexticSquareclass

abbrev L : Type := SexticAlgebra

private def thirteenUnit : ℚˣ :=
  Units.mk0 13 (by norm_num)

private theorem scalarThirteen_isUnit :
    IsUnit (algebraMap ℚ L 13) := by
  exact (Units.map (algebraMap ℚ L).toMonoidHom thirteenUnit).isUnit

theorem survivor_isUnit : IsUnit survivor := by
  have hprod : IsUnit (survivor * squareFactor ^ 2) := by
    rw [survivor_mul_square]
    exact scalarThirteen_isUnit
  exact ((Commute.all survivor (squareFactor ^ 2)).isUnit_mul_iff.mp hprod).1

theorem squareFactor_isUnit : IsUnit squareFactor := by
  have hprod : IsUnit (survivor * squareFactor ^ 2) := by
    rw [survivor_mul_square]
    exact scalarThirteen_isUnit
  have hsq :
      IsUnit (squareFactor ^ 2) :=
    ((Commute.all survivor (squareFactor ^ 2)).isUnit_mul_iff.mp hprod).2
  exact (isUnit_pow_iff (by decide : 2 ≠ 0)).mp hsq

theorem e2_isUnit : IsUnit e2 := by
  have h := survivor_isUnit
  rw [survivor] at h
  exact ((Commute.all e2 (primeA * primeQ)).isUnit_mul_iff.mp
    (by simpa [mul_assoc] using h)).1

theorem primeA_isUnit : IsUnit primeA := by
  have h := survivor_isUnit
  rw [survivor] at h
  have hrest :
      IsUnit (primeA * primeQ) :=
    ((Commute.all e2 (primeA * primeQ)).isUnit_mul_iff.mp
      (by simpa [mul_assoc] using h)).2
  exact ((Commute.all primeA primeQ).isUnit_mul_iff.mp hrest).1

theorem primeQ_isUnit : IsUnit primeQ := by
  have h := survivor_isUnit
  rw [survivor] at h
  have hrest :
      IsUnit (primeA * primeQ) :=
    ((Commute.all e2 (primeA * primeQ)).isUnit_mul_iff.mp
      (by simpa [mul_assoc] using h)).2
  exact ((Commute.all primeA primeQ).isUnit_mul_iff.mp hrest).2

theorem zeta_isUnit : IsUnit zeta := by
  have h := squareFactor_isUnit
  rw [squareFactor] at h
  exact ((Commute.all zeta (e1 * primeA)).isUnit_mul_iff.mp
    (by simpa [mul_assoc] using h)).1

theorem e1_isUnit : IsUnit e1 := by
  have h := squareFactor_isUnit
  rw [squareFactor] at h
  have hrest :
      IsUnit (e1 * primeA) :=
    ((Commute.all zeta (e1 * primeA)).isUnit_mul_iff.mp
      (by simpa [mul_assoc] using h)).2
  exact ((Commute.all e1 primeA).isUnit_mul_iff.mp hrest).1

def zetaUnit : Lˣ := zeta_isUnit.unit
def e1Unit : Lˣ := e1_isUnit.unit
def e2Unit : Lˣ := e2_isUnit.unit
def primeAUnit : Lˣ := primeA_isUnit.unit
def primeQUnit : Lˣ := primeQ_isUnit.unit

@[simp] theorem zetaUnit_val : (zetaUnit : L) = zeta :=
  IsUnit.unit_spec _

@[simp] theorem e1Unit_val : (e1Unit : L) = e1 :=
  IsUnit.unit_spec _

@[simp] theorem e2Unit_val : (e2Unit : L) = e2 :=
  IsUnit.unit_spec _

@[simp] theorem primeAUnit_val : (primeAUnit : L) = primeA :=
  IsUnit.unit_spec _

@[simp] theorem primeQUnit_val : (primeQUnit : L) = primeQ :=
  IsUnit.unit_spec _

def survivorUnit : Lˣ :=
  e2Unit * primeAUnit * primeQUnit

def squareFactorUnit : Lˣ :=
  zetaUnit * e1Unit * primeAUnit

@[simp] theorem survivorUnit_val :
    (survivorUnit : L) = survivor := by
  simp [survivorUnit, survivor, mul_assoc]

@[simp] theorem squareFactorUnit_val :
    (squareFactorUnit : L) = squareFactor := by
  simp [squareFactorUnit, squareFactor, mul_assoc]

/-- The nonzero first-jet survivor is already trivial in the fake target. -/
theorem survivorUnit_fake_class_eq_one :
    ((survivorUnit : Lˣ) :
      FakeSquareClass.Target (algebraMap ℚ L)) = 1 := by
  apply FakeSquareClass.eq_one_of_mul_sq_eq_scalar
    (algebraMap ℚ L) survivorUnit squareFactorUnit thirteenUnit
  apply Units.ext
  change survivor * squareFactor ^ 2 = algebraMap ℚ L (13 : ℚ)
  exact survivor_mul_square

/-- The global candidate attached to four binary exponents. -/
def candidateUnit (i j k s : ZMod 2) : Lˣ :=
  zetaUnit ^ i.val * e1Unit ^ j.val * e2Unit ^ k.val *
    (primeAUnit * primeQUnit) ^ s.val

def candidateClass (i j k s : ZMod 2) :
    FakeSquareClass.Target (algebraMap ℚ L) :=
  candidateUnit i j k s

/-- One `F₈` equation plus the scalar identity kills every candidate. -/
theorem candidateClass_eq_one_of_dlog_eq_zero
    (i j k s : ZMod 2)
    (hlocal : N13LocalDlogTwo.candidateDlog i j k s = 0) :
    candidateClass i j k s = 1 := by
  obtain ⟨hi, hj, hks⟩ :=
    (N13LocalDlogTwo.candidateDlog_eq_zero_iff i j k s).mp hlocal
  subst i
  subst j
  subst k
  have hs : s = 0 ∨ s = 1 := by
    fin_cases s
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hs with rfl | rfl
  · simp [candidateClass, candidateUnit]
    rfl
  · simp only [candidateClass, candidateUnit, ZMod.val_zero,
      ZMod.val_one 2, pow_zero, pow_one, one_mul]
    simpa [survivorUnit, mul_assoc] using survivorUnit_fake_class_eq_one

end

end MazurProof.N13CandidateCollapse


