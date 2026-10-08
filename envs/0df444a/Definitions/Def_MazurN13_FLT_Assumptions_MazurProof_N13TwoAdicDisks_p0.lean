-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicDisks_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicDisks_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:56:18.896743+00:00
-- url     : https://prove2.me/theorems/145a0a18-abd3-4668-8f06-65d0c880a731
-- title:
--   FLT.Assumptions.MazurProof.N13TwoAdicDisks source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoAdicDisks

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoAdicDisks
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodModelTwo_p0
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Henselian

set_option autoImplicit false




/-!
# The two integral residue disks used by the N13 Abel chart

For the good equation

`y² + (x³ + x + 1)y = x⁵ + x⁴`

over the two-adic integers, the fibres above the residue disks of `0` and
`-1` have a unique point whose `y`-coordinate lies in the maximal ideal.
Existence is one-variable Hensel lifting in the `y` coordinate.  Uniqueness
is the elementary factorization of the difference of two roots.

This is the local-curve part of the nonspecial Abel chart; it uses neither a
Picard scheme nor finite congruence tables.
-/

open Polynomial

namespace MazurProof.N13TwoAdicDisks

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

/-- The maximal ideal `(2)` of the two-adic integers. -/
abbrev maximal : Ideal R₂ :=
  IsLocalRing.maximalIdeal R₂

/-- A useful local-ring form of the fact that being congruent to a unit
modulo the maximal ideal implies being a unit. -/
theorem isUnit_of_sub_mem_maximal
    {a u : R₂} (hu : IsUnit u)
    (hau : a - u ∈ maximal) :
    IsUnit a := by
  by_contra ha
  have ha_mem : a ∈ maximal := by
    simpa only [maximal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using ha
  have hu_mem : u ∈ maximal := by
    have hsub := maximal.sub_mem ha_mem hau
    convert hsub using 1
    ring
  have hnot : ¬IsUnit u := by
    simpa only [maximal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using hu_mem
  exact hnot hu

/-- The good equation, viewed as a monic polynomial in `Y`. -/
abbrev yFiber (x : R₂) : R₂[X] :=
  N13GoodModelTwo.affineFiber x

theorem yFiber_monic (x : R₂) :
    (yFiber x).Monic := by
  unfold yFiber N13GoodModelTwo.affineFiber
  monicity <;> norm_num

@[simp] theorem yFiber_eval (x y : R₂) :
    (yFiber x).eval y =
      N13GoodModelTwo.affineResidual x y :=
  N13GoodModelTwo.affineFiber_eval x y

@[simp] theorem yFiber_derivative_eval_zero (x : R₂) :
    (yFiber x).derivative.eval 0 =
      N13GoodModelTwo.h x := by
  rw [N13GoodModelTwo.affineFiber_derivative_eval]
  simp [N13GoodModelTwo.affineDerivativeY]

/-- Hensel lifting in the `Y` coordinate under the exact two hypotheses
needed at a residue disk. -/
theorem exists_y_mem_maximal
    (x : R₂)
    (hh : IsUnit (N13GoodModelTwo.h x))
    (hrhs : N13GoodModelTwo.rhs x ∈ maximal) :
    ∃ y : R₂,
      N13GoodModelTwo.AffineEquation x y ∧
        y ∈ maximal := by
  have heval :
      (yFiber x).eval 0 ∈ maximal := by
    have hneg := maximal.neg_mem hrhs
    simpa [yFiber_eval, N13GoodModelTwo.affineResidual] using hneg
  have hderiv :
      IsUnit
        (Ideal.Quotient.mk maximal
          ((yFiber x).derivative.eval 0)) := by
    rw [yFiber_derivative_eval_zero]
    exact hh.map (Ideal.Quotient.mk maximal)
  obtain ⟨y, hy, hymem⟩ :=
    HenselianRing.is_henselian
      (R := R₂) (I := maximal)
      (yFiber x) (yFiber_monic x) 0 heval hderiv
  refine ⟨y, ?_, by simpa using hymem⟩
  rw [N13GoodModelTwo.affineEquation_iff_residual,
    ← yFiber_eval]
  exact hy

/-- Two roots in the same selected `Y` residue disk coincide. -/
theorem y_eq_of_mem_maximal
    (x y z : R₂)
    (hh : IsUnit (N13GoodModelTwo.h x))
    (hy : N13GoodModelTwo.AffineEquation x y)
    (hz : N13GoodModelTwo.AffineEquation x z)
    (hymem : y ∈ maximal)
    (hzmem : z ∈ maximal) :
    y = z := by
  have hyzero :
      y ^ 2 + N13GoodModelTwo.h x * y -
          N13GoodModelTwo.rhs x = 0 :=
    sub_eq_zero.mpr hy
  have hzzero :
      z ^ 2 + N13GoodModelTwo.h x * z -
          N13GoodModelTwo.rhs x = 0 :=
    sub_eq_zero.mpr hz
  have hsum_mem : y + z ∈ maximal :=
    maximal.add_mem hymem hzmem
  have hunit :
      IsUnit (y + z + N13GoodModelTwo.h x) := by
    apply isUnit_of_sub_mem_maximal hh
    convert hsum_mem using 1
    ring
  have hprod :
      (y - z) *
        (y + z + N13GoodModelTwo.h x) = 0 := by
    calc
      (y - z) *
          (y + z + N13GoodModelTwo.h x) =
        (y ^ 2 + N13GoodModelTwo.h x * y -
            N13GoodModelTwo.rhs x) -
          (z ^ 2 + N13GoodModelTwo.h x * z -
            N13GoodModelTwo.rhs x) := by ring
      _ = 0 := by rw [hyzero, hzzero, sub_self]
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_right hunit.ne_zero)

/-- The selected `Y` lift is unique whenever the fibre has unit derivative
and its constant term lies in the maximal ideal. -/
theorem existsUnique_y_mem_maximal
    (x : R₂)
    (hh : IsUnit (N13GoodModelTwo.h x))
    (hrhs : N13GoodModelTwo.rhs x ∈ maximal) :
    ∃! y : R₂,
      N13GoodModelTwo.AffineEquation x y ∧
        y ∈ maximal := by
  obtain ⟨y, hy, hymem⟩ :=
    exists_y_mem_maximal x hh hrhs
  refine ⟨y, ⟨hy, hymem⟩, ?_⟩
  intro z hz
  exact y_eq_of_mem_maximal x z y hh hz.1 hy hz.2 hymem

/-! ## The disk above `(0,0)` -/

theorem h_isUnit_of_mem_zeroDisk
    {x : R₂} (hx : x ∈ maximal) :
    IsUnit (N13GoodModelTwo.h x) := by
  apply isUnit_of_sub_mem_maximal isUnit_one
  have hm :=
    maximal.mul_mem_left (x ^ 2 + 1) hx
  convert hm using 1
  simp only [N13GoodModelTwo.h]
  ring

theorem rhs_mem_of_mem_zeroDisk
    {x : R₂} (hx : x ∈ maximal) :
    N13GoodModelTwo.rhs x ∈ maximal := by
  have hm :=
    maximal.mul_mem_left (x ^ 3 * (x + 1)) hx
  convert hm using 1
  simp only [N13GoodModelTwo.rhs]
  ring

theorem existsUnique_zeroDisk_y
    (x : R₂) (hx : x ∈ maximal) :
    ∃! y : R₂,
      N13GoodModelTwo.AffineEquation x y ∧
        y ∈ maximal :=
  existsUnique_y_mem_maximal x
    (h_isUnit_of_mem_zeroDisk hx)
    (rhs_mem_of_mem_zeroDisk hx)

/-- The unique `Y` coordinate above an `X` in the residue disk of zero. -/
def zeroDiskY (x : R₂) (hx : x ∈ maximal) : R₂ :=
  Classical.choose (existsUnique_zeroDisk_y x hx).exists

theorem zeroDiskY_spec
    (x : R₂) (hx : x ∈ maximal) :
    N13GoodModelTwo.AffineEquation x (zeroDiskY x hx) ∧
      zeroDiskY x hx ∈ maximal :=
  Classical.choose_spec (existsUnique_zeroDisk_y x hx).exists

theorem y_eq_zeroDiskY
    (x : R₂) (hx : x ∈ maximal)
    {y : R₂}
    (hy : N13GoodModelTwo.AffineEquation x y)
    (hymem : y ∈ maximal) :
    y = zeroDiskY x hx :=
  y_eq_of_mem_maximal x y (zeroDiskY x hx)
    (h_isUnit_of_mem_zeroDisk hx)
    hy (zeroDiskY_spec x hx).1 hymem
    (zeroDiskY_spec x hx).2

@[simp] theorem zeroDiskY_zero :
    zeroDiskY 0 maximal.zero_mem = 0 := by
  symm
  apply y_eq_zeroDiskY 0 maximal.zero_mem
  · simp [N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs]
  · exact maximal.zero_mem

/-! ## The disk above `(-1,0)` -/

theorem h_isUnit_of_mem_negOneDisk
    {x : R₂} (hx : x + 1 ∈ maximal) :
    IsUnit (N13GoodModelTwo.h x) := by
  apply isUnit_of_sub_mem_maximal isUnit_neg_one
  have hm :=
    maximal.mul_mem_left (x ^ 2 - x + 2) hx
  convert hm using 1
  simp only [N13GoodModelTwo.h]
  ring

theorem rhs_mem_of_mem_negOneDisk
    {x : R₂} (hx : x + 1 ∈ maximal) :
    N13GoodModelTwo.rhs x ∈ maximal := by
  have hm :=
    maximal.mul_mem_left (x ^ 4) hx
  convert hm using 1
  simp only [N13GoodModelTwo.rhs]
  ring

theorem existsUnique_negOneDisk_y
    (x : R₂) (hx : x + 1 ∈ maximal) :
    ∃! y : R₂,
      N13GoodModelTwo.AffineEquation x y ∧
        y ∈ maximal :=
  existsUnique_y_mem_maximal x
    (h_isUnit_of_mem_negOneDisk hx)
    (rhs_mem_of_mem_negOneDisk hx)

/-- The unique `Y` coordinate above an `X` in the residue disk of `-1`. -/
def negOneDiskY (x : R₂) (hx : x + 1 ∈ maximal) : R₂ :=
  Classical.choose (existsUnique_negOneDisk_y x hx).exists

theorem negOneDiskY_spec
    (x : R₂) (hx : x + 1 ∈ maximal) :
    N13GoodModelTwo.AffineEquation x (negOneDiskY x hx) ∧
      negOneDiskY x hx ∈ maximal :=
  Classical.choose_spec (existsUnique_negOneDisk_y x hx).exists

theorem y_eq_negOneDiskY
    (x : R₂) (hx : x + 1 ∈ maximal)
    {y : R₂}
    (hy : N13GoodModelTwo.AffineEquation x y)
    (hymem : y ∈ maximal) :
    y = negOneDiskY x hx :=
  y_eq_of_mem_maximal x y (negOneDiskY x hx)
    (h_isUnit_of_mem_negOneDisk hx)
    hy (negOneDiskY_spec x hx).1 hymem
    (negOneDiskY_spec x hx).2

@[simp] theorem negOneDiskY_negOne :
    negOneDiskY (-1) (by simp) = 0 := by
  symm
  apply y_eq_negOneDiskY (-1) (by simp)
  · simp [N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs]
    ring
  · exact maximal.zero_mem

end

end MazurProof.N13TwoAdicDisks


