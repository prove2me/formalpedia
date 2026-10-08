-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityChart_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityChart_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:32:39.342758+00:00
-- url     : https://prove2.me/theorems/2986b9c0-837b-464e-9195-69baf756e320
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialInfinityChart source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialInfinityChart

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialInfinityChart
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodCoordinateRingTwo_p0

set_option autoImplicit false




/-!
# The special N13 infinity chart is integral

Over `F₂`, the infinity chart is

`v² + (1+t²+t³)v = t+t²`.

Irreducibility follows from a degree gap.  A factorization of the monic
quadratic would give polynomials `a,b` with `a*b = t+t²` and
`a+b = 1+t²+t³`.  The product forces both factors to have degree at most
two, whereas their sum has degree three.

No polynomial enumeration or coefficient table is used.
-/

open Polynomial

namespace MazurProof.N13SpecialInfinityChart

noncomputable section

abbrev K : Type :=
  N13GoodModelTwo.F2

/-- Coefficient of `v` on the special infinity chart. -/
def hPoly : K[X] :=
  1 + X ^ 2 + X ^ 3

/-- Right-hand side on the special infinity chart. -/
def rhsPoly : K[X] :=
  X + X ^ 2

/-- The outer variable is `v`. -/
def curvePoly : K[X][X] :=
  X ^ 2 + C hPoly * X - C rhsPoly

theorem hPoly_monic : hPoly.Monic := by
  unfold hPoly
  monicity
  all_goals norm_num

theorem hPoly_natDegree :
    hPoly.natDegree = 3 := by
  unfold hPoly
  compute_degree
  all_goals norm_num

theorem rhsPoly_monic : rhsPoly.Monic := by
  unfold rhsPoly
  monicity
  all_goals norm_num

theorem rhsPoly_natDegree :
    rhsPoly.natDegree = 2 := by
  unfold rhsPoly
  compute_degree
  all_goals norm_num

theorem curvePoly_monic : curvePoly.Monic := by
  unfold curvePoly
  monicity
  all_goals norm_num

theorem curvePoly_natDegree :
    curvePoly.natDegree = 2 := by
  unfold curvePoly
  compute_degree
  all_goals norm_num

theorem curvePoly_irreducible :
    Irreducible curvePoly := by
  by_contra hred
  obtain ⟨a, b, hmul, hadd⟩ :=
    (curvePoly_monic.not_irreducible_iff_exists_add_mul_eq_coeff
      curvePoly_natDegree).mp hred
  have hmul' : rhsPoly = a * b := by
    calc
      rhsPoly = -rhsPoly := (CharTwo.neg_eq rhsPoly).symm
      _ = a * b := by simpa [curvePoly] using hmul
  have hadd' : hPoly = a + b := by
    simpa [curvePoly] using hadd
  have ha0 : a ≠ 0 := by
    intro ha
    apply rhsPoly_monic.ne_zero
    simpa [ha] using hmul'
  have hb0 : b ≠ 0 := by
    intro hb
    apply rhsPoly_monic.ne_zero
    simpa [hb] using hmul'
  have hdegMul :
      (a * b).natDegree = a.natDegree + b.natDegree :=
    Polynomial.natDegree_mul'
      (mul_ne_zero
        (leadingCoeff_ne_zero.mpr ha0)
        (leadingCoeff_ne_zero.mpr hb0))
  rw [← hmul', rhsPoly_natDegree] at hdegMul
  have haDegree : a.natDegree ≤ 2 := by omega
  have hbDegree : b.natDegree ≤ 2 := by omega
  have hsumDegree : (a + b).natDegree ≤ 2 :=
    (natDegree_add_le a b).trans
      (max_le haDegree hbDegree)
  rw [← hadd', hPoly_natDegree] at hsumDegree
  omega

instance curvePolyIrreducibleFact :
    Fact (Irreducible curvePoly) :=
  ⟨curvePoly_irreducible⟩

/-- Coordinate ring of the special infinity chart. -/
abbrev CoordinateRing : Type :=
  AdjoinRoot curvePoly

instance instIsDomainCoordinateRing : IsDomain CoordinateRing :=
  AdjoinRoot.isDomain_of_prime curvePoly_irreducible.prime

noncomputable instance instAlgebraKCoordinateRing : Algebra K CoordinateRing :=
  inferInstance

noncomputable instance instAlgebraPolynomialKCoordinateRing : Algebra K[X] CoordinateRing :=
  inferInstance

/-- The special coordinates `t` and `v`. -/
def tClass : CoordinateRing :=
  algebraMap K[X] CoordinateRing X

def vClass : CoordinateRing :=
  AdjoinRoot.root curvePoly

end

end MazurProof.N13SpecialInfinityChart


