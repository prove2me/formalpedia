-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FactorRigidity_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FactorRigidity_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:10:36.93904+00:00
-- url     : https://prove2.me/theorems/eab2eb82-6c9d-4f3c-8370-1ed84aee5502
-- title:
--   FLT.Assumptions.MazurProof.N13FactorRigidity source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13FactorRigidity

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13FactorRigidity
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13BranchLeading_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordNorm_p0

set_option autoImplicit false




/-!
# Small-factor rigidity on the `X₁(13)` sextic

Suppose two affine functions multiply to a polynomial of degree at most two
and neither has more than a simple pole at the positive infinity.  Then both
functions lie in the polynomial subring and have degree at most one.

The proof does not compare coefficients.  It uses the quadratic norm and both
infinity branches.  A nonzero `Y`-part forces pole degree at least three; the
two norm-degree inequalities then contradict the degree of the product.
-/

open Polynomial
open scoped LaurentSeries

namespace MazurProof.N13FactorRigidity

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

private theorem three_le_normDegree_add_positiveOrder
    (p q : K[X])
    (hz : N13BranchNorm.linearFunction K p q ≠ 0)
    (hq : q ≠ 0)
    (hnorm : N13BranchNorm.normNumerator K p q ≠ 0)
    (hplus : (-1 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K
        (N13BranchNorm.linearFunction K p q)).order) :
    (3 : ℤ) ≤
      ((N13BranchNorm.normNumerator K p q).natDegree : ℤ) +
        (N13Infinity.coordinateToLaurent K
          (N13BranchNorm.linearFunction K p q)).order := by
  let op : ℤ :=
    (N13Infinity.coordinateToLaurent K
      (N13BranchNorm.linearFunction K p q)).order
  let om : ℤ :=
    (N13InfinityMinus.coordinateToLaurentMinus K
      (N13BranchNorm.linearFunction K p q)).order
  let d : ℕ := (N13BranchNorm.normNumerator K p q).natDegree
  let e : ℕ := N13BranchLeading.poleDegree K p q
  have he : 3 ≤ e := by
    simp only [e, N13BranchLeading.poleDegree, hq, if_false]
    omega
  have hmin : min op om = -(e : ℤ) := by
    exact N13BranchLeading.branch_min_order K p q hz
  have hsum : op + om = -(d : ℤ) := by
    exact N13BranchNorm.branch_orders_add K p q hnorm
  have hop : (-1 : ℤ) ≤ op := hplus
  have hminus : om = -(e : ℤ) := by
    rcases min_choice op om with hleft | hright
    · have : op = -(e : ℤ) := hleft.symm.trans hmin
      omega
    · exact hright.symm.trans hmin
  change (3 : ℤ) ≤ (d : ℤ) + op
  omega

private theorem zero_le_normDegree_add_positiveOrder
    (p q : K[X])
    (hz : N13BranchNorm.linearFunction K p q ≠ 0)
    (hnorm : N13BranchNorm.normNumerator K p q ≠ 0)
    (hplus : (-1 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K
        (N13BranchNorm.linearFunction K p q)).order) :
    (0 : ℤ) ≤
      ((N13BranchNorm.normNumerator K p q).natDegree : ℤ) +
        (N13Infinity.coordinateToLaurent K
          (N13BranchNorm.linearFunction K p q)).order := by
  by_cases hq : q = 0
  · subst q
    have hp : p ≠ 0 := by
      intro hp
      apply hz
      simp [N13BranchNorm.linearFunction, hp]
    rw [N13BranchNorm.coordinateToLaurent_linearFunction]
    simp only [map_zero, zero_mul, add_zero,
      N13BranchNorm.normNumerator]
    norm_num only [zero_pow, zero_mul, sub_zero]
    rw [N13BranchNorm.evalPoly_order K p hp,
      Polynomial.natDegree_pow]
    omega
  · exact le_trans (by norm_num)
      (three_le_normDegree_add_positiveOrder K p q hz hq hnorm hplus)

theorem factor_pair_rigidity
    (z w : N13Mumford.CoordinateRing K) (P : K[X])
    (hP : P ≠ 0) (hdeg : P.natDegree ≤ 2)
    (hprod :
      z * w = SexticMumford.xClass (N13Mumford.model K) P)
    (hzplus : (-1 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K z).order)
    (hwplus : (-1 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K w).order) :
    SexticMumford.coeffY (N13Mumford.model K) z = 0 ∧
      SexticMumford.coeffY (N13Mumford.model K) w = 0 ∧
      (SexticMumford.coeff0
        (N13Mumford.model K) z).natDegree ≤ 1 ∧
      (SexticMumford.coeff0
        (N13Mumford.model K) w).natDegree ≤ 1 := by
  let M := N13Mumford.model K
  let pz := SexticMumford.coeff0 M z
  let qz := SexticMumford.coeffY M z
  let pw := SexticMumford.coeff0 M w
  let qw := SexticMumford.coeffY M w
  let Nz := N13BranchNorm.normNumerator K pz qz
  let Nw := N13BranchNorm.normNumerator K pw qw
  have hzlin : N13BranchNorm.linearFunction K pz qz = z := by
    exact SexticMumford.recompose M z
  have hwlin : N13BranchNorm.linearFunction K pw qw = w := by
    exact SexticMumford.recompose M w
  have hxP :
      SexticMumford.xClass M P ≠ 0 :=
    SexticMumford.xClass_ne_zero M hP
  have hzw : z * w ≠ 0 := by rw [hprod]; exact hxP
  have hz : z ≠ 0 := left_ne_zero_of_mul hzw
  have hw : w ≠ 0 := right_ne_zero_of_mul hzw
  have hNzEq :
      SexticMumford.norm M z = SexticMumford.xClass M Nz := by
    simpa [Nz, pz, qz, M, N13BranchNorm.normNumerator] using
      SexticMumford.norm_eq_xClass_coeff M z
  have hNwEq :
      SexticMumford.norm M w = SexticMumford.xClass M Nw := by
    simpa [Nw, pw, qw, M, N13BranchNorm.normNumerator] using
      SexticMumford.norm_eq_xClass_coeff M w
  have hnormProd := congrArg (SexticMumford.norm M) hprod
  have hpoly : Nz * Nw = P ^ 2 := by
    apply SexticMumford.xClass_injective M
    rw [SexticMumford.xClass_mul]
    calc
      SexticMumford.xClass M Nz * SexticMumford.xClass M Nw =
          SexticMumford.norm M z * SexticMumford.norm M w := by
            rw [hNzEq, hNwEq]
      _ = SexticMumford.norm M (z * w) :=
        (SexticMumford.norm_mul M z w).symm
      _ = SexticMumford.norm M (SexticMumford.xClass M P) := hnormProd
      _ = SexticMumford.xClass M (P ^ 2) :=
        SexticMumford.norm_xClass M P
  have hNN : Nz * Nw ≠ 0 := by
    rw [hpoly]
    exact pow_ne_zero 2 hP
  have hNz : Nz ≠ 0 := left_ne_zero_of_mul hNN
  have hNw : Nw ≠ 0 := right_ne_zero_of_mul hNN
  have hdegree :
      Nz.natDegree + Nw.natDegree = 2 * P.natDegree := by
    calc
      Nz.natDegree + Nw.natDegree = (Nz * Nw).natDegree :=
        (Polynomial.natDegree_mul hNz hNw).symm
      _ = (P ^ 2).natDegree := by rw [hpoly]
      _ = 2 * P.natDegree := Polynomial.natDegree_pow P 2
  have hplusSum :
      (N13Infinity.coordinateToLaurent K z).order +
          (N13Infinity.coordinateToLaurent K w).order =
        -(P.natDegree : ℤ) := by
    have hzL :
        N13Infinity.coordinateToLaurent K z ≠ 0 :=
      by simpa using (N13Infinity.coordinateToLaurent_injective K).ne hz
    have hwL :
        N13Infinity.coordinateToLaurent K w ≠ 0 :=
      by simpa using (N13Infinity.coordinateToLaurent_injective K).ne hw
    have hmapped := congrArg (N13Infinity.coordinateToLaurent K) hprod
    rw [map_mul, N13Infinity.coordinateToLaurent_xClass] at hmapped
    calc
      (N13Infinity.coordinateToLaurent K z).order +
            (N13Infinity.coordinateToLaurent K w).order =
          (N13Infinity.coordinateToLaurent K z *
            N13Infinity.coordinateToLaurent K w).order :=
        (HahnSeries.order_mul hzL hwL).symm
      _ = (N13BranchNorm.evalPoly K P).order := by
        rw [hmapped]
        rfl
      _ = -(P.natDegree : ℤ) :=
        N13BranchNorm.evalPoly_order K P hP
  have hqz : qz = 0 := by
    by_contra hqz
    have hstrong :=
      three_le_normDegree_add_positiveOrder K pz qz
        (hzlin.trans_ne hz) hqz hNz (by simpa only [hzlin] using hzplus)
    have hweak :=
      zero_le_normDegree_add_positiveOrder K pw qw
        (hwlin.trans_ne hw) hNw (by simpa only [hwlin] using hwplus)
    have hdegreeZ :
        (Nz.natDegree : ℤ) + (Nw.natDegree : ℤ) =
          2 * (P.natDegree : ℤ) := by
      exact_mod_cast hdegree
    rw [hzlin] at hstrong
    rw [hwlin] at hweak
    change (3 : ℤ) ≤ (Nz.natDegree : ℤ) +
      (N13Infinity.coordinateToLaurent K z).order at hstrong
    change (0 : ℤ) ≤ (Nw.natDegree : ℤ) +
      (N13Infinity.coordinateToLaurent K w).order at hweak
    omega
  have hqw : qw = 0 := by
    by_contra hqw
    have hweak :=
      zero_le_normDegree_add_positiveOrder K pz qz
        (hzlin.trans_ne hz) hNz (by simpa only [hzlin] using hzplus)
    have hstrong :=
      three_le_normDegree_add_positiveOrder K pw qw
        (hwlin.trans_ne hw) hqw hNw (by simpa only [hwlin] using hwplus)
    have hdegreeZ :
        (Nz.natDegree : ℤ) + (Nw.natDegree : ℤ) =
          2 * (P.natDegree : ℤ) := by
      exact_mod_cast hdegree
    rw [hzlin] at hweak
    rw [hwlin] at hstrong
    change (0 : ℤ) ≤ (Nz.natDegree : ℤ) +
      (N13Infinity.coordinateToLaurent K z).order at hweak
    change (3 : ℤ) ≤ (Nw.natDegree : ℤ) +
      (N13Infinity.coordinateToLaurent K w).order at hstrong
    omega
  have hpz : pz ≠ 0 := by
    intro hpz
    apply hz
    rw [← hzlin]
    simp [N13BranchNorm.linearFunction, hpz, hqz]
  have hpw : pw ≠ 0 := by
    intro hpw
    apply hw
    rw [← hwlin]
    simp [N13BranchNorm.linearFunction, hpw, hqw]
  have hdegz : pz.natDegree ≤ 1 := by
    have hzorder := N13BranchNorm.evalPoly_order K pz hpz
    rw [← hzlin, N13BranchNorm.coordinateToLaurent_linearFunction] at hzplus
    simp only [hqz, map_zero, zero_mul, add_zero] at hzplus
    omega
  have hdegw : pw.natDegree ≤ 1 := by
    have hworder := N13BranchNorm.evalPoly_order K pw hpw
    rw [← hwlin, N13BranchNorm.coordinateToLaurent_linearFunction] at hwplus
    simp only [hqw, map_zero, zero_mul, add_zero] at hwplus
    omega
  exact ⟨hqz, hqw, hdegz, hdegw⟩

private theorem minus_order_le_neg_three_of_coeffY_ne_zero
    (p q : K[X])
    (hz : N13BranchNorm.linearFunction K p q ≠ 0)
    (hq : q ≠ 0)
    (hplus : (-2 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K
        (N13BranchNorm.linearFunction K p q)).order) :
    (N13InfinityMinus.coordinateToLaurentMinus K
      (N13BranchNorm.linearFunction K p q)).order ≤ -3 := by
  have hmin :=
    N13BranchLeading.branch_min_order K p q hz
  have hpole :
      3 ≤ N13BranchLeading.poleDegree K p q := by
    simp only [N13BranchLeading.poleDegree, hq, if_false]
    omega
  omega

/-- If two affine functions with at most double poles at the positive
infinity multiply to a polynomial of degree at most four, neither function
has a `Y`-part.  If both had a `Y`-part, both negative-branch pole orders
would be at most `-3`, whereas their product has pole order at least `-4`.
Once one `Y`-part vanishes, the rank-two coefficient decomposition forces
the other to vanish as well. -/
theorem factor_pair_coeffY_eq_zero
    (z w : N13Mumford.CoordinateRing K) (P : K[X])
    (hP : P ≠ 0) (hdeg : P.natDegree ≤ 4)
    (hprod :
      z * w = SexticMumford.xClass (N13Mumford.model K) P)
    (hzplus : (-2 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K z).order)
    (hwplus : (-2 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K w).order) :
    SexticMumford.coeffY (N13Mumford.model K) z = 0 ∧
      SexticMumford.coeffY (N13Mumford.model K) w = 0 := by
  let M := N13Mumford.model K
  let pz := SexticMumford.coeff0 M z
  let qz := SexticMumford.coeffY M z
  let pw := SexticMumford.coeff0 M w
  let qw := SexticMumford.coeffY M w
  have hzlin : N13BranchNorm.linearFunction K pz qz = z :=
    SexticMumford.recompose M z
  have hwlin : N13BranchNorm.linearFunction K pw qw = w :=
    SexticMumford.recompose M w
  have hxP :
      SexticMumford.xClass M P ≠ 0 :=
    SexticMumford.xClass_ne_zero M hP
  have hzw : z * w ≠ 0 := by
    rw [hprod]
    exact hxP
  have hz : z ≠ 0 := left_ne_zero_of_mul hzw
  have hw : w ≠ 0 := right_ne_zero_of_mul hzw
  have hzMinus :
      N13InfinityMinus.coordinateToLaurentMinus K z ≠ 0 :=
    by simpa using
      (N13InfinityMinus.coordinateToLaurentMinus_injective K).ne hz
  have hwMinus :
      N13InfinityMinus.coordinateToLaurentMinus K w ≠ 0 :=
    by simpa using
      (N13InfinityMinus.coordinateToLaurentMinus_injective K).ne hw
  have hminusSum :
      (N13InfinityMinus.coordinateToLaurentMinus K z).order +
          (N13InfinityMinus.coordinateToLaurentMinus K w).order =
        -(P.natDegree : ℤ) := by
    have hmapped :=
      congrArg
        (N13InfinityMinus.coordinateToLaurentMinus K) hprod
    rw [map_mul,
      N13InfinityMinus.coordinateToLaurentMinus_xClass] at hmapped
    calc
      (N13InfinityMinus.coordinateToLaurentMinus K z).order +
            (N13InfinityMinus.coordinateToLaurentMinus K w).order =
          (N13InfinityMinus.coordinateToLaurentMinus K z *
            N13InfinityMinus.coordinateToLaurentMinus K w).order :=
        (HahnSeries.order_mul hzMinus hwMinus).symm
      _ = (N13BranchNorm.evalPoly K P).order := by
        rw [hmapped]
        rfl
      _ = -(P.natDegree : ℤ) :=
        N13BranchNorm.evalPoly_order K P hP
  have hone : qz = 0 ∨ qw = 0 := by
    by_contra hboth
    push Not at hboth
    have hzBound :=
      minus_order_le_neg_three_of_coeffY_ne_zero
        K pz qz (hzlin.trans_ne hz) hboth.1
          (by simpa only [hzlin] using hzplus)
    have hwBound :=
      minus_order_le_neg_three_of_coeffY_ne_zero
        K pw qw (hwlin.trans_ne hw) hboth.2
          (by simpa only [hwlin] using hwplus)
    rw [hzlin] at hzBound
    rw [hwlin] at hwBound
    have hdegZ : (P.natDegree : ℤ) ≤ 4 := by
      exact_mod_cast hdeg
    omega
  rcases hone with hqz | hqw
  · have hzpoly : z = SexticMumford.xClass M pz := by
      simpa [M, N13BranchNorm.linearFunction, hqz] using hzlin.symm
    have hpz : pz ≠ 0 := by
      intro hpz
      apply hz
      rw [hzpoly, hpz, SexticMumford.xClass_zero]
    have hcoeff : pz * qw = 0 := by
      have hcoeff' := congrArg (SexticMumford.coeffY M) hprod
      rw [hzpoly, SexticMumford.coeffY_xClass_mul] at hcoeff'
      simpa [M, qw] using hcoeff'
    exact ⟨hqz, (mul_eq_zero.mp hcoeff).resolve_left hpz⟩
  · have hwpoly : w = SexticMumford.xClass M pw := by
      simpa [M, N13BranchNorm.linearFunction, hqw] using hwlin.symm
    have hpw : pw ≠ 0 := by
      intro hpw
      apply hw
      rw [hwpoly, hpw, SexticMumford.xClass_zero]
    have hprod' :
        w * z = SexticMumford.xClass (N13Mumford.model K) P := by
      simpa [mul_comm] using hprod
    have hcoeff : pw * qz = 0 := by
      have hcoeff' := congrArg (SexticMumford.coeffY M) hprod'
      rw [hwpoly, SexticMumford.coeffY_xClass_mul] at hcoeff'
      simpa [M, qz] using hcoeff'
    exact ⟨(mul_eq_zero.mp hcoeff).resolve_left hpw, hqw⟩

end

end MazurProof.N13FactorRigidity


