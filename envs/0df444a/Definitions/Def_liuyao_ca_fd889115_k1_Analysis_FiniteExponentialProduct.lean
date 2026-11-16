-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteExponentialProduct
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteExponentialProduct
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:22:12.605946+00:00
-- url     : https://prove2.me/theorems/eb3142b4-0d19-4629-8114-bef842e4091e
-- title:
--   Computable analysis · FiniteExponentialProduct · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FiniteExponentialProduct.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ExpProofs
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteExponentialTaylor
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Series

set_option autoImplicit true

/-!
# Finite products of factorial exponential prefixes

This module develops the rational Cauchy-product algebra needed to identify
the negative exponential series with the reciprocal of the positive series.
It begins with the factorial/binomial coefficient identity and then exposes
the cancellation of every nonconstant diagonal at opposite inputs.
-/

namespace ComputableAnalysis
namespace FiniteExponentialProduct

private theorem rat_eq_of_mul_eq_mul_ne {a b c : Rat}
    (hc : c ≠ 0) (h : c * a = c * b) : a = b := by
  calc
    a = c⁻¹ * (c * a) := by
      have hcancel : c⁻¹ * c = 1 := Rat.inv_mul_cancel c hc
      grind [Rat.mul_assoc]
    _ = c⁻¹ * (c * b) := by rw [h]
    _ = b := by
      have hcancel : c⁻¹ * c = 1 := Rat.inv_mul_cancel c hc
      grind [Rat.mul_assoc]

private theorem expCoeff_shift (n : Nat) :
    (((n + 1 : Nat) : Rat)) * FormalPowerSeries.expCoeff (n + 1) =
      FormalPowerSeries.expCoeff n := by
  have h := congrFun FormalPowerSeries.expCoeff_derivative n
  exact h

/-- The factorial coefficients reproduce the project binomial coefficient.
This proof uses only Pascal recursion and the coefficient-shift identity
`(n+1)/(n+1)! = 1/n!`. -/
theorem expCoeff_mul_expCoeff_eq_expCoeff_mul_combination :
    forall n k : Nat, k <= n ->
      FormalPowerSeries.expCoeff k *
          FormalPowerSeries.expCoeff (n - k) =
        FormalPowerSeries.expCoeff n *
          (FiniteCounting.combination n k : Rat)
  | 0, k, hk => by
      have hk0 : k = 0 := by omega
      subst k
      decide +kernel
  | n + 1, 0, _hk => by
      simp [FormalPowerSeries.expCoeff, factorialRat, factorial,
        FiniteCounting.combination_zero_right]
      grind [Rat.div_def]
  | n + 1, k + 1, hk => by
      have hkn : k <= n := by omega
      by_cases htop : k = n
      · subst k
        simp [FormalPowerSeries.expCoeff, factorialRat, factorial,
          FiniteCounting.combination_rat_self]
        grind [Rat.div_def]
      · have hklt : k < n := by omega
        have hkSucc : k + 1 <= n := by omega
        have ihLeft :=
          expCoeff_mul_expCoeff_eq_expCoeff_mul_combination
            n (k + 1) hkSucc
        have ihRight :=
          expCoeff_mul_expCoeff_eq_expCoeff_mul_combination
            n k hkn
        have hshiftK := expCoeff_shift k
        have hshiftRest := expCoeff_shift (n - (k + 1))
        have hshiftN := expCoeff_shift n
        have hrestSucc : n - (k + 1) + 1 = n - k := by omega
        have hsub : n + 1 - (k + 1) = n - k := by omega
        have hcastSplit :
            ((((n - k : Nat) : Rat)) + (((k + 1 : Nat) : Rat))) =
              ((n + 1 : Nat) : Rat) := by
          exact_mod_cast (by omega : (n - k) + (k + 1) = n + 1)
        rw [FiniteCounting.combination_rat_pascal]
        apply rat_eq_of_mul_eq_mul_ne
          (c := ((n + 1 : Nat) : Rat))
          (by exact_mod_cast Nat.succ_ne_zero n)
        rw [hrestSucc] at hshiftRest
        rw [hsub]
        calc
          ((n + 1 : Nat) : Rat) *
              (FormalPowerSeries.expCoeff (k + 1) *
                FormalPowerSeries.expCoeff (n - k)) =
              ((((n - k : Nat) : Rat)) + (((k + 1 : Nat) : Rat))) *
                (FormalPowerSeries.expCoeff (k + 1) *
                  FormalPowerSeries.expCoeff (n - k)) := by rw [hcastSplit]
          _ = FormalPowerSeries.expCoeff n *
                (FiniteCounting.combination n (k + 1) : Rat) +
              FormalPowerSeries.expCoeff n *
                (FiniteCounting.combination n k : Rat) := by
            rw [← ihLeft, ← ihRight]
            grind [Rat.mul_add, Rat.add_mul,
              Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
          _ = ((n + 1 : Nat) : Rat) *
              (FormalPowerSeries.expCoeff (n + 1) *
                ((FiniteCounting.combination n k : Rat) +
                  (FiniteCounting.combination n (k + 1) : Rat))) := by
            grind [Rat.mul_add, Rat.add_mul,
              Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

/-- One diagonal term of the product of two factorial exponential prefixes. -/
def diagonalTerm (n k : Nat) (x y : Rat) : Rat :=
  FormalPowerSeries.expCoeff k * x ^ k *
    (FormalPowerSeries.expCoeff (n - k) * y ^ (n - k))

def diagonalSum (n : Nat) (x y : Rat) : Nat -> Rat
  | 0 => 0
  | k + 1 => diagonalSum n x y k + diagonalTerm n k x y

theorem diagonalSum_succ (n k : Nat) (x y : Rat) :
    diagonalSum n x y (k + 1) =
      diagonalSum n x y k + diagonalTerm n k x y := by
  rfl

theorem diagonalTerm_eq_expCoeff_mul_binomialTerm
    (n k : Nat) (hk : k <= n) (x y : Rat) :
    diagonalTerm n k x y =
      FormalPowerSeries.expCoeff n * Series.binomialTerm n k y x := by
  unfold diagonalTerm Series.binomialTerm
  have hcoeff :=
    expCoeff_mul_expCoeff_eq_expCoeff_mul_combination n k hk
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- A complete factorial Cauchy-product diagonal is the factorial coefficient
times the corresponding binomial power. -/
theorem diagonalSum_eq_expCoeff_mul_pow
    (n : Nat) (x y : Rat) :
    diagonalSum n x y (n + 1) =
      FormalPowerSeries.expCoeff n * (x + y) ^ n := by
  have hpartial : forall count : Nat, count <= n + 1 ->
      diagonalSum n x y count =
        FormalPowerSeries.expCoeff n * Series.binomialSum n y x count := by
    intro count hcount
    induction count with
    | zero => simp [diagonalSum, Series.binomialSum]
    | succ count ih =>
        rw [diagonalSum_succ, Series.binomialSum_succ, ih (by omega)]
        rw [diagonalTerm_eq_expCoeff_mul_binomialTerm n count (by omega)]
        grind [Rat.mul_add]
  rw [hpartial (n + 1) (Nat.le_refl _), Series.binomialSum_eq_pow]
  grind [Rat.add_comm]

/-- At opposite inputs every nonconstant factorial Cauchy-product diagonal
vanishes exactly. -/
theorem diagonalSum_opposite_eq_zero
    (n : Nat) (hn : 0 < n) (x : Rat) :
    diagonalSum n x (-x) (n + 1) = 0 := by
  rw [diagonalSum_eq_expCoeff_mul_pow]
  have hzero : x + -x = 0 := Rat.add_neg_cancel x
  rw [hzero]
  rw [Series.rat_zero_pow_of_pos hn]
  simp

theorem diagonalSum_zero_opposite_eq_one (x : Rat) :
    diagonalSum 0 x (-x) 1 = 1 := by
  simp [diagonalSum, diagonalTerm, FormalPowerSeries.expCoeff,
    factorialRat, factorial]
  grind [Rat.div_def]

/-! ## Quantitative outer-diagonal budget -/

/-- The complete absolute-value diagonal at radius `C` is exactly the
factorial-tail term with parameter `2*C`. -/
theorem diagonalSum_nonnegative_eq_factorialTailTerm
    (C : Rat) (n : Nat) :
    diagonalSum n C C (n + 1) =
      RationalMajorant.factorialTailTerm (2 * C) n := by
  rw [diagonalSum_eq_expCoeff_mul_pow]
  unfold FormalPowerSeries.expCoeff
    RationalMajorant.factorialTailTerm
  have hadd : C + C = 2 * C := by grind
  rw [hadd]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

/-- A finite budget for consecutive complete outer Cauchy-product diagonals.
It is definitionally the repository's factorial-tail partial sum at radius
`2*C`. -/
def outerDiagonalBudget (C : Rat) (start terms : Nat) : Rat :=
  RationalMajorant.factorialTailPartial (2 * C) start terms

theorem outerDiagonalBudget_succ
    (C : Rat) (start terms : Nat) :
    outerDiagonalBudget C start (terms + 1) =
      outerDiagonalBudget C start terms +
        diagonalSum (start + terms) C C (start + terms + 1) := by
  unfold outerDiagonalBudget
  rw [RationalMajorant.factorialTailPartial,
    diagonalSum_nonnegative_eq_factorialTailTerm]

theorem outerDiagonalBudget_nonneg
    (C : Rat) (hC : 0 <= C) (start terms : Nat) :
    0 <= outerDiagonalBudget C start terms := by
  unfold outerDiagonalBudget
  induction terms with
  | zero => simp [RationalMajorant.factorialTailPartial]
  | succ terms ih =>
      rw [RationalMajorant.factorialTailPartial]
      have hterm := RationalMajorant.factorialTailTerm_nonneg
        (C := 2 * C) (by grind) (start + terms)
      grind

/-- Once the outer diagonals enter the half-ratio region, every finite block
is bounded by twice its first complete diagonal. -/
theorem outerDiagonalBudget_le_two_first
    (C : Rat) (hC : 0 <= C) (start terms : Nat)
    (hstart : 2 * C <= (((start + 1 : Nat) : Rat) / 2)) :
    outerDiagonalBudget C start terms <=
      2 * RationalMajorant.factorialTailTerm (2 * C) start := by
  unfold outerDiagonalBudget
  exact RationalMajorant.factorialTailPartial_bound
    (C := 2 * C) (by grind) hstart terms

/-- The complete outer-diagonal budget has an executable epsilon schedule. -/
theorem outerDiagonalBudget_scheduled_le_eps
    (C : Rat) (hC : 0 <= C) (eps : QPos) (terms : Nat) :
    outerDiagonalBudget C
      (RationalMajorant.factorialTailStart (2 * C) +
        RationalMajorant.halfDecayShift
          (2 * RationalMajorant.factorialTailTerm (2 * C)
            (RationalMajorant.factorialTailStart (2 * C))) eps)
      terms <= eps.val := by
  unfold outerDiagonalBudget
  exact RationalMajorant.factorialTailPartial_shifted_le_eps
    (C := 2 * C) (by grind) eps terms

/-! ## Literal rectangular prefixes and their outer remainder -/

/-- The exact finite center used by the exponential evaluator, with the number
of included factorial terms made explicit. -/
def factorialPrefix (terms : Nat) (x : Rat) : Rat :=
  ExpProofs.powerSeriesCenterAtTerms x terms

theorem factorialPrefix_zero (x : Rat) : factorialPrefix 0 x = 0 := by
  rfl

theorem factorialPrefix_succ (terms : Nat) (x : Rat) :
    factorialPrefix (terms + 1) x =
      factorialPrefix terms x +
        FormalPowerSeries.expCoeff terms * x ^ terms := by
  unfold factorialPrefix
  rw [ExpProofs.powerSeriesCenterAtTerms_succ,
    ExpProofs.powerSeriesTermAtTerms_eq_expCoeff_monomial]

def factorialMonomial (degree : Nat) (x : Rat) : Rat :=
  FormalPowerSeries.expCoeff degree * x ^ degree

theorem factorialPrefix_succ_monomial (terms : Nat) (x : Rat) :
    factorialPrefix (terms + 1) x =
      factorialPrefix terms x + factorialMonomial terms x := by
  exact factorialPrefix_succ terms x

/-- The difference of two literal evaluator prefixes is the corresponding
finite block of factorial monomials. -/
theorem factorialPrefix_add_sub_eq_remainderPartial
    (x : Rat) (start count : Nat) :
    factorialPrefix (start + count) x - factorialPrefix start x =
      FiniteExponentialTaylor.remainderPartial x start count := by
  induction count with
  | zero =>
      rw [Nat.add_zero, FiniteExponentialTaylor.remainderPartial]
      grind [Rat.sub_eq_add_neg]
  | succ count ih =>
      rw [show start + (count + 1) = (start + count) + 1 by omega,
        factorialPrefix_succ_monomial,
        FiniteExponentialTaylor.remainderPartial, ← ih]
      rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
      unfold factorialMonomial
      grind [Rat.add_assoc, Rat.add_comm]

theorem factorialMonomial_eq_factorialTailTerm
    (C : Rat) (degree : Nat) :
    factorialMonomial degree C =
      RationalMajorant.factorialTailTerm C degree := by
  unfold factorialMonomial FormalPowerSeries.expCoeff
    RationalMajorant.factorialTailTerm
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

/-- At a nonnegative majorant input, the finite exponential remainder block
is definitionally the corresponding factorial-tail partial sum.  The
identity itself does not require the sign hypothesis. -/
theorem remainderPartial_eq_factorialTailPartial
    (C : Rat) (start terms : Nat) :
    FiniteExponentialTaylor.remainderPartial C start terms =
      RationalMajorant.factorialTailPartial C start terms := by
  induction terms with
  | zero => rfl
  | succ terms ih =>
      rw [FiniteExponentialTaylor.remainderPartial,
        RationalMajorant.factorialTailPartial, ih]
      have hterm := factorialMonomial_eq_factorialTailTerm
        C (start + terms)
      unfold factorialMonomial at hterm
      rw [hterm]

theorem factorialPrefix_eq_factorialTailPartial
    (C : Rat) (terms : Nat) :
    factorialPrefix terms C =
      RationalMajorant.factorialTailPartial C 0 terms := by
  have h := factorialPrefix_add_sub_eq_remainderPartial C 0 terms
  rw [Nat.zero_add, factorialPrefix_zero,
    remainderPartial_eq_factorialTailPartial] at h
  grind [Rat.sub_eq_add_neg]

theorem factorialPrefix_mono
    {C : Rat} (hC : 0 <= C) {a b : Nat} (hab : a <= b) :
    factorialPrefix a C <= factorialPrefix b C := by
  rw [factorialPrefix_eq_factorialTailPartial,
    factorialPrefix_eq_factorialTailPartial]
  exact RationalMajorant.factorialTailPartial_mono hC 0 a b hab

theorem factorialPrefix_nonneg
    {C : Rat} (hC : 0 <= C) (terms : Nat) :
    0 <= factorialPrefix terms C := by
  rw [factorialPrefix_eq_factorialTailPartial]
  have hmono := RationalMajorant.factorialTailPartial_mono hC 0 0 terms
    (Nat.zero_le terms)
  simpa [RationalMajorant.factorialTailPartial] using hmono

/-- A finite positive factorial prefix is monotone in its nonnegative rational
input.  This is a finite polynomial fact; no completed exponential or
continuity theorem is used. -/
theorem factorialPrefix_mono_input
    {a b : Rat} (ha : 0 <= a) (hab : a <= b) :
    forall terms : Nat, factorialPrefix terms a <= factorialPrefix terms b
  | 0 => Rat.le_refl
  | terms + 1 => by
      rw [factorialPrefix_succ, factorialPrefix_succ]
      apply rat_add_le_add
      · exact factorialPrefix_mono_input ha hab terms
      · have hb : 0 <= b := Rat.le_trans ha hab
        have hpow : a ^ terms <= b ^ terms := by
          induction terms with
          | zero => simp
          | succ terms ih =>
              rw [Rat.pow_succ, Rat.pow_succ]
              calc
                a ^ terms * a <= b ^ terms * a :=
                  Rat.mul_le_mul_of_nonneg_right ih ha
                _ <= b ^ terms * b :=
                  Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg hb)
        have hcoeff : 0 <= FormalPowerSeries.expCoeff terms := by
          unfold FormalPowerSeries.expCoeff
          rw [Rat.div_def, Rat.one_mul]
          exact Rat.le_of_lt
            ((Rat.inv_pos).2 (RationalMajorant.factorialRat_pos terms))
        exact Rat.mul_le_mul_of_nonneg_left hpow hcoeff

theorem factorialPrefix_ge_one_add
    {x : Rat} (hx : 0 <= x) (terms : Nat) (hterms : 2 <= terms) :
    1 + x <= factorialPrefix terms x := by
  have hmono := factorialPrefix_mono hx (a := 2) (b := terms) hterms
  have htwo : factorialPrefix 2 x = 1 + x := by
    rw [show 2 = 1 + 1 by omega, factorialPrefix_succ,
      show 1 = 0 + 1 by omega, factorialPrefix_succ,
      factorialPrefix_zero]
    simp [FormalPowerSeries.expCoeff, factorialRat, factorial]
    grind [Rat.div_def]
  rw [htwo] at hmono
  exact hmono

/-- The first `count` rows of the rectangular product with a fixed
`terms`-term second factor. -/
def rectangularRows (terms : Nat) (x y : Rat) : Nat -> Rat
  | 0 => 0
  | count + 1 =>
      rectangularRows terms x y count +
        factorialMonomial count x * factorialPrefix terms y

theorem rectangularRows_succ
    (terms count : Nat) (x y : Rat) :
    rectangularRows terms x y (count + 1) =
      rectangularRows terms x y count +
        factorialMonomial count x * factorialPrefix terms y := by
  rfl

theorem rectangularRows_eq_prefix_mul
    (terms count : Nat) (x y : Rat) :
    rectangularRows terms x y count =
      factorialPrefix count x * factorialPrefix terms y := by
  induction count with
  | zero => simp [rectangularRows, factorialPrefix_zero]
  | succ count ih =>
      rw [rectangularRows_succ, ih,
        factorialPrefix_succ_monomial]
      grind [Rat.add_mul]

/-- The first `count` rows below the total-degree boundary `degree < terms`.
The intended uses keep `count <= terms`; natural subtraction makes the
runtime definition total. -/
def completeTriangleRows (terms : Nat) (x y : Rat) : Nat -> Rat
  | 0 => 0
  | count + 1 =>
      completeTriangleRows terms x y count +
        factorialMonomial count x * factorialPrefix (terms - count) y

theorem completeTriangleRows_succ
    (terms count : Nat) (x y : Rat) :
    completeTriangleRows terms x y (count + 1) =
      completeTriangleRows terms x y count +
        factorialMonomial count x * factorialPrefix (terms - count) y := by
  rfl

private theorem diagonalTerm_eq_monomial_mul_monomial
    (n k : Nat) (x y : Rat) :
    diagonalTerm n k x y =
      factorialMonomial k x * factorialMonomial (n - k) y := by
  unfold diagonalTerm factorialMonomial
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- Increasing the total-degree boundary by one adds exactly one complete
Cauchy-product diagonal, row by row. -/
theorem completeTriangleRows_next
    (terms count : Nat) (hcount : count <= terms + 1) (x y : Rat) :
    completeTriangleRows (terms + 1) x y count =
      completeTriangleRows terms x y count +
        diagonalSum terms x y count := by
  induction count with
  | zero =>
      simp [completeTriangleRows, diagonalSum]
      grind
  | succ count ih =>
      have hcountTerms : count <= terms := by omega
      have hsub : terms + 1 - count = (terms - count) + 1 := by omega
      rw [completeTriangleRows_succ, completeTriangleRows_succ,
        diagonalSum_succ, ih (by omega), hsub,
        factorialPrefix_succ_monomial,
        diagonalTerm_eq_monomial_mul_monomial]
      grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]

theorem completeTriangleRows_extra_zero
    (terms : Nat) (x y : Rat) :
    completeTriangleRows terms x y (terms + 1) =
      completeTriangleRows terms x y terms := by
  rw [completeTriangleRows_succ]
  simp [factorialPrefix_zero]
  grind

/-- The complete inner triangle of a rectangular prefix. -/
def completeTrianglePrefix (terms : Nat) (x y : Rat) : Rat :=
  completeTriangleRows terms x y terms

/-- The first `count` row tails outside the complete total-degree triangle. -/
def outerRows (terms : Nat) (x y : Rat) : Nat -> Rat
  | 0 => 0
  | count + 1 =>
      outerRows terms x y count +
        factorialMonomial count x *
          (factorialPrefix terms y - factorialPrefix (terms - count) y)

theorem outerRows_succ
    (terms count : Nat) (x y : Rat) :
    outerRows terms x y (count + 1) =
      outerRows terms x y count +
        factorialMonomial count x *
          (factorialPrefix terms y - factorialPrefix (terms - count) y) := by
  rfl

/-- A nonnegative rational majorant for the row tails.  It has exactly the
same finite shape as `outerRows`, with each monomial and tail block replaced
by its factorial majorant. -/
def outerRowsMajorant (terms : Nat) (C : Rat) : Nat -> Rat
  | 0 => 0
  | count + 1 =>
      outerRowsMajorant terms C count +
        RationalMajorant.factorialTailTerm C count *
          RationalMajorant.factorialTailPartial C (terms - count) count

theorem outerRowsMajorant_succ
    (terms count : Nat) (C : Rat) :
    outerRowsMajorant terms C (count + 1) =
      outerRowsMajorant terms C count +
        RationalMajorant.factorialTailTerm C count *
          RationalMajorant.factorialTailPartial C (terms - count) count := by
  rfl

/-- Absolute majorization of every initial collection of rectangular row
tails.  This is the analytic estimate corresponding to the exact row-wise
decomposition. -/
theorem qabs_outerRows_le_majorant
    {C x y : Rat} (hC : 0 <= C) (hx : qabs x <= C)
    (hy : qabs y <= C) (terms count : Nat) (hcount : count <= terms) :
    qabs (outerRows terms x y count) <=
      outerRowsMajorant terms C count := by
  induction count with
  | zero =>
      change qabs 0 <= 0
      decide +kernel
  | succ count ih =>
      have hcountTerms : count <= terms := by omega
      have hsplit : (terms - count) + count = terms := by omega
      have hmon :=
        FinitePolynomial.qabs_expCoeff_monomial_le_factorialTailTerm
          hC hx count
      have htail :=
        FiniteExponentialTaylor.remainderPartial_abs_le_factorialTailPartial
          hC hy (terms - count) count
      have htailEq :
          factorialPrefix terms y - factorialPrefix (terms - count) y =
            FiniteExponentialTaylor.remainderPartial y
              (terms - count) count := by
        calc
          factorialPrefix terms y - factorialPrefix (terms - count) y =
              factorialPrefix ((terms - count) + count) y -
                factorialPrefix (terms - count) y := by rw [hsplit]
          _ = FiniteExponentialTaylor.remainderPartial y
                (terms - count) count :=
            factorialPrefix_add_sub_eq_remainderPartial _ _ _
      have hmul :
          qabs
              (factorialMonomial count x *
                (factorialPrefix terms y -
                  factorialPrefix (terms - count) y)) <=
            RationalMajorant.factorialTailTerm C count *
              RationalMajorant.factorialTailPartial C
                (terms - count) count := by
        rw [qabs_mul, htailEq]
        exact Rat.le_trans
          (Rat.mul_le_mul_of_nonneg_right hmon
            (qabs_nonneg
              (FiniteExponentialTaylor.remainderPartial y
                (terms - count) count)))
          (Rat.mul_le_mul_of_nonneg_left htail
            (RationalMajorant.factorialTailTerm_nonneg hC count))
      rw [outerRows_succ, outerRowsMajorant_succ]
      exact Rat.le_trans
        (qabs_add_le _ _)
        (rat_add_le_add (ih (by omega)) hmul)

/-- At the nonnegative radius itself, the analytic majorant is exactly the
corresponding rectangular row-tail sum. -/
theorem outerRowsMajorant_eq_outerRows_self
    (C : Rat) (terms count : Nat) (hcount : count <= terms) :
    outerRowsMajorant terms C count = outerRows terms C C count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hcountTerms : count <= terms := by omega
      have hsplit : (terms - count) + count = terms := by omega
      have htail :
          factorialPrefix terms C - factorialPrefix (terms - count) C =
            RationalMajorant.factorialTailPartial C
              (terms - count) count := by
        calc
          factorialPrefix terms C - factorialPrefix (terms - count) C =
              factorialPrefix ((terms - count) + count) C -
                factorialPrefix (terms - count) C := by rw [hsplit]
          _ = FiniteExponentialTaylor.remainderPartial C
                (terms - count) count :=
            factorialPrefix_add_sub_eq_remainderPartial _ _ _
          _ = RationalMajorant.factorialTailPartial C
                (terms - count) count :=
            remainderPartial_eq_factorialTailPartial _ _ _
      rw [outerRowsMajorant_succ, outerRows_succ,
        ih (by omega), ← htail,
        ← factorialMonomial_eq_factorialTailTerm]

theorem rectangularRows_eq_triangle_add_outer
    (terms count : Nat) (hcount : count <= terms) (x y : Rat) :
    rectangularRows terms x y count =
      completeTriangleRows terms x y count +
        outerRows terms x y count := by
  induction count with
  | zero =>
      simp [rectangularRows, completeTriangleRows, outerRows]
      grind
  | succ count ih =>
      rw [rectangularRows_succ, completeTriangleRows_succ,
        outerRows_succ, ih (by omega)]
      grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm,
        Rat.sub_eq_add_neg]

theorem completeTriangleRows_mono_count
    {C : Rat} (hC : 0 <= C) (terms : Nat) :
    forall a b : Nat, a <= b ->
      completeTriangleRows terms C C a <=
        completeTriangleRows terms C C b
  | a, 0, hab => by
      have ha : a = 0 := by omega
      subst a
      exact Rat.le_refl
  | a, b + 1, hab => by
      by_cases ha : a = b + 1
      · subst a
        exact Rat.le_refl
      · have hab' : a <= b := by omega
        have ih := completeTriangleRows_mono_count hC terms a b hab'
        rw [completeTriangleRows_succ]
        have hmon : 0 <= factorialMonomial b C := by
          rw [factorialMonomial_eq_factorialTailTerm]
          exact RationalMajorant.factorialTailTerm_nonneg hC b
        have hp := factorialPrefix_nonneg hC (terms - b)
        have hproduct :
            0 <= factorialMonomial b C *
              factorialPrefix (terms - b) C :=
          Rat.mul_nonneg hmon hp
        grind

/-- Every row of an `N` by `N` factorial rectangle lies inside the complete
total-degree triangle with boundary `2*N`. -/
theorem rectangularRows_le_doubleTriangle
    {C : Rat} (hC : 0 <= C) (terms count : Nat)
    (hcount : count <= terms) :
    rectangularRows terms C C count <=
      completeTriangleRows (terms + terms) C C count := by
  induction count with
  | zero =>
      exact Rat.le_refl
  | succ count ih =>
      have hcountTerms : count <= terms := by omega
      have hprefixIndex :
          terms <= terms + terms - count := by omega
      have hp := factorialPrefix_mono hC hprefixIndex
      have hmon : 0 <= factorialMonomial count C := by
        rw [factorialMonomial_eq_factorialTailTerm]
        exact RationalMajorant.factorialTailTerm_nonneg hC count
      have hrow := Rat.mul_le_mul_of_nonneg_left hp hmon
      rw [rectangularRows_succ, completeTriangleRows_succ]
      exact rat_add_le_add (ih (by omega)) hrow

/-- Sum of the complete Cauchy-product diagonals strictly below `terms`. -/
def completeDiagonalPrefix : Nat -> Rat -> Rat -> Rat
  | 0, _x, _y => 0
  | terms + 1, x, y =>
      completeDiagonalPrefix terms x y +
        diagonalSum terms x y (terms + 1)

theorem completeDiagonalPrefix_zero (x y : Rat) :
    completeDiagonalPrefix 0 x y = 0 := by
  rfl

theorem completeDiagonalPrefix_succ (terms : Nat) (x y : Rat) :
    completeDiagonalPrefix (terms + 1) x y =
      completeDiagonalPrefix terms x y +
        diagonalSum terms x y (terms + 1) := by
  rfl

/-- Accumulating any positive number of complete diagonals at opposite inputs
gives exactly the constant diagonal `1`. -/
theorem completeDiagonalPrefix_opposite_eq_one
    (terms : Nat) (hterms : 0 < terms) (x : Rat) :
    completeDiagonalPrefix terms x (-x) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hterms)
  induction k with
  | zero =>
      rw [completeDiagonalPrefix_succ, completeDiagonalPrefix_zero,
        diagonalSum_zero_opposite_eq_one]
      grind
  | succ k ih =>
      rw [completeDiagonalPrefix_succ,
        diagonalSum_opposite_eq_zero (k + 1) (Nat.succ_pos k),
        ih (Nat.succ_pos k)]
      grind

/-- The row-wise total-degree triangle is exactly the accumulated complete
diagonal prefix. -/
theorem completeTrianglePrefix_eq_completeDiagonalPrefix
    (terms : Nat) (x y : Rat) :
    completeTrianglePrefix terms x y =
      completeDiagonalPrefix terms x y := by
  induction terms with
  | zero => simp [completeTrianglePrefix, completeTriangleRows,
      completeDiagonalPrefix]
  | succ terms ih =>
      unfold completeTrianglePrefix
      rw [completeTriangleRows_next terms (terms + 1)
          (Nat.le_refl _) x y,
        completeTriangleRows_extra_zero]
      change completeTrianglePrefix terms x y +
          diagonalSum terms x y (terms + 1) =
        completeDiagonalPrefix (terms + 1) x y
      rw [ih, completeDiagonalPrefix_succ]

/-- Appending complete nonnegative diagonals is exactly the previously
scheduled outer-diagonal factorial budget. -/
theorem completeDiagonalPrefix_add_outerDiagonalBudget
    (C : Rat) (start count : Nat) :
    completeDiagonalPrefix (start + count) C C =
      completeDiagonalPrefix start C C +
        outerDiagonalBudget C start count := by
  induction count with
  | zero =>
      rw [Nat.add_zero]
      simp [outerDiagonalBudget,
        RationalMajorant.factorialTailPartial]
      grind
  | succ count ih =>
      rw [show start + (count + 1) = (start + count) + 1 by omega,
        completeDiagonalPrefix_succ, ih,
        outerDiagonalBudget_succ]
      grind [Rat.add_assoc, Rat.add_comm]

/-- The literal `N` by `N` factorial rectangle is contained in the complete
triangle through degree `2*N-1`.  We use boundary `2*N`, which also handles
the zero-term rectangle without a special predecessor convention. -/
theorem rectangularRows_le_completeDiagonalPrefix_double
    {C : Rat} (hC : 0 <= C) (terms : Nat) :
    rectangularRows terms C C terms <=
      completeDiagonalPrefix (terms + terms) C C := by
  rw [← completeTrianglePrefix_eq_completeDiagonalPrefix]
  unfold completeTrianglePrefix
  exact Rat.le_trans
    (rectangularRows_le_doubleTriangle hC terms terms (Nat.le_refl _))
    (completeTriangleRows_mono_count hC (terms + terms)
      terms (terms + terms) (by omega))

/-- The incomplete-outer-diagonal remainder of the literal rectangular
product.  Its forthcoming estimate is the sole missing finite reindexing step
in the reciprocal-exponential bridge. -/
def rectangularOuterRemainder (terms : Nat) (x y : Rat) : Rat :=
  factorialPrefix terms x * factorialPrefix terms y -
    completeDiagonalPrefix terms x y

theorem factorialPrefix_mul_eq_completeDiagonalPrefix_add_remainder
    (terms : Nat) (x y : Rat) :
    factorialPrefix terms x * factorialPrefix terms y =
      completeDiagonalPrefix terms x y +
        rectangularOuterRemainder terms x y := by
  unfold rectangularOuterRemainder
  grind [Rat.sub_eq_add_neg]

/-- The named rectangular remainder is literally the rectangular row sum
minus its complete total-degree triangle. -/
theorem rectangularOuterRemainder_eq_rows_sub_triangle
    (terms : Nat) (x y : Rat) :
    rectangularOuterRemainder terms x y =
      rectangularRows terms x y terms -
        completeTrianglePrefix terms x y := by
  unfold rectangularOuterRemainder
  rw [rectangularRows_eq_prefix_mul,
    completeTrianglePrefix_eq_completeDiagonalPrefix]

/-- The rectangular remainder is the executable sum of its row tails. -/
theorem rectangularOuterRemainder_eq_outerRows
    (terms : Nat) (x y : Rat) :
    rectangularOuterRemainder terms x y =
      outerRows terms x y terms := by
  rw [rectangularOuterRemainder_eq_rows_sub_triangle,
    rectangularRows_eq_triangle_add_outer terms terms (Nat.le_refl _) x y]
  unfold completeTrianglePrefix
  grind [Rat.sub_eq_add_neg]

/-- The literal rectangular Cauchy-product remainder is controlled by the
fully executable row-tail majorant. -/
theorem qabs_rectangularOuterRemainder_le_majorant
    {C x y : Rat} (hC : 0 <= C) (hx : qabs x <= C)
    (hy : qabs y <= C) (terms : Nat) :
    qabs (rectangularOuterRemainder terms x y) <=
      outerRowsMajorant terms C terms := by
  rw [rectangularOuterRemainder_eq_outerRows]
  exact qabs_outerRows_le_majorant hC hx hy terms terms (Nat.le_refl _)

/-- The row-tail majorant is a subset of the complete diagonals beginning at
the rectangular boundary.  This closes the finite reindexing estimate. -/
theorem outerRowsMajorant_le_outerDiagonalBudget
    {C : Rat} (hC : 0 <= C) (terms : Nat) :
    outerRowsMajorant terms C terms <=
      outerDiagonalBudget C terms terms := by
  rw [outerRowsMajorant_eq_outerRows_self C terms terms (Nat.le_refl _)]
  have hrect := rectangularRows_le_completeDiagonalPrefix_double hC terms
  have hsplit := rectangularRows_eq_triangle_add_outer
    terms terms (Nat.le_refl _) C C
  have htriangle := completeTrianglePrefix_eq_completeDiagonalPrefix
    terms C C
  have hbudget := completeDiagonalPrefix_add_outerDiagonalBudget
    C terms terms
  unfold completeTrianglePrefix at htriangle
  grind

/-- The actual rectangular remainder is bounded by the already scheduled
complete outer-diagonal budget. -/
theorem qabs_rectangularOuterRemainder_le_outerDiagonalBudget
    {C x y : Rat} (hC : 0 <= C) (hx : qabs x <= C)
    (hy : qabs y <= C) (terms : Nat) :
    qabs (rectangularOuterRemainder terms x y) <=
      outerDiagonalBudget C terms terms :=
  Rat.le_trans
    (qabs_rectangularOuterRemainder_le_majorant hC hx hy terms)
    (outerRowsMajorant_le_outerDiagonalBudget hC terms)

/-- Executable product stage at which every later complete outer-diagonal
block fits the requested positive rational tolerance. -/
def scheduledProductStage (C : Rat) (eps : QPos) : Nat :=
  RationalMajorant.factorialTailStart (2 * C) +
    RationalMajorant.halfDecayShift
      (2 * RationalMajorant.factorialTailTerm (2 * C)
        (RationalMajorant.factorialTailStart (2 * C))) eps

theorem scheduledProductStage_pos (C : Rat) (eps : QPos) :
    0 < scheduledProductStage C eps := by
  unfold scheduledProductStage RationalMajorant.factorialTailStart
  omega

theorem outerDiagonalBudget_later_scheduled_le_eps
    (C : Rat) (hC : 0 <= C) (eps : QPos)
    (start terms : Nat) (hstart : scheduledProductStage C eps <= start) :
    outerDiagonalBudget C start terms <= eps.val := by
  let scheduled := scheduledProductStage C eps
  have hadd : scheduled + (start - scheduled) = start := by omega
  have hsplit := RationalMajorant.factorialTailPartial_add
    (2 * C) scheduled (start - scheduled) terms
  rw [hadd] at hsplit
  have hfirst :
      0 <= RationalMajorant.factorialTailPartial
        (2 * C) scheduled (start - scheduled) := by
    exact outerDiagonalBudget_nonneg C hC scheduled (start - scheduled)
  have hwhole := outerDiagonalBudget_scheduled_le_eps
    C hC eps ((start - scheduled) + terms)
  change RationalMajorant.factorialTailPartial (2 * C) scheduled
      ((start - scheduled) + terms) <= eps.val at hwhole
  rw [hsplit] at hwhole
  unfold outerDiagonalBudget
  grind

/-- At opposite inputs the literal center product is `1` plus exactly the
named rectangular outer remainder. -/
theorem factorialPrefix_mul_opposite_eq_one_add_remainder
    (terms : Nat) (hterms : 0 < terms) (x : Rat) :
    factorialPrefix terms x * factorialPrefix terms (-x) =
      1 + rectangularOuterRemainder terms x (-x) := by
  rw [factorialPrefix_mul_eq_completeDiagonalPrefix_add_remainder,
    completeDiagonalPrefix_opposite_eq_one terms hterms]

/-- At the computable product stage, the literal opposite-input factorial
prefix product is within `eps` of one. -/
theorem factorialPrefix_mul_opposite_scheduled_close_to_one
    {C x : Rat} (hC : 0 <= C) (hx : qabs x <= C) (eps : QPos) :
    qabs
        (factorialPrefix (scheduledProductStage C eps) x *
            factorialPrefix (scheduledProductStage C eps) (-x) - 1) <=
      eps.val := by
  let stage := scheduledProductStage C eps
  have hstage : 0 < stage := scheduledProductStage_pos C eps
  have hproduct := factorialPrefix_mul_opposite_eq_one_add_remainder
    stage hstage x
  have hy : qabs (-x) <= C := by
    rw [qabs_neg]
    exact hx
  have hremainder :=
    qabs_rectangularOuterRemainder_le_outerDiagonalBudget
      (y := -x) hC hx hy stage
  have hscheduled := outerDiagonalBudget_scheduled_le_eps
    C hC eps stage
  change outerDiagonalBudget C stage stage <= eps.val at hscheduled
  change qabs
      (factorialPrefix stage x * factorialPrefix stage (-x) - 1) <=
    eps.val
  rw [hproduct]
  have heq :
      1 + rectangularOuterRemainder stage x (-x) - 1 =
        rectangularOuterRemainder stage x (-x) := by
    grind [Rat.sub_eq_add_neg]
  rw [heq]
  exact Rat.le_trans hremainder hscheduled

/-- The same product estimate holds at every later literal prefix, which is
the form needed to compare arbitrary earlier raw-real stages. -/
theorem factorialPrefix_mul_opposite_later_close_to_one
    {C x : Rat} (hC : 0 <= C) (hx : qabs x <= C) (eps : QPos)
    (terms : Nat) (hterms : scheduledProductStage C eps <= terms) :
    qabs (factorialPrefix terms x * factorialPrefix terms (-x) - 1) <=
      eps.val := by
  have htermsPos := Nat.lt_of_lt_of_le
    (scheduledProductStage_pos C eps) hterms
  rw [factorialPrefix_mul_opposite_eq_one_add_remainder
    terms htermsPos x]
  have heq :
      1 + rectangularOuterRemainder terms x (-x) - 1 =
        rectangularOuterRemainder terms x (-x) := by
    grind [Rat.sub_eq_add_neg]
  rw [heq]
  exact Rat.le_trans
    (qabs_rectangularOuterRemainder_le_outerDiagonalBudget
      (y := -x) hC hx (by simpa [qabs_neg] using hx) terms)
    (outerDiagonalBudget_later_scheduled_le_eps
      C hC eps terms terms hterms)

end FiniteExponentialProduct
end ComputableAnalysis


