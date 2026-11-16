-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteGaussianTail
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteGaussianTail
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:26:49.729173+00:00
-- url     : https://prove2.me/theorems/cdc48ec1-99bc-4689-bd08-d6bf3ad96664
-- title:
--   Computable analysis · FiniteGaussianTail · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FiniteGaussianTail.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteFTCIntervalRegular
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteGaussianIntegral
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_DirichletSeries
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteExponentialProduct
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PositiveReciprocal

set_option autoImplicit true

/-!
# Finite reciprocal-square tails for the Gaussian route

The bounded Gaussian integral is already represented by a valid rational
quadrature raw.  To pass from a bounded interval to the full line, this file
constructs the elementary continuous majorant

`integral from R to infinity of 1 / x^2 = 1 / R`

without an improper-integral primitive.  The substitution `x = R / t` folds
the positive tail onto `[0,1]`; after multiplying by its rational Jacobian,
the reciprocal-square density becomes the exact constant `1 / R`.

Besides the stagewise reciprocal presentation, this file transports the
domination result to the factorial-series presentation of `exp (-x^2)` in
the representative-invariant order on raw computable reals.  The result is
an explicit symmetric tail budget `2 / R`; it is not yet a construction of
an improper integral over the full line.
-/

namespace ComputableAnalysis

/-! ## A finite Euler-center inequality

The following rational inequality is the elementary finite core of
`exp(-a) <= 1 / (1+a)`.  It concerns only a repeated-multiplication center;
transport to the certified exponential raw remains a separate equivalence
obligation. -/

theorem unitPow_mul_affine_le_one
    (p : Rat) (hp0 : 0 <= p) (hp1 : p <= 1) :
    forall m : Nat,
      p ^ m * ((((m + 1 : Nat) : Rat)) - (m : Rat) * p) <= 1
  | 0 => by
      simp
      decide +kernel
  | m + 1 => by
      have ih := unitPow_mul_affine_le_one p hp0 hp1 m
      have honeMinus : 0 <= 1 - p := by
        grind [Rat.sub_eq_add_neg]
      have hfactor : 0 <= (((m + 1 : Nat) : Rat)) :=
        Rat.natCast_nonneg
      have hbracket :
          p * ((((m + 2 : Nat) : Rat)) - (((m + 1 : Nat) : Rat)) * p) <=
            (((m + 1 : Nat) : Rat)) - (m : Rat) * p := by
        have hsquare :
            0 <= (((m + 1 : Nat) : Rat)) * (1 - p) * (1 - p) :=
          Rat.mul_nonneg (Rat.mul_nonneg hfactor honeMinus) honeMinus
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm]
      have hpPow : 0 <= p ^ m := Rat.pow_nonneg hp0
      rw [Rat.pow_succ]
      calc
        p ^ m * p *
            ((((m + 2 : Nat) : Rat)) - (((m + 1 : Nat) : Rat)) * p) =
            p ^ m *
              (p * ((((m + 2 : Nat) : Rat)) -
                (((m + 1 : Nat) : Rat)) * p)) := by
                  grind [Rat.mul_assoc]
        _ <= p ^ m *
            ((((m + 1 : Nat) : Rat)) - (m : Rat) * p) :=
          Rat.mul_le_mul_of_nonneg_left hbracket hpPow
        _ <= 1 := ih

/-- Finite repeated multiplication at a negative argument lies below the
elementary reciprocal bound whenever the Euler mesh count dominates that
argument. -/
theorem one_sub_div_pow_le_one_div_one_add
    (a : Rat) (m : Nat) (ha0 : 0 <= a) (hm : 0 < m)
    (ham : a <= (m : Rat)) :
    (1 - a / (m : Rat)) ^ m <= 1 / (1 + a) := by
  let M : Rat := (m : Rat)
  let p : Rat := 1 - a / M
  have hMpos : 0 < M := by
    dsimp [M]
    exact (Rat.natCast_pos).2 hm
  have hMne : M ≠ 0 := Rat.ne_of_gt hMpos
  have hinv0 : 0 <= M⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hMpos)
  have hdiv0 : 0 <= a / M := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg ha0 hinv0
  have hdiv1 : a / M <= 1 := by
    rw [Rat.div_def]
    have hscaled := Rat.mul_le_mul_of_nonneg_right ham hinv0
    calc
      a * M⁻¹ <= M * M⁻¹ := hscaled
      _ = 1 := Rat.mul_inv_cancel M hMne
  have hp0 : 0 <= p := by
    dsimp [p]
    grind [Rat.sub_eq_add_neg]
  have hp1 : p <= 1 := by
    dsimp [p]
    grind [Rat.sub_eq_add_neg]
  have hfinite := unitPow_mul_affine_le_one p hp0 hp1 m
  have hcoefficient :
      (((m + 1 : Nat) : Rat)) - (m : Rat) * p = 1 + a := by
    dsimp [p, M]
    rw [Rat.div_def]
    have hcancel : ((m : Rat)) * ((m : Rat))⁻¹ = 1 :=
      Rat.mul_inv_cancel (m : Rat) hMne
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  rw [hcoefficient] at hfinite
  have honePlusPos : 0 < 1 + a := by grind
  apply Rat.le_of_mul_le_mul_right (c := 1 + a)
  · calc
      (1 - a / (m : Rat)) ^ m * (1 + a) <= 1 := by
        simpa [p] using hfinite
      _ = (1 / (1 + a)) * (1 + a) := by
        rw [Rat.div_def]
        have hne : 1 + a ≠ 0 := Rat.ne_of_gt honePlusPos
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact honePlusPos

/-- The imperative Euler center inherits the preceding closed-form negative
argument bound. -/
theorem eulerCenter_neg_le_one_div_one_add
    (a : Rat) (stage : Nat) (ha0 : 0 <= a)
    (haMesh : a <= ((((stage + 1) * (stage + 1) : Nat) : Rat))) :
    ExpProofs.eulerCenter (-a) stage <= 1 / (1 + a) := by
  let m : Nat := (stage + 1) * (stage + 1)
  have hm : 0 < m := Nat.mul_pos (Nat.succ_pos stage) (Nat.succ_pos stage)
  rw [ExpProofs.eulerCenter_eq_pow]
  have hbase :
      1 + (-a) / (m : Rat) = 1 - a / (m : Rat) := by
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.neg_mul, Rat.mul_neg]
  rw [hbase]
  exact one_sub_div_pow_le_one_div_one_add a m ha0 hm (by
    simpa [m] using haMesh)

/-- A finite stage of the repeated-multiplication exponential box is below
`1/a` once its mesh dominates `a` and its displayed radius fits in the exact
gap between `1/(1+a)` and `1/a`.  This theorem is entirely rational; the
remaining Gaussian bridge is equivalence of this negative-input evaluator
with the selected certified exponential representation. -/
theorem expEuler_neg_compute_hi_le_one_div
    (a : Rat) (stage : Nat) (ha : 0 < a)
    (haMesh : a <= ((((stage + 1) * (stage + 1) : Nat) : Rat)))
    (hradius : ExpProofs.stageRadius stage <=
      1 / a - 1 / (1 + a)) :
    ((expEuler (-a)).compute stage).hi <= 1 / a := by
  rw [ExpProofs.expEuler_compute_eq]
  unfold ExpProofs.intervalAround
  have hcenter := eulerCenter_neg_le_one_div_one_add
    a stage (Rat.le_of_lt ha) haMesh
  calc
    ExpProofs.eulerCenter (-a) stage + ExpProofs.stageRadius stage <=
        1 / (1 + a) + (1 / a - 1 / (1 + a)) :=
      rat_add_le_add hcenter hradius
    _ = 1 / a := by grind [Rat.sub_eq_add_neg]

/-- A fully explicit Euler stage for the negative square at a positive
natural tail point. -/
def gaussianEulerTailStage (k : Nat) : Nat :=
  let a := k * k
  a * (a + 1)

theorem gaussianEulerTailStage_pos (k : Nat) (hk : 0 < k) :
    0 < gaussianEulerTailStage k := by
  unfold gaussianEulerTailStage
  exact Nat.mul_pos (Nat.mul_pos hk hk) (Nat.succ_pos _)

/-- Every positive integer tail point has a symbolic finite-stage
repeated-multiplication certificate
`expEuler (-(k^2)) <= 1/(k^2)`.  Unlike the earlier numerical ladder, this
statement is uniform in `k`; it still concerns the Euler evaluator until the
negative-input representation-equivalence theorem is supplied. -/
theorem expEuler_neg_natSquare_compute_hi_le_reciprocalSquare
    (k : Nat) (hk : 0 < k) :
    ((expEuler (-(((k * k : Nat) : Rat)))).compute
      (gaussianEulerTailStage k)).hi <=
        1 / (((k * k : Nat) : Rat)) := by
  let A : Nat := k * k
  let s : Nat := gaussianEulerTailStage k
  have hA : 0 < A := by
    dsimp [A]
    exact Nat.mul_pos hk hk
  have hs : 0 < s := by
    dsimp [s]
    exact gaussianEulerTailStage_pos k hk
  apply expEuler_neg_compute_hi_le_one_div
  · exact_mod_cast hA
  · have hAs : A <= s := by
      dsimp [s, gaussianEulerTailStage]
      exact Nat.le_mul_of_pos_right A (Nat.succ_pos A)
    have hsSucc : s <= s + 1 := Nat.le_succ s
    have hSuccSquare : s + 1 <= (s + 1) * (s + 1) :=
      Nat.le_mul_of_pos_right (s + 1) (Nat.succ_pos s)
    exact_mod_cast (Nat.le_trans hAs (Nat.le_trans hsSucc hSuccSquare))
  · unfold ExpProofs.stageRadius
    rw [if_neg (Nat.ne_of_gt hs)]
    have hden : A * (A + 1) <= 2 * s := by
      have hsEq : s = A * (A + 1) := by
        dsimp [s, A, gaussianEulerTailStage]
      rw [hsEq]
      exact Nat.le_mul_of_pos_left _ (by decide +kernel)
    have hleftPos : 0 < A * (A + 1) :=
      Nat.mul_pos hA (Nat.succ_pos A)
    have hrightPos : 0 < 2 * s := Nat.mul_pos (by omega) hs
    have hrecip := Series.one_div_nat_antitone_series
      hleftPos hrightPos hden
    have hslack :
        1 / (((k * k : Nat) : Rat)) -
            1 / (1 + (((k * k : Nat) : Rat))) =
          1 / (((A * (A + 1) : Nat) : Rat)) := by
      let Q : Rat := (A : Rat)
      have hQpos : 0 < Q := by
        dsimp [Q]
        exact (Rat.natCast_pos).2 hA
      have hQne : Q ≠ 0 := Rat.ne_of_gt hQpos
      have hQOneNe : Q + 1 ≠ 0 := by
        exact Rat.ne_of_gt (by grind : 0 < Q + 1)
      have hcastA : (((k * k : Nat) : Rat)) = Q := by
        rfl
      have hcastProd : (((A * (A + 1) : Nat) : Rat)) = Q * (Q + 1) := by
        dsimp [Q]
        exact_mod_cast (rfl : A * (A + 1) = A * (A + 1))
      rw [hcastA, hcastProd]
      rw [Rat.div_def, Rat.div_def, Rat.div_def]
      have hQcancel : Q * Q⁻¹ = 1 := Rat.mul_inv_cancel Q hQne
      have hQOneCancel : (Q + 1) * (Q + 1)⁻¹ = 1 :=
        Rat.mul_inv_cancel (Q + 1) hQOneNe
      grind [Rat.sub_eq_add_neg, Rat.inv_mul_rev,
        Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
    rw [hslack]
    simpa [Rat.div_def] using hrecip

/-! ## A valid reciprocal presentation of the negative exponential

For tail estimates it is useful to compute `exp(-a)` as the reciprocal of
the positive factorial series at `a`.  The finite multiplicative identity
with `expPowerSeries (-a)` remains a separate representation-equivalence
theorem, but the reciprocal presentation is already a valid raw real and has
the elementary bound `1 / (1+a)` at every stage. -/

/-- A fully valid computable presentation of the negative exponential on a
nonnegative rational input, obtained by positive interval inversion. -/
def reciprocalNegativeExpRaw (a : Rat) : RealCompute :=
  RealCompute.positiveReciprocal (expPowerSeries a) (1 + a)

theorem reciprocalNegativeExpRaw_valid
    (a : Rat) (ha : 0 <= a) :
    (reciprocalNegativeExpRaw a).Valid := by
  unfold reciprocalNegativeExpRaw
  apply RealCompute.positiveReciprocal_valid
  · exact ExpProofs.expPowerSeries_valid a
  · grind
  · intro n
    exact ExpProofs.expPowerSeries_compute_hi_ge_one_add a ha n

/-- The reciprocal presentation inherits an explicit pointwise width bound
from the positive factorial-series evaluator. -/
theorem reciprocalNegativeExpRaw_compute_width_le_input
    (a : Rat) (ha : 0 <= a) (n : Nat) :
    ((reciprocalNegativeExpRaw a).compute n).width <=
      ((expPowerSeries a).compute n).width / ((1 + a) * (1 + a)) := by
  unfold reciprocalNegativeExpRaw
  exact RealCompute.positiveReciprocal_compute_width_le
    (expPowerSeries a) (1 + a)
    (ExpProofs.expPowerSeries_valid a) (by grind)
    (fun stage => ExpProofs.expPowerSeries_compute_hi_ge_one_add
      a ha stage) n

/-- Public geometric width bound for the reciprocal negative-exponential
presentation. -/
theorem reciprocalNegativeExpRaw_compute_width_le_geometric
    (a : Rat) (ha : 0 <= a) (n : Nat) :
    ((reciprocalNegativeExpRaw a).compute n).width <=
      ((4 * qabs (ExpProofs.powerSeriesTermAtTerms a
          (expPowerSeriesTerms a 0))) /
        ((1 + a) * (1 + a))) * ((1 : Rat) / 2) ^ n := by
  have hinput := ExpProofs.expPowerSeries_compute_width_le_geometric a n
  have hrecip := reciprocalNegativeExpRaw_compute_width_le_input a ha n
  have hdenPos : 0 < (1 + a) * (1 + a) := by
    exact Rat.mul_pos (by grind) (by grind)
  have hinvNonneg : 0 <= 1 / ((1 + a) * (1 + a)) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt ((Rat.inv_pos).2 hdenPos))
  have hscaled := Rat.mul_le_mul_of_nonneg_right hinput hinvNonneg
  calc
    ((reciprocalNegativeExpRaw a).compute n).width <=
      ((expPowerSeries a).compute n).width /
        ((1 + a) * (1 + a)) := hrecip
    _ <= ((4 * qabs (ExpProofs.powerSeriesTermAtTerms a
            (expPowerSeriesTerms a 0))) *
          ((1 : Rat) / 2) ^ n) /
        ((1 + a) * (1 + a)) := by
      simpa [Rat.div_def] using hscaled
    _ = ((4 * qabs (ExpProofs.powerSeriesTermAtTerms a
            (expPowerSeriesTerms a 0))) /
          ((1 + a) * (1 + a))) * ((1 : Rat) / 2) ^ n := by
      grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

private theorem expPowerSeries_literal_prefix_mem
    (x : Rat) (n : Nat) :
    ((expPowerSeries x).compute n).lo <=
        FiniteExponentialProduct.factorialPrefix
          (expPowerSeriesTerms x n) x /\
      FiniteExponentialProduct.factorialPrefix
          (expPowerSeriesTerms x n) x <=
        ((expPowerSeries x).compute n).hi := by
  rw [ExpProofs.expPowerSeries_compute_eq,
    ExpProofs.powerSeriesCenter_stage_eq]
  change
    ExpProofs.powerSeriesCenterAtTerms x (expPowerSeriesTerms x n) -
          ExpProofs.powerSeriesTailRadius x n <=
        ExpProofs.powerSeriesCenterAtTerms x (expPowerSeriesTerms x n) /\
      ExpProofs.powerSeriesCenterAtTerms x (expPowerSeriesTerms x n) <=
        ExpProofs.powerSeriesCenterAtTerms x (expPowerSeriesTerms x n) +
          ExpProofs.powerSeriesTailRadius x n
  have hradius := ExpProofs.powerSeriesTailRadius_nonneg_of_ratioBound
    x (ExpProofs.expPowerSeries_ratio_bound x) n
  constructor <;> grind [Rat.sub_eq_add_neg]

private theorem reciprocalNegativeExpRaw_inverse_prefix_mem
    (a : Rat) (ha : 0 <= a) (n : Nat) :
    ((reciprocalNegativeExpRaw a).compute n).lo <=
        1 / FiniteExponentialProduct.factorialPrefix
          (expPowerSeriesTerms a n) a /\
      1 / FiniteExponentialProduct.factorialPrefix
          (expPowerSeriesTerms a n) a <=
        ((reciprocalNegativeExpRaw a).compute n).hi := by
  let terms := expPowerSeriesTerms a n
  let p := FiniteExponentialProduct.factorialPrefix terms a
  have hterms : 2 <= terms := by
    dsimp [terms]
    unfold expPowerSeriesTerms
    omega
  have hprefixLower : 1 + a <= p := by
    dsimp [p]
    exact FiniteExponentialProduct.factorialPrefix_ge_one_add
      ha terms hterms
  have hprefixPos : 0 < p := by grind
  have hcenter := expPowerSeries_literal_prefix_mem a n
  change ((expPowerSeries a).compute n).lo <= p /\
      p <= ((expPowerSeries a).compute n).hi at hcenter
  have hmaxLe :
      maxRat2 ((expPowerSeries a).compute n).lo (1 + a) <= p := by
    unfold maxRat2
    by_cases h : ((expPowerSeries a).compute n).lo <= 1 + a
    · simp [h, hprefixLower]
    · simp [h, hcenter.1]
  have hmaxPos :
      0 < maxRat2 ((expPowerSeries a).compute n).lo (1 + a) := by
    unfold maxRat2
    by_cases h : ((expPowerSeries a).compute n).lo <= 1 + a
    · simp [h]
      grind
    · simp [h]
      grind
  have hhiPos : 0 < ((expPowerSeries a).compute n).hi := by
    grind
  unfold reciprocalNegativeExpRaw
  rw [RealCompute.positiveReciprocal_compute
    (expPowerSeries a) (1 + a) (by grind) n]
  dsimp [terms, p]
  constructor
  · exact RealCompute.one_div_antitone_of_pos hprefixPos hcenter.2
  · exact RealCompute.one_div_antitone_of_pos hmaxPos hmaxLe

private theorem qabs_opposite_prefix_sub_inverse_le_product_error
    (a : Rat) (ha : 0 <= a) (terms : Nat) (hterms : 2 <= terms) :
    qabs
        (FiniteExponentialProduct.factorialPrefix terms (-a) -
          1 / FiniteExponentialProduct.factorialPrefix terms a) <=
      qabs
        (FiniteExponentialProduct.factorialPrefix terms a *
          FiniteExponentialProduct.factorialPrefix terms (-a) - 1) := by
  let positive := FiniteExponentialProduct.factorialPrefix terms a
  let negative := FiniteExponentialProduct.factorialPrefix terms (-a)
  have hpositiveOne : 1 <= positive := by
    have h := FiniteExponentialProduct.factorialPrefix_ge_one_add
      ha terms hterms
    dsimp [positive]
    grind
  have hpositivePos : 0 < positive := by grind
  have hinvNonneg : 0 <= 1 / positive := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt ((Rat.inv_pos).2 hpositivePos))
  have hinvLeOne : 1 / positive <= 1 := by
    exact Rat.le_trans
      (RealCompute.one_div_antitone_of_pos
        (by decide +kernel : (0 : Rat) < 1) hpositiveOne)
      (by decide +kernel : (1 : Rat) / 1 <= 1)
  have hid :
      negative - 1 / positive =
        (positive * negative - 1) * (1 / positive) := by
    have hne : positive ≠ 0 := Rat.ne_of_gt hpositivePos
    grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm,
      Rat.div_def, Rat.mul_inv_cancel _ hne]
  rw [hid, qabs_mul, qabs_eq_self_of_nonneg hinvNonneg]
  calc
    qabs (positive * negative - 1) * (1 / positive) <=
        qabs (positive * negative - 1) * 1 :=
      Rat.mul_le_mul_of_nonneg_left hinvLeOne
        (qabs_nonneg (positive * negative - 1))
    _ = qabs (positive * negative - 1) := by
      rw [Rat.mul_one]

private def reciprocalExpComparisonStage
    (a : Rat) (eps : QPos) (n : Nat) : Nat :=
  n + FiniteExponentialProduct.scheduledProductStage a eps

private def reciprocalExpComparisonTerms
    (a : Rat) (eps : QPos) (n : Nat) : Nat :=
  expPowerSeriesTerms a (reciprocalExpComparisonStage a eps n)

private def negativePrefixCandidate
    (a : Rat) (eps : QPos) (n : Nat) : Rat :=
  FiniteExponentialProduct.factorialPrefix
    (reciprocalExpComparisonTerms a eps n) (-a)

private def inversePositivePrefixCandidate
    (a : Rat) (eps : QPos) (n : Nat) : Rat :=
  1 / FiniteExponentialProduct.factorialPrefix
    (reciprocalExpComparisonTerms a eps n) a

private theorem reciprocalExpComparisonCandidates
    (a : Rat) (ha : 0 <= a) (eps : QPos) (n : Nat) :
    (((expPowerSeries (-a)).compute n).lo <=
        negativePrefixCandidate a eps n /\
      negativePrefixCandidate a eps n <=
        ((expPowerSeries (-a)).compute n).hi) /\
    (((reciprocalNegativeExpRaw a).compute n).lo <=
        inversePositivePrefixCandidate a eps n /\
      inversePositivePrefixCandidate a eps n <=
        ((reciprocalNegativeExpRaw a).compute n).hi) /\
    qabs
        (negativePrefixCandidate a eps n -
          inversePositivePrefixCandidate a eps n) <= eps.val := by
  let stage := reciprocalExpComparisonStage a eps n
  let terms := reciprocalExpComparisonTerms a eps n
  have hnstage : n <= stage := by
    dsimp [stage, reciprocalExpComparisonStage]
    omega
  have htermsEqNeg : expPowerSeriesTerms (-a) stage = terms := by
    dsimp [terms, reciprocalExpComparisonTerms]
    rw [ExpProofs.expPowerSeriesTerms_neg]
  have htermsScheduled :
      FiniteExponentialProduct.scheduledProductStage a eps <= terms := by
    dsimp [terms, reciprocalExpComparisonTerms, stage,
      reciprocalExpComparisonStage]
    unfold expPowerSeriesTerms
    omega
  have htermsTwo : 2 <= terms := by
    dsimp [terms, reciprocalExpComparisonTerms]
    unfold expPowerSeriesTerms
    omega
  have hnegAtStage := expPowerSeries_literal_prefix_mem (-a) stage
  rw [htermsEqNeg] at hnegAtStage
  have hnegValid := ExpProofs.expPowerSeries_valid (-a)
  have hnegNested := hnegValid.2.1 n stage hnstage
  have hnegAtN :
      ((expPowerSeries (-a)).compute n).lo <=
          FiniteExponentialProduct.factorialPrefix terms (-a) /\
        FiniteExponentialProduct.factorialPrefix terms (-a) <=
          ((expPowerSeries (-a)).compute n).hi :=
    ⟨Rat.le_trans hnegNested.1 hnegAtStage.1,
      Rat.le_trans hnegAtStage.2 hnegNested.2.2⟩
  have hinvAtStage := reciprocalNegativeExpRaw_inverse_prefix_mem
    a ha stage
  change
      ((reciprocalNegativeExpRaw a).compute stage).lo <=
          1 / FiniteExponentialProduct.factorialPrefix terms a /\
        1 / FiniteExponentialProduct.factorialPrefix terms a <=
          ((reciprocalNegativeExpRaw a).compute stage).hi at hinvAtStage
  have hinvValid := reciprocalNegativeExpRaw_valid a ha
  have hinvNested := hinvValid.2.1 n stage hnstage
  have hinvAtN :
      ((reciprocalNegativeExpRaw a).compute n).lo <=
          1 / FiniteExponentialProduct.factorialPrefix terms a /\
        1 / FiniteExponentialProduct.factorialPrefix terms a <=
          ((reciprocalNegativeExpRaw a).compute n).hi :=
    ⟨Rat.le_trans hinvNested.1 hinvAtStage.1,
      Rat.le_trans hinvAtStage.2 hinvNested.2.2⟩
  have hproduct :=
    FiniteExponentialProduct.factorialPrefix_mul_opposite_later_close_to_one
      ha (by rw [qabs_eq_self_of_nonneg ha]; exact Rat.le_refl)
      eps terms htermsScheduled
  have hdistance := Rat.le_trans
    (qabs_opposite_prefix_sub_inverse_le_product_error
      a ha terms htermsTwo) hproduct
  change
    (((expPowerSeries (-a)).compute n).lo <=
        FiniteExponentialProduct.factorialPrefix terms (-a) /\
      FiniteExponentialProduct.factorialPrefix terms (-a) <=
        ((expPowerSeries (-a)).compute n).hi) /\
    (((reciprocalNegativeExpRaw a).compute n).lo <=
        1 / FiniteExponentialProduct.factorialPrefix terms a /\
      1 / FiniteExponentialProduct.factorialPrefix terms a <=
        ((reciprocalNegativeExpRaw a).compute n).hi) /\
    qabs
        (FiniteExponentialProduct.factorialPrefix terms (-a) -
          1 / FiniteExponentialProduct.factorialPrefix terms a) <= eps.val
  exact ⟨hnegAtN, hinvAtN, hdistance⟩

/-- The positive reciprocal construction is the same represented number as
the factorial-series evaluator at the opposite input.  The proof uses a
future finite prefix from each nested box and the scheduled product estimate;
it does not invoke a completed infinite series. -/
theorem expPowerSeries_neg_equiv_reciprocalNegativeExpRaw
    (a : Rat) (ha : 0 <= a) :
    (expPowerSeries (-a)).Equiv (reciprocalNegativeExpRaw a) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  rw [RealCompute.compareAt_overlap_iff]
  constructor
  · by_cases hle :
        ((expPowerSeries (-a)).compute n).lo <=
          ((reciprocalNegativeExpRaw a).compute n).hi
    · exact hle
    · have hstrict :
          ((reciprocalNegativeExpRaw a).compute n).hi <
            ((expPowerSeries (-a)).compute n).lo := by
        grind
      let gap : Rat :=
        ((expPowerSeries (-a)).compute n).lo -
          ((reciprocalNegativeExpRaw a).compute n).hi
      have hgap : 0 < gap := by
        dsimp [gap]
        grind [Rat.sub_eq_add_neg]
      let eps : QPos :=
        ⟨gap / 2, by
          rw [Rat.div_def]
          exact Rat.mul_pos hgap (by decide +kernel)⟩
      let p := negativePrefixCandidate a eps n
      let q := inversePositivePrefixCandidate a eps n
      have hcert := reciprocalExpComparisonCandidates a ha eps n
      have hgapLe : gap <= p - q := by
        dsimp [p, q]
        exact calc
          gap = ((expPowerSeries (-a)).compute n).lo -
              ((reciprocalNegativeExpRaw a).compute n).hi := rfl
          _ <= negativePrefixCandidate a eps n -
              inversePositivePrefixCandidate a eps n := by
            grind [hcert.1.1, hcert.2.1.2, Rat.sub_eq_add_neg]
      have hsmall : qabs (p - q) <= gap / 2 := by
        exact hcert.2.2
      have hself := self_le_qabs (p - q)
      have : gap <= gap / 2 :=
        Rat.le_trans hgapLe (Rat.le_trans hself hsmall)
      have hhalf : gap / 2 < gap := by
        simpa [Rat.div_def] using
          Rat.mul_lt_mul_of_pos_left
            (by decide +kernel : (1 : Rat) / 2 < 1) hgap
      grind
  · by_cases hle :
        ((reciprocalNegativeExpRaw a).compute n).lo <=
          ((expPowerSeries (-a)).compute n).hi
    · exact hle
    · have hstrict :
          ((expPowerSeries (-a)).compute n).hi <
            ((reciprocalNegativeExpRaw a).compute n).lo := by
        grind
      let gap : Rat :=
        ((reciprocalNegativeExpRaw a).compute n).lo -
          ((expPowerSeries (-a)).compute n).hi
      have hgap : 0 < gap := by
        dsimp [gap]
        grind [Rat.sub_eq_add_neg]
      let eps : QPos :=
        ⟨gap / 2, by
          rw [Rat.div_def]
          exact Rat.mul_pos hgap (by decide +kernel)⟩
      let p := negativePrefixCandidate a eps n
      let q := inversePositivePrefixCandidate a eps n
      have hcert := reciprocalExpComparisonCandidates a ha eps n
      have hgapLe : gap <= q - p := by
        dsimp [p, q]
        exact calc
          gap = ((reciprocalNegativeExpRaw a).compute n).lo -
              ((expPowerSeries (-a)).compute n).hi := rfl
          _ <= inversePositivePrefixCandidate a eps n -
              negativePrefixCandidate a eps n := by
            grind [hcert.2.1.1, hcert.1.2, Rat.sub_eq_add_neg]
      have hsmall : qabs (p - q) <= gap / 2 := by
        exact hcert.2.2
      have hdiff : q - p = -(p - q) := by
        grind [Rat.sub_eq_add_neg]
      have hself := self_le_qabs (q - p)
      have habs : qabs (q - p) = qabs (p - q) := by
        rw [hdiff, qabs_neg]
      have : gap <= gap / 2 := by
        calc
          gap <= q - p := hgapLe
          _ <= qabs (q - p) := hself
          _ = qabs (p - q) := habs
          _ <= gap / 2 := hsmall
      have hhalf : gap / 2 < gap := by
        simpa [Rat.div_def] using
          Rat.mul_lt_mul_of_pos_left
            (by decide +kernel : (1 : Rat) / 2 < 1) hgap
      grind

theorem reciprocalNegativeExpRaw_equiv_expPowerSeries_neg
    (a : Rat) (ha : 0 <= a) :
    (reciprocalNegativeExpRaw a).Equiv (expPowerSeries (-a)) :=
  RealCompute.equiv_symm (expPowerSeries_neg_equiv_reciprocalNegativeExpRaw a ha)

theorem reciprocalNegativeExpRaw_compute_hi_le_one_div_one_add
    (a : Rat) (ha : 0 <= a) (n : Nat) :
    ((reciprocalNegativeExpRaw a).compute n).hi <= 1 / (1 + a) := by
  unfold reciprocalNegativeExpRaw
  exact RealCompute.positiveReciprocal_compute_hi_le
    (expPowerSeries a) (1 + a) (by grind) n

theorem reciprocalNegativeExpRaw_compute_hi_le_one_div
    (a : Rat) (ha : 0 < a) (n : Nat) :
    ((reciprocalNegativeExpRaw a).compute n).hi <= 1 / a := by
  have hmain := reciprocalNegativeExpRaw_compute_hi_le_one_div_one_add
    a (Rat.le_of_lt ha) n
  have hrecip := RealCompute.one_div_antitone_of_pos ha (by grind : a <= 1 + a)
  exact Rat.le_trans hmain hrecip

theorem reciprocalNegativeExpRaw_compute_lo_nonneg
    (a : Rat) (ha : 0 <= a) (n : Nat) :
    0 <= ((reciprocalNegativeExpRaw a).compute n).lo := by
  unfold reciprocalNegativeExpRaw
  rw [RealCompute.positiveReciprocal_compute
    (expPowerSeries a) (1 + a) (by grind) n]
  have hhi : 0 < ((expPowerSeries a).compute n).hi := by
    have hbound := ExpProofs.expPowerSeries_compute_hi_ge_one_add a ha n
    grind
  rw [Rat.div_def]
  exact Rat.mul_nonneg (by decide +kernel)
    (Rat.le_of_lt ((Rat.inv_pos).2 hhi))

theorem reciprocalNegativeExpRaw_compute_lo_pos
    (a : Rat) (ha : 0 <= a) (n : Nat) :
    0 < ((reciprocalNegativeExpRaw a).compute n).lo := by
  unfold reciprocalNegativeExpRaw
  rw [RealCompute.positiveReciprocal_compute
    (expPowerSeries a) (1 + a) (by grind) n]
  have hhi : 0 < ((expPowerSeries a).compute n).hi := by
    have hbound := ExpProofs.expPowerSeries_compute_hi_ge_one_add a ha n
    grind
  rw [Rat.div_def]
  exact Rat.mul_pos (by decide +kernel)
    ((Rat.inv_pos).2 hhi)

/-- The Gaussian-shaped reciprocal presentation `1 / exp(x^2)`. -/
def reciprocalGaussianRaw (x : Rat) : RealCompute :=
  reciprocalNegativeExpRaw (x * x)

theorem reciprocalGaussianRaw_valid (x : Rat) :
    (reciprocalGaussianRaw x).Valid := by
  apply reciprocalNegativeExpRaw_valid
  exact rat_square_nonneg_basic x

theorem reciprocalGaussianRaw_compute_lo_pos (x : Rat) (n : Nat) :
    0 < ((reciprocalGaussianRaw x).compute n).lo := by
  unfold reciprocalGaussianRaw
  exact reciprocalNegativeExpRaw_compute_lo_pos
    (x * x) (rat_square_nonneg_basic x) n

/-- A finite rational lower bound for every reciprocal-Gaussian box on the
nonnegative interval `[0, radius]`.  The extra `1` makes positivity immediate
while retaining a stage-independent denominator. -/
def reciprocalGaussianUniformPositiveLowerBound (radius : Rat) : Rat :=
  1 / (1 + 3 *
    RationalMajorant.factorialSeriesFiniteBound (radius * radius))

theorem reciprocalGaussianUniformPositiveLowerBound_pos
    (radius : Rat) :
    0 < reciprocalGaussianUniformPositiveLowerBound radius := by
  have hsquare : 0 <= radius * radius := rat_square_nonneg_basic radius
  have hbound :=
    RationalMajorant.factorialSeriesFiniteBound_nonneg hsquare
  unfold reciprocalGaussianUniformPositiveLowerBound
  rw [Rat.div_def]
  exact Rat.mul_pos (by decide +kernel)
    ((Rat.inv_pos).2 (by grind))

/-- The lower endpoint of every reciprocal-Gaussian approximation box is
bounded below by one explicit positive rational depending only on the
ambient nonnegative radius, not on the point or approximation stage. -/
theorem reciprocalGaussianUniformPositiveLowerBound_le_compute_lo
    {x radius : Rat} (hx : 0 <= x) (hxr : x <= radius) (n : Nat) :
    reciprocalGaussianUniformPositiveLowerBound radius <=
      ((reciprocalGaussianRaw x).compute n).lo := by
  have hsquare : x * x <= radius * radius :=
    rat_mul_le_mul_of_nonneg hx hxr hx hxr
  have hexpUpper :=
    ExpProofs.expPowerSeries_compute_hi_le_three_mul_factorialSeriesFiniteBound
      (x := x * x) (C := radius * radius)
      (rat_square_nonneg_basic x) hsquare n
  have hexpPos : 0 < ((expPowerSeries (x * x)).compute n).hi := by
    have hlower := ExpProofs.expPowerSeries_compute_hi_ge_one_add
      (x * x) (rat_square_nonneg_basic x) n
    have hsquareNonneg := rat_square_nonneg_basic x
    grind
  have hdenom :
      ((expPowerSeries (x * x)).compute n).hi <=
        1 + 3 * RationalMajorant.factorialSeriesFiniteBound
          (radius * radius) := by
    grind
  unfold reciprocalGaussianRaw reciprocalNegativeExpRaw
  rw [RealCompute.positiveReciprocal_compute
    (expPowerSeries (x * x)) (1 + x * x)
      (by have hsquareNonneg := rat_square_nonneg_basic x; grind) n]
  unfold reciprocalGaussianUniformPositiveLowerBound
  exact RealCompute.one_div_antitone_of_pos hexpPos hdenom

theorem reciprocalGaussianRaw_compute_width_le_geometric
    (x : Rat) (n : Nat) :
    ((reciprocalGaussianRaw x).compute n).width <=
      ((4 * qabs (ExpProofs.powerSeriesTermAtTerms (x * x)
          (expPowerSeriesTerms (x * x) 0))) /
        ((1 + x * x) * (1 + x * x))) * ((1 : Rat) / 2) ^ n := by
  unfold reciprocalGaussianRaw
  exact reciprocalNegativeExpRaw_compute_width_le_geometric
    (x * x) (rat_square_nonneg_basic x) n

/-- The reciprocal Gaussian and the negative-input factorial exponential are
now connected as representations, closing the semantic bridge used by the
bounded Gaussian construction. -/
theorem reciprocalGaussianRaw_equiv_expPowerSeries_neg_square (x : Rat) :
    (reciprocalGaussianRaw x).Equiv (expPowerSeries (-(x * x))) := by
  unfold reciprocalGaussianRaw
  exact reciprocalNegativeExpRaw_equiv_expPowerSeries_neg
    (x * x) (rat_square_nonneg_basic x)

theorem expPowerSeries_neg_square_equiv_reciprocalGaussianRaw (x : Rat) :
    (expPowerSeries (-(x * x))).Equiv (reciprocalGaussianRaw x) :=
  RealCompute.equiv_symm
    (reciprocalGaussianRaw_equiv_expPowerSeries_neg_square x)

/-- The factorial-series Gaussian is even as a represented raw function. -/
theorem expPowerSeries_neg_square_even (x : Rat) :
    (expPowerSeries (-((-x) * (-x)))).Equiv
      (expPowerSeries (-(x * x))) := by
  have harg : -((-x) * (-x)) = -(x * x) := by
    grind
  rw [harg]
  exact RealCompute.equiv_refl _
    (ExpProofs.expPowerSeries_valid (-(x * x)))

theorem reciprocalGaussianRaw_compute_hi_le_reciprocalSquare
    (x : Rat) (hx : 0 < x) (n : Nat) :
    ((reciprocalGaussianRaw x).compute n).hi <= 1 / (x * x) := by
  apply reciprocalNegativeExpRaw_compute_hi_le_one_div
  exact Rat.mul_pos hx hx

/-- Representation-independent Gaussian domination: for positive rational
`x`, the negative-input exponential lies below the exact rational
`1 / x^2` in the raw-real order. -/
theorem expPowerSeries_neg_square_le_reciprocalSquareRaw
    (x : Rat) (hx : 0 < x) :
    (expPowerSeries (-(x * x))).Le (RealCompute.ofRat (1 / (x * x))) := by
  have hexpValid := ExpProofs.expPowerSeries_valid (-(x * x))
  have hrecipValid := reciprocalGaussianRaw_valid x
  have hequiv := expPowerSeries_neg_square_equiv_reciprocalGaussianRaw x
  have hexpLeRecip := RealCompute.le_of_equiv hexpValid hrecipValid hequiv
  have hrecipLeExact :
      (reciprocalGaussianRaw x).Le (RealCompute.ofRat (1 / (x * x))) := by
    intro n m
    have horder := RealCompute.interval_order_of_valid
      (reciprocalGaussianRaw x) hrecipValid n
    have hhi := reciprocalGaussianRaw_compute_hi_le_reciprocalSquare x hx n
    change ((reciprocalGaussianRaw x).compute n).lo <= 1 / (x * x)
    exact Rat.le_trans horder hhi
  exact RealCompute.le_trans hrecipValid hexpLeRecip hrecipLeExact

/-- A rational range box enclosing the reciprocal Gaussian presentation on a
positive cell.  Its upper endpoint is the reciprocal square at the left edge,
independently of the evaluator stage. -/
def reciprocalGaussianPositiveCellRange
    {a b : Rat} (C : RationalSubinterval a b) : QInterval :=
  { lo := 0, hi := 1 / (C.lower * C.lower) }

theorem reciprocalGaussianPositiveCellRange_contains
    {a b : Rat} (C : RationalSubinterval a b)
    (hlower : 0 < C.lower) (x : Rat)
    (hx : C.lower <= x /\ x <= C.upper) (n : Nat) :
    (reciprocalGaussianPositiveCellRange C).ContainsInterval
      ((reciprocalGaussianRaw x).compute n) := by
  have hxpos : 0 < x := by
    grind
  have hsquare : C.lower * C.lower <= x * x :=
    rat_mul_le_mul_of_nonneg
      (Rat.le_of_lt hlower) hx.1
      (Rat.le_of_lt hlower) hx.1
  have hrecip := RealCompute.one_div_antitone_of_pos
    (Rat.mul_pos hlower hlower) hsquare
  constructor
  · exact reciprocalNegativeExpRaw_compute_lo_nonneg
      (x * x) (rat_square_nonneg_basic x) n
  · exact Rat.le_trans
      (reciprocalGaussianRaw_compute_hi_le_reciprocalSquare x hxpos n)
      hrecip

/-! ## Positive reciprocal-tail compactification -/

/-- Finite data defining a positive half-line tail by the rational reciprocal
chart `x = cutoff / t`.  The compact density includes its removable value at
`t = 0`, so its computation is an ordinary certified integral on `[0,1]`.
The fold identity is required only where division by `t` is meaningful. -/
structure PositiveReciprocalTailCompactification
    (kernel compactDensity : Rat -> Rat) (cutoff : Rat) where
  cutoff_pos : 0 < cutoff
  fold_agrees : forall t, 0 < t -> t <= 1 ->
    compactDensity t =
      (cutoff / (t * t)) * kernel (cutoff / t)
  construction : Integral.CandidateConstructionFor
    (FunctionOnInterval.exactRat compactDensity 0 1)

namespace PositiveReciprocalTailCompactification

/-- The compact `[0,1]` computation representing the supplied positive tail
chart. -/
def tailIntegral
    {kernel compactDensity : Rat -> Rat} {cutoff : Rat}
    (C : PositiveReciprocalTailCompactification
      kernel compactDensity cutoff) : RealCompute :=
  Integral.candidateValueFor
    (FunctionOnInterval.exactRat compactDensity 0 1) C.construction

theorem tailIntegral_valid
    {kernel compactDensity : Rat -> Rat} {cutoff : Rat}
    (C : PositiveReciprocalTailCompactification
      kernel compactDensity cutoff) :
    C.tailIntegral.Valid :=
  Integral.candidateValueFor_valid _ C.construction

end PositiveReciprocalTailCompactification

/-! ## Exact reciprocal-square instance -/

def reciprocalSquareKernel (x : Rat) : Rat :=
  1 / (x * x)

def reciprocalSquareTailCompactDensity (cutoff : Rat) (_t : Rat) : Rat :=
  1 / cutoff

/-- The Jacobian-weighted reciprocal-square kernel is exactly constant under
`x = cutoff / t`.  This is the finite rational change-of-variables identity
behind the tail formula. -/
theorem reciprocalSquareTail_fold_agrees
    (cutoff t : Rat) (hcutoff : 0 < cutoff) (ht : 0 < t) :
    reciprocalSquareTailCompactDensity cutoff t =
      (cutoff / (t * t)) * reciprocalSquareKernel (cutoff / t) := by
  have hcne : cutoff ≠ 0 := Rat.ne_of_gt hcutoff
  have htne : t ≠ 0 := Rat.ne_of_gt ht
  unfold reciprocalSquareTailCompactDensity reciprocalSquareKernel
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have httne : t * t ≠ 0 := Rat.ne_of_gt (Rat.mul_pos ht ht)
  have hquotpos : 0 < cutoff * t⁻¹ :=
    Rat.mul_pos hcutoff ((Rat.inv_pos).2 ht)
  have hquotne : cutoff * t⁻¹ ≠ 0 := Rat.ne_of_gt hquotpos
  have hquotsqne :
      (cutoff * t⁻¹) * (cutoff * t⁻¹) ≠ 0 :=
    Rat.ne_of_gt (Rat.mul_pos hquotpos hquotpos)
  have htcancel : t * t⁻¹ = 1 := Rat.mul_inv_cancel t htne
  have hccancel : cutoff * cutoff⁻¹ = 1 :=
    Rat.mul_inv_cancel cutoff hcne
  have httcancel : (t * t) * (t * t)⁻¹ = 1 :=
    Rat.mul_inv_cancel (t * t) httne
  have hquotcancel :
      ((cutoff * t⁻¹) * (cutoff * t⁻¹)) *
          ((cutoff * t⁻¹) * (cutoff * t⁻¹))⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hquotsqne
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_rev]

def reciprocalSquarePositiveTailCompactification
    (cutoff : Rat) (hcutoff : 0 < cutoff) :
    PositiveReciprocalTailCompactification reciprocalSquareKernel
      (reciprocalSquareTailCompactDensity cutoff) cutoff where
  cutoff_pos := hcutoff
  fold_agrees := by
    intro t ht _ht1
    exact reciprocalSquareTail_fold_agrees cutoff t hcutoff ht
  construction :=
    (Integral.constantMonotoneCandidateConstructionFor (1 / cutoff) 0 1).construction

def reciprocalSquarePositiveTailRaw
    (cutoff : Rat) (hcutoff : 0 < cutoff) : RealCompute :=
  (reciprocalSquarePositiveTailCompactification cutoff hcutoff).tailIntegral

theorem reciprocalSquarePositiveTailRaw_compute
    (cutoff : Rat) (hcutoff : 0 < cutoff) (stage : Nat) :
    (reciprocalSquarePositiveTailRaw cutoff hcutoff).compute stage =
      { lo := 1 / cutoff, hi := 1 / cutoff } := by
  unfold reciprocalSquarePositiveTailRaw
    PositiveReciprocalTailCompactification.tailIntegral
    reciprocalSquarePositiveTailCompactification
    Integral.constantMonotoneCandidateConstructionFor Integral.candidateValueFor
  simp [RealCompute.ofRat]
  grind [Rat.sub_eq_add_neg]

theorem reciprocalSquarePositiveTailRaw_equiv_ofRat
    (cutoff : Rat) (hcutoff : 0 < cutoff) :
    (reciprocalSquarePositiveTailRaw cutoff hcutoff).Equiv
      (RealCompute.ofRat (1 / cutoff)) := by
  intro stage
  apply (RealCompute.compareAt_overlap_iff _ _ stage stage).2
  rw [reciprocalSquarePositiveTailRaw_compute]
  exact ⟨Rat.le_refl, Rat.le_refl⟩

theorem reciprocalSquarePositiveTailRaw_valid
    (cutoff : Rat) (hcutoff : 0 < cutoff) :
    (reciprocalSquarePositiveTailRaw cutoff hcutoff).Valid :=
  (reciprocalSquarePositiveTailCompactification cutoff hcutoff).tailIntegral_valid

/-- The two equal reciprocal-square tails outside `[-cutoff, cutoff]`. -/
def reciprocalSquareSymmetricTailRaw
    (cutoff : Rat) (hcutoff : 0 < cutoff) : RealCompute :=
  RealCompute.scaleRat 2 (reciprocalSquarePositiveTailRaw cutoff hcutoff)

theorem reciprocalSquareSymmetricTailRaw_valid
    (cutoff : Rat) (hcutoff : 0 < cutoff) :
    (reciprocalSquareSymmetricTailRaw cutoff hcutoff).Valid :=
  RealCompute.scaleRat_valid
    (reciprocalSquarePositiveTailRaw_valid cutoff hcutoff)

theorem reciprocalSquareSymmetricTailRaw_compute
    (cutoff : Rat) (hcutoff : 0 < cutoff) (stage : Nat) :
  (reciprocalSquareSymmetricTailRaw cutoff hcutoff).compute stage =
      { lo := 2 / cutoff, hi := 2 / cutoff } := by
  unfold reciprocalSquareSymmetricTailRaw RealCompute.scaleRat
    RealCompute.scaleRatCompute
  simp only
  rw [if_pos (by decide +kernel : (0 : Rat) <= 2),
    reciprocalSquarePositiveTailRaw_compute]
  grind [Rat.div_def, Rat.mul_assoc]

theorem reciprocalSquareSymmetricTailRaw_equiv_ofRat
    (cutoff : Rat) (hcutoff : 0 < cutoff) :
    (reciprocalSquareSymmetricTailRaw cutoff hcutoff).Equiv
      (RealCompute.ofRat (2 / cutoff)) := by
  intro stage
  apply (RealCompute.compareAt_overlap_iff _ _ stage stage).2
  rw [reciprocalSquareSymmetricTailRaw_compute]
  exact ⟨Rat.le_refl, Rat.le_refl⟩

/-! ## Raw-kernel domination by the compactified tail -/

/-- A complete finite certificate that a nonnegative raw kernel on a positive
half-line is pointwise dominated by `1/x^2`.  Its associated continuous tail
budget is the exact compactified raw `1/cutoff` above. -/
structure ReciprocalSquareTailCertificate
    (kernel : Rat -> RealCompute) (cutoff : Rat) where
  cutoff_pos : 0 < cutoff
  kernel_valid : forall x, cutoff <= x -> (kernel x).Valid
  kernel_nonnegative : forall x, cutoff <= x -> forall stage,
    0 <= ((kernel x).compute stage).lo
  kernel_upper : forall x, cutoff <= x -> forall stage,
    ((kernel x).compute stage).hi <= reciprocalSquareKernel x

namespace ReciprocalSquareTailCertificate

/-- Exact positive-tail budget supplied by a reciprocal-square domination
certificate. -/
def positiveTailBudgetRaw
    {kernel : Rat -> RealCompute} {cutoff : Rat}
    (C : ReciprocalSquareTailCertificate kernel cutoff) : RealCompute :=
  reciprocalSquarePositiveTailRaw cutoff C.cutoff_pos

theorem positiveTailBudgetRaw_valid
    {kernel : Rat -> RealCompute} {cutoff : Rat}
    (C : ReciprocalSquareTailCertificate kernel cutoff) :
    C.positiveTailBudgetRaw.Valid :=
  reciprocalSquarePositiveTailRaw_valid cutoff C.cutoff_pos

theorem positiveTailBudgetRaw_equiv_ofRat
    {kernel : Rat -> RealCompute} {cutoff : Rat}
    (C : ReciprocalSquareTailCertificate kernel cutoff) :
    C.positiveTailBudgetRaw.Equiv (RealCompute.ofRat (1 / cutoff)) :=
  reciprocalSquarePositiveTailRaw_equiv_ofRat cutoff C.cutoff_pos

/-- Symmetric budget obtained by reflecting the positive-tail certificate. -/
def symmetricTailBudgetRaw
    {kernel : Rat -> RealCompute} {cutoff : Rat}
    (C : ReciprocalSquareTailCertificate kernel cutoff) : RealCompute :=
  reciprocalSquareSymmetricTailRaw cutoff C.cutoff_pos

theorem symmetricTailBudgetRaw_valid
    {kernel : Rat -> RealCompute} {cutoff : Rat}
    (C : ReciprocalSquareTailCertificate kernel cutoff) :
    C.symmetricTailBudgetRaw.Valid :=
  reciprocalSquareSymmetricTailRaw_valid cutoff C.cutoff_pos

theorem symmetricTailBudgetRaw_equiv_ofRat
    {kernel : Rat -> RealCompute} {cutoff : Rat}
    (C : ReciprocalSquareTailCertificate kernel cutoff) :
    C.symmetricTailBudgetRaw.Equiv (RealCompute.ofRat (2 / cutoff)) :=
  reciprocalSquareSymmetricTailRaw_equiv_ofRat cutoff C.cutoff_pos

end ReciprocalSquareTailCertificate

/-! ## Representative-invariant tail certificates -/

/-- A value-level reciprocal-square tail certificate.  In contrast with
`ReciprocalSquareTailCertificate`, its inequalities use `RealCompute.Le`, so the
certificate can be transported across equivalent raw presentations without
claiming that equivalent algorithms have the same stagewise intervals. -/
structure RepresentedReciprocalSquareTailCertificate
    (kernel : Rat -> RealCompute) (cutoff : Rat) where
  cutoff_pos : 0 < cutoff
  kernel_valid : forall x, cutoff <= x -> (kernel x).Valid
  kernel_nonnegative : forall x, cutoff <= x ->
    (RealCompute.ofRat 0).Le (kernel x)
  kernel_upper : forall x, cutoff <= x ->
    (kernel x).Le (RealCompute.ofRat (reciprocalSquareKernel x))

namespace RepresentedReciprocalSquareTailCertificate

/-- Forget the same-stage bounds of a stagewise certificate while retaining
their representative-invariant order consequences. -/
theorem ofStagewise
    {kernel : Rat -> RealCompute} {cutoff : Rat}
    (C : ReciprocalSquareTailCertificate kernel cutoff) :
    RepresentedReciprocalSquareTailCertificate kernel cutoff where
  cutoff_pos := C.cutoff_pos
  kernel_valid := C.kernel_valid
  kernel_nonnegative := by
    intro x hx n m
    rw [RealCompute.ofRat_compute]
    have hlo := C.kernel_nonnegative x hx m
    have hordered := (C.kernel_valid x hx).1 m
    change 0 <= ((kernel x).compute m).hi - ((kernel x).compute m).lo at hordered
    dsimp
    grind [Rat.sub_eq_add_neg]
  kernel_upper := by
    intro x hx n m
    rw [RealCompute.ofRat_compute]
    have hhi := C.kernel_upper x hx n
    have hordered := (C.kernel_valid x hx).1 n
    change 0 <= ((kernel x).compute n).hi - ((kernel x).compute n).lo at hordered
    dsimp
    grind [Rat.sub_eq_add_neg]

/-- Transport a tail certificate from one raw presentation to an equivalent
one.  Only exact represented order is transported; no same-stage enclosure
is asserted for the target algorithm. -/
theorem transport
    {source target : Rat -> RealCompute} {cutoff : Rat}
    (C : RepresentedReciprocalSquareTailCertificate source cutoff)
    (target_valid : forall x, cutoff <= x -> (target x).Valid)
    (target_equiv_source : forall x, cutoff <= x ->
      (target x).Equiv (source x)) :
    RepresentedReciprocalSquareTailCertificate target cutoff where
  cutoff_pos := C.cutoff_pos
  kernel_valid := target_valid
  kernel_nonnegative := by
    intro x hx
    have hsourceTarget : (source x).Le (target x) :=
      RealCompute.le_of_equiv (C.kernel_valid x hx) (target_valid x hx)
        (RealCompute.equiv_symm (target_equiv_source x hx))
    exact RealCompute.le_trans (C.kernel_valid x hx)
      (C.kernel_nonnegative x hx) hsourceTarget
  kernel_upper := by
    intro x hx
    have htargetSource : (target x).Le (source x) :=
      RealCompute.le_of_equiv (target_valid x hx) (C.kernel_valid x hx)
        (target_equiv_source x hx)
    exact RealCompute.le_trans (C.kernel_valid x hx)
      htargetSource (C.kernel_upper x hx)

/-- Exact positive-tail budget associated with a represented certificate. -/
def positiveTailBudgetRaw
    {kernel : Rat -> RealCompute} {cutoff : Rat}
    (C : RepresentedReciprocalSquareTailCertificate kernel cutoff) : RealCompute :=
  reciprocalSquarePositiveTailRaw cutoff C.cutoff_pos

theorem positiveTailBudgetRaw_valid
    {kernel : Rat -> RealCompute} {cutoff : Rat}
    (C : RepresentedReciprocalSquareTailCertificate kernel cutoff) :
    C.positiveTailBudgetRaw.Valid :=
  reciprocalSquarePositiveTailRaw_valid cutoff C.cutoff_pos

theorem positiveTailBudgetRaw_equiv_ofRat
    {kernel : Rat -> RealCompute} {cutoff : Rat}
    (C : RepresentedReciprocalSquareTailCertificate kernel cutoff) :
    C.positiveTailBudgetRaw.Equiv (RealCompute.ofRat (1 / cutoff)) :=
  reciprocalSquarePositiveTailRaw_equiv_ofRat cutoff C.cutoff_pos

/-- Explicit budget for the two reflected tails. -/
def symmetricTailBudgetRaw
    {kernel : Rat -> RealCompute} {cutoff : Rat}
    (C : RepresentedReciprocalSquareTailCertificate kernel cutoff) : RealCompute :=
  reciprocalSquareSymmetricTailRaw cutoff C.cutoff_pos

theorem symmetricTailBudgetRaw_valid
    {kernel : Rat -> RealCompute} {cutoff : Rat}
    (C : RepresentedReciprocalSquareTailCertificate kernel cutoff) :
    C.symmetricTailBudgetRaw.Valid :=
  reciprocalSquareSymmetricTailRaw_valid cutoff C.cutoff_pos

theorem symmetricTailBudgetRaw_equiv_ofRat
    {kernel : Rat -> RealCompute} {cutoff : Rat}
    (C : RepresentedReciprocalSquareTailCertificate kernel cutoff) :
    C.symmetricTailBudgetRaw.Equiv (RealCompute.ofRat (2 / cutoff)) :=
  reciprocalSquareSymmetricTailRaw_equiv_ofRat cutoff C.cutoff_pos

end RepresentedReciprocalSquareTailCertificate

/-- The reciprocal presentation `1/exp(x^2)` is dominated by the continuous
reciprocal-square tail beyond every positive rational cutoff. -/
theorem reciprocalGaussianTailCertificate
    (cutoff : Rat) (hcutoff : 0 < cutoff) :
    ReciprocalSquareTailCertificate reciprocalGaussianRaw cutoff where
  cutoff_pos := hcutoff
  kernel_valid := by
    intro x _hx
    exact reciprocalGaussianRaw_valid x
  kernel_nonnegative := by
    intro x _hx stage
    exact reciprocalNegativeExpRaw_compute_lo_nonneg
      (x * x) (rat_square_nonneg_basic x) stage
  kernel_upper := by
    intro x hx stage
    unfold reciprocalSquareKernel
    exact reciprocalGaussianRaw_compute_hi_le_reciprocalSquare
      x (by grind) stage

/-- The factorial-series presentation of `exp (-x^2)` has the same explicit
reciprocal-square tail domination as the reciprocal presentation.  This is
the representative-invariant tail interface used by the full-line Gaussian
and heat-kernel route. -/
theorem expPowerSeriesGaussianRepresentedTailCertificate
    (cutoff : Rat) (hcutoff : 0 < cutoff) :
    RepresentedReciprocalSquareTailCertificate
      (fun x => expPowerSeries (-(x * x))) cutoff := by
  apply RepresentedReciprocalSquareTailCertificate.transport
    (RepresentedReciprocalSquareTailCertificate.ofStagewise
      (reciprocalGaussianTailCertificate cutoff hcutoff))
  · intro x _hx
    exact ExpProofs.expPowerSeries_valid (-(x * x))
  · intro x _hx
    exact expPowerSeries_neg_square_equiv_reciprocalGaussianRaw x

/-- The concrete executable two-sided tail budget for the factorial-series
Gaussian outside `[-cutoff, cutoff]`. -/
def expPowerSeriesGaussianSymmetricTailBudgetRaw
    (cutoff : Rat) (hcutoff : 0 < cutoff) : RealCompute :=
  RepresentedReciprocalSquareTailCertificate.symmetricTailBudgetRaw
    (expPowerSeriesGaussianRepresentedTailCertificate cutoff hcutoff)

theorem expPowerSeriesGaussianSymmetricTailBudgetRaw_valid
    (cutoff : Rat) (hcutoff : 0 < cutoff) :
    (expPowerSeriesGaussianSymmetricTailBudgetRaw cutoff hcutoff).Valid :=
  RepresentedReciprocalSquareTailCertificate.symmetricTailBudgetRaw_valid
    (expPowerSeriesGaussianRepresentedTailCertificate cutoff hcutoff)

/-- The computed symmetric budget represents exactly `2 / cutoff`. -/
theorem expPowerSeriesGaussianSymmetricTailBudgetRaw_equiv_ofRat
    (cutoff : Rat) (hcutoff : 0 < cutoff) :
    (expPowerSeriesGaussianSymmetricTailBudgetRaw cutoff hcutoff).Equiv
      (RealCompute.ofRat (2 / cutoff)) :=
  RepresentedReciprocalSquareTailCertificate.symmetricTailBudgetRaw_equiv_ofRat
    (expPowerSeriesGaussianRepresentedTailCertificate cutoff hcutoff)

theorem reciprocalGaussianTailCertificate_cell_range
    (cutoff : Rat) (hcutoff : 0 < cutoff)
    {a b : Rat} (C : RationalSubinterval a b)
    (hcell : cutoff <= C.lower) (x : Rat)
    (hx : C.lower <= x /\ x <= C.upper) (stage : Nat) :
    (reciprocalGaussianPositiveCellRange C).ContainsInterval
      ((reciprocalGaussianRaw x).compute stage) := by
  exact reciprocalGaussianPositiveCellRange_contains C
    (by grind) x hx stage

/-! ## Discrete compatibility and a symmetric vanishing envelope -/

/-- The older Gaussian-tail finite sum is literally the standard finite
zeta-two tail when its cutoff is a positive natural number. -/
theorem reciprocalSquareTailPartial_natCast_eq_zetaTwoFiniteTail
    (cutoff terms : Nat) :
    reciprocalSquareTailPartial (cutoff : Rat) terms =
      DirichletSeries.zetaTwoFiniteTail cutoff terms := by
  induction terms with
  | zero => rfl
  | succ terms ih =>
      rw [reciprocalSquareTailPartial_succ,
        DirichletSeries.zetaTwoFiniteTail_succ, ih]
      unfold DirichletSeries.zetaTwoTerm
      have hcast :
          (cutoff : Rat) + ((terms + 1 : Nat) : Rat) =
            (((cutoff + terms) + 1 : Nat) : Rat) := by
        exact_mod_cast (by omega : cutoff + (terms + 1) =
          (cutoff + terms) + 1)
      rw [hcast]
      rw [show 2 = 1 + 1 by omega, Rat.pow_succ, Rat.pow_succ]
      simp

/-- Every finite block of reciprocal-square unit-cell budgets beyond a
positive natural cutoff is bounded by the continuous compactified tail
`1 / cutoff`. -/
theorem reciprocalSquareTailPartial_natCast_le_one_div
    (cutoff terms : Nat) (hcutoff : 0 < cutoff) :
    reciprocalSquareTailPartial (cutoff : Rat) terms <=
      1 / (cutoff : Rat) := by
  rw [reciprocalSquareTailPartial_natCast_eq_zetaTwoFiniteTail]
  exact DirichletSeries.zetaTwoFiniteTail_le_tailBound
    cutoff hcutoff terms

/-- The symmetric reciprocal-square budget outside radius `stage+1`. -/
def symmetricReciprocalSquareTailRadius (stage : Nat) : Rat :=
  2 / (((stage + 1 : Nat) : Rat))

/-- A shrinking rational envelope for an as-yet-supplied symmetric tail.
It represents a vanishing error budget, not the Gaussian tail by itself. -/
def symmetricReciprocalSquareTailEnvelopeRaw : RealCompute where
  compute := fun stage =>
    { lo := 0, hi := symmetricReciprocalSquareTailRadius stage }

theorem symmetricReciprocalSquareTailRadius_nonneg (stage : Nat) :
    0 <= symmetricReciprocalSquareTailRadius stage := by
  unfold symmetricReciprocalSquareTailRadius
  rw [Rat.div_def]
  exact Rat.mul_nonneg (by decide +kernel)
    (Rat.le_of_lt ((Rat.inv_pos).2
      ((Rat.natCast_pos).2 (Nat.succ_pos stage))))

theorem symmetricReciprocalSquareTailRadius_antitone
    (stage next : Nat) (h : stage <= next) :
    symmetricReciprocalSquareTailRadius next <=
      symmetricReciprocalSquareTailRadius stage := by
  have hrecip := Series.one_div_nat_antitone_series
    (n := stage + 1) (m := next + 1)
    (Nat.succ_pos stage) (Nat.succ_pos next) (by omega)
  have hscaled := Rat.mul_le_mul_of_nonneg_left hrecip
    (by decide +kernel : (0 : Rat) <= 2)
  simpa [symmetricReciprocalSquareTailRadius, Rat.div_def,
    Rat.mul_assoc] using hscaled

theorem symmetricReciprocalSquareTailEnvelopeRaw_width (stage : Nat) :
    (symmetricReciprocalSquareTailEnvelopeRaw.compute stage).width =
      symmetricReciprocalSquareTailRadius stage := by
  unfold symmetricReciprocalSquareTailEnvelopeRaw QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem symmetricReciprocalSquareTailRadius_shrinks :
    ShrinksToZero symmetricReciprocalSquareTailRadius :=
  shrinksToZero_of_natOverSuccBound (C := 2) (by
    intro stage
    exact Rat.le_refl)

theorem symmetricReciprocalSquareTailEnvelopeRaw_valid :
    symmetricReciprocalSquareTailEnvelopeRaw.Valid := by
  constructor
  · intro stage
    rw [symmetricReciprocalSquareTailEnvelopeRaw_width]
    exact symmetricReciprocalSquareTailRadius_nonneg stage
  constructor
  · intro stage next h
    unfold symmetricReciprocalSquareTailEnvelopeRaw
    exact ⟨Rat.le_refl,
      symmetricReciprocalSquareTailRadius_nonneg next,
      symmetricReciprocalSquareTailRadius_antitone stage next h⟩
  · exact shrinksToZero_of_natOverSuccBound (C := 2) (by
      intro stage
      rw [symmetricReciprocalSquareTailEnvelopeRaw_width]
      exact Rat.le_refl)

theorem symmetricReciprocalSquareTailEnvelopeRaw_compute (stage : Nat) :
    symmetricReciprocalSquareTailEnvelopeRaw.compute stage =
      { lo := 0, hi := 2 / (((stage + 1 : Nat) : Rat)) } := by
  rfl

/-- At radius `stage+1`, the vanishing symmetric envelope contains the exact
compactified reciprocal-square tail at every evaluator precision. -/
theorem symmetricReciprocalSquareTailEnvelopeRaw_contains_compactifiedTail
    (stage precision : Nat) :
    (symmetricReciprocalSquareTailEnvelopeRaw.compute stage).ContainsInterval
      ((reciprocalSquareSymmetricTailRaw
        ((stage + 1 : Nat) : Rat)
        ((Rat.natCast_pos).2 (Nat.succ_pos stage))).compute precision) := by
  rw [symmetricReciprocalSquareTailEnvelopeRaw_compute,
    reciprocalSquareSymmetricTailRaw_compute]
  unfold QInterval.ContainsInterval
  exact ⟨symmetricReciprocalSquareTailRadius_nonneg stage, Rat.le_refl⟩

/-- The represented Gaussian certificate at growing cutoff `n+1`. -/
theorem expPowerSeriesGaussianStageTailCertificate (n : Nat) :
    RepresentedReciprocalSquareTailCertificate
      (fun x => expPowerSeries (-(x * x))) (((n + 1 : Nat) : Rat)) := by
  exact expPowerSeriesGaussianRepresentedTailCertificate _
    ((Rat.natCast_pos).2 (Nat.succ_pos n))

/-- The concrete symmetric Gaussian budget at cutoff `n+1` represents the
rational radius `2/(n+1)` used by full-line gluing. -/
theorem expPowerSeriesGaussianStageTailBudget_equiv_radius (n : Nat) :
    (expPowerSeriesGaussianSymmetricTailBudgetRaw
      (((n + 1 : Nat) : Rat))
      ((Rat.natCast_pos).2 (Nat.succ_pos n))).Equiv
        (RealCompute.ofRat (symmetricReciprocalSquareTailRadius n)) := by
  exact expPowerSeriesGaussianSymmetricTailBudgetRaw_equiv_ofRat _
    ((Rat.natCast_pos).2 (Nat.succ_pos n))

/-! ## Anchor-free full-line Gaussian gluing -/

/-- Finite data sufficient to glue growing symmetric Gaussian integral
boxes. `candidate.compute n` is intended to be a bounded integral box on
`[-(n+1), n+1]`, already evaluated finely enough that its own width shrinks.
The `future_contained` field is the remaining function-specific annular
comparison: every later bounded integral lies in the earlier box widened by
the certified symmetric tail budget `2/(n+1)`.

The structure does not postulate an improper integral or a completed real
limit. The theorem `stabilizedRaw_valid` below constructs the full-line raw
directly from finite intersections. -/
structure GaussianFullLineGluingData where
  candidate : RealCompute
  candidate_ordered : forall n,
    (candidate.compute n).lo <= (candidate.compute n).hi
  candidate_widths_shrink : RealCompute.WidthsShrinkToZero candidate.compute
  future_contained : forall k n, k <= n ->
    (QInterval.expand (candidate.compute k)
      (symmetricReciprocalSquareTailRadius k)).ContainsInterval
        (candidate.compute n)

namespace GaussianFullLineGluingData

/-- The direct full-line evaluator intersects all growing-domain candidate
boxes seen so far after widening stage `k` by its omitted-tail budget. -/
def stabilizedRaw (G : GaussianFullLineGluingData) : RealCompute :=
  RealCompute.prefixStabilize G.candidate symmetricReciprocalSquareTailRadius

/-- The growing-domain construction is a valid raw computable real without
using a pre-existing full-line value as an anchor. -/
theorem stabilizedRaw_valid (G : GaussianFullLineGluingData) :
    G.stabilizedRaw.Valid :=
  RealCompute.prefixStabilize_valid_of_future_containment
    G.candidate_ordered G.candidate_widths_shrink G.future_contained
    symmetricReciprocalSquareTailRadius_shrinks

/-- Every stabilized stage still contains its direct bounded-integral
candidate at the same radius. -/
theorem stabilizedRaw_contains_current
    (G : GaussianFullLineGluingData) (n : Nat) :
    (G.stabilizedRaw.compute n).ContainsInterval (G.candidate.compute n) :=
  RealCompute.prefixStabilize_contains_current_of_future G.future_contained n

/-- Runtime width is the bounded quadrature width plus twice the widening
radius used by finite-prefix stabilization. -/
theorem stabilizedRaw_width_le
    (G : GaussianFullLineGluingData) (n : Nat) :
    (G.stabilizedRaw.compute n).width <=
      (G.candidate.compute n).width +
        2 * symmetricReciprocalSquareTailRadius n := by
  have hcontains := RealCompute.prefixStabilize_contained_in_current_expand
    G.candidate symmetricReciprocalSquareTailRadius n
  have hwidth := QInterval.width_le_of_contains hcontains
  rw [QInterval.expand_width] at hwidth
  exact hwidth

end GaussianFullLineGluingData

end ComputableAnalysis


