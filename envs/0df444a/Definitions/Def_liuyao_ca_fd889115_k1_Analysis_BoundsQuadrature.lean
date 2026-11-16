-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_BoundsQuadrature
-- name    : liuyao_ca_fd889115_k1_Analysis_BoundsQuadrature
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:54:37.195511+00:00
-- url     : https://prove2.me/theorems/5f9e8825-23d5-49e9-b17d-0932a09ce100
-- title:
--   Computable analysis · BoundsQuadrature · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/BoundsQuadrature.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ParametrizedLimits
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralBoundsComparison

set_option autoImplicit true

/-! A supplied sequence of genuine finite bounds with shrinking gaps constructs
an integral by finite prefix intersections. This is one sufficient construction
route, and does not require a pre-existing integral value. -/
namespace ComputableAnalysis.BoundsQuadrature
open Integral RawLimit
set_option maxHeartbeats 1000000

/-- Spacing of the absolute dyadic grid, with the integers at level zero. -/
def dyadicSpacing (n : Nat) : Rat := allowance n

theorem dyadicSpacing_pos (n : Nat) : 0 < dyadicSpacing n := allowance_pos n

private def firstIndex (a : Rat) (n : Nat) : Int := (a / dyadicSpacing n).floor
private def lastIndex (b : Rat) (n : Nat) : Int := (b / dyadicSpacing n).ceil
private def cellCount (a b : Rat) (n : Nat) : Nat := max 1 (lastIndex b n - firstIndex a n).toNat

private def latticePoint (a : Rat) (n k : Nat) : Rat :=
  ((firstIndex a n + (k : Int) : Int) : Rat) * dyadicSpacing n

private def clip (a b x : Rat) : Rat := minRat b (maxRat2 a x)

private theorem clip_mono (a b : Rat) {x y : Rat} (h : x ≤ y) :
    clip a b x ≤ clip a b y := by
  unfold clip minRat maxRat2
  grind

private theorem clip_step (a b : Rat) {x y : Rat} (h : x ≤ y) :
    clip a b y - clip a b x ≤ y-x := by
  unfold clip minRat maxRat2
  grind

private theorem lattice_left (a : Rat) (n : Nat) : latticePoint a n 0 ≤ a := by
  have h := dyadicSpacing_pos n
  have H := Rat.mul_le_mul_of_nonneg_right (Rat.floor_le (a / dyadicSpacing n)) (Rat.le_of_lt h)
  rw [Rat.div_mul_cancel (Rat.ne_of_gt h)] at H
  simpa [latticePoint, firstIndex] using H

private theorem lattice_right (a b : Rat) (n : Nat) : b ≤ latticePoint a n (cellCount a b n) := by
  have h := dyadicSpacing_pos n
  have H := Rat.mul_le_mul_of_nonneg_right (Rat.le_ceil (x := b / dyadicSpacing n)) (Rat.le_of_lt h)
  rw [Rat.div_mul_cancel (Rat.ne_of_gt h)] at H
  apply Rat.le_trans H
  apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt h)
  rw [Rat.intCast_le_intCast]
  change lastIndex b n ≤ firstIndex a n + (cellCount a b n : Int)
  have hk : (lastIndex b n - firstIndex a n).toNat ≤ cellCount a b n := Nat.le_max_right _ _
  omega

private theorem lattice_mono (a : Rat) (n : Nat) {i j : Nat} (h : i ≤ j) :
    latticePoint a n i ≤ latticePoint a n j := by
  apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt (dyadicSpacing_pos n))
  rw [Rat.intCast_le_intCast]
  omega

/-- The points of the absolute dyadic lattice clipped to the integration interval. -/
def dyadicPartition (a b : Rat) (hab : a ≤ b) (n : Nat) : RationalPartition a b where
  pieces := cellCount a b n
  positive := Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_left _ _)
  point k := clip a b (latticePoint a n k)
  left_endpoint := by
    have H := lattice_left a n
    unfold clip minRat maxRat2
    grind
  right_endpoint := by
    have H := lattice_right a b n
    unfold clip minRat maxRat2
    grind
  monotone _ _ hij _ := clip_mono a b (lattice_mono a n hij)

theorem dyadicPartition_step_le (a b : Rat) (hab : a ≤ b) (n k : Nat) :
    (dyadicPartition a b hab n).point (k+1) - (dyadicPartition a b hab n).point k
      ≤ dyadicSpacing n := by
  have H := clip_step a b (lattice_mono a n (Nat.le_succ k))
  have E : latticePoint a n (k+1) - latticePoint a n k = dyadicSpacing n := by
    simp only [latticePoint, Int.natCast_succ, Rat.intCast_add, Rat.intCast_one]
    grind only
  rwa [E] at H

/-- Every lattice point in the interior occurs in the finite partition. -/
theorem dyadicPartition_contains_lattice (a b : Rat) (hab : a ≤ b) (n : Nat) (j : Int)
    (ha : a < (j : Rat) * dyadicSpacing n) (hb : (j : Rat) * dyadicSpacing n < b) :
    ∃ k ≤ (dyadicPartition a b hab n).pieces,
      (dyadicPartition a b hab n).point k = (j : Rat) * dyadicSpacing n := by
  let d := dyadicSpacing n
  have hd : 0 < d := dyadicSpacing_pos n
  have hd' : 0 < d⁻¹ := Rat.inv_pos.mpr hd
  have E : ((j : Rat) * dyadicSpacing n) * d⁻¹ = (j : Rat) := by
    change ((j : Rat) * d) * d⁻¹ = _
    rw [Rat.mul_assoc, Rat.mul_inv_cancel d (Rat.ne_of_gt hd), Rat.mul_one]
  have H := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt ha) (Rat.le_of_lt hd')
  have J := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt hb) (Rat.le_of_lt hd')
  rw [E] at H J
  have hj₁ : firstIndex a n ≤ j := by
    have h : a/d ≤ (j : Rat) := H
    simpa only [firstIndex, d, Rat.floor_intCast] using Rat.floor_monotone h
  have hj₂ : j ≤ lastIndex b n := by
    have h : (j : Rat) ≤ b/d := J
    exact Rat.intCast_le_intCast.mp (Rat.le_trans h Rat.le_ceil)
  let k := (j - firstIndex a n).toNat
  have hk : (k : Int) = j - firstIndex a n := Int.toNat_of_nonneg (by omega)
  have hN : (lastIndex b n - firstIndex a n).toNat ≤ cellCount a b n := Nat.le_max_right _ _
  refine ⟨k, (show k ≤ cellCount a b n by dsimp only [k]; omega), ?_⟩
  have hk' : firstIndex a n + (k : Int) = j := by omega
  change clip a b (latticePoint a n k) = (j : Rat) * d
  unfold latticePoint
  rw [hk']
  change clip a b ((j : Rat)*d) = _
  unfold clip minRat maxRat2
  grind only

/-- Cell bounds on the fixed grid, with a proof that the total area gap shrinks. -/
structure DyadicData (F : FunctionOnInterval) where
  ordered : F.lower ≤ F.upper
  tests : Nat → Bounds F
  onGrid : ∀ n, (tests n).partition = dyadicPartition F.lower F.upper ordered n
  shrinks : ShrinksToZero (fun n => (tests n).upperSum - (tests n).lowerSum)

def box {F : FunctionOnInterval} (tests : Nat → Bounds F) (n : Nat) : QInterval :=
  ⟨(tests n).lowerSum,(tests n).upperSum⟩

def raw (F : FunctionOnInterval) (tests : Nat → Bounds F) : RealCompute :=
  prefixRaw (box tests)

private theorem box_cross (F : FunctionOnInterval) (tests : Nat → Bounds F) (n m : Nat) :
    (box tests n).lo≤
      (box tests m).hi :=
  Bounds.lowerSum_le_upperSum _ _

private theorem prefix_cross (B : Nat → QInterval)
    (cross : ∀ n m,(B n).lo≤(B m).hi) (n m : Nat) :
    (prefixCompute B n).lo≤(prefixCompute B m).hi := by
  have left : ∀ n m,(prefixCompute B n).lo≤(B m).hi := by
    intro n m
    induction n with
    | zero => exact cross 0 m
    | succ n ih =>
      have hn := cross (n+1) m
      dsimp [prefixCompute,QInterval.intersection,maxRat2]
      grind
  induction m with
  | zero => exact left n 0
  | succ m ih =>
    have hn := left n (m+1)
    dsimp [prefixCompute,QInterval.intersection,minRat]
    grind

private theorem prefix_tests (F : FunctionOnInterval) (tests : Nat → Bounds F) (A : Bounds F) (n : Nat) :
    A.lowerSum≤((raw F tests).compute n).hi ∧
      ((raw F tests).compute n).lo≤A.upperSum := by
  induction n with
  | zero => exact ⟨Bounds.lowerSum_le_upperSum A _,Bounds.lowerSum_le_upperSum _ A⟩
  | succ n ih =>
    have h1 : A.lowerSum≤(box tests (n+1)).hi :=
      Bounds.lowerSum_le_upperSum A _
    have h2 : (box tests (n+1)).lo≤A.upperSum :=
      Bounds.lowerSum_le_upperSum _ A
    change A.lowerSum≤(QInterval.intersection ((raw F tests).compute n)
      (box tests (n+1))).hi ∧
      (QInterval.intersection ((raw F tests).compute n)
      (box tests (n+1))).lo≤A.upperSum
    dsimp [QInterval.intersection,maxRat2,minRat]
    constructor <;> grind

theorem valid (F : FunctionOnInterval) (tests : Nat → Bounds F)
    (shrink : ShrinksToZero (fun n => (tests n).upperSum-(tests n).lowerSum)) :
    (raw F tests).Valid := by
  have order (n : Nat) : ((raw F tests).compute n).lo≤((raw F tests).compute n).hi :=
    prefix_cross _ (box_cross F tests) n n
  refine ⟨?_,?_,?_⟩
  · intro n
    have := order n
    dsimp [QInterval.width]
    grind only
  · intro n m hnm
    induction hnm with
    | refl => exact ⟨Rat.le_refl,order n,Rat.le_refl⟩
    | @step m hnm ih =>
      have hs := QInterval.intersection_contained_left ((raw F tests).compute m)
        (box tests (m+1))
      exact ⟨Rat.le_trans ih.1 hs.1,order (m+1),Rat.le_trans hs.2 ih.2.2⟩
  · intro eps
    obtain ⟨N,hN⟩ := shrink eps
    refine ⟨N,?_⟩
    intro n hn
    have hc := prefix_current (box tests) n
    have he := hN n hn
    change (box tests n).hi-(box tests n).lo≤eps.val at he
    change ((raw F tests).compute n).hi-((raw F tests).compute n).lo≤eps.val
    change (box tests n).lo≤((raw F tests).compute n).lo ∧
      ((raw F tests).compute n).hi≤(box tests n).hi at hc
    grind only

theorem hasIntegral (F : FunctionOnInterval) (tests : Nat → Bounds F)
    (shrink : ShrinksToZero (fun n => (tests n).upperSum-(tests n).lowerSum)) :
    HasIntegral F (raw F tests) := by
  refine ⟨valid F tests shrink,fun A => prefix_tests F tests A,?_⟩
  intro eps
  obtain ⟨N,hN⟩ := shrink eps
  exact ⟨tests N,hN N (Nat.le_refl _)⟩


theorem width_sum {F : FunctionOnInterval} (B : Bounds F) :
    B.upperSum - B.lowerSum = rectangleSum
      (fun k => (B.partition.point (k+1) - B.partition.point k) * (B.upper k - B.lower k))
      B.partition.pieces := by
  let w k := B.partition.point (k+1) - B.partition.point k
  change rectangleSum (fun k => w k * B.upper k) B.partition.pieces -
    rectangleSum (fun k => w k * B.lower k) B.partition.pieces = _
  have H := rectangleSum_add (fun k => w k * (B.upper k - B.lower k))
    (fun k => w k * B.lower k) B.partition.pieces
  have E : (fun k => w k * (B.upper k - B.lower k) + w k * B.lower k) =
      (fun k => w k * B.upper k) := by funext k; grind only
  rw [E] at H
  grind only

/-- Length of the cells marked as containing unresolved turns. -/
def exceptionalLength {F : FunctionOnInterval} (B : Bounds F) (exceptional : Nat → Bool) : Rat :=
  rectangleSum (fun k => if exceptional k then B.partition.point (k+1) - B.partition.point k else 0)
    B.partition.pieces

/-- Upper bound for the area gap. Ordinary cells can have individual error
budgets, for example width times the variation of monotone endpoint values. -/
theorem turning_gap {F : FunctionOnInterval} (B : Bounds F) (exceptional : Nat → Bool)
    (height : Rat) (ordinaryError : Nat → Rat)
    (herror : ∀ k, k < B.partition.pieces → 0 ≤ ordinaryError k)
    (ordinary : ∀ k, k < B.partition.pieces → exceptional k = false →
      (B.partition.point (k+1) - B.partition.point k) * (B.upper k - B.lower k) ≤ ordinaryError k)
    (turn : ∀ k, k < B.partition.pieces → exceptional k = true → B.upper k - B.lower k ≤ height) :
    B.upperSum - B.lowerSum ≤ rectangleSum ordinaryError B.partition.pieces +
      exceptionalLength B exceptional * height := by
  rw [width_sum, exceptionalLength, ← rectangleSum_scale, ← rectangleSum_add]
  apply rectangleSum_mono
  intro k hk
  cases he : exceptional k
  · simpa only [he, Bool.false_eq_true, ↓reduceIte, Rat.zero_mul, Rat.add_zero] using ordinary k hk he
  · simp only [↓reduceIte]
    have hs := B.partition.monotone k (k+1) (Nat.le_succ k) (Nat.succ_le_of_lt hk)
    have H := Rat.mul_le_mul_of_nonneg_left (turn k hk he)
      (show 0 ≤ B.partition.point (k+1) - B.partition.point k by grind only)
    have := herror k hk
    grind only

/-- Finitely many exceptional cells, with a stage-independent count bound,
have shrinking total length on the fixed grid. -/
theorem exceptionalLength_shrinks_of_count {F : FunctionOnInterval}
    (ordered : F.lower ≤ F.upper) (tests : Nat → Bounds F)
    (onGrid : ∀ n, (tests n).partition = dyadicPartition F.lower F.upper ordered n)
    (exceptional : Nat → Nat → Bool) (count : Nat)
    (hcount : ∀ n, rectangleSum (fun k => if exceptional n k then 1 else 0)
      (tests n).partition.pieces ≤ (count : Rat)) :
    ShrinksToZero (fun n => exceptionalLength (tests n) (exceptional n)) := by
  intro eps
  let C : Rat := (count : Rat)
  refine ⟨RationalMajorant.halfDecayShift C eps, fun n hn => ?_⟩
  let B := tests n
  let d := dyadicSpacing n
  have H := rectangleSum_mono
    (fun k => if exceptional n k then B.partition.point (k+1) - B.partition.point k else 0)
    (fun k => (if exceptional n k then (1 : Rat) else 0)*d) B.partition.pieces (by
      intro k _
      split
      · rename_i he
        simp only [he, ↓reduceIte, Rat.one_mul]
        rw [show B.partition = dyadicPartition F.lower F.upper ordered n from onGrid n]
        exact dyadicPartition_step_le _ _ _ _ _
      · rename_i he
        simp only [he, ↓reduceIte, Rat.zero_mul]
        exact Rat.le_refl)
  rw [rectangleSum_scale] at H
  exact Rat.le_trans H (Rat.le_trans
    (Rat.mul_le_mul_of_nonneg_right (hcount n) (Rat.le_of_lt (dyadicSpacing_pos n)))
    (RationalMajorant.halfDecayShift_spec_of_le Rat.natCast_nonneg eps hn))

/-- Build a valid dyadic integral from ordinary cell error bounds and fixed
heights on exceptional cells whose total length tends to zero. -/
def DyadicData.ofTurningCells {F : FunctionOnInterval}
    (ordered : F.lower ≤ F.upper) (tests : Nat → Bounds F)
    (onGrid : ∀ n, (tests n).partition = dyadicPartition F.lower F.upper ordered n)
    (exceptional : Nat → Nat → Bool) (lo hi : Rat) (heightOrdered : lo ≤ hi)
    (ordinaryError : Nat → Nat → Rat)
    (herror : ∀ n k, k < (tests n).partition.pieces → 0 ≤ ordinaryError n k)
    (ordinary : ∀ n k, k < (tests n).partition.pieces → exceptional n k = false →
      ((tests n).partition.point (k+1) - (tests n).partition.point k) *
        ((tests n).upper k - (tests n).lower k) ≤ ordinaryError n k)
    (turn : ∀ n k, k < (tests n).partition.pieces → exceptional n k = true →
      (tests n).lower k = lo ∧ (tests n).upper k = hi)
    (ordinaryShrinks : ShrinksToZero (fun n => rectangleSum (ordinaryError n) (tests n).partition.pieces))
    (exceptionalShrinks : ShrinksToZero (fun n => exceptionalLength (tests n) (exceptional n))) :
    DyadicData F where
  ordered := ordered
  tests := tests
  onGrid := onGrid
  shrinks := by
    intro eps
    let first : QPos := ⟨eps.val / 2, by have := eps.property; grind only⟩
    let second : QPos := ⟨eps.val / (2 * (1 + (hi-lo))), by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by grind only))⟩
    obtain ⟨N,hN⟩ := ordinaryShrinks first
    obtain ⟨M,hM⟩ := exceptionalShrinks second
    refine ⟨max N M, fun n hn => ?_⟩
    have h₁ := hN n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have h₂ := Rat.mul_le_mul_of_nonneg_right (hM n (Nat.le_trans (Nat.le_max_right _ _) hn))
      (show 0 ≤ hi-lo by grind only)
    have hbudget : second.val * (hi-lo) ≤ eps.val / 2 := by
      have hp : 0 < 2 * (1 + (hi-lo)) := by grind only
      have E := Rat.div_mul_cancel (a := eps.val) (Rat.ne_of_gt hp)
      have E' := Rat.div_mul_cancel (a := eps.val) (b := 2) (by decide +kernel)
      have hpos : 0 ≤ second.val := Rat.le_of_lt second.property
      change (eps.val / (2 * (1 + (hi-lo)))) * (hi-lo) ≤ eps.val / 2
      apply Rat.le_of_mul_le_mul_right _ (by decide : (0:Rat)<2)
      change 0 ≤ eps.val / (2 * (1 + (hi-lo))) at hpos
      grind only
    have H := turning_gap (tests n) (exceptional n) (hi-lo) (ordinaryError n)
      (herror n) (ordinary n) (fun k hk he => by rw [(turn n k hk he).1, (turn n k hk he).2]; exact Rat.le_refl)
    change rectangleSum (ordinaryError n) (tests n).partition.pieces ≤ eps.val / 2 at h₁
    have h₂' := Rat.le_trans h₂ hbudget
    grind only

/-- Sum the certified rectangles and intersect the finite prefix of bounds. -/
def DyadicData.integral {F : FunctionOnInterval} (D : DyadicData F) : RealCompute :=
  raw F D.tests

theorem DyadicData.hasIntegral {F : FunctionOnInterval} (D : DyadicData F) :
    HasIntegral F D.integral :=
  BoundsQuadrature.hasIntegral F D.tests D.shrinks

theorem DyadicData.valid {F : FunctionOnInterval} (D : DyadicData F) : D.integral.Valid :=
  D.hasIntegral.valid

theorem DyadicData.agrees {F : FunctionOnInterval} (D : DyadicData F) {I : RealCompute}
    (hI : HasIntegral F I) : D.integral.Equiv I :=
  D.hasIntegral.unique hI

end ComputableAnalysis.BoundsQuadrature


