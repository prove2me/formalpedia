-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricSinCos
-- name    : liuyao_ca_fd889115_k1_Analysis_GeometricSinCos
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:31:44.217197+00:00
-- url     : https://prove2.me/theorems/65a2e1f8-a177-49a6-a717-2ef16a701857
-- title:
--   Computable analysis · GeometricSinCos · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/GeometricSinCos.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ArctanInverseCircle
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricTrigChart
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealApproximationOrder

set_option autoImplicit true

/-! Public real trigonometry. The primary rational samplers `sin` and `cos`
use geometric quarter-circles and period two: their physical angle is pi times
the input. Real evaluation is derived from these samplers, not from a series. -/
namespace ComputableAnalysis.GeometricTrig
open ArctanSecantFoundation ArctanInverseConstruction GeometricTrigChart
open ArctanGeometry
open RationalCircleDifferences ComputableCoefficient
set_option maxHeartbeats 3000000

def unitArea : RealCompute := value 1
theorem unitArea_valid : unitArea.Valid := value_valid ⟨by decide +kernel,by decide +kernel⟩

theorem precision_ge (n : Nat) : n≤precision n := by
  have h : n≤2^n := by
    induction n with
    | zero => decide
    | succ n ih => rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := n); omega
  unfold precision
  omega

def areaSchedule : RealCompute.StageSchedule where
  stage := precision
  monotone i j hij := by
    unfold precision
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0<2) hij)
  cofinal n := ⟨n,precision_ge n⟩

def pi : RealCompute := RealCompute.scaleRat 4 (RealCompute.schedule areaSchedule unitArea)
theorem pi_valid : pi.Valid := RealCompute.scaleRat_valid (RealCompute.schedule_valid _ unitArea_valid _)

theorem pi_geometric : pi.Equiv (RealCompute.scaleRat 4 (ArctanGeometry.arctanGeom 1)) :=
  RealCompute.scaleRat_equiv (RealCompute.equiv_trans (RealCompute.schedule_valid _ unitArea_valid _)
    unitArea_valid ArctanGeometry.arctanGeom_one_valid
    (RealCompute.equiv_symm (RealCompute.schedule_equiv _ unitArea_valid areaSchedule))
    (arctanScheduledRectangleRaw_equiv_arctanGeom (by decide +kernel) (by decide +kernel)))

/-- The derivative's constant is the actual circle-area value. -/
theorem pi_circleArea : pi.Equiv piCircleArea :=
  RealCompute.equiv_trans pi_valid
    (RealCompute.scaleRat_valid ArctanGeometry.arctanGeom_one_valid)
    (by
      change RealCompute.ValidCompute piCircleArea.compute
      have he : piCircleArea.compute=(RealCompute.scaleRat 4 (ArctanGeometry.arctanGeom 1)).compute :=
        funext (fun n => (ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute n).symm)
      rw [he]
      exact RealCompute.scaleRat_valid ArctanGeometry.arctanGeom_one_valid) pi_geometric
    ArctanGeometry.four_arctanGeom_one_equiv_piCircleArea

def quarter (cosine : Bool) (q : Rat) : RealCompute :=
  if cosine then ArctanInverseCircle.cosineQuarter (2*q) else ArctanInverseCircle.sineQuarter (2*q)
theorem quarter_valid (cosine : Bool) (q : Rat) : (quarter cosine q).Valid := by
  cases cosine
  · exact ArctanInverseCircle.sineQuarter_valid _
  · exact ArctanInverseCircle.cosineQuarter_valid _

def quarterIndex (q : Rat) : Int := (2*q).floor
def quarterArgument (q : Rat) : Rat := 2*q-(quarterIndex q : Rat)

theorem quarterArgument_bounds (q : Rat) : 0≤quarterArgument q ∧ quarterArgument q<1 := by
  have hl := Rat.floor_le (2*q)
  have hu := Rat.lt_floor_add_one (2*q)
  change 0≤2*q-((2*q).floor:Rat) ∧ 2*q-((2*q).floor:Rat)<1
  rw [Rat.intCast_add] at hu
  constructor <;> grind only

def turn (j : Int) (cosine : Bool) (q : Rat) : RealCompute :=
  if j%4=0 then quarter cosine q
  else if j%4=1 then (if cosine then -(quarter false q) else quarter true q)
  else if j%4=2 then -(quarter cosine q)
  else (if cosine then quarter false q else -(quarter true q))

theorem turn_valid (j : Int) (cosine : Bool) (q : Rat) : (turn j cosine q).Valid := by
  unfold turn
  split
  · exact quarter_valid cosine q
  · split
    · cases cosine
      · simpa only [Bool.false_eq_true,↓reduceIte] using quarter_valid true q
      · exact RealCompute.neg_valid (quarter_valid false q)
    · split
      · exact RealCompute.neg_valid (quarter_valid cosine q)
      · cases cosine
        · simpa only [Bool.false_eq_true,↓reduceIte] using RealCompute.neg_valid (quarter_valid true q)
        · exact quarter_valid false q

def sample (cosine : Bool) (q : Rat) : RealCompute :=
  turn (quarterIndex q) cosine (quarterArgument q/2)

/-- Public sine: rational normalized angle, period two. -/
def sin (q : Rat) : RealCompute := sample false q
/-- Public cosine in the same normalized coordinate. -/
def cos (q : Rat) : RealCompute := sample true q
theorem sample_valid (cosine : Bool) (q : Rat) : (sample cosine q).Valid := turn_valid _ _ _
theorem sin_valid (q : Rat) : (sin q).Valid := sample_valid false q
theorem cos_valid (q : Rat) : (cos q).Valid := sample_valid true q

theorem quarterIndex_period (q : Rat) : quarterIndex (q+2)=quarterIndex q+4 := by
  have he : 2*(q+2)=2*q+(4:Int) := by grind only
  unfold quarterIndex
  rw [he,Rat.floor_add_intCast]

theorem quarterArgument_period (q : Rat) : quarterArgument (q+2)=quarterArgument q := by
  unfold quarterArgument
  rw [quarterIndex_period,Rat.intCast_add]
  grind only

theorem sample_period (cosine : Bool) (q : Rat) : sample cosine (q+2)=sample cosine q := by
  unfold sample
  rw [quarterIndex_period,quarterArgument_period]
  unfold turn
  have he : (quarterIndex q+4)%4=quarterIndex q%4 := by omega
  rw [he]

theorem sin_period (q : Rat) : sin (q+2)=sin q := sample_period false q
theorem cos_period (q : Rat) : cos (q+2)=cos q := sample_period true q

def piValue : Value := RealApproximationOrder.parameter pi pi_valid
def quarterValue (cosine : Bool) (q : Rat) : Value :=
  RealApproximationOrder.parameter (quarter cosine q) (quarter_valid cosine q)

def slopeValue (cosine : Bool) (q : Rat) : Value :=
  Value.mul piValue (if cosine then Value.neg (quarterValue false q) else quarterValue true q)

def slope (q : Rat) (n : Nat) : QInterval := (ArctanInverseCircle.quarterSlope (2*q)).compute n
def chartPoint (q : Rat) (n : Nat) : Rat := (slope q n).lo

theorem slope_geometry (q : Rat) (n : Nat) :
    0≤(slope q n).lo ∧ (slope q n).lo≤(slope q n).hi ∧
    (slope q n).hi≤1 ∧ (slope q n).width=width n := bracket_geometry _ n

theorem width_le_one (n : Nat) : width n≤1 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    change ((1:Rat)/2)^(n+1)≤1
    rw [Rat.pow_succ]
    have hp : 0≤width n := Rat.pow_nonneg (by decide +kernel)
    change 0≤((1:Rat)/2)^n at hp
    change ((1:Rat)/2)^n≤1 at ih
    grind only

theorem unitArea_bounds (n : Nat) :
    (1:Rat)/4≤(unitArea.compute (precision n)).lo ∧ (unitArea.compute (precision n)).hi≤2 := by
  have h := increment_bounds (x := 0) (y := 1) (by decide +kernel) (by decide +kernel) (precision n)
  have hzlo : ((value 0).compute (precision n)).lo=0 := ArctanGeometry.arctanIntegralRectangleCompute_zero_lower _
  have hzhi : ((value 0).compute (precision n)).hi=0 := ArctanGeometry.arctanIntegralRectangleCompute_zero_upper _
  have hw := source_width 1 ⟨by decide +kernel,by decide +kernel⟩ n
  have hn := width_le_one n
  rw [hzlo,hzhi] at h
  have hk0 : integralKernel (0:Rat)=1 := by decide +kernel
  have hk1 : integralKernel (1:Rat)=1/2 := by decide +kernel
  rw [hk0,hk1] at h
  change ((value 1).compute (precision n)).hi-((value 1).compute (precision n)).lo≤width n/128 at hw
  change (1:Rat)/4≤((value 1).compute (precision n)).lo ∧ ((value 1).compute (precision n)).hi≤2
  constructor <;> grind only

end ComputableAnalysis.GeometricTrig


