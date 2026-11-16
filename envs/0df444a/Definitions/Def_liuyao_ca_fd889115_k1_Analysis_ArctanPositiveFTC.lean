-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ArctanPositiveFTC
-- name    : liuyao_ca_fd889115_k1_Analysis_ArctanPositiveFTC
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:35:14.323408+00:00
-- url     : https://prove2.me/theorems/4d7c0306-a594-481e-b3d9-60e72ac07465
-- title:
--   Computable analysis · ArctanPositiveFTC · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ArctanPositiveFTC.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ArctanSecantFoundation
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCStepQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricSinCos
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueCongruence

set_option autoImplicit true

/-! Geometric arctangent FTC on the unit slope interval and rational
kernel estimates on the positive half line. -/
namespace ComputableAnalysis.ArctanPositiveFTC
open ComputableCoefficient RealApproximationOrder FTCRealOrder FTCRealCalculus
open ArctanGeometry LipschitzQuadrature
set_option maxHeartbeats 600000

private theorem sub_hi (x y : RealCompute) (n : Nat) : ((x-y).compute n).hi=(x.compute n).hi-(y.compute n).lo := by rfl
private theorem sub_lo (x y : RealCompute) (n : Nat) : ((x-y).compute n).lo=(x.compute n).lo-(y.compute n).hi := by rfl
private theorem scale_hi (c : Rat) (x : RealCompute) (n : Nat) (hc : 0≤c) :
    ((RealCompute.scaleRat c x).compute n).hi=c*(x.compute n).hi := by simp only [RealCompute.scaleRat,RealCompute.scaleRatCompute,if_pos hc]
private theorem scale_lo (c : Rat) (x : RealCompute) (n : Nat) (hc : 0≤c) :
    ((RealCompute.scaleRat c x).compute n).lo=c*(x.compute n).lo := by simp only [RealCompute.scaleRat,RealCompute.scaleRatCompute,if_pos hc]

def atan (q : Rat) : Value := if h : 0≤q ∧ q≤1 then
  parameter (ArctanSecantFoundation.value q) (ArctanSecantFoundation.value_valid h) else Value.rational 0

def kernel (q : Rat) : Value := Value.rational (integralKernel q)

theorem kernel_variation (u v : Rat) (hu : 0≤u) (huv : u≤v) :
    0≤integralKernel u-integralKernel v ∧ integralKernel u-integralKernel v≤2*(v-u) := by
  have hv : 0≤v := Rat.le_trans hu huv
  have U := RationalCircle.Stage.one_add_square_pos u
  have V := RationalCircle.Stage.one_add_square_pos v
  have uc := Rat.mul_inv_cancel (1+u*u) (Rat.ne_of_gt U)
  have vc := Rat.mul_inv_cancel (1+v*v) (Rat.ne_of_gt V)
  have up : 0≤(1+u*u)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr U)
  have vp : 0≤(1+v*v)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr V)
  have ub := integralKernel_le_one u
  have vb := integralKernel_le_one v
  simp only [integralKernel,Rat.div_def,Rat.one_mul] at ub vb
  have us := RationalCircle.Stage.ratSquare_nonneg (u-1)
  have vs := RationalCircle.Stage.ratSquare_nonneg (v-1)
  have ut : u≤1+u*u := by grind only
  have vt : v≤1+v*v := by grind only
  have ur := Rat.mul_le_mul_of_nonneg_right ut up
  have vr := Rat.mul_le_mul_of_nonneg_right vt vp
  have ur' : u*(1+u*u)⁻¹≤1 := by grind only
  have vr' : v*(1+v*v)⁻¹≤1 := by grind only
  have A := rat_mul_le_mul_of_nonneg (Rat.mul_nonneg hu up) ur' vp vb
  have B := rat_mul_le_mul_of_nonneg (Rat.mul_nonneg hv vp) vr' up ub
  have F : (u+v)*((1+u*u)⁻¹*(1+v*v)⁻¹)≤2 := by grind only
  have H := Rat.mul_le_mul_of_nonneg_left F (by grind only : 0≤v-u)
  have eq : integralKernel u-integralKernel v=(v-u)*(u+v)*((1+u*u)⁻¹*(1+v*v)⁻¹) := by
    simp only [integralKernel,Rat.div_def,Rat.one_mul]; grind only
  constructor
  · have M := integralKernel_antitone_nonneg hu huv; grind only
  · rw [eq]; grind only

theorem kernel_lipschitz (l r : Rat) (hl : 0≤l) : LipschitzIntegralBounds.Lipschitz kernel l r 2 := by
  intro u v hu huv _
  have H := kernel_variation u v (Rat.le_trans hl hu) huv
  constructor
  · intro i j; change -(2*(v-u))≤integralKernel v-integralKernel u; grind only
  · intro i j; change integralKernel v-integralKernel u≤2*(v-u); grind only

def kernelData (l r : Rat) (hl : 0≤l) (hlr : l≤r) : Data kernel l r where
  ordered := hlr
  constant := 2
  nonnegative := by decide +kernel
  lipschitz := kernel_lipschitz l r hl

theorem increment (u v : Rat) (hu : 0≤u) (huv : u≤v) (hv : v≤1) :
    LE (Value.rational ((v-u)*integralKernel v)) (sub (atan v) (atan u)) ∧
    LE (sub (atan v) (atan u)) (Value.rational ((v-u)*integralKernel u)) := by
  have ud : 0≤u ∧ u≤1 := ⟨hu,Rat.le_trans huv hv⟩
  have vd : 0≤v ∧ v≤1 := ⟨Rat.le_trans hu huv,hv⟩
  constructor
  · intro i j
    have H := (ArctanSecantFoundation.increment_bounds hu huv j).1
    simpa only [atan,dif_pos ud,dif_pos vd,sub,parameter,Value.parameter,RealCompute.Certified.ofRaw,RealCompute.Certified.preferred,Value.rational,RealCompute.Certified.ofRat,RealCompute.ofRat,RealCompute.instHSub,RealCompute.sub,RealCompute.subCompute,sub_hi,sub_lo] using H
  · intro i j
    have H := (ArctanSecantFoundation.increment_bounds hu huv i).2
    simpa only [atan,dif_pos ud,dif_pos vd,sub,parameter,Value.parameter,RealCompute.Certified.ofRaw,RealCompute.Certified.preferred,Value.rational,RealCompute.Certified.ofRat,RealCompute.ofRat,RealCompute.instHSub,RealCompute.sub,RealCompute.subCompute,sub_hi,sub_lo] using H

def step : Step atan kernel 0 1 where
  error := 2
  error_nonnegative := by decide +kernel
  radius := ⟨1,by decide +kernel⟩
  firstOrder := by
    intro u v hu huv hv _
    have H := increment u v hu (Rat.le_of_lt huv) hv
    have K := kernel_variation u v hu (Rat.le_of_lt huv)
    have Q := Rat.mul_le_mul_of_nonneg_left K.2 (by grind only : 0≤v-u)
    constructor
    · intro i j
      simp only [sub,scale,kernel,Value.rational,RealCompute.Certified.ofRat,RealCompute.Certified.ofRaw,RealCompute.ofRat,RealCompute.scaleRat]
      have A := H.1 0 j
      change (v-u)*integralKernel v≤((atan v).real.compute j).hi-((atan u).real.compute j).lo at A
      rw [sub_hi,sub_hi]
      simp only [RealCompute.scaleRatCompute,if_pos (show 0≤v-u by grind only)]
      change -(2*(v-u)*(v-u))≤((atan v).real.compute j).hi-((atan u).real.compute j).lo-(v-u)*integralKernel u
      grind only
    · intro i j
      simp only [sub,scale,kernel,Value.rational,RealCompute.Certified.ofRat,RealCompute.Certified.ofRaw,RealCompute.ofRat,RealCompute.scaleRat]
      have A := H.2 i 0
      change ((atan v).real.compute i).lo-((atan u).real.compute i).hi≤(v-u)*integralKernel u at A
      rw [sub_lo,sub_lo]
      simp only [RealCompute.scaleRatCompute,if_pos (show 0≤v-u by grind only)]
      change ((atan v).real.compute i).lo-((atan u).real.compute i).hi-(v-u)*integralKernel u≤2*(v-u)*(v-u)
      have P := Rat.mul_nonneg (by grind only : 0≤v-u) (by grind only : 0≤v-u)
      grind only
  variation := 2
  variation_nonnegative := by decide +kernel
  lipschitz := kernel_lipschitz 0 1 Rat.le_refl

theorem atan_zero : Same (atan 0) (Value.rational 0) := by
  change (atan 0).real.preferred.Equiv (RealCompute.ofRat 0)
  simp only [atan,dif_pos (show (0:Rat)≤0 ∧ (0:Rat)≤1 by decide +kernel)]
  have H := arctanScheduledRectangleRaw_equiv_arctanGeom (x := (0:Rat)) (by decide +kernel) (by decide +kernel)
  rw [arctanGeom_zero] at H
  exact H

theorem atan_small (q : Rat) (hq : 0≤q) (hq1 : q≤1) : Small (atan q) q := by
  have H := increment 0 q Rat.le_refl hq hq1
  have lo := H.1
  have up := H.2
  have kz : integralKernel 0=1 := by decide +kernel
  have H' : Small (sub (atan q) (atan 0)) q := by
    constructor
    · intro i j
      have A := lo 0 j
      have P := Rat.mul_nonneg hq (Rat.le_of_lt (integralKernel_pos q))
      change (q-0)*integralKernel q≤((atan q).real.compute j).hi-((atan 0).real.compute j).lo at A
      change -q≤((atan q).real.compute j).hi-((atan 0).real.compute j).lo
      grind only
    · intro i j
      have A := up i 0
      change ((atan q).real.compute i).lo-((atan 0).real.compute i).hi≤q
      change ((atan q).real.compute i).lo-((atan 0).real.compute i).hi≤(q-0)*integralKernel 0 at A
      rw [kz] at A
      grind only
  have A := (Same.refl (atan q)).sub atan_zero
  have B : Same (sub (atan q) (Value.rational 0)) (atan q) := by
    apply arithmetic_identity; intro s; simp only [sub,Value.rational]; grind only
  exact H'.congr (A.trans B)

/-- Monotone endpoint rectangles on the integer-first grid. -/
def kernelDyadic (a b : Rat) (ha : 0 ≤ a) (hab : a ≤ b) :
    BoundsQuadrature.DyadicData (LipschitzIntegralBounds.onInterval kernel a b) := by
  let F := LipschitzIntegralBounds.onInterval kernel a b
  have ev (q : Rat) (hq : inDomainInterval a b q) (n : Nat) :
      (SecantFoundation.value F q).compute n = ⟨integralKernel q,integralKernel q⟩ := by
    exact ConvexFTC.value_onInterval (fun x => (kernel x).real.preferred) a b
      (fun x _ => (kernel x).real.valid) hq n
  have dec : ∀ u v, inDomainInterval a b u → inDomainInterval a b v → u ≤ v →
      (SecantFoundation.value F v).Le (SecantFoundation.value F u) := by
    intro u v hu hv h i j
    rw [ev v hv i,ev u hu j]
    exact integralKernel_antitone_nonneg (Rat.le_trans ha hu.1) h
  let P := BoundsQuadrature.dyadicPartition a b hab
  let T (n : Nat) : Integral.Bounds F :=
    MonotoneIntegralBounds.partitionEndpointBounds F dec (P n) (fun _ => 0)
  refine ⟨hab, T, fun _ => rfl, ?_⟩
  intro eps
  let C := integralKernel a - integralKernel b
  have hC : 0 ≤ C := by have := integralKernel_antitone_nonneg ha hab; dsimp only [C]; grind only
  refine ⟨RationalMajorant.halfDecayShift C eps, fun n hn => ?_⟩
  apply Rat.le_trans _ (RationalMajorant.halfDecayShift_spec_of_le hC eps hn)
  change (T n).upperSum - (T n).lowerSum ≤ C * BoundsQuadrature.dyadicSpacing n
  rw [BoundsQuadrature.width_sum]
  let w (k : Nat) := (P n).point (k+1) - (P n).point k
  let v (k : Nat) := -(integralKernel ((P n).point k))
  let h := BoundsQuadrature.dyadicSpacing n
  have H := Integral.rectangleSum_mono (fun k => w k * ((T n).upper k - (T n).lower k))
    (fun k => (v (k+1) - v k)*h) (P n).pieces (by
      intro k hk
      have hL := (P n).point_in_bounds (Nat.le_of_lt hk)
      have hR := (P n).point_in_bounds (Nat.succ_le_of_lt hk)
      have hm := (P n).monotone k (k+1) (Nat.le_succ k) (Nat.succ_le_of_lt hk)
      change w k * (((SecantFoundation.value F ((P n).point k)).compute 0).hi -
        ((SecantFoundation.value F ((P n).point (k+1))).compute 0).lo) ≤ _
      rw [ev _ hL,ev _ hR]
      have hd := integralKernel_antitone_nonneg (Rat.le_trans ha hL.1) hm
      have hw : w k ≤ h := BoundsQuadrature.dyadicPartition_step_le a b hab n k
      have K := Rat.mul_le_mul_of_nonneg_right hw
        (show 0 ≤ integralKernel ((P n).point k) - integralKernel ((P n).point (k+1)) by grind only)
      dsimp only [v]
      grind only)
  rw [Integral.rectangleSum_scale,Integral.rectangleSum_telescope] at H
  dsimp only [v] at H
  rw [(P n).right_endpoint,(P n).left_endpoint] at H
  exact Rat.le_trans H (by dsimp only [C]; grind only)

/-- Integrate the arctangent kernel on any subinterval of the unit chart
using the absolute dyadic grid and monotone endpoint bounds. -/
def dyadicIntegral (a b : Rat) (ha : 0 ≤ a) (hab : a ≤ b) (_hb : b ≤ 1) : RealCompute :=
  (kernelDyadic a b ha hab).integral

theorem dyadicIntegral_hasIntegral (a b : Rat) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Integral.HasIntegral (LipschitzIntegralBounds.onInterval kernel a b)
      (dyadicIntegral a b ha hab hb) :=
  (kernelDyadic a b ha hab).hasIntegral

theorem dyadicIntegral_equiv_endpoint (a b : Rat) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Same (parameter (dyadicIntegral a b ha hab hb)
      (dyadicIntegral_hasIntegral a b ha hab hb).valid) (sub (atan b) (atan a)) :=
  (step.restrict a b ha hb).ftc (dyadicIntegral_hasIntegral a b ha hab hb)

theorem dyadicIntegral_from_zero (b : Rat) (hb : 0 ≤ b) (hb' : b ≤ 1) :
    (dyadicIntegral 0 b Rat.le_refl hb hb').Equiv (atan b).real.preferred := by
  let I := parameter (dyadicIntegral 0 b Rat.le_refl hb hb')
    (dyadicIntegral_hasIntegral 0 b Rat.le_refl hb hb').valid
  change Same I (atan b)
  refine (dyadicIntegral_equiv_endpoint 0 b Rat.le_refl hb hb').trans
    (((Same.refl (atan b)).sub atan_zero).trans ?_)
  apply arithmetic_identity
  intro s
  simp only [sub,Value.rational,Rat.sub_eq_add_neg,Rat.neg_zero,Rat.add_zero]

theorem dyadicIntegral_equiv_geometric (b : Rat) (hb : 0 ≤ b) (hb' : b ≤ 1) :
    (dyadicIntegral 0 b Rat.le_refl hb hb').Equiv (arctanGeom b) := by
  have H : (atan b).real.preferred.Equiv (arctanGeom b) := by
    simp only [atan,dif_pos (And.intro hb hb')]
    exact arctanScheduledRectangleRaw_equiv_arctanGeom hb hb'
  exact RealCompute.equiv_trans (dyadicIntegral_hasIntegral 0 b Rat.le_refl hb hb').valid
    (atan b).real.valid (arctanGeom_valid_on_unit hb hb')
    (dyadicIntegral_from_zero b hb hb') H

end ComputableAnalysis.ArctanPositiveFTC


