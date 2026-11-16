-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_DyadicReciprocalIntegral
-- name    : liuyao_ca_fd889115_k1_Analysis_DyadicReciprocalIntegral
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:56:42.058587+00:00
-- url     : https://prove2.me/theorems/2059a36e-ecb0-45ce-a19e-e5198b9c48e4
-- title:
--   Computable analysis · DyadicReciprocalIntegral · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/DyadicReciprocalIntegral.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_BoundsQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_MonotoneIntegralBounds
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralValueBounds

set_option autoImplicit true

/-! Fixed dyadic endpoint quadrature of the positive reciprocal. Its actual
finite rectangle bounds and shrinking errors construct an integral directly;
no exponential, pre-existing logarithm, or antiderivative is imported. -/
namespace ComputableAnalysis.DyadicReciprocalIntegral
open Integral SecantFoundation
set_option maxHeartbeats 1000000

theorem reciprocal_antitone {x y : Rat} (hx : 0<x) (hxy : x≤y) : 1/y≤1/x := by
  have hy : 0<y := (by grind only : 0<y)
  have hxi := Rat.inv_pos.mpr hx
  have hyi := Rat.inv_pos.mpr hy
  have hxv := Rat.mul_inv_cancel x (Rat.ne_of_gt hx)
  have hyv := Rat.mul_inv_cancel y (Rat.ne_of_gt hy)
  have hm := Rat.mul_le_mul_of_nonneg_left hxy (Rat.mul_nonneg (Rat.le_of_lt hxi) (Rat.le_of_lt hyi))
  simp only [Rat.div_def,Rat.one_mul]
  have h1 : x⁻¹*y⁻¹*x=y⁻¹ := by
    calc
      _=(x*x⁻¹)*y⁻¹ := by grind only
      _=y⁻¹ := by rw [hxv,Rat.one_mul]
  have h2 : x⁻¹*y⁻¹*y=x⁻¹ := by
    calc
      _=x⁻¹*(y*y⁻¹) := by grind only
      _=x⁻¹ := by rw [hyv,Rat.mul_one]
  rw [h1,h2] at hm
  exact hm

def function (a b : Rat) (ha : 0<a) : FunctionOnInterval where
  raw := { definedAt := fun q => 0<q, compute := fun q _ _ => ⟨1/q,1/q⟩ }
  lower := a
  upper := b
  defined_on := fun q hq => (by have := hq.1; grind only)
  valid_on := fun q _ => RealCompute.ofRat_valid (1/q)

theorem decreasing (a b : Rat) (ha : 0<a) :
    ∀ x y,inDomainInterval a b x → inDomainInterval a b y → x≤y →
      (value (function a b ha) y).Le (value (function a b ha) x) := by
  intro x y hx hy hxy n m
  rw [value_compute _ y hy,value_compute _ x hx]
  exact reciprocal_antitone ((by have hax : a≤x := hx.1; grind only : 0<x)) hxy

def tests (a b : Rat) (ha : 0<a) (hab : a≤b) (n : Nat) : Bounds (function a b ha) :=
  MonotoneIntegralBounds.partitionEndpointBounds (function a b ha) (decreasing a b ha)
    (BoundsQuadrature.dyadicPartition a b hab n) (fun _ => 0)

theorem gap_bound (a b : Rat) (ha : 0<a) (hab : a≤b) (n : Nat) :
    (tests a b ha hab n).upperSum-(tests a b ha hab n).lowerSum ≤
      (1/a - 1/b) * BoundsQuadrature.dyadicSpacing n := by
  let P := BoundsQuadrature.dyadicPartition a b hab n
  let B := tests a b ha hab n
  let d := BoundsQuadrature.dyadicSpacing n
  let v (k : Nat) := -(1 / P.point k)
  change B.upperSum - B.lowerSum ≤ (1/a - 1/b)*d
  rw [BoundsQuadrature.width_sum]
  have H := rectangleSum_mono
    (fun k => (P.point (k+1)-P.point k)*(B.upper k-B.lower k))
    (fun k => (v (k+1)-v k)*d) P.pieces (by
      intro k hk
      have hp : 0 < P.point k := by have := (P.point_in_bounds (Nat.le_of_lt hk)).1; grind only
      have hm := P.monotone k (k+1) (Nat.le_succ k) (Nat.succ_le_of_lt hk)
      have he := reciprocal_antitone hp hm
      have hw := BoundsQuadrature.dyadicPartition_step_le a b hab n k
      change (P.point (k+1)-P.point k)*
        (((value (function a b ha) (P.point k)).compute 0).hi -
          ((value (function a b ha) (P.point (k+1))).compute 0).lo) ≤ _
      rw [value_compute (function a b ha) (P.point k) (P.point_in_bounds (Nat.le_of_lt hk)),
          value_compute (function a b ha) (P.point (k+1)) (P.point_in_bounds (Nat.succ_le_of_lt hk))]
      change (P.point (k+1)-P.point k)*(1/P.point k-1/P.point (k+1)) ≤ _
      have K := Rat.mul_le_mul_of_nonneg_right hw (show 0 ≤ 1/P.point k-1/P.point (k+1) by grind only)
      dsimp only [v]
      grind only)
  rw [rectangleSum_scale,rectangleSum_telescope] at H
  dsimp only [v] at H
  rw [P.right_endpoint,P.left_endpoint] at H
  exact Rat.le_trans H (by grind only)

theorem gaps_shrink (a b : Rat) (ha : 0<a) (hab : a≤b) :
    ShrinksToZero (fun n => (tests a b ha hab n).upperSum-(tests a b ha hab n).lowerSum) := by
  intro eps
  let C := 1/a - 1/b
  have hC : 0 ≤ C := by have := reciprocal_antitone ha hab; dsimp only [C]; grind only
  refine ⟨RationalMajorant.halfDecayShift C eps, fun n hn => ?_⟩
  exact Rat.le_trans (gap_bound a b ha hab n)
    (RationalMajorant.halfDecayShift_spec_of_le hC eps hn)

def quadrature (a b : Rat) (ha : 0<a) (hab : a≤b) :
    BoundsQuadrature.DyadicData (function a b ha) :=
  ⟨hab, tests a b ha hab, fun _ => rfl, gaps_shrink a b ha hab⟩

def integral (a b : Rat) (ha : 0<a) (hab : a≤b) : RealCompute :=
  (quadrature a b ha hab).integral

theorem valid (a b : Rat) (ha : 0<a) (hab : a≤b) : (integral a b ha hab).Valid :=
  (quadrature a b ha hab).valid

theorem hasIntegral (a b : Rat) (ha : 0<a) (hab : a≤b) :
    HasIntegral (function a b ha) (integral a b ha hab) :=
  (quadrature a b ha hab).hasIntegral

theorem value_bounds (a b : Rat) (ha : 0<a) (hab : a≤b) :
    (RealCompute.ofRat ((b-a)/b)).Le (integral a b ha hab) ∧
      (integral a b ha hab).Le (RealCompute.ofRat ((b-a)/a)) := by
  have hi := hasIntegral a b ha hab
  constructor
  · have h := hi.lower_bound (1/b) (by
      intro x hx n
      exact reciprocal_antitone ((by have hax : a≤x := hx.1; grind only : 0<x)) hx.2)
    simpa only [function,Rat.div_def,Rat.one_mul] using h
  · have h := hi.upper_bound (1/a) (by intro x hx n; exact reciprocal_antitone ha hx.1)
    simpa only [function,Rat.div_def,Rat.one_mul] using h

end ComputableAnalysis.DyadicReciprocalIntegral


