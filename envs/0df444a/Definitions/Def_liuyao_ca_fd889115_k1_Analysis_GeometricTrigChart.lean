-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricTrigChart
-- name    : liuyao_ca_fd889115_k1_Analysis_GeometricTrigChart
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:09:23.775067+00:00
-- url     : https://prove2.me/theorems/cd96b787-4a90-4d9f-92ef-f1727078acdf
-- title:
--   Computable analysis · GeometricTrigChart · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/GeometricTrigChart.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ArctanSecantFoundation
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RationalCircleDifferences

set_option autoImplicit true

/-! Geometric circle velocity in sector-area time. The estimates below use
only rational circle identities and geometric arctangent rectangle bounds. -/
namespace ComputableAnalysis.GeometricTrigChart
open ArctanSecantFoundation RationalCircleDifferences ArctanGeometry
set_option maxHeartbeats 3000000

def coordinate (cosine : Bool) (u : Rat) : Rat := if cosine then pointRe u else pointIm u
def tangent (cosine : Bool) (u : Rat) : Rat := if cosine then -pointIm u else pointRe u

theorem velocity (cosine : Bool) (u : Rat) :
    (if cosine then pointReDerivative u else pointImDerivative u)=
      2*tangent cosine u*integralKernel u := by
  have hp := RationalCircle.Stage.one_add_square_pos u
  have hc := Rat.mul_inv_cancel (1+u*u) (Rat.ne_of_gt hp)
  cases cosine <;>
    dsimp [tangent,pointRe,pointIm,pointReDerivative,pointImDerivative,
      RationalCircle.Stage.point,RationalCircle.Stage.pointDerivative,integralKernel] <;>
    simp only [Rat.div_def,Rat.inv_mul_rev] <;> grind only

theorem coordinate_bounds (cosine : Bool) {u : Rat} (hu : 0≤u ∧ u≤1) :
    0≤coordinate cosine u ∧ coordinate cosine u≤1 := by
  have hp := RationalCircle.Stage.one_add_square_pos u
  have hc := Rat.mul_inv_cancel (1+u*u) (Rat.ne_of_gt hp)
  have hsq := rat_square_nonneg_basic (u-1)
  have hu2 := rat_mul_le_mul_of_nonneg hu.1 hu.2 hu.1 hu.2
  have hi := Rat.le_of_lt (Rat.inv_pos.mpr hp)
  cases cosine
  · change 0≤(2*u)/(1+u*u) ∧ (2*u)/(1+u*u)≤1
    constructor
    · rw [Rat.div_def]; exact Rat.mul_nonneg (by grind only) hi
    · apply Rat.le_of_mul_le_mul_right (c := 1+u*u) _ hp
      rw [Rat.div_mul_cancel (Rat.ne_of_gt hp)]
      grind only
  · change 0≤(1-u*u)/(1+u*u) ∧ (1-u*u)/(1+u*u)≤1
    constructor
    · rw [Rat.div_def]; exact Rat.mul_nonneg (by grind only) hi
    · apply Rat.le_of_mul_le_mul_right (c := 1+u*u) _ hp
      rw [Rat.div_mul_cancel (Rat.ne_of_gt hp)]
      have := rat_square_nonneg_basic u
      grind only

theorem tangent_abs (cosine : Bool) {u : Rat} (hu : 0≤u ∧ u≤1) :
    qabs (tangent cosine u)≤1 := by
  cases cosine
  · have h := coordinate_bounds true hu
    change 0≤pointRe u ∧ pointRe u≤1 at h
    change qabs (pointRe u)≤1
    rw [qabs_eq_self_of_nonneg h.1]
    exact h.2
  · have h := coordinate_bounds false hu
    change 0≤pointIm u ∧ pointIm u≤1 at h
    change qabs (-pointIm u)≤1
    rw [qabs_neg,qabs_eq_self_of_nonneg h.1]
    exact h.2

/-- Exact circle-chart increments have a quadratic finite remainder. -/
theorem chart_remainder (cosine : Bool) {u v : Rat}
    (hu : 0≤u) (huv : u≤v) (hv : v≤1) :
    qabs (coordinate cosine v-coordinate cosine u-
      (v-u)*(2*tangent cosine u*integralKernel u))≤12*(v-u)*(v-u) := by
  by_cases he : u=v
  · subst v
    have he : coordinate cosine u-coordinate cosine u-(u-u)*(2*tangent cosine u*integralKernel u)=0 := by grind only
    rw [he]
    change qabs (0:Rat)≤12*(u-u)*(u-u)
    have hz : qabs (0:Rat)=0 := by decide +kernel
    rw [hz]; grind only
  have hp : 0<v-u := by grind only
  have hq : qabs ((coordinate cosine v-coordinate cosine u)/(v-u)-
      (if cosine then pointReDerivative u else pointImDerivative u))≤12*qabs (v-u) := by
    cases cosine
    · simpa only [coordinate,Bool.false_eq_true,↓reduceIte,show u+(v-u)=v by grind only] using
        pointIm_secant_error_le_twelve hu (Rat.le_trans huv hv)
          (show 0≤u+(v-u) by grind only) (show u+(v-u)≤1 by grind only) (Rat.ne_of_gt hp)
    · simpa only [coordinate,Bool.false_eq_true,↓reduceIte,show u+(v-u)=v by grind only] using
        pointRe_secant_error_le_twelve hu (Rat.le_trans huv hv)
          (show 0≤u+(v-u) by grind only) (show u+(v-u)≤1 by grind only) (Rat.ne_of_gt hp)
  rw [velocity] at hq
  have hm := Rat.mul_le_mul_of_nonneg_right hq (Rat.le_of_lt hp)
  have hc := Rat.mul_inv_cancel (v-u) (Rat.ne_of_gt hp)
  have hid : coordinate cosine v-coordinate cosine u-(v-u)*(2*tangent cosine u*integralKernel u)=
      ((coordinate cosine v-coordinate cosine u)/(v-u)-2*tangent cosine u*integralKernel u)*(v-u) := by
    rw [Rat.div_def]
    grind only
  rw [hid,qabs_mul,qabs_eq_self_of_nonneg (Rat.le_of_lt hp)]
  simpa only [qabs_eq_self_of_nonneg (Rat.le_of_lt hp)] using hm

private theorem padded_scaled_interval (X : RealCompute) (a delta q c E : Rat)
    (hd : 0≤delta) (hE : 0≤E)
    (hx : (RealCompute.ofRat (a-delta)).Le X ∧ X.Le (RealCompute.ofRat a))
    (hq : qabs (q-c*a)≤E) :
    (RealCompute.ofRat (-(E+qabs c*delta))).Le (RealCompute.ofRat q-RealCompute.scaleRat c X) ∧
    (RealCompute.ofRat q-RealCompute.scaleRat c X).Le (RealCompute.ofRat (E+qabs c*delta)) := by
  have hLo := neg_qabs_le_self (q-c*a)
  have hHi := self_le_qabs (q-c*a)
  by_cases hc : 0≤c
  · rw [qabs_eq_self_of_nonneg hc]
    constructor
    · intro i j
      have hu := Rat.mul_le_mul_of_nonneg_left (hx.2 j 0) hc
      change c*(X.compute j).lo≤c*a at hu
      change -(E+c*delta)≤q-(RealCompute.scaleRatCompute c X j).lo
      simp only [RealCompute.scaleRatCompute,if_pos hc]
      have hp := Rat.mul_nonneg hc hd
      grind only
    · intro i j
      have hl := Rat.mul_le_mul_of_nonneg_left (hx.1 0 i) hc
      change q-(RealCompute.scaleRatCompute c X i).hi≤E+c*delta
      simp only [RealCompute.scaleRatCompute,if_pos hc]
      change c*(a-delta)≤c*(X.compute i).hi at hl
      grind only
  · have hn : c≤0 := by grind only
    rw [qabs_eq_neg_of_nonpos hn]
    constructor
    · intro i j
      have hl := rat_mul_le_mul_of_nonpos_left (hx.1 0 j) hn
      change -(E+(-c)*delta)≤q-(RealCompute.scaleRatCompute c X j).lo
      simp only [RealCompute.scaleRatCompute,if_neg hc]
      change c*(X.compute j).hi≤c*(a-delta) at hl
      have hp := Rat.mul_nonneg (show 0≤-c by grind only) hd
      grind only
    · intro i j
      have hu := rat_mul_le_mul_of_nonpos_left (hx.2 i 0) hn
      change q-(RealCompute.scaleRatCompute c X i).hi≤E+(-c)*delta
      simp only [RealCompute.scaleRatCompute,if_neg hc]
      change c*a≤c*(X.compute i).lo at hu
      have hp := Rat.mul_nonneg (show 0≤-c by grind only) hd
      grind only

/-- The geometric angular derivative before inversion: the circle tangent
multiplies twice the sector-area increment, with a quadratic error. -/
theorem area_remainder (cosine : Bool) {u v : Rat}
    (hu : 0≤u) (huv : u≤v) (hv : v≤1) :
    (RealCompute.ofRat (-16*(v-u)*(v-u))).Le
      (RealCompute.ofRat (coordinate cosine v-coordinate cosine u)-
        RealCompute.scaleRat (2*tangent cosine u) (value v-value u)) ∧
    (RealCompute.ofRat (coordinate cosine v-coordinate cosine u)-
      RealCompute.scaleRat (2*tangent cosine u) (value v-value u)).Le
        (RealCompute.ofRat (16*(v-u)*(v-u))) := by
  have hd : 0≤v-u := by grind only
  have hs := Rat.mul_nonneg hd hd
  have hk := kernel_variation hu huv hv
  have hm := Rat.mul_le_mul_of_nonneg_left hk.2 hd
  have hinc : (RealCompute.ofRat ((v-u)*integralKernel u-2*(v-u)*(v-u))).Le (value v-value u) ∧
      (value v-value u).Le (RealCompute.ofRat ((v-u)*integralKernel u)) := by
    constructor
    · intro i j
      have h := (increment_bounds hu huv j).1
      change (v-u)*integralKernel u-2*(v-u)*(v-u)≤((value v).compute j).hi-((value u).compute j).lo
      grind only
    · intro i j; exact (increment_bounds hu huv i).2
  have hq := chart_remainder cosine hu huv hv
  have he : (v-u)*(2*tangent cosine u*integralKernel u)=
      (2*tangent cosine u)*((v-u)*integralKernel u) := by grind only
  rw [he] at hq
  have h := padded_scaled_interval (value v-value u) ((v-u)*integralKernel u)
    (2*(v-u)*(v-u)) (coordinate cosine v-coordinate cosine u) (2*tangent cosine u)
    (12*(v-u)*(v-u)) (by grind only) (by grind only) hinc hq
  have ht := tangent_abs cosine ⟨hu,Rat.le_trans huv hv⟩
  have hb : qabs (2*tangent cosine u)*(2*(v-u)*(v-u))≤4*(v-u)*(v-u) := by
    rw [qabs_mul,show qabs (2:Rat)=2 by decide +kernel]
    have ht' := Rat.mul_le_mul_of_nonneg_left ht (by decide +kernel : (0:Rat)≤2)
    have hm' := Rat.mul_le_mul_of_nonneg_right ht' (show 0≤2*(v-u)*(v-u) by grind only)
    grind only
  constructor
  · intro i j
    have hh := h.1 i j
    change -(12*(v-u)*(v-u)+qabs (2*tangent cosine u)*(2*(v-u)*(v-u)))≤_ at hh
    change -16*(v-u)*(v-u)≤_
    grind only
  · intro i j
    have hh := h.2 i j
    change _≤12*(v-u)*(v-u)+qabs (2*tangent cosine u)*(2*(v-u)*(v-u)) at hh
    change _≤16*(v-u)*(v-u)
    grind only

end ComputableAnalysis.GeometricTrigChart


