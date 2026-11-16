-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerRealOrder
-- name    : liuyao_ca_fd889115_k1_Analysis_EulerRealOrder
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:18:10.345209+00:00
-- url     : https://prove2.me/theorems/e2f17c2b-4426-45b9-9e23-f8dc82463a9a
-- title:
--   Computable analysis · EulerRealOrder · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/EulerRealOrder.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerTaylorFTC

set_option autoImplicit true

/-! Order and decay of the constructed Euler exponential, including a
weighted first-order bound for negative exponential parameters. -/
namespace ComputableAnalysis.EulerReal
open EulerFinite ComputableCoefficient RealApproximationOrder FTCRealOrder
set_option maxHeartbeats 800000

theorem eval_monotone {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (hxy : x.Le y) :
    (eval x).Le (eval y) := by
  intro i j
  have ha := input_within hx i
  have hb := input_within hy j
  have hn := count_large (inputBound x) i
  have hm := count_large (inputBound y) j
  change lower (x.compute i).lo (count (inputBound x) i)≤upper (y.compute j).hi (count (inputBound y) j)
  exact cross_bound (count_positive _ _) (count_positive _ _) (by grind only) (by grind only) (hxy i j)

theorem eval_nonnegative {x : RealCompute} (hx : x.Valid) : (RealCompute.ofRat 0).Le (eval x) := by
  obtain ⟨k,hk⟩ := eval_positive hx
  intro i j
  have H := RealCompute.le_refl _ (eval_valid hx) k j
  change 0≤((eval x).compute j).hi
  grind only

theorem negative_small {x : RealCompute} (hx : x.Valid) (hneg : x.Le (RealCompute.ofRat 0)) :
    Small (parameter (eval x) (eval_valid hx)) 1 := by
  have H := eval_monotone (y := RealCompute.ofRat 0) hx (RealCompute.ofRat_valid 0) hneg
  have hu := RealCompute.le_trans (sample_valid 0) H
    (RealCompute.le_of_equiv (y := RealCompute.ofRat 1) (sample_valid 0) (RealCompute.ofRat_valid 1) sample_zero)
  have hl := eval_nonnegative hx
  constructor
  · intro i j
    have L := hl 0 j
    change -(1:Rat)≤((eval x).compute j).hi
    change (0:Rat)≤((eval x).compute j).hi at L
    grind only
  · exact hu

/-- A finite Bernoulli bound gives an actual exponential decay bound. -/
theorem sample_negative_decay (s : Rat) (hs : 0≤s) :
    (sample (-s)).Le (RealCompute.ofRat (1/(1+s))) := by
  intro i j
  let N := count (inputBound (RealCompute.ofRat (-s))) i
  have hn : 0<(N:Rat) := count_positive _ _
  have hc := Rat.mul_inv_cancel (N:Rat) (Rat.ne_of_gt hn)
  have hi : 0≤(N:Rat)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hn)
  have ht : -1≤s/(N:Rat) := by
    have H := Rat.mul_nonneg hs hi
    simp only [Rat.div_def] at *
    grind only
  have H := bernoulli ht N
  have he : 1+(N:Rat)*(s/(N:Rat))=1+s := by simp only [Rat.div_def]; grind only
  rw [he] at H
  have hp : 0<1+s := by grind only
  have inv := inv_antitone hp H
  have ordered := RealCompute.interval_order_of_valid _ (sample_valid (-s)) i
  change ((sample (-s)).compute i).lo≤1/(1+s)
  have hb : ((sample (-s)).compute i).hi≤1/(1+s) := by
    change upper (-s) N≤1/(1+s)
    simp only [EulerFinite.upper,Rat.neg_neg,EulerFinite.lower,Rat.div_def,Rat.one_mul] at *
    exact inv
  exact Rat.le_trans ordered hb

def negativeSample (q t : Rat) : Value := EulerTaylorFTC.value (-q*t)

def parameterRemainder (q u v : Rat) : Value :=
  sub (sub (negativeSample q v) (negativeSample q u))
    (scale (v-u) (Value.neg (scale q (negativeSample q u))))

/-- Convex supporting secants give the second-order error with its damping
factor retained. This is stronger than an undamped uniform bound. -/
theorem negative_parameter_remainder (q u v : Rat) (hq : 0≤q) (huv : u<v) :
    LE (Value.rational 0) (parameterRemainder q u v) ∧
    LE (parameterRemainder q u v) (scale (q*q*(v-u)*(v-u)) (negativeSample q u)) := by
  by_cases hz : q=0
  · subst q
    have H : (parameterRemainder 0 u v).real.preferred.Equiv (Value.rational 0).real.preferred := by
      apply arithmetic_identity; intro s
      simp only [parameterRemainder,negativeSample,Rat.zero_mul,Rat.neg_zero,Value.neg,scale,sub,Value.rational]
      grind only
    have G : (scale ((0:Rat)*0*(v-u)*(v-u)) (negativeSample 0 u)).real.preferred.Equiv (Value.rational 0).real.preferred := by
      apply arithmetic_identity; intro s; simp only [scale,Value.rational,Rat.zero_mul]
    have z : LE (Value.rational 0) (Value.rational 0) := fun _ _ => Rat.le_refl
    exact ⟨le_congr z (RealCompute.equiv_refl _ (RealCompute.ofRat_valid 0)) (RealCompute.equiv_symm H),
      le_congr z (RealCompute.equiv_symm H) (RealCompute.equiv_symm G)⟩
  have qp : 0<q := by grind only
  have hh : 0≤q*(v-u) := Rat.mul_nonneg hq (by grind only)
  have hp : -q*v< -q*u := by
    have H := Rat.mul_lt_mul_of_pos_left huv qp
    grind only
  have H := EulerTaylorFTC.supports (-q*v) (-q*u) hp
  let U := negativeSample q u
  let V := negativeSample q v
  let d := sub U V
  let k := q*(v-u)
  have lower : LE (scale k V) d := by
    apply le_congr H.1
    · apply arithmetic_identity; intro s; simp only [scale,k,negativeSample,V]; grind only
    · exact RealCompute.equiv_refl _ d.real.valid
  have upper : LE d (scale k U) := by
    apply le_congr H.2
    · exact RealCompute.equiv_refl _ d.real.valid
    · apply arithmetic_identity; intro s; simp only [scale,k,negativeSample,U]; grind only
  have lowerR := RealCompute.le_sub_le_sub upper (RealCompute.le_refl d.real.preferred d.real.valid)
  have lowerR' : LE (Value.rational 0) (parameterRemainder q u v) := by
    apply le_congr (x := sub d d) (y := sub (scale k U) d) lowerR
    · apply arithmetic_identity (sub d d) (Value.rational 0); intro s; simp only [sub,Value.rational]; grind only
    · apply arithmetic_identity (sub (scale k U) d) (parameterRemainder q u v)
      intro s; simp only [parameterRemainder,sub,scale,Value.neg,k,d,U,V]; grind only
  have midR := RealCompute.le_sub_le_sub (RealCompute.le_refl (scale k U).real.preferred (scale k U).real.valid) lower
  have midR' : LE (parameterRemainder q u v) (scale k d) := by
    apply le_congr (x := sub (scale k U) d) (y := sub (scale k U) (scale k V)) midR
    · apply arithmetic_identity (sub (scale k U) d) (parameterRemainder q u v)
      intro s; simp only [parameterRemainder,sub,scale,Value.neg,k,d,U,V]; grind only
    · apply arithmetic_identity (sub (scale k U) (scale k V)) (scale k d)
      intro s; simp only [sub,scale,d]; grind only
  have upperR := le_scale upper hh
  have upperR' : LE (scale k d) (scale (q*q*(v-u)*(v-u)) U) := by
    apply le_congr upperR
    · exact RealCompute.equiv_refl _ (scale k d).real.valid
    · apply arithmetic_identity; intro s; simp only [scale,k]; grind only
  exact ⟨lowerR',RealCompute.le_trans (scale k d).real.valid midR' upperR'⟩

end ComputableAnalysis.EulerReal


