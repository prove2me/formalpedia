-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerPowerLimit
-- name    : liuyao_ca_fd889115_k1_Analysis_EulerPowerLimit
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:57:35.480302+00:00
-- url     : https://prove2.me/theorems/2978c137-cb1b-4e2f-a0be-e5a6d236ac0d
-- title:
--   Computable analysis · EulerPowerLimit · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/EulerPowerLimit.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerReal
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueBounds

set_option autoImplicit true

/-! The full integer-step Euler limit on arbitrary represented real inputs.
No series is used in this module. -/
namespace ComputableAnalysis.EulerPowerLimit
open EulerFinite EulerReal ComputableCoefficient RealApproximationOrder RawLimit
set_option maxHeartbeats 2500000

def power (X : Value) : Nat → Value
  | 0 => Value.rational 1
  | n+1 => Value.mul (power X n) X

theorem power_sample (X : Value) (n : Nat) (s : RealCompute.Certified → Rat) :
    (power X n).sample s=(X.sample s)^n := by
  induction n with
  | zero => simp only [power,Value.rational,Rat.pow_zero]
  | succ n ih => simp only [power,Value.mul,ih,Rat.pow_succ]

def approximation (X : Value) (N : Nat) : Value :=
  power (Value.add (Value.rational 1) (scale (1/(N:Rat)) X)) N

theorem approximation_sample (X : Value) (N : Nat) (s : RealCompute.Certified → Rat) :
    (approximation X N).sample s=lower (X.sample s) N := by
  rw [approximation,power_sample]
  simp only [Value.add,Value.rational,scale,lower]
  congr 1
  grind only [Rat.div_def]

def threshold (C : Rat) : Nat := start (C+2*C*C)
def errorConstant (C : Rat) : Rat := 2*budget C*C*C

theorem errorConstant_nonnegative {C : Rat} (hC : 0≤C) : 0≤errorConstant C := by
  have H := Rat.mul_nonneg (Rat.le_of_lt (budget_positive C)) (Rat.mul_nonneg hC hC)
  dsimp [errorConstant]
  grind only

theorem threshold_properties {C : Rat} (hC : 0≤C) {N : Nat} (hN : threshold C≤N) :
    0<(N:Rat) ∧ C<(N:Rat) ∧ 2*C*C<(N:Rat) := by
  have H := start_large (C+2*C*C)
  have H0 := start_positive (C+2*C*C)
  have HC := Rat.mul_nonneg hC hC
  have HN : (threshold C:Rat)≤(N:Rat) := by exact_mod_cast hN
  exact ⟨by dsimp [threshold] at HN; grind only,
    by dsimp [threshold] at HN; grind only,
    by dsimp [threshold] at HN; grind only⟩

/-- A uniform bound for the reciprocal enclosure, valid at every sufficiently
large integer step count, not merely at the scheduled dyadic counts. -/
theorem upper_bound {C q : Rat} (hC : 0≤C) (hq : qabs q≤C) {N : Nat}
    (hN : threshold C≤N) : upper q N≤2*budget C := by
  obtain ⟨hNp,hNC,hN2⟩ := threshold_properties hC hN
  have hlo : -C≤q := by have := neg_qabs_le_self q; grind only
  have hhi : q≤C := Rat.le_trans (self_le_qabs q) hq
  have H := gap_bound hNp (q := q) (by grind only) (by grind only)
  have hu := upper_positive hNp (q := q) (by grind only)
  have HL := cross_bound hNp (start_positive C) (a := q) (b := C)
    (by grind only) (start_large C) hhi
  have hs : q*q≤C*C := by
    have H := Rat.mul_nonneg (show 0≤C-q by grind only) (show 0≤C+q by grind only)
    grind only
  have hi := Rat.inv_pos.mpr hNp
  have hc := Rat.mul_inv_cancel (N:Rat) (Rat.ne_of_gt hNp)
  have hb := Rat.mul_lt_mul_of_pos_right hN2 hi
  have hprod := Rat.mul_le_mul_of_nonneg_left hs (Rat.le_of_lt hu)
  have he := Rat.mul_le_mul_of_nonneg_right hprod (Rat.le_of_lt hi)
  change lower q N≤budget C at HL
  have half : q*q/(N:Rat)≤1/2 := by
    have h := Rat.mul_le_mul_of_nonneg_right hs (Rat.le_of_lt hi)
    grind only [Rat.div_def]
  have hp := Rat.mul_le_mul_of_nonneg_left half (Rat.le_of_lt hu)
  simp only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul] at H
  grind only [Rat.div_def]

theorem gap_uniform {C q : Rat} (hC : 0≤C) (hq : qabs q≤C) {N : Nat}
    (hN : threshold C≤N) : upper q N-lower q N≤errorConstant C/(N:Rat) := by
  obtain ⟨hNp,hNC,_⟩ := threshold_properties hC hN
  have hlo := neg_qabs_le_self q
  have hhi := self_le_qabs q
  have H := gap_bound hNp (q := q) (by grind only) (by grind only)
  have U := upper_bound hC hq hN
  have hs : q*q≤C*C := by
    have H := Rat.mul_nonneg (show 0≤C-q by grind only) (show 0≤C+q by grind only)
    grind only
  have hprod := rat_mul_le_mul_of_nonneg (Rat.le_of_lt (upper_positive hNp (by grind only))) U
    (rat_square_nonneg_basic q) hs
  have hi := Rat.le_of_lt (Rat.inv_pos.mpr hNp)
  have hr := Rat.mul_le_mul_of_nonneg_right hprod hi
  dsimp [errorConstant]
  simp only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul] at H
  grind only [Rat.div_def]

/-- Quantitative comparison of the full represented power with the ODE Euler
value. Input observation errors vanish inside the proof, not as caller data. -/
theorem approximation_error {x : RealCompute} (hx : x.Valid) {N : Nat}
    (hN : threshold (inputBound x)≤N) :
    Small (sub (parameter (eval x) (eval_valid hx)) (approximation (parameter x hx) N))
      (errorConstant (inputBound x)/(N:Rat)) := by
  let C := inputBound x
  have hC := Rat.le_of_lt (inputBound_positive x)
  obtain ⟨hNp,hNC,_⟩ := threshold_properties hC hN
  apply small_of_approximate_samples _ _ (fun n => ((eval x).compute n).width) (eval_valid hx).2.2 0
  intro m hm s hs
  have Hx := (parameter x hx).encloses m m (Nat.le_refl _) s hs
  have Hy := (parameter (eval x) (eval_valid hx)).encloses m m (Nat.le_refl _) s hs
  change (x.compute m).lo≤(parameter x hx).sample s ∧ (parameter x hx).sample s≤(x.compute m).hi at Hx
  change ((eval x).compute m).lo≤(parameter (eval x) (eval_valid hx)).sample s ∧
    (parameter (eval x) (eval_valid hx)).sample s≤((eval x).compute m).hi at Hy
  have HC := input_within hx m
  let q := (parameter x hx).sample s
  change (x.compute m).lo≤q ∧ q≤(x.compute m).hi at Hx
  have hq : qabs q≤C := qabs_le_of_neg_le_le (Rat.le_trans HC.1 Hx.1) (Rat.le_trans Hx.2 HC.2)
  have HP := gap_uniform hC hq hN
  have HE0 : 0≤errorConstant (inputBound x)/(N:Rat) :=
    Rat.mul_nonneg (errorConstant_nonnegative hC) (Rat.le_of_lt (Rat.inv_pos.mpr hNp))
  have H1 := cross_bound (count_positive C m) hNp (a := (x.compute m).lo) (b := q)
    (by have := count_large C m; change -C≤(x.compute m).lo ∧ (x.compute m).hi≤C at HC; grind only)
    (by have := self_le_qabs q; grind only) Hx.1
  have H2 := cross_bound hNp (count_positive C m) (a := q) (b := (x.compute m).hi)
    (by have := neg_qabs_le_self q; grind only)
    (by have := count_large C m; change -C≤(x.compute m).lo ∧ (x.compute m).hi≤C at HC; grind only) Hx.2
  change ((eval x).compute m).lo≤upper q N at H1
  change lower q N≤((eval x).compute m).hi at H2
  simp only [sub,approximation_sample]
  change qabs ((parameter (eval x) (eval_valid hx)).sample s-lower q N)≤_
  apply qabs_le_of_neg_le_le <;> unfold QInterval.width <;> grind only

/-- The classical limit uses every integer step count. Its domain is every
valid represented real, including irrational and negative inputs. -/
theorem powers_tend_to {x : RealCompute} (hx : x.Valid) :
    TendsTo (fun N => (approximation (parameter x hx) N).real.preferred) (eval x) := by
  refine ⟨eval_valid hx,fun N => (approximation (parameter x hx) N).real.valid,?_⟩
  intro m eps
  obtain ⟨K,hK⟩ := shrinksToZero_of_ratOverSuccBound
    (C := errorConstant (inputBound x)) (fun _ => Rat.le_refl) eps
  refine ⟨max (threshold (inputBound x)) (K+1),fun N hN => ?_⟩
  have H := (approximation_error hx (by omega : threshold (inputBound x)≤N)).neg
  have HE : Small (sub (approximation (parameter x hx) N) (parameter (eval x) (eval_valid hx)))
      (errorConstant (inputBound x)/(N:Rat)) := by
    apply H.congr
    apply arithmetic_identity
    intro s; simp only [Value.neg,sub]; grind only
  have HB := inInterval_of_sub_bound (approximation (parameter x hx) N).real.valid (eval_valid hx)
    _ HE.1 HE.2 m
  have hk := hK (N-1) (by omega)
  change errorConstant (inputBound x)/((N-1+1:Nat):Rat)≤eps.val at hk
  rw [show N-1+1=N by have := (threshold_properties (Rat.le_of_lt (inputBound_positive x))
    (show threshold (inputBound x)≤N by omega)).1; have : 0<N := Rat.natCast_pos.mp this; omega] at hk
  apply RealIntervalImage.weaken HB
  unfold QInterval.ContainsInterval QInterval.expand
  constructor <;> grind only

theorem power_congr {X Y : Value} (h : X.real.preferred.Equiv Y.real.preferred) (N : Nat) :
    (power X N).real.preferred.Equiv (power Y N).real.preferred := by
  induction N with
  | zero => exact RealCompute.equiv_refl _ (RealCompute.ofRat_valid 1)
  | succ N ih =>
    exact RealCompute.mul_equiv (power X N).real.valid (power Y N).real.valid
      X.real.valid Y.real.valid ih h

theorem approximation_congr {X Y : Value} (h : X.real.preferred.Equiv Y.real.preferred) (N : Nat) :
    (approximation X N).real.preferred.Equiv (approximation Y N).real.preferred := by
  apply power_congr
  exact RealCompute.add_equiv (RealCompute.ofRat_valid 1) (RealCompute.ofRat_valid 1)
    (scale (1/(N:Rat)) X).real.valid (scale (1/(N:Rat)) Y).real.valid
    (RealCompute.equiv_refl _ (RealCompute.ofRat_valid 1)) (RealCompute.scaleRat_equiv h)

end ComputableAnalysis.EulerPowerLimit


