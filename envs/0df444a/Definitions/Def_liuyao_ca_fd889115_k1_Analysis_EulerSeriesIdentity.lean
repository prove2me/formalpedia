-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerSeriesIdentity
-- name    : liuyao_ca_fd889115_k1_Analysis_EulerSeriesIdentity
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:09:50.987366+00:00
-- url     : https://prove2.me/theorems/5885b773-ac43-4ce2-9898-1b1743a1d5bd
-- title:
--   Computable analysis · EulerSeriesIdentity · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/EulerSeriesIdentity.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerSeriesFinite
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerPowerLimit
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RepresentedSeries

set_option autoImplicit true

/-! Exact agreement between the ODE Euler construction, the full power
limit, and the factorial exponential series on every represented real. -/
namespace ComputableAnalysis.EulerSeriesIdentity
open ComputableCoefficient RealApproximationOrder RawLimit EulerReal EulerPowerLimit
open EulerSeriesFinite RationalMajorant
set_option maxHeartbeats 2500000

def terms (X : Value) (k : Nat) : Value := scale (1/factorialRat k) (power X k)
def finiteValue (X : Value) (k : Nat) : Value := RepresentedSeries.finiteSum (terms X) k

theorem partial_sample (X : Value) (k : Nat) (s : RealCompute.Certified → Rat) :
    (finiteValue X k).sample s=factorialPrefix (X.sample s) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (finiteValue X k).sample s+(terms X k).sample s=_
    rw [ih,factorialPrefix]
    simp only [terms,scale,power_sample,term]
    grind only [Rat.div_def]

def factorialConstant (C : Rat) : Rat := C*C*factorialSeriesFiniteBound C
def constant (C : Rat) : Rat := errorConstant C+factorialConstant C

theorem constant_nonnegative {C : Rat} (hC : 0≤C) : 0≤constant C :=
  Rat.add_nonneg (errorConstant_nonnegative hC)
    (Rat.mul_nonneg (Rat.mul_nonneg hC hC) (factorialSeriesFiniteBound_nonneg hC))

theorem finite_series_error {x : RealCompute} (hx : x.Valid) {N : Nat} (hN : 0<N) :
    Small (sub (finiteValue (parameter x hx) (N+1)) (approximation (parameter x hx) N))
      (factorialConstant (inputBound x)/(N:Rat)) := by
  apply small_of_samples _ _ 0
  intro m hm s hs
  have Hx := (parameter x hx).encloses 0 m (Nat.zero_le _) s hs
  change (x.compute 0).lo≤(parameter x hx).sample s ∧ (parameter x hx).sample s≤(x.compute 0).hi at Hx
  have HC := input_within hx 0
  have Hq : qabs ((parameter x hx).sample s)≤inputBound x :=
    qabs_le_of_neg_le_le (Rat.le_trans HC.1 Hx.1) (Rat.le_trans Hx.2 HC.2)
  simpa only [sub,partial_sample,approximation_sample,factorialConstant] using
    euler_factorial_error hN (Rat.le_of_lt (inputBound_positive x)) Hq

/-- A finite factorial prefix approximates the actual ODE Euler value.
This proves the identification, without assuming an ODE uniqueness law. -/
theorem partial_error {x : RealCompute} (hx : x.Valid) {N : Nat}
    (hN : threshold (inputBound x)≤N) :
    Small (sub (parameter (eval x) (eval_valid hx)) (finiteValue (parameter x hx) (N+1)))
      (constant (inputBound x)/(N:Rat)) := by
  have hNp : 0<N := Rat.natCast_pos.mp
    (threshold_properties (Rat.le_of_lt (inputBound_positive x)) hN).1
  have H := (approximation_error hx hN).add (finite_series_error hx hNp).neg
  have HB : errorConstant (inputBound x)/(N:Rat)+factorialConstant (inputBound x)/(N:Rat)=
      constant (inputBound x)/(N:Rat) := by dsimp [constant]; grind only [Rat.div_def]
  rw [HB] at H
  apply H.congr
  apply arithmetic_identity
  intro s
  simp only [Value.add,Value.neg,sub]
  grind only

/-- The actual factorial power series converges to the Euler ODE function at
every valid represented real, including irrational coefficients/inputs. -/
theorem exponential_hasSum {x : RealCompute} (hx : x.Valid) :
    RepresentedSeries.HasSum (terms (parameter x hx)) (eval x) := by
  refine ⟨eval_valid hx,fun n => (finiteValue (parameter x hx) n).real.valid,?_⟩
  intro m eps
  obtain ⟨K,hK⟩ := shrinksToZero_of_ratOverSuccBound
    (C := constant (inputBound x)) (fun _ => Rat.le_refl) eps
  refine ⟨max (threshold (inputBound x)+1) (K+2),fun n hn => ?_⟩
  have H := (partial_error hx (N := n-1) (by omega)).neg
  have HE : Small (sub (finiteValue (parameter x hx) n) (parameter (eval x) (eval_valid hx)))
      (constant (inputBound x)/((n-1:Nat):Rat)) := by
    rw [show n-1+1=n by omega] at H
    apply H.congr
    apply arithmetic_identity
    intro s; simp only [Value.neg,sub]; grind only
  have HB := inInterval_of_sub_bound (finiteValue (parameter x hx) n).real.valid (eval_valid hx) _ HE.1 HE.2 m
  have hk := hK (n-2) (by omega)
  change constant (inputBound x)/((n-2+1:Nat):Rat)≤eps.val at hk
  rw [show n-2+1=n-1 by omega] at hk
  apply RealIntervalImage.weaken HB
  unfold QInterval.ContainsInterval QInterval.expand
  constructor <;> grind only

def seriesStage (x : RealCompute) (n : Nat) : Nat := threshold (inputBound x)+n

def seriesError (x : RealCompute) (n : Nat) : Rat := constant (inputBound x)/(seriesStage x n:Rat)

theorem seriesError_shrinks (x : RealCompute) : ShrinksToZero (seriesError x) := by
  apply shrinksToZero_of_ratOverSuccBound (C := constant (inputBound x))
  intro n
  have ht : 0<threshold (inputBound x) := Rat.natCast_pos.mp (start_positive _)
  have H : ((n+1:Nat):Rat)≤(seriesStage x n:Rat) := by exact_mod_cast (show n+1≤seriesStage x n by dsimp [seriesStage]; omega)
  have hn : 0<((n+1:Nat):Rat) := Rat.natCast_pos.mpr (Nat.succ_pos n)
  have HI := EulerFinite.inv_antitone hn H
  exact Rat.mul_le_mul_of_nonneg_left HI (constant_nonnegative (Rat.le_of_lt (inputBound_positive x)))

/-- A series evaluator with finite factorial prefixes and errors in its
boxes. Its runtime does not evaluate the Euler ODE function. -/
def seriesAt (x : RealCompute) (hx : x.Valid) : RealCompute :=
  RepresentedSeries.sum (fun n => finiteValue (parameter x hx) (seriesStage x n+1)) (seriesError x)

theorem seriesAt_valid {x : RealCompute} (hx : x.Valid) : (seriesAt x hx).Valid :=
  RepresentedSeries.sum_valid _ _ (seriesError_shrinks x) (parameter (eval x) (eval_valid hx))
    (fun n => partial_error hx (by dsimp [seriesStage]; omega))

/-- Exact equality of values, not equality of finite-stage intervals. -/
theorem seriesAt_equiv_euler {x : RealCompute} (hx : x.Valid) : (seriesAt x hx).Equiv (eval x) :=
  RepresentedSeries.sum_identify _ _ (parameter (eval x) (eval_valid hx))
    (fun n => partial_error hx (by dsimp [seriesStage]; omega))

theorem seriesAt_congr {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (h : x.Equiv y) :
    (seriesAt x hx).Equiv (seriesAt y hy) :=
  RealCompute.equiv_trans (seriesAt_valid hx) (eval_valid hx) (seriesAt_valid hy)
    (seriesAt_equiv_euler hx)
    (RealCompute.equiv_trans (eval_valid hx) (eval_valid hy) (seriesAt_valid hy)
      (eval_congr hx hy h) (RealCompute.equiv_symm (seriesAt_equiv_euler hy)))

/-- The full integer-step power limit also converges to the independent
factorial-prefix evaluator. -/
theorem powers_tend_to_series {x : RealCompute} (hx : x.Valid) :
    TendsTo (fun N => (approximation (parameter x hx) N).real.preferred) (seriesAt x hx) :=
  congr_target (powers_tend_to hx) (seriesAt_valid hx) (RealCompute.equiv_symm (seriesAt_equiv_euler hx))

end ComputableAnalysis.EulerSeriesIdentity


