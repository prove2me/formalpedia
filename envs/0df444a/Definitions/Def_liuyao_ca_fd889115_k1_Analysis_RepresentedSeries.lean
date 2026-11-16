-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RepresentedSeries
-- name    : liuyao_ca_fd889115_k1_Analysis_RepresentedSeries
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:09:23.067859+00:00
-- url     : https://prove2.me/theorems/08fcda00-3781-4ba9-a5f4-44b9260f46f9
-- title:
--   Computable analysis · RepresentedSeries · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RepresentedSeries.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCRealCalculus

set_option autoImplicit true

/-! Sums of represented real terms. A summation claim is convergence of the
actual finite sums. Computation uses finite polynomial/value boxes and an
explicit error, with finite intersections for nesting. -/
namespace ComputableAnalysis.RepresentedSeries
open ComputableCoefficient RealApproximationOrder RawLimit
set_option maxHeartbeats 600000

def finiteSum (u : Nat → Value) : Nat → Value
  | 0 => Value.rational 0
  | n+1 => Value.add (finiteSum u n) (u n)

def HasSum (u : Nat → Value) (x : RealCompute) : Prop :=
  TendsTo (fun n => (finiteSum u n).real.preferred) x

theorem HasSum.unique {u : Nat → Value} {x y : RealCompute} (hx : HasSum u x) (hy : HasSum u y) : x.Equiv y :=
  RawLimit.unique hx hy

theorem finiteSum_congr {u v : Nat → Value}
    (h : ∀ n, (u n).real.preferred.Equiv (v n).real.preferred) (N : Nat) :
    (finiteSum u N).real.preferred.Equiv (finiteSum v N).real.preferred := by
  induction N with
  | zero => exact RealCompute.equiv_refl _ (RealCompute.ofRat_valid 0)
  | succ n ih =>
    exact RealCompute.add_equiv (finiteSum u n).real.valid (finiteSum v n).real.valid
      (u n).real.valid (v n).real.valid ih (h n)

theorem HasSum.congr_terms {u v : Nat → Value} {x : RealCompute} (h : HasSum u x)
    (terms : ∀ n, (u n).real.preferred.Equiv (v n).real.preferred) : HasSum v x :=
  RawLimit.congr_sequence h (fun n => (finiteSum v n).real.valid) (finiteSum_congr terms)

def stage (P : Nat → Value) (n : Nat) : Nat :=
  ConvexFTC.WidthSearch.stage (P n).real.preferred (P n).real.valid ⟨allowance n,allowance_pos n⟩

def box (P : Nat → Value) (e : Nat → Rat) (n : Nat) : QInterval :=
  QInterval.expand ((P n).real.compute (stage P n)) (e n)

def sum (P : Nat → Value) (e : Nat → Rat) : RealCompute := prefixRaw (box P e)

theorem box_width (P : Nat → Value) (e : Nat → Rat) (n : Nat) :
    (box P e n).width≤allowance n+2*e n := by
  have hw := ConvexFTC.WidthSearch.stage_spec (P n).real.preferred (P n).real.valid ⟨allowance n,allowance_pos n⟩
  change ((P n).real.compute (stage P n)).width≤allowance n at hw
  unfold box QInterval.expand QInterval.width at *
  grind only

theorem box_shrinks (P : Nat → Value) (e : Nat → Rat) (he : ShrinksToZero e) :
    RealCompute.WidthsShrinkToZero (box P e) := by
  intro eps
  let third : QPos := ⟨eps.val/3,by have := eps.property; grind only⟩
  obtain ⟨N,hN⟩ := allowance_shrinks third
  obtain ⟨M,hM⟩ := he third
  refine ⟨max N M,fun n hn => ?_⟩
  have ha := hN n (by omega)
  have hb := hM n (by omega)
  have hw := box_width P e n
  change allowance n≤eps.val/3 at ha
  change e n≤eps.val/3 at hb
  grind only

theorem box_covers (P : Nat → Value) (e : Nat → Rat) (X : Value)
    (bound : ∀ n, Small (sub X (P n)) (e n)) (n : Nat) : InInterval X.real.preferred (box P e n) :=
  inInterval_of_sub_bound X.real.valid (P n).real.valid (e n) (bound n).1 (bound n).2 (stage P n)

theorem sum_valid (P : Nat → Value) (e : Nat → Rat) (he : ShrinksToZero e) (X : Value)
    (bound : ∀ n, Small (sub X (P n)) (e n)) : (sum P e).Valid :=
  prefix_valid (tests := fun _ y => y=X.real.preferred) (s := fun n => n)
    (fun _ _ _ _ h => h) (fun _ => ⟨X.real.preferred,X.real.valid,rfl⟩)
    (by intro k y hy; subst y; exact box_covers P e X bound k) (box_shrinks P e he)

/-- The equality follows from the independently proved finite errors. The
sum program itself only evaluates finite sums, error budgets and intersections. -/
theorem sum_identify (P : Nat → Value) (e : Nat → Rat) (X : Value)
    (bound : ∀ n, Small (sub X (P n)) (e n)) : (sum P e).Equiv X.real.preferred := by
  intro n
  have h := prefix_cover (tests := fun _ y => y=X.real.preferred) (s := fun n => n)
    (fun _ _ _ _ h => h) (by intro k y hy; subst y; exact box_covers P e X bound k)
    n X.real.preferred rfl
  apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
  exact ⟨h.1 0 n,h.2 n 0⟩

theorem hasSum_of_errors (u : Nat → Value) (X : Value) (e : Nat → Rat) (he : ShrinksToZero e)
    (bound : ∀ n, Small (sub X (finiteSum u n)) (e n)) : HasSum u X.real.preferred := by
  refine ⟨X.real.valid,fun n => (finiteSum u n).real.valid,?_⟩
  intro m eps
  obtain ⟨N,hN⟩ := he eps
  refine ⟨N,fun n hn => ?_⟩
  have H := (bound n).neg
  have H' : Small (sub (finiteSum u n) X) (e n) := by
    apply H.congr
    apply arithmetic_identity
    intro s
    simp only [Value.neg,sub]
    grind only
  have h := inInterval_of_sub_bound (finiteSum u n).real.valid X.real.valid (e n) H'.1 H'.2 m
  apply RealIntervalImage.weaken h
  unfold QInterval.ContainsInterval QInterval.expand
  have heps := hN n hn
  constructor <;> grind only

end ComputableAnalysis.RepresentedSeries


