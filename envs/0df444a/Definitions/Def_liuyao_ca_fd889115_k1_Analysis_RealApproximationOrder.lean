-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealApproximationOrder
-- name    : liuyao_ca_fd889115_k1_Analysis_RealApproximationOrder
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:55:41.54898+00:00
-- url     : https://prove2.me/theorems/35518371-daf5-4ece-9cf7-9e3a7bc80bb4
-- title:
--   Computable analysis · RealApproximationOrder · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RealApproximationOrder.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComputableCoefficient
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteDerivativeLimit

set_option autoImplicit true

/-! Passing shrinking rational approximation errors to exact real order.
All proofs use real intervals and rational arithmetic. -/
namespace ComputableAnalysis.RealApproximationOrder
open ComputableCoefficient
set_option maxHeartbeats 2000000

def parameter (x : RealCompute) (hx : x.Valid) : Value := Value.parameter (RealCompute.Certified.ofRaw x hx)

def sub (x y : Value) : Value where
  real := RealCompute.Certified.ofRaw (x.real.preferred-y.real.preferred) (RealCompute.sub_valid x.real.valid y.real.valid)
  sample s := x.sample s-y.sample s
  observation n := max (x.observation n) (y.observation n)
  encloses := by
    intro n m hm s hs
    have hx := x.encloses n m (by omega) s hs
    have hy := y.encloses n m (by omega) s hs
    change (x.real.compute n).lo-(y.real.compute n).hi≤_ ∧
      _≤(x.real.compute n).hi-(y.real.compute n).lo
    constructor <;> grind only

def scale (c : Rat) (x : Value) : Value where
  real := RealCompute.Certified.ofRaw (RealCompute.scaleRat c x.real.preferred) (RealCompute.scaleRat_valid x.real.valid)
  sample s := c*x.sample s
  observation := x.observation
  encloses n m hm s hs := QInterval.scaleRat_mem (x.encloses n m hm s hs)

def Small (x : Value) (B : Rat) : Prop :=
  (RealCompute.ofRat (-B)).Le x.real.preferred ∧ x.real.preferred.Le (RealCompute.ofRat B)

theorem le_of_approximate_samples (x y : Value) (error : Nat → Rat)
    (shrinks : ShrinksToZero error) (N : Nat)
    (h : ∀ m, N≤m → ∀ s, Samples m s → x.sample s≤y.sample s+error m) :
    x.real.preferred.Le y.real.preferred := by
  intro i j
  by_cases he : (x.real.compute i).lo≤(y.real.compute j).hi
  · exact he
  have hp : 0<((x.real.compute i).lo-(y.real.compute j).hi)/2 := by grind only
  obtain ⟨K,hK⟩ := shrinks ⟨_,hp⟩
  let m := max N (max K (max (x.observation i) (y.observation j)))
  have hs := samples_lower m
  have hx := x.encloses i m (by dsimp [m]; omega) _ hs
  have hy := y.encloses j m (by dsimp [m]; omega) _ hs
  have ha := h m (by dsimp [m]; omega) _ hs
  have hk := hK m (by dsimp [m]; omega)
  change error m≤((x.real.compute i).lo-(y.real.compute j).hi)/2 at hk
  grind only

theorem small_of_approximate_samples (x : Value) (B : Rat) (error : Nat → Rat)
    (shrinks : ShrinksToZero error) (N : Nat)
    (h : ∀ m, N≤m → ∀ s, Samples m s → qabs (x.sample s)≤B+error m) : Small x B := by
  constructor
  · apply le_of_approximate_samples (Value.rational (-B)) x error shrinks N
    intro m hm s hs
    have ha := h m hm s hs
    have hl := neg_qabs_le_self (x.sample s)
    change -B≤x.sample s+error m
    grind only
  · apply le_of_approximate_samples x (Value.rational B) error shrinks N
    intro m hm s hs
    have ha := h m hm s hs
    have hu := self_le_qabs (x.sample s)
    exact Rat.le_trans hu ha

theorem le_of_samples (x y : Value) (N : Nat)
    (h : ∀ m, N≤m → ∀ s, Samples m s → x.sample s≤y.sample s) :
    x.real.preferred.Le y.real.preferred := by
  apply le_of_approximate_samples x y (fun _ => 0) (fun eps => ⟨0,fun _ _ => Rat.le_of_lt eps.property⟩) N
  intro m hm s hs
  have hh := h m hm s hs
  simpa only [Rat.add_zero] using hh

theorem small_of_samples (x : Value) (B : Rat) (N : Nat)
    (h : ∀ m, N≤m → ∀ s, Samples m s → qabs (x.sample s)≤B) : Small x B :=
  small_of_approximate_samples x B (fun _ => 0) (fun eps => ⟨0,fun _ _ => Rat.le_of_lt eps.property⟩)
    N (fun m hm s hs => by simpa only [Rat.add_zero] using h m hm s hs)

theorem constant_le_of_shrinking_errors (x : RealCompute) (L : Rat) (error : Nat → Rat)
    (shrinks : ShrinksToZero error)
    (h : ∀ n, L-error n≤(x.compute n).hi) (hx : x.Valid) : (RealCompute.ofRat L).Le x := by
  intro i j
  by_cases he : L≤(x.compute j).hi
  · exact he
  have hp : 0<(L-(x.compute j).hi)/2 := by grind only
  obtain ⟨N,hN⟩ := shrinks ⟨_,hp⟩
  let n := max N j
  have hn := hN n (Nat.le_max_left _ _)
  have hh := h n
  have hb := hx.2.1 j n (Nat.le_max_right _ _)
  change error n≤(L-(x.compute j).hi)/2 at hn
  grind only

end ComputableAnalysis.RealApproximationOrder


