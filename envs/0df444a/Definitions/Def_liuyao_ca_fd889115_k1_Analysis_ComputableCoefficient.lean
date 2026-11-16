-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComputableCoefficient
-- name    : liuyao_ca_fd889115_k1_Analysis_ComputableCoefficient
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:52:35.361243+00:00
-- url     : https://prove2.me/theorems/0e389be2-4449-449f-9e97-050024f74f67
-- title:
--   Computable analysis · ComputableCoefficient · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComputableCoefficient.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexMultiplication

set_option autoImplicit true

/-!
# Computable coefficients and finite rational identities

A coefficient is a certified interval computation with a rational sampling
semantics. Sampling is a proof device, not a conversion of an irrational
coefficient to a rational one. Arithmetic computes on the original intervals.
Finite observation bounds let rational algebra prove equivalence of the
resulting raw computations, without a completed-real field or equality test.
-/

namespace ComputableAnalysis
namespace ComputableCoefficient

def Samples (n : Nat) (s : RealCompute.Certified → Rat) : Prop :=
  ∀ x, (x.compute n).lo ≤ s x ∧ s x ≤ (x.compute n).hi

theorem samples_lower (n : Nat) : Samples n (fun x => (x.compute n).lo) := by
  intro x
  exact ⟨Rat.le_refl, RealCompute.interval_order_of_valid _ x.valid n⟩

structure Value where
  real : RealCompute.Certified
  sample : (RealCompute.Certified → Rat) → Rat
  observation : Nat → Nat
  encloses : ∀ n m, observation n ≤ m → ∀ s, Samples m s →
    (real.compute n).lo ≤ sample s ∧ sample s ≤ (real.compute n).hi

namespace Value

def parameter (x : RealCompute.Certified) : Value where
  real := x
  sample := fun s => s x
  observation := id
  encloses := by
    intro n m hnm s hs
    have hn := x.valid.2.1 n m hnm
    have hh := hs x
    exact ⟨Rat.le_trans hn.1 hh.1, Rat.le_trans hh.2 hn.2.2⟩

def rational (q : Rat) : Value where
  real := RealCompute.Certified.ofRat q
  sample := fun _ => q
  observation := fun _ => 0
  encloses := by intros; exact ⟨Rat.le_refl, Rat.le_refl⟩

def add (x y : Value) : Value where
  real := RealCompute.Certified.ofRaw (RealCompute.add x.real.preferred y.real.preferred)
    (RealCompute.add_valid x.real.valid y.real.valid)
  sample := fun s => x.sample s + y.sample s
  observation := fun n => max (x.observation n) (y.observation n)
  encloses := by
    intro n m hm s hs
    have hx := x.encloses n m (Nat.le_trans (Nat.le_max_left _ _) hm) s hs
    have hy := y.encloses n m (Nat.le_trans (Nat.le_max_right _ _) hm) s hs
    change (x.real.compute n).lo + (y.real.compute n).lo ≤ _ ∧
      _ ≤ (x.real.compute n).hi + (y.real.compute n).hi
    constructor <;> grind

def neg (x : Value) : Value where
  real := RealCompute.Certified.ofRaw (RealCompute.neg x.real.preferred) (RealCompute.neg_valid x.real.valid)
  sample := fun s => -x.sample s
  observation := x.observation
  encloses := by
    intro n m hm s hs
    have hx := x.encloses n m hm s hs
    exact ⟨Rat.neg_le_neg hx.2, Rat.neg_le_neg hx.1⟩

def sub (x y : Value) : Value := add x (neg y)

def mul (x y : Value) : Value where
  real := RealCompute.Certified.ofRaw (RealCompute.mul x.real.preferred y.real.preferred)
    (RealCompute.mul_valid x.real.valid y.real.valid)
  sample := fun s => x.sample s * y.sample s
  observation := fun n => max (x.observation n) (y.observation n)
  encloses := by
    intro n m hm s hs
    have hx := x.encloses n m (Nat.le_trans (Nat.le_max_left _ _) hm) s hs
    have hy := y.encloses n m (Nat.le_trans (Nat.le_max_right _ _) hm) s hs
    exact QBox.mulRealInterval_contains hx.1 hx.2 hy.1 hy.2

def positiveInv (x : Value) (N : Nat) (hp : 0 < (x.real.compute N).lo) : Value where
  real := RealCompute.Certified.ofRaw (RealCompute.positiveInv x.real.preferred N)
    (RealCompute.positiveInv_valid x.real.valid hp)
  sample := fun s => (x.sample s)⁻¹
  observation := fun n => x.observation (max n N)
  encloses := by
    intro n m hm s hs
    have hx := x.encloses (max n N) m hm s hs
    have hN := x.real.valid.2.1 N (max n N) (Nat.le_max_right _ _)
    have hn := x.real.valid.2.1 n (max n N) (Nat.le_max_left _ _)
    have hxp : 0 < x.sample s := by
      have hh : (x.real.compute N).lo ≤ x.sample s := Rat.le_trans hN.1 hx.1
      grind
    change (RealCompute.positiveInvCompute x.real.preferred N n).lo ≤ _ ∧
      _ ≤ (RealCompute.positiveInvCompute x.real.preferred N n).hi
    unfold RealCompute.positiveInvCompute
    split
    · change 0 ≤ _ ∧ _ ≤ 1 / (x.real.compute N).lo
      constructor
      · exact Rat.le_of_lt (Rat.inv_pos.mpr hxp)
      · simpa only [Rat.div_def, Rat.one_mul] using
          QInterval.one_div_le_one_div_of_pos hp (Rat.le_trans hN.1 hx.1)
    · rename_i hnot
      have hnN : N ≤ n := by omega
      have hNN := x.real.valid.2.1 N n hnN
      have hnp : 0 < (x.real.preferred.compute n).lo := by
        change (x.real.compute N).lo ≤ (x.real.compute n).lo ∧ _ at hNN
        change 0 < (x.real.compute n).lo
        grind
      rw [QInterval.inv_of_pos hnp]
      constructor
      · simpa only [Rat.div_def, Rat.one_mul] using
          QInterval.one_div_le_one_div_of_pos hxp (Rat.le_trans hx.2 hn.2.2)
      · simpa only [Rat.div_def, Rat.one_mul] using
          QInterval.one_div_le_one_div_of_pos hnp (Rat.le_trans hn.1 hx.1)

/-- A finite interval test. Failure requests more precision or a genuine
nonzero hypothesis; it never treats an undecided coefficient as zero. -/
def inv? (x : Value) (N : Nat) : Option Value :=
  if hp : 0 < (x.real.compute N).lo then some (positiveInv x N hp)
  else if hn : (x.real.compute N).hi < 0 then
    some (neg (positiveInv (neg x) N (by change 0 < -(x.real.compute N).hi; grind)))
  else none

theorem inv?_sample (x y : Value) (N : Nat) (h : x.inv? N = some y) (s : RealCompute.Certified → Rat) :
    y.sample s = (x.sample s)⁻¹ := by
  unfold inv? at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
      change -(-x.sample s)⁻¹ = _
      grind [Rat.inv_def]
    · cases h

/-- An identity valid for all sufficiently fine rational samples is an
identity of the original computable coefficients. -/
theorem equiv_of_samples (x y : Value) (N : Nat)
    (h : ∀ m, N ≤ m → ∀ s, Samples m s → x.sample s = y.sample s) :
    x.real.preferred.Equiv y.real.preferred := by
  intro n
  let m := max N (max (x.observation n) (y.observation n))
  let s : RealCompute.Certified → Rat := fun r => (r.compute m).lo
  have hs : Samples m s := samples_lower m
  have hx := x.encloses n m (by dsimp [m]; omega) s hs
  have hy := y.encloses n m (by dsimp [m]; omega) s hs
  have he := h m (by dsimp [m]; omega) s hs
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  change (x.real.compute n).lo ≤ (y.real.compute n).hi ∧
    (y.real.compute n).lo ≤ (x.real.compute n).hi
  rw [he] at hx
  exact ⟨Rat.le_trans hx.1 hy.2, Rat.le_trans hy.1 hx.2⟩

end Value

/-- Rational arithmetic over arbitrary certified computable-real parameters.
Inversion is partial at the evaluation interface, with finite apartness tests. -/
inductive Expr where
  | parameter (x : RealCompute.Certified)
  | rational (q : Rat)
  | add (x y : Expr)
  | neg (x : Expr)
  | mul (x y : Expr)
  | inv (x : Expr)

namespace Expr

def sub (x y : Expr) : Expr := .add x (.neg y)
def div (x y : Expr) : Expr := .mul x (.inv y)
def pow (x : Expr) : Nat → Expr
  | 0 => .rational 1
  | n+1 => .mul (pow x n) x

def sample (s : RealCompute.Certified → Rat) : Expr → Rat
  | .parameter x => s x
  | .rational q => q
  | .add x y => sample s x + sample s y
  | .neg x => -sample s x
  | .mul x y => sample s x * sample s y
  | .inv x => (sample s x)⁻¹

def realize (N : Nat) : Expr → Option Value
  | .parameter x => some (.parameter x)
  | .rational q => some (.rational q)
  | .add x y => do return .add (← realize N x) (← realize N y)
  | .neg x => do return .neg (← realize N x)
  | .mul x y => do return .mul (← realize N x) (← realize N y)
  | .inv x => do (← realize N x).inv? N

@[simp] theorem sample_sub (s : RealCompute.Certified → Rat) (x y : Expr) :
    (x.sub y).sample s = x.sample s - y.sample s := by
  simp only [sub, sample, Rat.sub_eq_add_neg]
@[simp] theorem sample_div (s : RealCompute.Certified → Rat) (x y : Expr) :
    (x.div y).sample s = x.sample s / y.sample s := rfl
@[simp] theorem sample_pow (s : RealCompute.Certified → Rat) (x : Expr) (n : Nat) :
    (x.pow n).sample s = x.sample s ^ n := by
  induction n with
  | zero => simp only [pow, sample, Rat.pow_zero]
  | succ n ih => simp only [pow, sample, ih, Rat.pow_succ]

/-- Every successful evaluation already carries `RealCompute.Valid`. -/
theorem realize_sample (e : Expr) (N : Nat) (v : Value)
    (h : e.realize N = some v) (s : RealCompute.Certified → Rat) : v.sample s = e.sample s := by
  induction e generalizing v with
  | parameter x => cases h; rfl
  | rational q => cases h; rfl
  | add x y ihx ihy =>
      cases hx : x.realize N <;> cases hy : y.realize N <;> simp [realize, hx, hy] at h
      cases h
      change _ + _ = _ + _
      rw [ihx _ hx, ihy _ hy]
  | neg x ih =>
      cases hx : x.realize N <;> simp [realize, hx] at h
      cases h
      exact congrArg Neg.neg (ih _ hx)
  | mul x y ihx ihy =>
      cases hx : x.realize N <;> cases hy : y.realize N <;> simp [realize, hx, hy] at h
      cases h
      change _ * _ = _ * _
      rw [ihx _ hx, ihy _ hy]
  | inv x ih =>
      cases hx : x.realize N <;> simp [realize, hx] at h
      rename_i u
      rw [Value.inv?_sample u v N h, ih u hx]
      rfl

/-- Lift a finite rational identity to interval-computation equivalence. -/
theorem realize_equiv (e f : Expr) (N M : Nat) (v w : Value)
    (hv : e.realize N = some v) (hw : f.realize M = some w)
    (K : Nat) (h : ∀ m, K ≤ m → ∀ s, Samples m s → e.sample s = f.sample s) :
    v.real.preferred.Equiv w.real.preferred := by
  apply Value.equiv_of_samples v w K
  intro m hm s hs
  rw [realize_sample e N v hv, realize_sample f M w hw]
  exact h m hm s hs

end Expr
end ComputableCoefficient
end ComputableAnalysis


