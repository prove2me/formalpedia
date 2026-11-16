-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerReal
-- name    : liuyao_ca_fd889115_k1_Analysis_EulerReal
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:51:14.641349+00:00
-- url     : https://prove2.me/theorems/b1015d6a-fb19-48a8-9443-4dddadaaa5fd
-- title:
--   Computable analysis · EulerReal · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/EulerReal.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerFinite

set_option autoImplicit true

/-! Executable nested rational bounds from forward/backward Euler steps.
The runtime uses only finite rational powers. -/
namespace ComputableAnalysis.EulerReal
open EulerFinite
set_option maxHeartbeats 1500000

def start (M : Rat) : Nat := M.floor.toNat+2
def count (M : Rat) (n : Nat) : Nat := start M*2^n

theorem start_positive (M : Rat) : 0<(start M:Rat) :=
  Rat.natCast_pos.mpr (by unfold start; omega)

theorem start_large (M : Rat) : M<(start M:Rat) := by
  have h := Rat.lt_floor_add_one M
  have hi : M.floor≤(M.floor.toNat:Int) := by omega
  have hr : (M.floor:Rat)≤(M.floor.toNat:Rat) := by exact_mod_cast hi
  rw [Rat.intCast_add] at h
  dsimp [start]
  rw [Rat.natCast_add]
  change M<(M.floor.toNat:Rat)+2
  grind only

theorem count_ge_start (M : Rat) (n : Nat) : start M≤count M n :=
  Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))

theorem count_positive (M : Rat) (n : Nat) : 0<(count M n:Rat) := by
  have h := count_ge_start M n
  have hs := start_positive M
  have hc : (start M:Rat)≤(count M n:Rat) := by exact_mod_cast h
  grind only

theorem count_large (M : Rat) (n : Nat) : M<(count M n:Rat) := by
  have h : (start M:Rat)≤(count M n:Rat) := by exact_mod_cast count_ge_start M n
  have hs := start_large M
  grind only

theorem count_succ (M : Rat) (n : Nat) : count M (n+1)=2*count M n := by
  simp only [count,Nat.pow_succ]
  grind only

theorem count_zero (M : Rat) : count M 0=start M := by simp [count]

theorem nat_succ_le_two_pow (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem count_ge_index (M : Rat) (n : Nat) : n+1≤count M n := by
  have hs : 0<start M := by unfold start; omega
  have H : 2^n≤start M*2^n := Nat.le_mul_of_pos_left _ hs
  exact Nat.le_trans (nat_succ_le_two_pow n) H

theorem count_decay (M C : Rat) (hC : 0≤C) :
    ShrinksToZero (fun n => C/(count M n:Rat)) := by
  apply shrinksToZero_of_ratOverSuccBound (C := C)
  intro n
  have hn : 0<((n+1:Nat):Rat) := Rat.natCast_pos.mpr (Nat.succ_pos n)
  have h : ((n+1:Nat):Rat)≤(count M n:Rat) := by exact_mod_cast count_ge_index M n
  have H := Rat.mul_le_mul_of_nonneg_left (inv_antitone hn h) hC
  simpa only [Rat.div_def] using H

def budget (M : Rat) : Rat := upper M (start M)

theorem budget_positive (M : Rat) : 0<budget M :=
  upper_positive (start_positive M) (start_large M)

theorem upper_le_budget {M q : Rat} (hM : 0≤M) (hq : q≤M) (n : Nat) :
    upper q (count M n)≤budget M := by
  calc
    _≤upper M (count M n) := upper_mono (count_positive M n) (count_large M n) hq
    _≤upper M (start M) := upper_refine (start_positive M) (Nat.pow_pos (by decide)) (start_large M)

def enclosure (M : Rat) (I : QInterval) (n : Nat) : QInterval :=
  ⟨lower I.lo (count M n),upper I.hi (count M n)⟩

def within (M : Rat) (x : RealCompute) : Prop :=
  ∀ n,-M≤(x.compute n).lo ∧ (x.compute n).hi≤M

def inBound (M : Rat) (x : RealCompute) : RealCompute where
  compute n := enclosure M (x.compute n) n

theorem enclosure_ordered {M : Rat} (hM : 0≤M) {I : QInterval}
    (ho : I.lo≤I.hi) (hl : -M≤I.lo) (hr : I.hi≤M) (n : Nat) :
    (enclosure M I n).lo≤(enclosure M I n).hi := by
  exact cross_bound (count_positive M n) (count_positive M n)
    (by have := count_large M n; grind only) (by have := count_large M n; grind only) ho

theorem enclosure_width {M : Rat} (hM : 0≤M) {I : QInterval}
    (ho : I.lo≤I.hi) (hl : -M≤I.lo) (hr : I.hi≤M) (n : Nat) :
    (enclosure M I n).width≤budget M*(I.width+M^2/(count M n:Rat)) := by
  have hn := count_positive M n
  have hlarge := count_large M n
  have hg := gap_bound hn (q := I.hi) (by grind only) (by grind only)
  have hlip := lower_lipschitz hM hl ho hr hlarge
  have hB := upper_le_budget hM hr n
  have hBM := upper_le_budget hM (Rat.le_refl : M≤M) n
  have hs : I.hi^2≤M^2 := by
    have H := Rat.mul_nonneg (show 0≤M-I.hi by grind only) (show 0≤M+I.hi by grind only)
    simp only [Rat.pow_succ,Rat.pow_zero]
    grind only
  have hsq : 0≤I.hi^2/(count M n:Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by simpa only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul] using rat_square_nonneg_basic I.hi)
      (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  have hs' := Rat.mul_le_mul_of_nonneg_right hs (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  change I.hi^2/(count M n:Rat)≤M^2/(count M n:Rat) at hs'
  have H1 := rat_mul_le_mul_of_nonneg (Rat.le_of_lt (upper_positive hn (by grind only))) hB hsq hs'
  have H2 := Rat.mul_le_mul_of_nonneg_left hBM (show 0≤I.hi-I.lo by grind only)
  dsimp [enclosure,QInterval.width]
  grind only

theorem scaled_sum_shrinks {u v : Nat → Rat} {C : Rat} (hC : 0≤C)
    (hu : ShrinksToZero u) (hv : ShrinksToZero v) :
    ShrinksToZero (fun n => C*(u n+v n)) := by
  intro eps
  let eta : QPos := ⟨eps.val/(2*(C+1)),by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by grind only))⟩
  obtain ⟨A,hA⟩ := hu eta
  obtain ⟨B,hB⟩ := hv eta
  refine ⟨max A B,?_⟩
  intro n hn
  have H1 := hA n (by omega)
  have H2 := hB n (by omega)
  have H3 := Rat.mul_le_mul_of_nonneg_left (show u n+v n≤2*eta.val by grind only) hC
  have H4 := Rat.mul_le_mul_of_nonneg_right (show C≤C+1 by grind only)
    (show 0≤2*eta.val by have := eta.property; grind only)
  have hc : eta.val*(2*(C+1))=eps.val := Rat.div_mul_cancel (by grind only)
  grind only

theorem inBound_valid {M : Rat} (hM : 0≤M) {x : RealCompute} (hx : x.Valid)
    (hw : within M x) : (inBound M x).Valid := by
  have ordered (n : Nat) := enclosure_ordered hM (RealCompute.interval_order_of_valid x hx n)
    (hw n).1 (hw n).2 n
  have step (n : Nat) :
      ((inBound M x).compute n).lo≤((inBound M x).compute (n+1)).lo ∧
      ((inBound M x).compute (n+1)).hi≤((inBound M x).compute n).hi := by
    have h := hx.2.1 n (n+1) (by omega)
    have hp := count_positive M n
    have hp' := count_positive M (n+1)
    have hb := count_large M n
    have hb' := count_large M (n+1)
    constructor
    · exact Rat.le_trans (lower_double hp (by have := (hw n).1; grind only))
        (by rw [←count_succ]; exact lower_mono hp' (by have := (hw n).1; grind only) h.1)
    · exact Rat.le_trans
        (upper_mono hp' (by have := (hw n).2; grind only) h.2.2)
        (by rw [count_succ]; exact upper_double hp (by have := (hw n).2; grind only))
  refine ⟨?_,?_,?_⟩
  · intro n
    have H := ordered n
    change ((inBound M x).compute n).lo≤((inBound M x).compute n).hi at H
    change 0≤_ - _
    grind only
  · intro n m hnm
    induction hnm with
    | refl => exact ⟨Rat.le_refl,ordered n,Rat.le_refl⟩
    | @step m hnm ih =>
      have h := step m
      exact ⟨Rat.le_trans ih.1 h.1,ordered (m+1),Rat.le_trans h.2 ih.2.2⟩
  · have hs := scaled_sum_shrinks (Rat.le_of_lt (budget_positive M)) hx.2.2
      (count_decay M (M^2) (by simpa only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul] using rat_square_nonneg_basic M))
    intro eps
    obtain ⟨N,hN⟩ := hs eps
    refine ⟨N,fun n hn => Rat.le_trans
      (enclosure_width hM (RealCompute.interval_order_of_valid x hx n) (hw n).1 (hw n).2 n) (hN n hn)⟩

def inputBound (x : RealCompute) : Rat := qabs (x.compute 0).lo+qabs (x.compute 0).hi+1

theorem inputBound_positive (x : RealCompute) : 0<inputBound x := by
  have := qabs_nonneg (x.compute 0).lo
  have := qabs_nonneg (x.compute 0).hi
  dsimp [inputBound]; grind only

theorem input_within {x : RealCompute} (hx : x.Valid) : within (inputBound x) x := by
  intro n
  have H := hx.2.1 0 n (Nat.zero_le n)
  have h1 := neg_qabs_le_self (x.compute 0).lo
  have h2 := self_le_qabs (x.compute 0).hi
  have h3 := qabs_nonneg (x.compute 0).lo
  have h4 := qabs_nonneg (x.compute 0).hi
  dsimp [inputBound]; constructor <;> grind only

/-- Derived represented-input evaluation using one finite mesh seed on the
entire initial input bracket. Its rational restriction is the primary sampler. -/
def eval (x : RealCompute) : RealCompute := inBound (inputBound x) x
def sample (q : Rat) : RealCompute := eval (RealCompute.ofRat q)

theorem eval_valid {x : RealCompute} (hx : x.Valid) : (eval x).Valid :=
  inBound_valid (Rat.le_of_lt (inputBound_positive x)) hx (input_within hx)

theorem sample_valid (q : Rat) : (sample q).Valid := eval_valid (RealCompute.ofRat_valid q)

theorem inBound_equiv {M K : Rat} {x y : RealCompute} (hM : 0≤M) (hK : 0≤K)
    (hx : x.Valid) (hy : y.Valid) (hMx : within M x) (hKy : within K y) (he : x.Equiv y) :
    (inBound M x).Equiv (inBound K y) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
  constructor
  · apply cross_bound (count_positive M n) (count_positive K n)
    · have := count_large M n; have := (hMx n).1; grind only
    · have := count_large K n; have := (hKy n).2; grind only
    · exact RealCompute.le_of_equiv hx hy he n n
  · apply cross_bound (count_positive K n) (count_positive M n)
    · have := count_large K n; have := (hKy n).1; grind only
    · have := count_large M n; have := (hMx n).2; grind only
    · exact RealCompute.le_of_equiv hy hx (RealCompute.equiv_symm he) n n

theorem eval_congr {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (he : x.Equiv y) :
    (eval x).Equiv (eval y) :=
  inBound_equiv (Rat.le_of_lt (inputBound_positive x)) (Rat.le_of_lt (inputBound_positive y))
    hx hy (input_within hx) (input_within hy) he

theorem sample_zero : (sample 0).Equiv (RealCompute.ofRat 1) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
  change lower 0 _≤1 ∧ 1≤upper 0 _
  rw [lower_zero,upper_zero]
  exact ⟨Rat.le_refl,Rat.le_refl⟩

theorem eval_positive {x : RealCompute} (hx : x.Valid) : (eval x).Pos := by
  refine ⟨0,?_⟩
  apply lower_positive (count_positive (inputBound x) 0)
  have h := input_within hx 0
  have hs := count_large (inputBound x) 0
  grind only

def rationalFunction : PartialRealFunRaw where
  definedAt _ := True
  compute q _ := (sample q).compute

theorem rationalFunction_valid : rationalFunction.Valid := fun q _ => sample_valid q

end ComputableAnalysis.EulerReal


