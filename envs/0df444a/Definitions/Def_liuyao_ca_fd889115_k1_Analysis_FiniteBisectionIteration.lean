-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteBisectionIteration
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteBisectionIteration
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:50:00.67121+00:00
-- url     : https://prove2.me/theorems/7f3301fc-f00b-432b-8d84-483ff3d4c72f
-- title:
--   Computable analysis · FiniteBisectionIteration · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FiniteBisectionIteration.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteBisection

set_option autoImplicit true

/-!
# Finite rational bisection iterations

This module iterates the exact rational bisection step.  All invariants are
finite certificates: the interval remains rational, the sign bracket is
preserved, and the width is known exactly at every finite stage.  No zero
existence or completeness principle is used.
-/

namespace ComputableAnalysis

open QInterval

/-- Apply `monotoneBisectionStep` exactly `n` times. -/
def monotoneBisectionIterate (f : Rat -> Rat) : Nat -> QInterval -> QInterval
  | 0, I => I
  | n + 1, I => monotoneBisectionStep f (monotoneBisectionIterate f n I)

theorem monotoneBisectionIterate_ordered {f : Rat -> Rat} {I : QInterval}
    (hI : I.lo ≤ I.hi) (n : Nat) :
    (monotoneBisectionIterate f n I).lo ≤
      (monotoneBisectionIterate f n I).hi := by
  induction n generalizing I with
  | zero => exact hI
  | succ n ih =>
      exact monotoneBisectionStep_ordered (ih hI)

theorem monotoneBisectionIterate_subinterval {f : Rat -> Rat} {I : QInterval}
    (hI : I.lo ≤ I.hi) (n : Nat) :
    (monotoneBisectionIterate f n I).lo ≥ I.lo /\
      (monotoneBisectionIterate f n I).hi ≤ I.hi := by
  induction n generalizing I with
  | zero => exact ⟨Rat.le_refl, Rat.le_refl⟩
  | succ n ih =>
      have hJ := ih hI
      have hJord := monotoneBisectionIterate_ordered (f := f) hI n
      have hstep := monotoneBisectionStep_subinterval (f := f) hJord
      exact ⟨Rat.le_trans hJ.1 hstep.1, Rat.le_trans hstep.2 hJ.2⟩

theorem monotoneBisectionIterate_preserves_bracket
    {f : Rat -> Rat} {I : QInterval}
    (hI : I.lo ≤ I.hi)
    (hf : ∀ ⦃x y : Rat⦄, x ≤ y -> f x ≤ f y)
    (hlo : f I.lo ≤ 0) (hhi : 0 ≤ f I.hi) (n : Nat) :
    f (monotoneBisectionIterate f n I).lo ≤ 0 /\
      0 ≤ f (monotoneBisectionIterate f n I).hi := by
  induction n generalizing I with
  | zero => exact ⟨hlo, hhi⟩
  | succ n ih =>
      have hJ := ih hI hlo hhi
      exact monotoneBisectionStep_preserves_bracket
        (monotoneBisectionIterate_ordered hI n) hf hJ.1 hJ.2

/-! Iterated target bracketing for the constructive inverse interface. -/

def monotoneTargetBisectionIterate (f : Rat -> Rat) (y : Rat) :
    Nat -> QInterval -> QInterval
  | 0, I => I
  | n + 1, I =>
      monotoneTargetBisectionStep f y (monotoneTargetBisectionIterate f y n I)

theorem monotoneTargetBisectionIterate_ordered
    {f : Rat -> Rat} {I : QInterval} (y : Rat)
    (hI : I.lo ≤ I.hi) (n : Nat) :
    (monotoneTargetBisectionIterate f y n I).lo ≤
      (monotoneTargetBisectionIterate f y n I).hi := by
  induction n generalizing I with
  | zero => exact hI
  | succ n ih =>
      have hprev := ih hI
      have hm := (monotoneTargetBisectionIterate f y n I).midpoint_mem hprev
      by_cases hmid : y ≤ f (monotoneTargetBisectionIterate f y n I).midpoint
      · simp [monotoneTargetBisectionIterate, monotoneTargetBisectionStep,
          hmid, hm.1]
      · simp [monotoneTargetBisectionIterate, monotoneTargetBisectionStep,
          hmid, hm.2]

theorem monotoneTargetBisectionIterate_subinterval
    {f : Rat -> Rat} {I : QInterval} (y : Rat)
    (hI : I.lo ≤ I.hi) (n : Nat) :
    (monotoneTargetBisectionIterate f y n I).lo ≥ I.lo /\
      (monotoneTargetBisectionIterate f y n I).hi ≤ I.hi := by
  induction n generalizing I with
  | zero => exact ⟨Rat.le_refl, Rat.le_refl⟩
  | succ n ih =>
      have hprev := ih hI
      have hprevOrd := monotoneTargetBisectionIterate_ordered
        (f := f) y hI n
      have hstep := monotoneTargetBisectionStep_subinterval (f := f) y hprevOrd
      exact ⟨Rat.le_trans hprev.1 hstep.1,
        Rat.le_trans hstep.2 hprev.2⟩

theorem monotoneTargetBisectionIterate_add
    {f : Rat -> Rat} (y : Rat) (m n : Nat) (I : QInterval) :
    monotoneTargetBisectionIterate f y (m + n) I =
      monotoneTargetBisectionIterate f y n
        (monotoneTargetBisectionIterate f y m I) := by
  induction n with
  | zero => simp [monotoneTargetBisectionIterate]
  | succ n ih =>
      simp only [monotoneTargetBisectionIterate]
      exact congrArg (monotoneTargetBisectionStep f y) ih

theorem monotoneTargetBisectionIterate_later_subinterval
    {f : Rat -> Rat} {I : QInterval} (y : Rat)
    (hI : I.lo ≤ I.hi) {m n : Nat} (hmn : m ≤ n) :
    (monotoneTargetBisectionIterate f y n I).lo ≥
        (monotoneTargetBisectionIterate f y m I).lo /\
      (monotoneTargetBisectionIterate f y n I).hi ≤
        (monotoneTargetBisectionIterate f y m I).hi := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [monotoneTargetBisectionIterate_add]
  exact monotoneTargetBisectionIterate_subinterval y
    (monotoneTargetBisectionIterate_ordered (f := f) y hI m) k

theorem monotoneTargetBisectionIterate_width
    {f : Rat -> Rat} {I : QInterval} (y : Rat) (n : Nat) :
    (monotoneTargetBisectionIterate f y n I).width =
      I.width / (2 ^ n : Rat) := by
  induction n with
  | zero =>
      simp only [monotoneTargetBisectionIterate, QInterval.width, Rat.div_def]
      have hinv : (1 : Rat)⁻¹ = 1 := by
        have h := Rat.mul_inv_cancel (1 : Rat) (by decide)
        simpa using h
      rw [Rat.pow_zero, hinv, Rat.mul_one]
  | succ n ih =>
      rw [monotoneTargetBisectionIterate,
        monotoneTargetBisectionStep_width, ih]
      rw [Rat.pow_succ]
      grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

theorem monotoneTargetBisectionIterate_width_pos
    {f : Rat -> Rat} {I : QInterval} (y : Rat) (n : Nat)
    (hwidth : 0 < I.width) :
    0 < (monotoneTargetBisectionIterate f y n I).width := by
  rw [monotoneTargetBisectionIterate_width]
  rw [Rat.div_def]
  exact Rat.mul_pos hwidth
    ((Rat.inv_pos).2 (Rat.pow_pos (by decide +kernel)))

theorem monotoneTargetBisectionIterate_width_le_of_power_budget
    {f : Rat -> Rat} {I : QInterval} {y eps : Rat} {n : Nat}
    (hbudget : I.width <= eps * (2 ^ n : Rat)) :
    (monotoneTargetBisectionIterate f y n I).width <= eps := by
  rw [monotoneTargetBisectionIterate_width]
  rw [Rat.div_def]
  have hpow : 0 < (2 ^ n : Rat) := by
    exact Rat.pow_pos (by decide +kernel)
  have hpow0 : (2 ^ n : Rat) ≠ 0 := Rat.ne_of_gt hpow
  have hinv : 0 <= (2 ^ n : Rat)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hpow)
  calc
    I.width * (2 ^ n : Rat)⁻¹ <=
        (eps * (2 ^ n : Rat)) * (2 ^ n : Rat)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hbudget hinv
    _ = eps := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hpow0, Rat.mul_one]

private theorem nat_succ_le_two_pow (n : Nat) :
    n + 1 <= 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

theorem monotoneTargetBisectionIterate_width_le_one_div_succ
    {f : Rat -> Rat} {I : QInterval} (y : Rat) (n : Nat)
    (hwidth : I.width <= 1) :
    (monotoneTargetBisectionIterate f y n I).width <=
      1 / (((n + 1 : Nat) : Rat)) := by
  rw [monotoneTargetBisectionIterate_width]
  let A : Rat := ((n + 1 : Nat) : Rat)
  let B : Rat := (2 ^ n : Rat)
  have hApos : 0 < A := by
    dsimp [A]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hBpos : 0 < B := by
    dsimp [B]
    exact Rat.pow_pos (by decide +kernel)
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
  have hAB : A <= B := by
    dsimp [A, B]
    exact_mod_cast nat_succ_le_two_pow n
  apply Rat.le_of_mul_le_mul_right (c := A * B)
  · calc
      (I.width / B) * (A * B) = I.width * A := by
        rw [Rat.div_def]
        have hcancel : B⁻¹ * B = 1 := Rat.inv_mul_cancel B hBne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= 1 * A := Rat.mul_le_mul_of_nonneg_right hwidth
        (Rat.le_of_lt hApos)
      _ = A := by rw [Rat.one_mul]
      _ <= B := hAB
      _ = (1 / A) * (A * B) := by
        rw [Rat.div_def]
        have hcancel : A * A⁻¹ = 1 := Rat.mul_inv_cancel A hAne
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact Rat.mul_pos hApos hBpos

theorem monotoneTargetBisectionIterate_reaches_of_positive_tolerance
    {f : Rat -> Rat} {I : QInterval} (y : Rat)
    (hwidth : I.width <= 1) (eps : QPos) :
    (monotoneTargetBisectionIterate f y eps.val.den I).width <= eps.val := by
  calc
    (monotoneTargetBisectionIterate f y eps.val.den I).width <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) :=
      monotoneTargetBisectionIterate_width_le_one_div_succ y
        eps.val.den hwidth
    _ <= eps.val := one_div_den_succ_le_of_pos eps.property

theorem monotoneBisectionIterate_preserves_target_bracket
    {f : Rat -> Rat} {I : QInterval} (y : Rat)
    (hI : I.lo ≤ I.hi)
    (hlo : f I.lo ≤ y) (hhi : y ≤ f I.hi) (n : Nat) :
    f (monotoneTargetBisectionIterate f y n I).lo ≤ y /\
      y ≤ f (monotoneTargetBisectionIterate f y n I).hi := by
  induction n generalizing I with
  | zero => exact ⟨hlo, hhi⟩
  | succ n ih =>
      have hJ := ih hI hlo hhi
      have hJord := monotoneTargetBisectionIterate_ordered (f := f) y hI n
      exact monotoneBisectionStep_preserves_target_bracket y hJord hJ.1 hJ.2

/-! A single finite certificate packages the invariants needed by an inverse
search client.  It records no limiting point: the output is still the exact
rational interval produced after the requested finite number of steps. -/
theorem monotoneTargetBisectionIterate_certificate
    {f : Rat -> Rat} {I : QInterval} (y : Rat)
    (hI : I.lo ≤ I.hi)
    (hlo : f I.lo ≤ y) (hhi : y ≤ f I.hi) (n : Nat) :
    (monotoneTargetBisectionIterate f y n I).lo ≤
        (monotoneTargetBisectionIterate f y n I).hi /\
      (f (monotoneTargetBisectionIterate f y n I).lo ≤ y /\
        y ≤ f (monotoneTargetBisectionIterate f y n I).hi) /\
      ((monotoneTargetBisectionIterate f y n I).lo ≥ I.lo /\
        (monotoneTargetBisectionIterate f y n I).hi ≤ I.hi) /\
      (monotoneTargetBisectionIterate f y n I).width =
        I.width / (2 ^ n : Rat) := by
  refine ⟨monotoneTargetBisectionIterate_ordered y hI n, ?_, ?_,
    monotoneTargetBisectionIterate_width y n⟩
  · exact monotoneBisectionIterate_preserves_target_bracket y hI hlo hhi n
  · exact monotoneTargetBisectionIterate_subinterval y hI n

/-! The tolerance-indexed form is the object an inverse-search client can
consume directly: the stage is chosen from the positive rational budget, and
all finite invariants are returned together with the width bound. -/
theorem monotoneTargetBisectionIterate_tolerance_certificate
    {f : Rat -> Rat} {I : QInterval} (y : Rat)
    (hI : I.lo ≤ I.hi)
    (hlo : f I.lo ≤ y) (hhi : y ≤ f I.hi)
    (hwidth : I.width ≤ 1) (eps : QPos) :
    let J := monotoneTargetBisectionIterate f y eps.val.den I
    J.lo ≤ J.hi /\
      (f J.lo ≤ y /\ y ≤ f J.hi) /\
      (J.lo ≥ I.lo /\ J.hi ≤ I.hi) /\
      J.width ≤ eps.val := by
  let J := monotoneTargetBisectionIterate f y eps.val.den I
  have hcert := monotoneTargetBisectionIterate_certificate
    (f := f) (I := I) y hI hlo hhi eps.val.den
  have hreach := monotoneTargetBisectionIterate_reaches_of_positive_tolerance
    (f := f) (I := I) y hwidth eps
  dsimp [J]
  exact ⟨hcert.1, hcert.2.1, hcert.2.2.1, hreach⟩

theorem monotoneBisectionIterate_width {f : Rat -> Rat} {I : QInterval}
    (n : Nat) :
    (monotoneBisectionIterate f n I).width = I.width / (2 ^ n : Rat) := by
  induction n with
  | zero =>
      simp only [monotoneBisectionIterate, QInterval.width, Rat.div_def]
      have hinv : (1 : Rat)⁻¹ = 1 := by
        have h := Rat.mul_inv_cancel (1 : Rat) (by decide)
        simpa using h
      rw [Rat.pow_zero, hinv, Rat.mul_one]
  | succ n ih =>
      rw [monotoneBisectionIterate, monotoneBisectionStep_width, ih]
      rw [Rat.pow_succ]
      grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

theorem monotoneBisectionIterate_width_pos
    {f : Rat -> Rat} {I : QInterval} (n : Nat)
    (hwidth : 0 < I.width) :
    0 < (monotoneBisectionIterate f n I).width := by
  rw [monotoneBisectionIterate_width]
  rw [Rat.div_def]
  exact Rat.mul_pos hwidth
    ((Rat.inv_pos).2 (Rat.pow_pos (by decide +kernel)))

/-- A supplied rational power budget turns the exact finite width formula into
an executable bisection precision certificate. -/
theorem monotoneBisectionIterate_width_le_of_power_budget
    {f : Rat -> Rat} {I : QInterval} {n : Nat} {eps : Rat}
    (hbudget : I.width <= eps * (2 ^ n : Rat)) :
    (monotoneBisectionIterate f n I).width <= eps := by
  rw [monotoneBisectionIterate_width]
  rw [Rat.div_def]
  have hpow : 0 < (2 ^ n : Rat) := by
    exact Rat.pow_pos (by decide +kernel)
  have hpow0 : (2 ^ n : Rat) ≠ 0 := Rat.ne_of_gt hpow
  have hinv : 0 <= (2 ^ n : Rat)⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hpow)
  calc
    I.width * (2 ^ n : Rat)⁻¹ <=
        (eps * (2 ^ n : Rat)) * (2 ^ n : Rat)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hbudget hinv
    _ = eps := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hpow0, Rat.mul_one]

end ComputableAnalysis


