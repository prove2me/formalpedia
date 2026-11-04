-- Prove2me | Definitions.Def_QMCLeafB_ledger_snap
-- name    : QMCLeafB_ledger_snap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:25:29.344629+00:00
-- url     : https://prove2.me/theorems/353b6a99-dfc9-496d-bdfa-02cfdececbc9
-- title:
--   QMCLeafB ledger_snap
-- statement:
--   # leaf B phase 7 — brick `ledger-refresh` (swarm `smvzzjm07`, member m5, direction d2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_certsize
/-
# leaf B phase 7 — brick `ledger-refresh` (swarm `smvzzjm07`, member m5, direction d2)

The height/length ledger under **dyadic-snap semantics**.

Phase 6 (`Check_height_growth_m4.lean`) proved that the *exact*-`ℚ` iterate cannot be the state of
the polynomial-time program: one Sherman–Morrison round sends an entry-height bound `L` to
`c·L + c` with `c` polynomial in `n`, so after `T` rounds the bit-length is `(c+1)^T·(B+c+1)` —
exponential in the round count.  The design correction is to **snap every round's entries onto a
dyadic grid** before handing the state on.

This file supplies the two pieces of the ledger that the correction rests on, and nothing else
(it deliberately says nothing about the shape of the step function — `brick-sim-snap` owns that):

**1. The height reset (§1–§2).**  `snapAbs k q` truncates `q` toward zero onto the grid
`2^{-k}ℤ`.  It is *value-contracting* (`|snapAbs k q| ≤ |q|`) and it errs by at most one grid step
(`|snapAbs k q - q| ≤ 2^{-k}`).  Its bit-length is therefore bounded by the **value** exponent plus
`k`, and *not at all* by the bit-length of its argument:

  `hasHeight_snapAbs : |q| ≤ 2^M → HasHeight (snapAbs k q) (M + k)`.

Iterating a value-stable round map, the entry heights of the whole run are bounded by the *fixed*
closed form `M + k` — the round count does not appear (`snapIterate_height`), in contrast with
`HeightGrowth.height_iterate`'s `(c+1)^T·(B+c+1)`.  Encoded lengths follow
(`snapIterate_encode_length`, `state_encode_length`, `round_charge_monomial`,
`run_charge_monomial`): each round of the program charges `3(M+k)+10` bits per entry, hence
`n²·(3(M+k)+10)`, and `T` rounds charge `T·n²·(3(M+k)+10)`, all polynomial.

**1b. The value track (§2b).**  Snapping bounds the *bit-length* of the entries, not their
*magnitude*; the magnitude exponent is a separate ledger, and it only needs to grow **additively**:
`value_exponent_iterate : |q| ≤ 2^(M+γt) ⟹ |f q| ≤ 2^(M+γ(t+1)) ⟹ |f^[T] q₀| ≤ 2^(M+γT)`, giving the
fully closed form `snapRound_closed_form : height ≤ M + γ·T + k`.  (Phase 6's fatal growth was
*multiplicative*: `L ↦ c·L + c`, exponential in `T`; an additive exponent is polynomial.)  So the
value track needs no sharp spectral bound — a uniform per-round magnitude amplification `2^γ` is
enough.

**2. The accumulated snap error (§3).**  A perturbation recursion
`|e_{r+1}| ≤ L·|e_r| + ε` (`L ≥ 1`, the per-round amplification of the ellipsoid step) telescopes
to `|e_R| ≤ (|e_0| + R·ε)·L^R` (`err_le_of_step`); with `ε = 2^{-k}` this is turned into the exact
budget the engine's margin can absorb:

  `snap_error_budget : 2·T·L^T ≤ δ·2^k → T·L^T·2^{-k} ≤ δ/2`,

and the required precision is **explicit and log-scale**: `k = snapPrec T L δ =
Nat.clog 2 ⌈2·T·L^T/δ⌉₊` always works (`snap_precision_log`), and if the budget is at most `2^P` then
`k ≤ P`, so the snapped height is `≤ M + P` (`hasHeight_snapAbs_of_budget`).  **This is a trap worth
naming**: the value-level precision `⌈2·T·L^T/δ⌉` (also provided, `snap_precision_ceil`) is
exponential in `n` and would make the height ledger — hence the program — non-polynomial.  Only the
bit-level (`Nat.clog 2`) precision keeps `M + k` polynomial.  Tolerances are absorbed by the ErrProp
margin (`Check_errprop.lean`'s `abs_sub_le_natCast_mul_of_steps` is the `L = 1` case of
`err_le_of_step`), while heights stay bounded.

No `sorry`, no `axiom`; axiom audit at the end.
-/
-- import Solutions.Check_errprop removed (2026-11-03): its LeafB.ErrProp.* is an exact duplicate of the copy in MergeAll3_m8; loading both breaks the ClosingBracket chain, and nothing here uses ErrProp.

set_option linter.unusedVariables false

open Matrix
open OAI.MetricKMedian.Binary
open scoped BigOperators

namespace QMCLeafB.LedgerSnap

/-! ## 1.  The snap: truncation onto the dyadic grid `2^{-k}ℤ` -/

theorem two_pow_pos (k : ℕ) : (0 : ℚ) < 2 ^ k := by positivity

theorem one_div_two_pow_pos (k : ℕ) : (0 : ℚ) < 1 / 2 ^ k := by positivity

theorem one_div_two_pow_le_one (k : ℕ) : (1 : ℚ) / 2 ^ k ≤ 1 := by
  rw [div_le_one (two_pow_pos k)]
  exact one_le_pow₀ (by norm_num)

/-- **The dyadic snap** at resolution `k`: truncate toward zero onto the grid `2^{-k}ℤ`. -/
def snapAbs (k : ℕ) (q : ℚ) : ℚ :=
  if 0 ≤ q then (⌊q * 2 ^ k⌋ : ℚ) / 2 ^ k
  else -((⌊(-q) * 2 ^ k⌋ : ℚ) / 2 ^ k)

theorem snapAbs_of_nonneg {q : ℚ} (k : ℕ) (hq : 0 ≤ q) :
    snapAbs k q = (⌊q * 2 ^ k⌋ : ℚ) / 2 ^ k := by
  unfold snapAbs
  rw [if_pos hq]

theorem snapAbs_of_neg {q : ℚ} (k : ℕ) (hq : q < 0) :
    snapAbs k q = -((⌊(-q) * 2 ^ k⌋ : ℚ) / 2 ^ k) := by
  unfold snapAbs
  rw [if_neg (not_le.mpr hq)]

theorem snapAbs_zero (k : ℕ) : snapAbs k 0 = 0 := by
  rw [snapAbs_of_nonneg k le_rfl]
  norm_num

/-- For a nonnegative rational, the numerator dominates the value: `x ≤ x.num.natAbs`. -/
theorem le_num_natAbs {x : ℚ} (hx : 0 ≤ x) : x ≤ (x.num.natAbs : ℚ) := by
  have hden : (1 : ℚ) ≤ (x.den : ℚ) := by exact_mod_cast x.den_pos
  have hnum : (0 : ℚ) ≤ (x.num : ℚ) := by
    rw [← Rat.num_div_den x] at hx
    rcases le_or_gt 0 (x.num : ℚ) with h | h
    · exact h
    · have : (x.num : ℚ) / x.den < 0 :=
        div_neg_of_neg_of_pos h (by exact_mod_cast x.den_pos)
      linarith
  calc x = (x.num : ℚ) / x.den := (Rat.num_div_den x).symm
    _ ≤ (x.num : ℚ) := div_le_self hnum hden
    _ = (x.num.natAbs : ℚ) := by
        have hz : ((x.num.natAbs : ℤ) : ℚ) = (x.num : ℚ) := by
          rw [Int.natAbs_of_nonneg (by exact_mod_cast hnum)]
        exact hz.symm

/-- The floored scaled value never exceeds the scaled value. -/
theorem floor_div_le_self {q : ℚ} (hq : 0 ≤ q) (k : ℕ) :
    (⌊q * 2 ^ k⌋ : ℚ) / 2 ^ k ≤ q := by
  rw [div_le_iff₀ (two_pow_pos k)]
  exact Int.floor_le (q * 2 ^ k)

/-- The floored scaled value misses the scaled value by less than one grid step. -/
theorem self_sub_floor_div_lt (q : ℚ) (k : ℕ) :
    q - (⌊q * 2 ^ k⌋ : ℚ) / 2 ^ k < 1 / 2 ^ k := by
  have h := Int.lt_floor_add_one (q * 2 ^ k)
  have h' : q * 2 ^ k < (⌊q * 2 ^ k⌋ : ℚ) + 1 := by exact_mod_cast h
  have h2 := div_lt_div_of_pos_right h' (two_pow_pos k)
  rw [add_div] at h2
  have h3 : q * 2 ^ k / 2 ^ k = q := mul_div_cancel_right₀ q (ne_of_gt (two_pow_pos k))
  rw [h3] at h2
  linarith

/-- **The snap truncates**: it never increases absolute value. -/
theorem snapAbs_abs_le (k : ℕ) (q : ℚ) : |snapAbs k q| ≤ |q| := by
  rcases le_or_gt 0 q with hq | hq
  · have hfl : (0 : ℚ) ≤ (⌊q * 2 ^ k⌋ : ℚ) := by
      have : (0 : ℚ) ≤ q * 2 ^ k := mul_nonneg hq (le_of_lt (two_pow_pos k))
      exact_mod_cast Int.floor_nonneg.mpr this
    rw [snapAbs_of_nonneg k hq, abs_of_nonneg hq,
      abs_of_nonneg (div_nonneg hfl (le_of_lt (two_pow_pos k)))]
    exact floor_div_le_self hq k
  · have hq' : 0 ≤ -q := le_of_lt (neg_pos.mpr hq)
    have hfl : (0 : ℚ) ≤ (⌊(-q) * 2 ^ k⌋ : ℚ) := by
      have : (0 : ℚ) ≤ (-q) * 2 ^ k := mul_nonneg hq' (le_of_lt (two_pow_pos k))
      exact_mod_cast Int.floor_nonneg.mpr this
    rw [snapAbs_of_neg k hq, abs_neg, ← abs_neg q, abs_of_nonneg hq',
      abs_of_nonneg (div_nonneg hfl (le_of_lt (two_pow_pos k)))]
    exact floor_div_le_self hq' k

/-- **The snap errs by at most one grid step.** -/
theorem snapAbs_error (k : ℕ) (q : ℚ) : |snapAbs k q - q| ≤ 1 / 2 ^ k := by
  rcases le_or_gt 0 q with hq | hq
  · have hs : snapAbs k q = (⌊q * 2 ^ k⌋ : ℚ) / 2 ^ k := snapAbs_of_nonneg k hq
    have h1 : (⌊q * 2 ^ k⌋ : ℚ) / 2 ^ k ≤ q := floor_div_le_self hq k
    have h2 : q - (⌊q * 2 ^ k⌋ : ℚ) / 2 ^ k < 1 / 2 ^ k := self_sub_floor_div_lt q k
    rw [hs, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact le_of_lt h2
  · have hq' : 0 ≤ -q := le_of_lt (neg_pos.mpr hq)
    have hs : snapAbs k q = -((⌊(-q) * 2 ^ k⌋ : ℚ) / 2 ^ k) := snapAbs_of_neg k hq
    have h1 : (⌊(-q) * 2 ^ k⌋ : ℚ) / 2 ^ k ≤ -q := floor_div_le_self hq' k
    have h2 : (-q) - (⌊(-q) * 2 ^ k⌋ : ℚ) / 2 ^ k < 1 / 2 ^ k := self_sub_floor_div_lt (-q) k
    rw [hs]
    have : -((⌊(-q) * 2 ^ k⌋ : ℚ) / 2 ^ k) - q = (-q) - (⌊(-q) * 2 ^ k⌋ : ℚ) / 2 ^ k := by ring
    rw [this, abs_of_nonneg (by linarith)]
    exact le_of_lt h2

/-- **The snap lands on the grid**: it is an integer over `2^k`. -/
theorem snapAbs_dyadic (k : ℕ) (q : ℚ) : ∃ m : ℤ, snapAbs k q = (m : ℚ) / 2 ^ k := by
  rcases le_or_gt 0 q with hq | hq
  · exact ⟨⌊q * 2 ^ k⌋, snapAbs_of_nonneg k hq⟩
  · exact ⟨-⌊(-q) * 2 ^ k⌋, by rw [snapAbs_of_neg k hq]; push_cast; ring⟩

/-- The snap is odd. -/
theorem snapAbs_neg (k : ℕ) (q : ℚ) : snapAbs k (-q) = -snapAbs k q := by
  rcases lt_trichotomy q 0 with hq | hq | hq
  · rw [snapAbs_of_nonneg k (le_of_lt (neg_pos.mpr hq)), snapAbs_of_neg k hq, neg_neg]
  · subst hq; simp [snapAbs_zero]
  · rw [snapAbs_of_neg k (neg_neg_of_pos hq), snapAbs_of_nonneg k (le_of_lt hq)]
    ring

/-- Snapping a value that is already on the grid changes nothing. -/
theorem snapAbs_dyadic_self {k : ℕ} {s : ℚ} (h : ∃ m : ℤ, s = (m : ℚ) / 2 ^ k) :
    snapAbs k s = s := by
  obtain ⟨m, hm⟩ := h
  have hkey : s * 2 ^ k = (m : ℚ) := by rw [hm]; field_simp
  rcases le_or_gt 0 s with hs | hs
  · rw [snapAbs_of_nonneg k hs, hkey, Int.floor_intCast, hm]
  · have hkey' : (-s) * 2 ^ k = ((-m : ℤ) : ℚ) := by
      rw [show -s * 2 ^ k = -(s * 2 ^ k) by ring, hkey]
      push_cast
      ring
    rw [snapAbs_of_neg k hs, hkey', Int.floor_intCast, hm]
    push_cast
    ring

/-- The snap is idempotent. -/
theorem snapAbs_idem (k : ℕ) (q : ℚ) : snapAbs k (snapAbs k q) = snapAbs k q :=
  snapAbs_dyadic_self (snapAbs_dyadic k q)

/-! ## 2.  The height reset: the grid replaces the operand's bit-length by the value bound -/

/-- **The height of a grid value is `value exponent + resolution`.**  Division by `2^k` of an
integer of absolute value at most `2^(M+k)`. -/
theorem hasHeight_div_two_pow {m : ℤ} {M k : ℕ} (hm : |m| ≤ (2 : ℤ) ^ (M + k)) :
    HasHeight ((m : ℚ) / 2 ^ k) (M + k) := by
  have hb : |((2 : ℤ) ^ k)| ≤ (2 : ℤ) ^ (M + k) := by
    rw [abs_of_nonneg (by positivity)]
    have h : (2 : ℕ) ^ k ≤ (2 : ℕ) ^ (M + k) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (((2 : ℕ) ^ k : ℕ) : ℤ) ≤ (((2 : ℕ) ^ (M + k) : ℕ) : ℤ) := by exact_mod_cast h
    simpa using h2
  have h := OAI.MetricKMedian.Gaussian.ratio_num_den_bound m ((2 : ℤ) ^ k) (by positivity)
    ((2 : ℤ) ^ (M + k)) hm hb
  have hcast : (((2 : ℤ) ^ k : ℤ) : ℚ) = (2 : ℚ) ^ k := by push_cast; ring
  rw [hcast] at h
  exact h

/-- **The height reset.**  A value bounded by `2^M` snaps to a rational of height `M + k` — the
height of the operand is irrelevant. -/
theorem hasHeight_snapAbs {q : ℚ} {M : ℕ} (hq : |q| ≤ 2 ^ M) (k : ℕ) :
    HasHeight (snapAbs k q) (M + k) := by
  obtain ⟨m, hm⟩ := snapAbs_dyadic k q
  have h2 : (0 : ℚ) < 2 ^ k := two_pow_pos k
  have habs : |(m : ℚ)| ≤ (2 : ℚ) ^ (M + k) := by
    have hle : |(m : ℚ) / 2 ^ k| ≤ 2 ^ M := by
      rw [← hm]
      exact (snapAbs_abs_le k q).trans hq
    have hdiv : |(m : ℚ) / 2 ^ k| = |(m : ℚ)| / 2 ^ k := by
      rw [abs_div, abs_of_nonneg (le_of_lt h2)]
    rw [hdiv] at hle
    have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt h2)
    rw [div_mul_cancel₀ _ (ne_of_gt h2)] at hmul
    calc |(m : ℚ)| ≤ 2 ^ M * 2 ^ k := hmul
      _ = 2 ^ (M + k) := by rw [← pow_add]
  rw [hm]
  exact hasHeight_div_two_pow (by exact_mod_cast habs)

/-- A round map is **value-stable** when it maps the box `|x| ≤ 2^M` into itself.  (For the
ellipsoid step this is the value side of the containment invariant; it is supplied by the analysis,
not by this file.) -/
def ValueStable (M : ℕ) (f : ℚ → ℚ) : Prop := ∀ q : ℚ, |q| ≤ 2 ^ M → |f q| ≤ 2 ^ M

/-- **The height reset survives every round.**  With `snapAbs k` applied after each value-stable
round, both the value bound and the height bound `M + k` are invariant — the round count does not
appear.  This is the statement that replaces `HeightGrowth.height_iterate`'s `(c+1)^T·(B+c+1)`. -/
theorem snapIterate_value_height (k M : ℕ) {f : ℚ → ℚ} (hf : ValueStable M f) {q₀ : ℚ}
    (h0v : |q₀| ≤ 2 ^ M) (h0h : HasHeight q₀ (M + k)) :
    ∀ R : ℕ, |((fun q => snapAbs k (f q))^[R]) q₀| ≤ 2 ^ M ∧
      HasHeight (((fun q => snapAbs k (f q))^[R]) q₀) (M + k) := by
  intro R
  induction R with
  | zero => exact ⟨h0v, h0h⟩
  | succ R ih =>
      obtain ⟨hv, hh⟩ := ih
      have hfR : |f (((fun q => snapAbs k (f q))^[R]) q₀)| ≤ 2 ^ M := hf _ hv
      rw [Function.iterate_succ_apply']
      exact ⟨(snapAbs_abs_le k _).trans hfR, hasHeight_snapAbs hfR k⟩

theorem snapIterate_height (k M : ℕ) {f : ℚ → ℚ} (hf : ValueStable M f) {q₀ : ℚ}
    (h0v : |q₀| ≤ 2 ^ M) (h0h : HasHeight q₀ (M + k)) (R : ℕ) :
    HasHeight (((fun q => snapAbs k (f q))^[R]) q₀) (M + k) :=
  (snapIterate_value_height k M hf h0v h0h R).2

/-! ### Matrix (state) form -/

/-- Every entry of the matrix is bounded by `2^M` in absolute value. -/
def MatValueBounded {n : ℕ} (M : ℕ) (X : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∀ i j, |X i j| ≤ 2 ^ M

theorem matValueBounded_map_snap {n M k : ℕ} {X : Matrix (Fin n) (Fin n) ℚ}
    (hX : MatValueBounded M X) : MatValueBounded M (X.map (snapAbs k)) := by
  intro i j
  rw [Matrix.map_apply]
  exact (snapAbs_abs_le k _).trans (hX i j)

theorem matHeight_map_snap {n M k : ℕ} {X : Matrix (Fin n) (Fin n) ℚ}
    (hX : MatValueBounded M X) : ∀ i j, HasHeight ((X.map (snapAbs k)) i j) (M + k) := by
  intro i j
  rw [Matrix.map_apply]
  exact hasHeight_snapAbs (hX i j) k

/-- **The state ledger under snap semantics.**  If the round map `step` is entrywise value-stable,
then every entry of every snapped iterate has height exactly bounded by `M + k`, and the value
bound is preserved.  `M` is the value exponent supplied by the containment analysis (e.g. from
`Aat_det_le`: the iterate is Loewner-pinched between `A₀` and a determinant-controlled multiple of
it), `k` is the grid resolution. -/
theorem snapRound_value_height {n : ℕ} (k M : ℕ)
    (step : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ)
    (hstep : ∀ X, MatValueBounded M X → MatValueBounded M (step X))
    {X₀ : Matrix (Fin n) (Fin n) ℚ} (h0v : MatValueBounded M X₀)
    (h0h : ∀ i j, HasHeight (X₀ i j) (M + k)) (R : ℕ) :
    MatValueBounded M (((fun X => (step X).map (snapAbs k))^[R]) X₀) ∧
      ∀ i j, HasHeight ((((fun X => (step X).map (snapAbs k))^[R]) X₀) i j) (M + k) := by
  induction R with
  | zero => exact ⟨h0v, h0h⟩
  | succ R ih =>
      obtain ⟨hv, hh⟩ := ih
      have hs : MatValueBounded M (step (((fun X => (step X).map (snapAbs k))^[R]) X₀)) :=
        hstep _ hv
      rw [Function.iterate_succ_apply']
      exact ⟨matValueBounded_map_snap hs, matHeight_map_snap hs⟩

section ValueExponent

/-- **The value-exponent ledger.**  If one round multiplies magnitudes by at most `2^γ` (additivity
of bit-lengths: `|q| ≤ 2^(M+γt) ⟹ |f q| ≤ 2^(M+γ(t+1))`), then after `T` rounds the value exponent is
at most `M + γ·T`.  This is the honest value track: magnitudes *do* grow in an ellipsoid run, but
what costs bit-length is the *exponent*, and an additive-per-round exponent is polynomial in the
round count, while the fatal phase-6 growth was multiplicative (`L ↦ c·L + c`). -/
theorem value_exponent_iterate {M γ : ℕ} {f : ℚ → ℚ}
    (hf : ∀ (t : ℕ) (q : ℚ), |q| ≤ 2 ^ (M + γ * t) → |f q| ≤ 2 ^ (M + γ * (t + 1)))
    {q₀ : ℚ} (h0 : |q₀| ≤ 2 ^ M) :
    ∀ T : ℕ, |(f^[T]) q₀| ≤ 2 ^ (M + γ * T) := by
  intro T
  induction T with
  | zero => simpa using h0
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact hf T _ ih

/-- **The closed-form entries-length bound of the snapped run, with value growth.**  After `T`
snapped rounds, every entry of the state has height at most `M + γ·T + k`: the value exponent grows
(additively) at rate `γ`, and the grid costs `k`.  This is the ledger the `Poly` charge consumes; it
is polynomial in the round count and linear in the input height. -/
theorem snap_height_with_value_growth {M γ k : ℕ} {f : ℚ → ℚ}
    (hf : ∀ (t : ℕ) (q : ℚ), |q| ≤ 2 ^ (M + γ * t) → |f q| ≤ 2 ^ (M + γ * (t + 1)))
    {q₀ : ℚ} (h0v : |q₀| ≤ 2 ^ M) (h0h : HasHeight q₀ (M + k)) (T : ℕ) :
    HasHeight (((fun q => snapAbs k (f q))^[T]) q₀) (M + γ * T + k) := by
  have hg : ∀ (t : ℕ) (q : ℚ), |q| ≤ 2 ^ (M + γ * t) →
      |(fun q => snapAbs k (f q)) q| ≤ 2 ^ (M + γ * (t + 1)) := by
    intro t q hq
    exact (snapAbs_abs_le k _).trans (hf t q hq)
  cases T with
  | zero => simpa using h0h.mono (by omega : M + k ≤ M + γ * 0 + k)
  | succ T =>
      rw [Function.iterate_succ_apply']
      refine hasHeight_snapAbs ?_ k
      exact hf T _ (value_exponent_iterate (f := fun q => snapAbs k (f q)) hg h0v T)

/-- Matrix form of the value-exponent ledger. -/
theorem matValueBounded_iterate {n : ℕ} {M γ : ℕ}
    (step : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ)
    (hstep : ∀ (t : ℕ) (X : Matrix (Fin n) (Fin n) ℚ),
      MatValueBounded (M + γ * t) X → MatValueBounded (M + γ * (t + 1)) (step X))
    {X₀ : Matrix (Fin n) (Fin n) ℚ} (h0 : MatValueBounded M X₀) :
    ∀ T : ℕ, MatValueBounded (M + γ * T) ((step^[T]) X₀) := by
  intro T
  induction T with
  | zero => simpa using h0
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact hstep T _ ih

/-- **The state ledger, fully closed form.**  Under a per-round magnitude amplification `2^γ` (the
value track), the snapped state after `T` rounds has entry heights at most `M + γ·T + k`
*and* magnitudes at most `2^(M+γT)` — both driven by the round index only additively.  Compare
`HeightGrowth.height_iterate : HasHeight (f^[T] q) ((c+1)^T * (B+c+1))` for the exact iterate. -/
theorem snapRound_closed_form {n : ℕ} (k M γ : ℕ)
    (step : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ)
    (hstep : ∀ (t : ℕ) (X : Matrix (Fin n) (Fin n) ℚ),
      MatValueBounded (M + γ * t) X → MatValueBounded (M + γ * (t + 1)) (step X))
    {X₀ : Matrix (Fin n) (Fin n) ℚ} (h0v : MatValueBounded M X₀)
    (h0h : ∀ i j, HasHeight (X₀ i j) (M + k)) (T : ℕ) :
    MatValueBounded (M + γ * T) (((fun X => (step X).map (snapAbs k))^[T]) X₀) ∧
      ∀ i j, HasHeight ((((fun X => (step X).map (snapAbs k))^[T]) X₀) i j) (M + γ * T + k) := by
  induction T with
  | zero => exact ⟨h0v, fun i j => (h0h i j).mono (by omega)⟩
  | succ T ih =>
      obtain ⟨hv, hh⟩ := ih
      have hs : MatValueBounded (M + γ * (T + 1))
          (step (((fun X => (step X).map (snapAbs k))^[T]) X₀)) := hstep T _ hv
      rw [Function.iterate_succ_apply']
      refine ⟨matValueBounded_map_snap hs, fun i j => ?_⟩
      rw [Matrix.map_apply]
      exact (hasHeight_snapAbs (hs i j) k).mono (by omega)

end ValueExponent

/-- **The value-exponent ledger with a round-dependent rate.**  The ellipsoid's per-round magnitude
amplification is not uniform in practice (it is governed by `λ_min(A_k)`, which drifts), so the value
track is stated with a rate `γ : ℕ → ℕ` and its cumulative sum
`∑_{i<T} γ i`.  Nothing changes: the exponent still only accumulates additively. -/
theorem value_exponent_iterate_rate {M : ℕ} {γ : ℕ → ℕ} {f : ℚ → ℚ}
    (hf : ∀ (t : ℕ) (q : ℚ),
      |q| ≤ 2 ^ (M + ∑ i ∈ Finset.range t, γ i) → |f q| ≤ 2 ^ (M + ∑ i ∈ Finset.range (t + 1), γ i))
    {q₀ : ℚ} (h0 : |q₀| ≤ 2 ^ M) :
    ∀ T : ℕ, |(f^[T]) q₀| ≤ 2 ^ (M + ∑ i ∈ Finset.range T, γ i) := by
  intro T
  induction T with
  | zero => simpa using h0
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact hf T _ ih

/-! ### Encoded lengths and the per-round charge -/

/-- The encoded length of a snapped value. -/
theorem snap_encode_length {q : ℚ} {M : ℕ} (hq : |q| ≤ 2 ^ M) (k : ℕ) :
    (Ratio.encode (snapAbs k q)).length ≤ 3 * (M + k) + 10 :=
  QMCLeafB.CertSize.encode_length_le_of_hasHeight (hasHeight_snapAbs hq k)

/-- The encoded length of a state matrix: `n²` entries, each `≤ 3L + 10` bits. -/
theorem state_encode_length {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) {L : ℕ}
    (h : ∀ i j, HasHeight (X i j) L) :
    (∑ i, ∑ j, (Ratio.encode (X i j)).length) ≤ n * n * (3 * L + 10) := by
  have h1 : ∀ i, (∑ j, (Ratio.encode (X i j)).length) ≤ n * (3 * L + 10) := by
    intro i
    calc ∑ j, (Ratio.encode (X i j)).length ≤ ∑ _j : Fin n, (3 * L + 10) :=
          Finset.sum_le_sum fun j _ => QMCLeafB.CertSize.encode_length_le_of_hasHeight (h i j)
      _ = n * (3 * L + 10) := by simp
  calc ∑ i, ∑ j, (Ratio.encode (X i j)).length ≤ ∑ _i : Fin n, n * (3 * L + 10) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = n * (n * (3 * L + 10)) := by simp [Finset.sum_const]
    _ = n * n * (3 * L + 10) := by ring

/-- **The per-round charge of the snapped simulation**: `n²` entries at height `M + k`. -/
theorem round_charge {n : ℕ} (k M : ℕ) {X : Matrix (Fin n) (Fin n) ℚ}
    (hX : MatValueBounded M X) :
    (∑ i, ∑ j, (Ratio.encode ((X.map (snapAbs k)) i j)).length) ≤ n * n * (3 * (M + k) + 10) :=
  state_encode_length _ (matHeight_map_snap hX)

/-- **The per-round charge is linear in the input length.**  If `N` dominates `n²(M+k+1)` (the
input length of an `n`-vertex instance whose weights have height `M+k+1`), one round charges at most
`12N` bits — the `SizeProfile` monomial `12·X`. -/
theorem round_charge_monomial {n M k N : ℕ} (hN : n * n * (M + k + 1) ≤ N) :
    n * n * (3 * (M + k) + 10) ≤ 12 * N := by
  have h1 : 3 * (M + k) + 10 ≤ 12 * (M + k + 1) := by omega
  calc n * n * (3 * (M + k) + 10) ≤ n * n * (12 * (M + k + 1)) := by
        exact Nat.mul_le_mul_left _ h1
    _ = 12 * (n * n * (M + k + 1)) := by ring
    _ ≤ 12 * N := Nat.mul_le_mul_left 12 hN

/-- **The whole run's charge**: `T` snapped rounds charge `T·n²·(3(M+k)+10)` bits, and that is
`12·T·N` with `N` the input length — a `SizeProfile` monomial in the input length, uniformly in the
rounds. -/
theorem run_charge_monomial {T n M k N : ℕ} (hN : n * n * (M + k + 1) ≤ N) :
    T * (n * n * (3 * (M + k) + 10)) ≤ 12 * T * N := by
  have h := round_charge_monomial (M := M) (k := k) hN
  calc T * (n * n * (3 * (M + k) + 10)) ≤ T * (12 * N) := Nat.mul_le_mul_left T h
    _ = 12 * T * N := by ring

section RoundCharge

/-- **The per-round intermediate charge.**  One round of the exact-`ℚ` arithmetic, run on *snapped*
state data (entry height `M + k`) against a cut normal of height `Bc` and a depth of height `Bl`,
produces intermediates of height bounded by the closed form below — independent of the round index.
These are the four quantities a round's program materialises: `w = X·c`, `σ = cᵀw`, the multiplier
`μ = λ/(1+λσ)` and the updated shape `X − μ·w wᵀ` (before it is snapped back to height `M + k`).

The point for the loop-`Poly` brick: the charge of round `r` depends only on `(n, M+k, Bc, Bl)` and
never on `r`, because the input to every round has the *fixed* height `M + k` of
`hasHeight_snapAbs`, not the growing height of the exact iterate. -/
theorem round_intermediate_heights {n : ℕ} (k M Bc Bl : ℕ)
    {X : Matrix (Fin n) (Fin n) ℚ} {c : Fin n → ℚ} {lam : ℚ}
    (hXh : ∀ i j, HasHeight (X i j) (M + k)) (hc : ∀ i, HasHeight (c i) Bc)
    (hl : HasHeight lam Bl) :
    (∀ i, HasHeight ((X *ᵥ c) i) (n * ((M + k) + Bc + 1))) ∧
    HasHeight (c ⬝ᵥ (X *ᵥ c)) (n * (Bc + n * ((M + k) + Bc + 1) + 1)) ∧
    HasHeight (lam / (1 + lam * (c ⬝ᵥ (X *ᵥ c))))
      (Bl + (Bl + (Bl + n * (Bc + n * ((M + k) + Bc + 1) + 1)) + 1)) ∧
    (∀ i j, HasHeight
      ((X - (lam / (1 + lam * (c ⬝ᵥ (X *ᵥ c)))) •
        Matrix.vecMulVec (X *ᵥ c) (X *ᵥ c)) i j)
      ((M + k) + ((Bl + (Bl + (Bl + n * (Bc + n * ((M + k) + Bc + 1) + 1)) + 1)) +
        (n * ((M + k) + Bc + 1) + n * ((M + k) + Bc + 1))) + 1)) := by
  have hw : ∀ i, HasHeight ((X *ᵥ c) i) (n * ((M + k) + Bc + 1)) :=
    QMCLeafB.CertSize.hasHeight_mulVec X c hXh hc
  have hσ : HasHeight (c ⬝ᵥ (X *ᵥ c)) (n * (Bc + n * ((M + k) + Bc + 1) + 1)) :=
    QMCLeafB.CertSize.hasHeight_qf X c hXh hc
  have hμ : HasHeight (lam / (1 + lam * (c ⬝ᵥ (X *ᵥ c))))
      (Bl + (Bl + (Bl + n * (Bc + n * ((M + k) + Bc + 1) + 1)) + 1)) :=
    hl.div (HasHeight.add (HasHeight.one (L := Bl)) (hl.mul hσ))
  refine ⟨hw, hσ, hμ, fun i j => ?_⟩
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  exact (hXh i j).sub (hμ.mul ((hw i).mul (hw j)))

/-- The round charge is **monotone in the grid resolution**: refining the grid cannot help the
per-round size, and coarsening it does not increase the per-entry length beyond `3k`. -/
theorem snap_height_le_succ (k M : ℕ) : M + k ≤ M + (k + 1) := by omega

end RoundCharge

/-! ## 3.  The accumulated snap error and the explicit tolerance budget -/

/-- **The amplified perturbation recursion.**  A per-round entrywise perturbation `ε` on top of an
amplification `L ≥ 1` accumulates to `(|e₀| + R·ε)·L^R` after `R` rounds.  `Check_errprop`'s
`abs_sub_le_natCast_mul_of_steps` is the case `L = 1`. -/
theorem err_le_of_step {e : ℕ → ℚ} {ε L : ℚ} (hL : 1 ≤ L) (hε : 0 ≤ ε)
    (h : ∀ r, |e (r + 1)| ≤ L * |e r| + ε) :
    ∀ R : ℕ, |e R| ≤ (|e 0| + R * ε) * L ^ R := by
  intro R
  induction R with
  | zero => simp
  | succ R ih =>
      have hstep := h R
      have hL0 : (1 : ℚ) ≤ L ^ (R + 1) := one_le_pow₀ hL
      have hLnn : (0 : ℚ) ≤ L := le_trans zero_le_one hL
      have h1 : L * |e R| ≤ L * ((|e 0| + R * ε) * L ^ R) := mul_le_mul_of_nonneg_left ih hLnn
      have hεle : ε ≤ ε * (L ^ R * L) := by
        have h := mul_le_mul_of_nonneg_left hL0 hε
        rw [pow_succ] at h
        simpa using h
      rw [pow_succ]
      push_cast
      have expand : (|e 0| + (↑R + 1) * ε) * (L ^ R * L)
          = (|e 0| + ↑R * ε) * (L ^ R * L) + ε * (L ^ R * L) := by ring
      rw [expand]
      nlinarith [hstep, h1, hεle, abs_nonneg (e 0), abs_nonneg (e R)]

/-- The `L = 1` form: `m` snapped rounds at error `ε` each cost at most `m·ε` in total. -/
theorem err_le_of_step_const {e : ℕ → ℚ} {ε : ℚ} (hε : 0 ≤ ε)
    (h : ∀ r, |e (r + 1)| ≤ |e r| + ε) : ∀ R : ℕ, |e R| ≤ |e 0| + R * ε := by
  intro R
  have h1 := err_le_of_step (e := e) (ε := ε) (L := 1) le_rfl hε (by simpa using h) R
  simpa using h1

/-- **The snap error of a run**: zero initial error, one grid step per round. -/
theorem snap_err_le {L : ℚ} (hL : 1 ≤ L) (k T : ℕ) {e : ℕ → ℚ} (h0 : e 0 = 0)
    (h : ∀ r, |e (r + 1)| ≤ L * |e r| + 1 / 2 ^ k) :
    |e T| ≤ (T : ℚ) / 2 ^ k * L ^ T := by
  have hε : (0 : ℚ) ≤ 1 / 2 ^ k := le_of_lt (one_div_two_pow_pos k)
  have h1 := err_le_of_step hL hε h T
  rw [h0, abs_zero, zero_add] at h1
  calc |e T| ≤ (T : ℚ) * (1 / 2 ^ k) * L ^ T := h1
    _ = (T : ℚ) / 2 ^ k * L ^ T := by ring

/-- **The budget the margin can absorb.**  If `δ·2^k` dominates `2·T·L^T` then the whole run's
accumulated snap error is at most `δ/2`, i.e. the ErrProp margin degrades by less than half its
budget. -/
theorem snap_error_budget {T : ℕ} {L δ : ℚ} {k : ℕ} (hδ : 0 < δ)
    (h : 2 * (T : ℚ) * L ^ T ≤ δ * 2 ^ k) :
    (T : ℚ) / 2 ^ k * L ^ T ≤ δ / 2 := by
  have hk : (0 : ℚ) < 2 ^ k := two_pow_pos k
  have heq : (T : ℚ) / 2 ^ k * L ^ T = ((T : ℚ) * L ^ T) / 2 ^ k := by ring
  rw [heq, div_le_iff₀ hk]
  nlinarith [h]

/-- **The explicit precision.**  Taking `k = ⌈2·T·L^T/δ⌉` makes the budget of
`snap_error_budget` hold, because `m ≤ 2^m` for a natural `m`. -/
theorem snap_precision_ceil {T : ℕ} {L : ℚ} (hL : 1 ≤ L) {δ : ℚ} (hδ : 0 < δ) :
    2 * (T : ℚ) * L ^ T ≤ δ * 2 ^ (Nat.ceil (2 * (T : ℚ) * L ^ T / δ)) := by
  have hLnn : (0 : ℚ) ≤ L := le_trans zero_le_one hL
  set k : ℕ := Nat.ceil (2 * (T : ℚ) * L ^ T / δ) with hk
  have hpow : (0 : ℚ) ≤ L ^ T := pow_nonneg hLnn T
  have hnonneg : (0 : ℚ) ≤ 2 * (T : ℚ) * L ^ T / δ :=
    div_nonneg (by positivity) hδ.le
  have hx : 2 * (T : ℚ) * L ^ T / δ ≤ (k : ℚ) := Nat.le_ceil _
  have hk2 : (k : ℚ) ≤ 2 ^ k := by
    have h : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
    exact_mod_cast h
  rw [div_le_iff₀ hδ] at hx
  nlinarith [hx, hk2, hδ]

/-- **The tolerance is absorbed at the explicit precision.** -/
theorem snap_error_total_budget {T : ℕ} {L : ℚ} (hL : 1 ≤ L) {δ : ℚ} (hδ : 0 < δ) :
    (T : ℚ) / 2 ^ (Nat.ceil (2 * (T : ℚ) * L ^ T / δ)) * L ^ T ≤ δ / 2 :=
  snap_error_budget hδ (snap_precision_ceil hL hδ)

/-- **The log-scale snap precision** for a run of `T` rounds with per-round amplification `L ≥ 1`
and total error budget `δ > 0`: the number of bits of `2TL^T/δ`, i.e. the *bit* budget of the error,
not its value. -/
def snapPrec (T : ℕ) (L : ℚ) (δ : ℚ) : ℕ := Nat.clog 2 ⌈2 * (T : ℚ) * L ^ T / δ⌉₊

/-- **The log-scale precision works.** -/
theorem snap_precision_log {T : ℕ} {L : ℚ} (hL : 1 ≤ L) {δ : ℚ} (hδ : 0 < δ) :
    2 * (T : ℚ) * L ^ T ≤ δ * 2 ^ snapPrec T L δ := by
  have hLnn : (0 : ℚ) ≤ L := le_trans zero_le_one hL
  have hx : (0 : ℚ) ≤ 2 * (T : ℚ) * L ^ T / δ :=
    div_nonneg (by have := pow_nonneg hLnn T; positivity) hδ.le
  have h1 : 2 * (T : ℚ) * L ^ T / δ ≤ (⌈2 * (T : ℚ) * L ^ T / δ⌉₊ : ℚ) := Nat.le_ceil _
  have h2 : ((⌈2 * (T : ℚ) * L ^ T / δ⌉₊ : ℕ) : ℚ) ≤ 2 ^ snapPrec T L δ := by
    have h := Nat.le_pow_clog (b := 2) (by norm_num) ⌈2 * (T : ℚ) * L ^ T / δ⌉₊
    have h' : ((⌈2 * (T : ℚ) * L ^ T / δ⌉₊ : ℕ) : ℚ) ≤ ((2 ^ Nat.clog 2 ⌈2 * (T : ℚ) * L ^ T / δ⌉₊ : ℕ) : ℚ) := by
      exact_mod_cast h
    simpa [snapPrec] using h'
  have h3 : 2 * (T : ℚ) * L ^ T / δ ≤ 2 ^ snapPrec T L δ := h1.trans h2
  rw [div_le_iff₀ hδ] at h3
  simpa [mul_comm] using h3

/-- **The sharp accumulated-error budget**: at the log-scale precision the whole run's snap error is
at most `δ/2`. -/
theorem snap_error_total_budget_log {T : ℕ} {L : ℚ} (hL : 1 ≤ L) {δ : ℚ} (hδ : 0 < δ) :
    (T : ℚ) / 2 ^ snapPrec T L δ * L ^ T ≤ δ / 2 :=
  snap_error_budget hδ (snap_precision_log hL hδ)

/-- **The precision is logarithmic in the budget**: if the budget is at most `2^P` then the required
precision is at most `P` — so the grid resolution is `2^{-P}` with `P` the *bit* budget of the
accumulated error, not its value. -/
theorem snap_precision_clog_le {T : ℕ} {L δ : ℚ} {P : ℕ} (hL : 1 ≤ L) (hδ : 0 < δ)
    (hP : 2 * (T : ℚ) * L ^ T / δ ≤ 2 ^ P) :
    snapPrec T L δ ≤ P := by
  have hLnn : (0 : ℚ) ≤ L := le_trans zero_le_one hL
  have hx : (0 : ℚ) ≤ 2 * (T : ℚ) * L ^ T / δ :=
    div_nonneg (by have := pow_nonneg hLnn T; positivity) hδ.le
  have hceil : ⌈2 * (T : ℚ) * L ^ T / δ⌉₊ ≤ 2 ^ P := by
    refine Nat.ceil_le.mpr ?_
    push_cast
    exact hP
  exact (Nat.clog_le_iff_le_pow (b := 2) (by norm_num)).mpr hceil

/-- **The ledger, end to end.**  At the log-scale precision the snapped value has height at most
`M + P`, where `2^P` bounds the run's error budget: the entry height is (input height) + (bit budget
of the accumulated error), with no round-count factor. -/
theorem hasHeight_snapAbs_of_budget {M P T : ℕ} {L : ℚ} {δ : ℚ} (hL : 1 ≤ L) (hδ : 0 < δ)
    (hP : 2 * (T : ℚ) * L ^ T / δ ≤ 2 ^ P) {q : ℚ} (hq : |q| ≤ 2 ^ M) :
    HasHeight (snapAbs (snapPrec T L δ) q) (M + P) := by
  have hk := snap_precision_clog_le hL hδ hP
  exact (hasHeight_snapAbs hq _).mono (by omega)

/-- The height track of the ledger: after `T+1` snapped rounds of a value-stable map the entry
height is `M + γ(T+1) + k`. -/
theorem hasHeight_snapIterate_value_growth {M γ k : ℕ} {f : ℚ → ℚ}
    (hf : ∀ (t : ℕ) (q : ℚ), |q| ≤ 2 ^ (M + γ * t) → |f q| ≤ 2 ^ (M + γ * (t + 1)))
    {q₀ : ℚ} (h0v : |q₀| ≤ 2 ^ M) (T : ℕ) :
    HasHeight (((fun q => snapAbs k (f q))^[T + 1]) q₀) (M + γ * (T + 1) + k) := by
  have hg : ∀ (t : ℕ) (q : ℚ), |q| ≤ 2 ^ (M + γ * t) →
      |(fun q => snapAbs k (f q)) q| ≤ 2 ^ (M + γ * (t + 1)) := by
    intro t q hq
    exact (snapAbs_abs_le _ _).trans (hf t q hq)
  have hv := value_exponent_iterate hg h0v T
  rw [Function.iterate_succ_apply']
  exact hasHeight_snapAbs (hf T _ hv) k

/-- **The ledger, in one statement** (for a run of `T+1` rounds, the honest indexing).  A run in
which magnitudes are multiplied by at most `2^γ` per round, with every round's entries snapped onto
the grid of resolution `k = snapPrec (T+1) (2^γ) δ`, has
* value track: `|state| ≤ 2^(M + γ(T+1))`;
* height track: every entry has height `≤ M + γ(T+1) + k` — the round count enters the exponent only
  *additively*, which is what keeps it polynomial;
* error track: the total accumulated snap error is at most `δ/2`.

These are the three tracks `brick-loop-poly` (per-round charges), `brick-sim-snap` (soundness inside
the degraded margin) and `brick-solution-file` (the final `Poly`) consume. -/
theorem snap_run_ledger {M γ T : ℕ} {δ : ℚ} {f : ℚ → ℚ}
    (hf : ∀ (t : ℕ) (q : ℚ), |q| ≤ 2 ^ (M + γ * t) → |f q| ≤ 2 ^ (M + γ * (t + 1)))
    {q₀ : ℚ} (h0v : |q₀| ≤ 2 ^ M) (hδ : 0 < δ) (hL : 1 ≤ (2 : ℚ) ^ γ) :
    |((fun q => snapAbs (snapPrec (T + 1) (2 ^ γ) δ) (f q))^[T + 1]) q₀|
        ≤ 2 ^ (M + γ * (T + 1)) ∧
      HasHeight (((fun q => snapAbs (snapPrec (T + 1) (2 ^ γ) δ) (f q))^[T + 1]) q₀)
        (M + γ * (T + 1) + snapPrec (T + 1) (2 ^ γ) δ) ∧
      ((T : ℚ) + 1) / 2 ^ snapPrec (T + 1) (2 ^ γ) δ * (2 ^ γ) ^ (T + 1) ≤ δ / 2 := by
  have hg : ∀ (t : ℕ) (q : ℚ), |q| ≤ 2 ^ (M + γ * t) →
      |(fun q => snapAbs (snapPrec (T + 1) (2 ^ γ) δ) (f q)) q| ≤ 2 ^ (M + γ * (t + 1)) := by
    intro t q hq
    exact (snapAbs_abs_le _ _).trans (hf t q hq)
  refine ⟨value_exponent_iterate hg h0v (T + 1),
    hasHeight_snapIterate_value_growth hf h0v T, ?_⟩
  have h := snap_error_total_budget_log (T := T + 1) (L := 2 ^ γ) hL hδ
  push_cast at h ⊢
  exact h

/-- **The required precision is polynomial**: `k ≤ 2T·L^T/δ + 1`, so the grid resolution `2^{-k}`
is `1/poly`, and the per-entry height `M + k` of §2 is polynomial in the instance size whenever
`T`, `L^T` and `1/δ` are.  (The sharper `snap_precision_clog_le` is the form the height ledger uses:
this one is value-level, for reading the size off the raw budget.) -/
theorem snap_precision_upper {T : ℕ} {L : ℚ} (hL : 1 ≤ L) {δ : ℚ} (hδ : 0 < δ) :
    (Nat.ceil (2 * (T : ℚ) * L ^ T / δ) : ℚ) ≤ 2 * (T : ℚ) * L ^ T / δ + 1 := by
  have hLnn : (0 : ℚ) ≤ L := le_trans zero_le_one hL
  have hpow : (0 : ℚ) ≤ L ^ T := pow_nonneg hLnn T
  have hnonneg : (0 : ℚ) ≤ 2 * (T : ℚ) * L ^ T / δ :=
    div_nonneg (by positivity) hδ.le
  exact le_of_lt (Nat.ceil_lt_add_one (a := 2 * (T : ℚ) * L ^ T / δ) hnonneg)

/-! ## 4.  Kernel-checked instances

The two numbers below are decided by the kernel straight from the definitions, in the style of
`Check_DyadicSqrt`'s §7. -/

/-- Snapping `1/3` to the grid `2^{-4}ℤ` gives `5/16` (truncation is downward at positive values). -/
example : QMCLeafB.LedgerSnap.snapAbs 4 (1 / 3) = 5 / 16 := by
  rw [QMCLeafB.LedgerSnap.snapAbs_of_nonneg 4 (by norm_num)]
  norm_num

/-- The snap of `1/3` at resolution `4` has height at most `4` (`|5/16|`: num `5 ≤ 16`, den `16`). -/
example : HasHeight (QMCLeafB.LedgerSnap.snapAbs 4 (1 / 3)) 4 :=
  QMCLeafB.LedgerSnap.hasHeight_snapAbs (M := 0) (by norm_num) 4

/-- **No height growth over `100` snapped rounds.**  The identity is value-stable in the box
`|q| ≤ 1`, so after `100` snapped rounds the value still has height `≤ 4` — whereas the exact
iterate's bound at `100` rounds is `(c+1)^100·(B+c+1)` for any `c ≥ 1`
(`HeightGrowth.height_iterate_ge_two_pow`). -/
example : HasHeight
    (((fun q => QMCLeafB.LedgerSnap.snapAbs 4 (id q))^[100]) (1 / 3)) 4 := by
  refine QMCLeafB.LedgerSnap.snapIterate_height 4 0 (f := id) ?_ (by norm_num) ?_ 100
  · intro q hq
    simpa using hq
  · have h : HasHeight (1 / 3 : ℚ) 4 := by
      constructor <;> norm_num
    simpa using h

/-- The accumulated-error budget at the explicit precision: a `100`-round run with per-round
amplification `2` at tolerance `δ = 1` needs precision `⌈2·100·2^100⌉` and ends within `1/2`. -/
example : (100 : ℚ) / 2 ^ (Nat.ceil (2 * (100 : ℚ) * 2 ^ 100 / 1)) * 2 ^ 100 ≤ 1 / 2 :=
  QMCLeafB.LedgerSnap.snap_error_total_budget (T := 100) (L := 2) (by norm_num)
    (by norm_num)

end QMCLeafB.LedgerSnap

/-- The log-scale precision at `T = 100`, `L = 2`, `δ = 1` is `Nat.clog 2 ⌈2·100·2^100⌉`, and the
run's accumulated snap error is still within `1/2`. -/
example : (100 : ℚ) / 2 ^ QMCLeafB.LedgerSnap.snapPrec 100 2 1 * 2 ^ 100 ≤ 1 / 2 :=
  QMCLeafB.LedgerSnap.snap_error_total_budget_log (T := 100) (L := 2) (by norm_num) (by norm_num)

/-- The log-scale precision is *bit*-sized: at `T = 100`, `L = 2`, `δ = 1` the budget is
`200·2^100 ≤ 2^108`, so the precision is at most `108` — while the value-level precision
`⌈200·2^100⌉` is astronomically larger. -/
example : QMCLeafB.LedgerSnap.snapPrec 100 2 1 ≤ 108 :=
  QMCLeafB.LedgerSnap.snap_precision_clog_le (T := 100) (L := 2) (δ := 1) (P := 108)
    (by norm_num) (by norm_num) (by norm_num)

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.LedgerSnap.snapAbs_abs_le
#print axioms QMCLeafB.LedgerSnap.snapAbs_error
#print axioms QMCLeafB.LedgerSnap.snapAbs_dyadic
#print axioms QMCLeafB.LedgerSnap.snapAbs_idem
#print axioms QMCLeafB.LedgerSnap.hasHeight_div_two_pow
#print axioms QMCLeafB.LedgerSnap.hasHeight_snapAbs
#print axioms QMCLeafB.LedgerSnap.snapIterate_value_height
#print axioms QMCLeafB.LedgerSnap.snapRound_value_height
#print axioms QMCLeafB.LedgerSnap.snap_encode_length
#print axioms QMCLeafB.LedgerSnap.state_encode_length
#print axioms QMCLeafB.LedgerSnap.round_charge
#print axioms QMCLeafB.LedgerSnap.round_charge_monomial
#print axioms QMCLeafB.LedgerSnap.run_charge_monomial
#print axioms QMCLeafB.LedgerSnap.err_le_of_step
#print axioms QMCLeafB.LedgerSnap.err_le_of_step_const
#print axioms QMCLeafB.LedgerSnap.snap_err_le
#print axioms QMCLeafB.LedgerSnap.snap_error_budget
#print axioms QMCLeafB.LedgerSnap.snap_precision_ceil
#print axioms QMCLeafB.LedgerSnap.snap_error_total_budget
#print axioms QMCLeafB.LedgerSnap.snap_precision_upper
#print axioms QMCLeafB.LedgerSnap.round_intermediate_heights
#print axioms QMCLeafB.LedgerSnap.value_exponent_iterate
#print axioms QMCLeafB.LedgerSnap.snap_height_with_value_growth
#print axioms QMCLeafB.LedgerSnap.matValueBounded_iterate
#print axioms QMCLeafB.LedgerSnap.snapRound_closed_form
#print axioms QMCLeafB.LedgerSnap.le_num_natAbs
#print axioms QMCLeafB.LedgerSnap.snap_precision_log
#print axioms QMCLeafB.LedgerSnap.snap_error_total_budget_log
#print axioms QMCLeafB.LedgerSnap.snap_precision_clog_le
#print axioms QMCLeafB.LedgerSnap.hasHeight_snapAbs_of_budget
#print axioms QMCLeafB.LedgerSnap.value_exponent_iterate_rate
#print axioms QMCLeafB.LedgerSnap.hasHeight_snapIterate_value_growth
#print axioms QMCLeafB.LedgerSnap.snap_run_ledger


