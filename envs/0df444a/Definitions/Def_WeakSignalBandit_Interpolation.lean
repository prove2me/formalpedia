-- Prove2me | Definitions.Def_WeakSignalBandit_Interpolation
-- name    : WeakSignalBandit_Interpolation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:29.946672+00:00
-- url     : https://prove2.me/theorems/99c7ca47-1cdf-4e1c-9c5a-c208d695cc5b
-- title:
--   Piecewise-linear interpolation $\bar Z^n_t=(1-tn+\lfloor tn\rfloor)Z^n_{\lfloor tn\rfloor}+(tn-\lfloor tn\rfloor)Z^n_{\lfloor tn\rfloor+1}$
-- statement:
--   For a sequence $(Z_i)_{i\in\mathbb N}$ in a normed space and $n\in\mathbb N$, the interpolated path on the time scale $i/n$ is
--   $$\bar Z^n_t=(1-tn+\lfloor tn\rfloor)\,Z_{\lfloor tn\rfloor}+(tn-\lfloor tn\rfloor)\,Z_{\lfloor tn\rfloor+1},\qquad t\in[0,1].$$
--   It is the continuous, piecewise-linear path through the points $(i/n, Z_i)$, $i=0,1,\dots,n$, and is an element of $C([0,1],\cdot)$.
--
--   The paper uses it to turn the scaled state of a sequential experiment (3.2), and the Markov chains of the Stroock–Varadhan theorem (A.5), into random elements of the path space $\mathcal C$.
--
--   **Formalization Note** The path is built as a finite sum of hat functions $\sum_{m\le n+1}\max(0,1-|tn-m|)\,Z_m$, which is visibly continuous; the module proves that its value at every $t\in[0,1]$ equals the printed formula.
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, (3.2) p.12; (A.5) p.31

import Mathlib

namespace WeakSignalBandit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The piecewise-linear interpolation of a sequence `(z_i)_{i ∈ ℕ}` at real time `t`, on the time
scale `i/n`, exactly as printed:
`Z̄^n_t = (1 − tn + ⌊tn⌋) Z^n_{⌊tn⌋} + (tn − ⌊tn⌋) Z^n_{⌊tn⌋+1}`.
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, (3.2) p.12 and (A.5) p.31.

**Formalization Note** `⌊tn⌋` is the natural-number floor (only `t ≥ 0` is used). -/
noncomputable def interpFormula (n : ℕ) (z : ℕ → E) (t : ℝ) : E :=
  (1 - t * n + ⌊t * n⌋₊) • z ⌊t * n⌋₊ + (t * n - ⌊t * n⌋₊) • z (⌊t * n⌋₊ + 1)

/-- The hat function `max(0, 1 − |x|)`. -/
noncomputable def hat (x : ℝ) : ℝ := max 0 (1 - |x|)

/-- The same interpolation written as a finite sum of hat functions, which is visibly continuous. -/
noncomputable def interpHat (n : ℕ) (z : ℕ → E) (t : ℝ) : E :=
  ∑ m ∈ Finset.range (n + 2), hat (t * n - m) • z m

lemma hat_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ |x|) : hat x = 0 := by
  unfold hat; exact max_eq_left (by linarith)

lemma interpHat_eq_interpFormula (n : ℕ) (z : ℕ → E) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    interpHat n z t = interpFormula n z t := by
  set x : ℝ := t * n with hx
  have hx0 : 0 ≤ x := mul_nonneg ht0 (Nat.cast_nonneg n)
  have hxn : x ≤ n := by
    have := mul_le_mul_of_nonneg_right ht1 (Nat.cast_nonneg (α := ℝ) n); simpa [hx] using this
  set k : ℕ := ⌊x⌋₊ with hk
  have hkx : (k : ℝ) ≤ x := Nat.floor_le hx0
  have hxk : x < k + 1 := Nat.lt_floor_add_one x
  have hkn : k ≤ n := by
    have : (k : ℝ) ≤ n := le_trans hkx hxn
    exact_mod_cast this
  unfold interpHat interpFormula
  rw [← hx, ← hk]
  rw [Finset.sum_eq_add_of_mem k (k + 1) (by simp; omega) (by simp; omega) (by omega)]
  · congr 1
    · congr 1
      unfold hat
      rw [abs_of_nonneg (show (0 : ℝ) ≤ x - k by linarith)]
      rw [max_eq_right (show (0 : ℝ) ≤ 1 - (x - k) by linarith)]
      ring
    · congr 1
      unfold hat
      push_cast
      rw [abs_of_neg (by linarith)]
      rw [max_eq_right (by linarith)]
      ring
  · intro c _ hc
    rw [hat_eq_zero_of_one_le, zero_smul]
    rcases lt_or_gt_of_ne hc.1 with h | h
    · have : (c : ℝ) + 1 ≤ k := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
    · have h2 : k + 1 < c := lt_of_le_of_ne h hc.2.symm
      have : (k : ℝ) + 2 ≤ c := by exact_mod_cast h2
      rw [abs_of_neg (by linarith)]; linarith

lemma continuous_interpHat (n : ℕ) (z : ℕ → E) : Continuous (interpHat n z) := by
  unfold interpHat hat
  fun_prop

/-- The interpolated path `t ↦ Z̄^n_t`, `t ∈ [0,1]`, as an element of `C([0,1], E)`.
Kuang, Wager, arXiv:2101.09855v7, (3.2) p.12 and (A.5) p.31; `interpPath_apply` shows that its
value at `t` is the printed formula `interpFormula`. -/
noncomputable def interpPath (n : ℕ) (z : ℕ → E) : C(unitInterval, E) :=
  ⟨fun t => interpHat n z t, (continuous_interpHat n z).comp continuous_subtype_val⟩

lemma interpPath_apply (n : ℕ) (z : ℕ → E) (t : unitInterval) :
    interpPath n z t = interpFormula n z t :=
  interpHat_eq_interpFormula n z t.2.1 t.2.2

end WeakSignalBandit


