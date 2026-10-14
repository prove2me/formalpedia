-- Prove2me | solution 1 for Apery.Eout_expand
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T16:13:02.537103+00:00
-- url     : https://prove2.me/submissions/020d56f4-aed5-450a-90d2-5bae41d93bf6

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The expansion of the outer profile (source `Apery/Growth/TableGen.lean`)

This file proves the platform theorem `Apery.Eout_expand`:

$$E_{\mathrm{out}}(x) = -2\lambda x q + \Bigl(2\mu\lambda x - \frac{\mu(\mu+1)}{2}\Bigr)
- 2\sum_{i,j} G_{ij}(q)\,c_{ij}(x - q,\ \alpha x - q') + \max\Bigl(0, \frac{13}{10}x - 2\Bigr)$$

on every window $q \le x < q+1$, $q' \le \alpha x < q'+1$, $\mu \le 2\lambda x < \mu + 1$
(with $\lambda = 37/40$, $\alpha = 3/40$), together with the closed form
$2J(u) = 2u^2 - u + \{2u\}(1-\{2u\})/2$, the class-function identity `psiR_eq` and the nine
continuous interval counts $c_{ij}$ (`cc00`..`cc22`). A faithful port of the pinned source
project mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, module
`Apery/Growth/TableGen.lean`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

set_option autoImplicit false

section Port0
/-!
# The table expansion lemmas (source `Apery/Growth/TableGen.lean`)

This file proves the platform theorem `Apery.Eout_expand`, the expansion of the continuous
outer profile on a window `[q, q+1) × [q', q'+1)` of the (floor, floor(3x/40), floor(74x/40))
coordinates, together with the inner expansion `Ein_expand`, the closed form `two_Jc_lin` of
the tridiagonal sum, the class-function identity `psiR_eq` and the continuous interval counts
`cc00`..`cc22`. A faithful port of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
module `Apery/Growth/TableGen.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open Finset

namespace Apery

/-! ## Elementary helpers (`Apery/Growth/TailPrime.lean`) -/

/-! ## Elementary helpers (`Apery/Growth/TailPrime.lean`) -/

lemma sum_range_tri (t : ℚ) (L : ℕ) :
    ∑ i ∈ range L, ((t - 2 * i) / 2) = (L : ℚ) * (t - L + 1) / 2 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma two_Jc_eq {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 500) :
    2 * Jc u = 2 * u ^ 2 - u + Int.fract (2 * u) * (1 - Int.fract (2 * u)) / 2 := by
  set μ := ⌊2 * u⌋₊ with hμ
  have hμ1 : (μ : ℝ) ≤ 2 * u := Nat.floor_le (by linarith)
  have hμ2 : 2 * u < μ + 1 := Nat.lt_floor_add_one _
  have hμ1000 : μ ≤ 1000 := by
    have : (μ : ℝ) ≤ 1000 := by linarith
    exact_mod_cast this
  have hfr : Int.fract (2 * u) = 2 * u - μ := by
    rw [Int.fract, show ⌊2 * u⌋ = (μ : ℤ) by
      rw [hμ, ← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by linarith))]]
    push_cast; ring
  have hsplit : Jc u = ∑ j ∈ (Icc 1 μ : Finset ℕ), (u - (j : ℝ) / 2) := by
    unfold Jc
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hμ1000) (fun j hj hjn => by
      simp only [Finset.mem_Icc, not_and, not_le] at hj hjn
      have := hjn hj.1
      have : (μ : ℝ) + 1 ≤ j := by exact_mod_cast this
      exact max_eq_left (by linarith))]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := (Finset.mem_Icc.mp hj).2
    have : (j : ℝ) ≤ μ := by exact_mod_cast this
    exact max_eq_right (by linarith)
  have hclosed : ∑ j ∈ (Icc 1 μ : Finset ℕ), (u - (j : ℝ) / 2) = μ * u - (μ : ℝ) * (μ + 1) / 4 := by
    induction μ with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring
  rw [hsplit, hclosed, hfr]
  ring

/-! ## The table expansion lemmas (`Apery/Growth/TableGen.lean`) -/

/-!
# Helpers for the piece tables

On a piece where `⌊x⌋`, `⌊αx⌋`, `⌊2λx⌋` are constant, `Ê_in(x, k)` and `Ê_out(x)` are explicit
combinations of the interval counts `c_{ij}({x}, {αx})`; the counts have closed forms.
-/

open Finset


lemma nat_floor_of_bounds {x : ℝ} {q : ℕ} (h1 : (q : ℝ) ≤ x) (h2 : x < q + 1) : ⌊x⌋₊ = q := by
  rw [Nat.floor_eq_iff (by linarith)]; exact ⟨h1, h2⟩

lemma fract_of_bounds {x : ℝ} {q : ℕ} (h1 : (q : ℝ) ≤ x) (h2 : x < q + 1) : Int.fract x = x - q := by
  rw [Int.fract, show ⌊x⌋ = (q : ℤ) by rw [Int.floor_eq_iff]; push_cast; exact ⟨h1, h2⟩]
  push_cast; ring

lemma two_Jc_lin {u : ℝ} (μ : ℕ) (h1 : (μ : ℝ) ≤ 2 * u) (h2 : 2 * u < μ + 1) (hu : u ≤ 500) :
    2 * Jc u = 2 * μ * u - (μ : ℝ) * (μ + 1) / 2 := by
  have hu0 : 0 ≤ u := by have : (0 : ℝ) ≤ μ := by positivity
                         linarith
  have e := two_Jc_eq hu0 hu
  have hfr : Int.fract (2 * u) = 2 * u - μ := fract_of_bounds h1 h2
  rw [e, hfr]; ring

/-- `ψ` in closed form. -/
lemma psiR_eq (k β : ℤ) : psiR k β = (lrow k β : ℚ) * (((k - β : ℤ) : ℚ) - lrow k β + 1) / 2 := by
  unfold psiR
  rw [← sum_range_tri]
  refine Finset.sum_congr rfl fun i _ => ?_; push_cast; ring

/-! ### Closed forms of the interval counts -/

section
variable {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)

include hf0 hf1 hg0 hg1 in
lemma cc00 : ccount f g 0 0 = 1 / 2 := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc01 : ccount f g 0 1 = min g (1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc02 : ccount f g 0 2 = max 0 (g - 1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc10 : ccount f g 1 0 = min f (1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc20 : ccount f g 2 0 = max 0 (f - 1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc11 : ccount f g 1 1 = min (min f g) (1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc12 : ccount f g 1 2 = max 0 (min f (1 / 2) + g - 1) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc21 : ccount f g 2 1 = max 0 (min g (1 / 2) + f - 1) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc22 : ccount f g 2 2 = max 0 (min f g - 1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

end

/-- `Ê_in` on a piece. -/
lemma Ein_expand {x : ℝ} (k : ℤ) {q q' μ : ℕ} (hq1 : (q : ℝ) ≤ x) (hq2 : x < q + 1)
    (hr1 : (q' : ℝ) ≤ 3 / 40 * x) (hr2 : 3 / 40 * x < q' + 1)
    (hm1 : (μ : ℝ) ≤ 2 * (37 / 40 * x)) (hm2 : 2 * (37 / 40 * x) < μ + 1) (hx : x ≤ 400) :
    Ein x k = -2 * (37 / 40 * x) * q + 12 * (37 / 40 * x) * q' +
      (2 * μ * (37 / 40 * x) - (μ : ℝ) * (μ + 1) / 2) - 37 / 40 * x * k +
      2 * ∑ i, ∑ j, bIn q q' k i j * ccount (x - q) (3 / 40 * x - q') i j := by
  unfold Ein
  rw [nat_floor_of_bounds hq1 hq2, nat_floor_of_bounds hr1 hr2, fract_of_bounds hq1 hq2,
    fract_of_bounds hr1 hr2, two_Jc_lin μ hm1 hm2 (by linarith)]

/-- `Ê_out` on a piece. -/
lemma Eout_expand {x : ℝ} {q q' μ : ℕ} (hq1 : (q : ℝ) ≤ x) (hq2 : x < q + 1)
    (hr1 : (q' : ℝ) ≤ 3 / 40 * x) (hr2 : 3 / 40 * x < q' + 1)
    (hm1 : (μ : ℝ) ≤ 2 * (37 / 40 * x)) (hm2 : 2 * (37 / 40 * x) < μ + 1) (hx : x ≤ 400) :
    Eout x = -2 * (37 / 40 * x) * q + (2 * μ * (37 / 40 * x) - (μ : ℝ) * (μ + 1) / 2) -
      2 * ∑ i, ∑ j, bGO q i j * ccount (x - q) (3 / 40 * x - q') i j + max 0 (13 / 10 * x - 2) := by
  unfold Eout
  rw [nat_floor_of_bounds hq1 hq2, fract_of_bounds hq1 hq2, fract_of_bounds hr1 hr2,
    two_Jc_lin μ hm1 hm2 (by linarith)]

theorem toNat_cast_q (a : ℤ) : ((a.toNat : ℕ) : ℚ) = max (a : ℚ) 0 := by
  have := Int.toNat_eq_max a
  have h2 : (((a.toNat : ℕ) : ℤ) : ℚ) = ((max a 0 : ℤ) : ℚ) := by rw [this]
  push_cast at h2; exact h2


/-! ## The outer table (`Apery/Growth/OuterTable.lean`) -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

/-! Generated by `gen_lean_outer.py`: the table of `Ê_out` on `[20/37, 3]`. -/

end Apery

#check @Apery.Eout_expand
end Port0


open Finset in
/-- The platform target `Apery.Eout_expand`, restated at top level as `solution`. -/
theorem solution {x : ℝ} {q q' μ : ℕ} (hq1 : (q : ℝ) ≤ x) (hq2 : x < q + 1)
    (hr1 : (q' : ℝ) ≤ 3 / 40 * x) (hr2 : 3 / 40 * x < q' + 1)
    (hm1 : (μ : ℝ) ≤ 2 * (37 / 40 * x)) (hm2 : 2 * (37 / 40 * x) < μ + 1) (hx : x ≤ 400) :
    Apery.Eout x = -2 * (37 / 40 * x) * q + (2 * μ * (37 / 40 * x) - (μ : ℝ) * (μ + 1) / 2) -
      2 * ∑ i, ∑ j, Apery.bGO q i j * Apery.ccount (x - q) (3 / 40 * x - q') i j +
        max 0 (13 / 10 * x - 2) :=
  Apery.Eout_expand hq1 hq2 hr1 hr2 hm1 hm2 hx
