-- Prove2me | solution 1 for Apery.inner_integrals
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T17:47:39.113959+00:00
-- url     : https://prove2.me/submissions/4fae0af5-4846-496f-b7db-3ebd23808d1e

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The inner integrals (source `Apery/Growth/TableIntegrals.lean`)

This file proves the platform theorem `Apery.inner_integrals`:

$$\sum_{i<125}\int_{t_i}^{t_{i+1}} \frac{g_{\mathrm{in},i}(x)}{x^3}\,dx
= \frac{322437603634266857629}{7535670527041937280000},$$

the numerical evaluation of the 125-piece inner table, by the antiderivative
$\int (Ax+B)/x^3 = A(1/a - 1/b) + \frac{B}{2}(1/a^2 - 1/b^2)$. A faithful port of the
pinned source project mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, modules
`Apery/Growth/PieceIdx.lean`, `Apery/Growth/InnerSum.lean` and
`Apery/Growth/TableIntegrals.lean`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

set_option autoImplicit false

section Port0
/-!
# The inner integrals (`Apery/Growth/TableIntegrals.lean`)

This file proves the platform theorem `Apery.inner_integrals`:

`∑_{i<125} ∫_{tIn i}^{tIn (i+1)} gIn i x / x³ dx = 322437603634266857629 / 7535670527041937280000`,

the numerical evaluation of the 125-piece inner table. A faithful port of mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, modules `Apery/Growth/PieceIdx.lean`
(`grid_mono`), `Apery/Growth/InnerSum.lean` (`tIn_mono`) and
`Apery/Growth/TableIntegrals.lean` (`integral_lin_div_cube`, `tIn_pos`, `inner_integrals`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open Finset intervalIntegral

namespace Apery

lemma integral_lin_div_cube (A B : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, (A * x + B) / x ^ 3 = A * (1 / a - 1 / b) + B / 2 * (1 / a ^ 2 - 1 / b ^ 2) := by
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx; rcases Set.mem_uIcc.mp hx with h | h <;> linarith [h.1]
  have hb : 0 < b := by linarith
  rw [integral_eq_sub_of_hasDerivAt (f := fun x => -A / x - B / 2 / x ^ 2)]
  · field_simp; ring
  · intro x hx
    have hx0 := (hpos x hx).ne'
    have d1 := (hasDerivAt_const x (-A)).div (hasDerivAt_id x) hx0
    have d2 := (hasDerivAt_const x (B / 2)).div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx0)
    have := d1.sub d2
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx; exact pow_ne_zero 3 (hpos x hx).ne'

lemma grid_mono {t : ℕ → ℝ} {m : ℕ} (h : ∀ i < m, t i < t (i + 1)) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m) :
    t i ≤ t j := by
  induction j with
  | zero => have : i = 0 := by omega
            rw [this]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h1 | h1
    · exact (ih (by omega) (by omega)).trans (h j (by omega)).le
    · have : i = j + 1 := by omega
      rw [this]

theorem tIn_mono : ∀ i < 125, tIn i < tIn (i + 1) := by
  intro i hi
  interval_cases i <;> simp only [tIn, tInL, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num

lemma tIn_pos (i : ℕ) (hi : i ≤ 125) : 0 < tIn i := by
  have h0 : tIn 0 = 3 := by simp [tIn, tInL]
  have := grid_mono tIn_mono (Nat.zero_le i) hi
  linarith

set_option maxRecDepth 100000 in
theorem inner_integrals :
    ∑ i ∈ range 125, ∫ x in tIn i..tIn (i + 1), gIn i x / x ^ 3 =
      322437603634266857629 / 7535670527041937280000 := by
  rw [Finset.sum_congr rfl fun i hi => by
    have hi' := Finset.mem_range.mp hi
    exact integral_lin_div_cube _ _ (tIn_pos i hi'.le) (tIn_mono i hi').le]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tIn, tInL, aInL, bInL,
    List.getD_cons_succ, List.getD_cons_zero]
  norm_num

end Apery

#check @Apery.inner_integrals
end Port0


open Finset intervalIntegral in
/-- The platform target `Apery.inner_integrals`, restated at top level as `solution`. -/
theorem solution :
    ∑ i ∈ range 125, ∫ x in Apery.tIn i..Apery.tIn (i + 1), Apery.gIn i x / x ^ 3 =
      322437603634266857629 / 7535670527041937280000 :=
  Apery.inner_integrals
