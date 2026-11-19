-- Prove2me | Definitions.Def_a166944_window_core
-- name    : a166944_window_core
-- status  : Definition
-- author  : @tara_sooo
-- created : 2026-11-19T00:20:47.183461+00:00
-- url     : https://prove2.me/theorems/23d234de-ec78-431a-b5e0-0c52e3364d19
-- title:
--   OEIS A166944 - the quiet-window condition without division atoms
-- statement:
--   At a terminal state of a capped canonical replay of the OEIS A166944 recurrence, the quiet-window condition
--
--   $$
--   2q < C_f - s_f \qquad\text{for every } q \text{ with } q^2 \le C_f + 1
--   $$
--
--   is what lets the terminal horizon be read off the arithmetic of the twin factors. It is used to conclude $2\sqrt{C_f+1} < C_f - s_f$, the input to the factor certificates at the next record.
--
--   The window follows from two inequalities on the replay: the index cap $4s \le 7M-1$ and the horizon cap $C \le 3M+4$, together with $2M-2 \le C$ and $M \ge 968$. The content of this bundle is that the conclusion does not need the square root at all; it holds for an arbitrary integer $q$ carrying only $q^2 \le C+1$, so that the argument is available in environments whose library has no integer square root.
--
--   The mechanism is a division-free bound. From $q^2 \le C+1 \le 3M+5$ one gets $8q+7 < M$, and the index cap then gives the window by linear arithmetic alone. The quadratic intermediate estimate is discharged by sandwiching $(M-7)^2$ between $200(M-7)$ and the linear form $192M+320$, which stays inside linear arithmetic.
--
--   **Formalization Note** Everything here is core Lean: no Mathlib import, no `ring`, no `norm_num`, no division tactic. The helper `mul64` bridges the products `(8q)(8q)` and `64(q*q)` that `omega` treats as separate atoms, and `sq_sub_seven` is the quadratic estimate stated in a form linear arithmetic can consume.
-- source:
--   Derived within this development from TwoCapGate.b_tight, which proves the same window with q fixed to isqrt (C+1); see A166944/WindowCore.lean at https://github.com/tara-sooo/A166944-Lean

/-!
# The quiet-window condition, proved without division tactics

`TwoCapGate.b_tight` proves `2 * isqrt (C+1) < C - s` from `4*s <= 7*M-1` and
`C <= 3*M+4`, but its final `omega` mixes a division atom `M/8` with products and
succeeds only because `q` is fixed to `isqrt (C+1)`. Replacing cap (A) by the
quadratic form `C+1 < (M/8)*(M/8)` -- which the quiet branch never needed --
made `omega` fail (`TwoCapGate`, "NOTE (E13c)").

This module removes the division entirely. The two facts the proof actually uses
are isolated as `eight_q_add_seven`, whose proof is linear arithmetic plus one
product monotonicity, and the window follows for any `q`.

Everything here is core-only: no Mathlib, no `ring`, no `norm_num`.
-/

namespace A166944Research

theorem sq_sub_seven (M : Nat) (h : 968 ≤ M) :
    192 * M + 320 < (M - 7) * (M - 7) := by
  have h7 : 7 ≤ M := by omega
  have h200 : 200 ≤ M - 7 := by omega
  have hmul : 200 * (M - 7) ≤ (M - 7) * (M - 7) := by
    rw [Nat.mul_comm 200 (M - 7)]
    exact Nat.mul_le_mul_left (M - 7) h200
  have hlin : 192 * M + 320 < 200 * (M - 7) := by omega
  omega

theorem mul64 (q : Nat) : (8 * q) * (8 * q) = 64 * (q * q) := by
  have h1 : (8 * q) * (8 * q) = 8 * (q * (8 * q)) := by rw [Nat.mul_assoc]
  have h2 : q * (8 * q) = 8 * (q * q) := by
    rw [Nat.mul_comm q (8 * q), Nat.mul_assoc 8 q q]
  rw [h1, h2, ← Nat.mul_assoc, Nat.mul_assoc]

theorem mul64c (M : Nat) : 64 * (3 * M + 5) = 192 * M + 320 := by omega

/-- **The sharp form the window needs.**  Any `q` with `q*q <= C+1`, under
`C <= 3*M+4` and `M >= 968`, satisfies `8*q + 7 < M`.  This is the division-free
surrogate for `q < M/8`, and it is what `omega` can consume. -/
theorem eight_q_add_seven (M C q : Nat) (hM : 968 ≤ M) (hhi : C ≤ 3 * M + 4)
    (hq : q * q ≤ C + 1) : 8 * q + 7 < M := by
  by_cases h : 8 * q + 7 < M
  · exact h
  · have hM7 : M - 7 ≤ 8 * q := by omega
    have hsq : (M - 7) * (M - 7) ≤ (8 * q) * (8 * q) := Nat.mul_le_mul hM7 hM7
    rw [mul64] at hsq
    have hup : 64 * (q * q) ≤ 64 * (C + 1) := Nat.mul_le_mul_left 64 hq
    have hC1 : C + 1 ≤ 3 * M + 5 := by omega
    have h64b : 64 * (C + 1) ≤ 64 * (3 * M + 5) := Nat.mul_le_mul_left 64 hC1
    rw [mul64c] at h64b
    have hbig := sq_sub_seven M hM
    omega

/-- **The quiet-window condition, division-free.**  With the index cap
`4*s <= 7*M-1` and the horizon cap `C <= 3*M+4`, every `q` with `q*q <= C+1`
satisfies `2*q < C - s`.  Taking `q = isqrt (C+1)` recovers
`TwoCapGate.b_tight` without any division atom. -/
theorem window_condition (M s C q : Nat) (hM : 968 ≤ M)
    (h : 4 * s ≤ 7 * M - 1) (hlo : 2 * M - 2 ≤ C)
    (hhi : C ≤ 3 * M + 4) (hq : q * q ≤ C + 1) :
    2 * q < C - s := by
  have hq8 := eight_q_add_seven M C q hM hhi hq
  omega

end A166944Research


