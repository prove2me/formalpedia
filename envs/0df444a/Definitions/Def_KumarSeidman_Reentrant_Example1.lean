-- Prove2me | Definitions.Def_KumarSeidman_Reentrant_Example1
-- name    : KumarSeidman_Reentrant_Example1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:14:24.66955+00:00
-- url     : https://prove2.me/theorems/1a6fa0f3-b35e-4d12-9c28-c1f2b6bd2e3b
-- title:
--   Example 1, pp. 291–292 — the re-entrant line 1 → 2 → 2 → 1, its initial state (ξ, 0, 0, 0), and the constants λ, α, β
-- statement:
--   The system of **Example 1** (Fig. 1): a single part type, arriving at rate $d = 1$ part per time unit, first visits machine 1, then machine 2, then machine 2 again, and finally machine 1 again. The successive buffers are denoted $1, 2, 3, 4$, so
--   $$B_1 = \{1, 4\}, \qquad B_2 = \{2, 3\}.$$
--   The processing times at the buffers are $\tau_1, \tau_2, \tau_3, \tau_4 > 0$. The time for setting up *to* buffer $k$ at its machine is $\delta_k \ge 0$; that is, $\delta_{4,1} = \delta_1$, $\delta_{1,4} = \delta_4$, $\delta_{3,2} = \delta_2$, $\delta_{2,3} = \delta_3$.
--
--   The **initial state** of both cases of the example is
--   $$x(0) = (x_1(0), x_2(0), x_3(0), x_4(0)) = (\xi, 0, 0, 0),$$
--   with machine 1 set up for buffer 4 and machine 2 set up for buffer 3.
--
--   The constants of p. 292 are
--   $$\lambda := \frac{\tau_4}{1-\tau_2}, \qquad \alpha := \frac{(\tau_4+1)(\delta_1+\delta_2)}{1-\tau_2} + \delta_3(\tau_4+1) + \delta_4, \qquad \beta := \frac{\tau_4(\delta_1+\delta_2)}{1-\tau_2} + \tau_4\delta_3 + \delta_4.$$
--
--   **Formalization Note** Paper buffer $k$ is Lean `ex1Buf (k-1)`, paper machine $m$ is Lean machine $m-1$, and $\tau_k$, $\delta_k$ are `τ (k-1)`, `δ (k-1)`. The set-up time between distinct buffers depends only on the target; between buffers at different machines it is never used. The constants are defined for every $\tau$, but every statement using them assumes $\tau_2 < 1$ (implied by (3)–(5)), so the division by $1 - \tau_2$ is never at a junk value.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 291, §III Example 1 (system, Fig. 1, Case 1 initial state); p. 292 (λ, α, β; Case 2 initial state)

import Mathlib
import Definitions.Def_KumarSeidman_Reentrant_System
import Definitions.Def_KumarSeidman_Reentrant_Trajectory

namespace KumarSeidman.Reentrant

/-- The buffer type of Example 1: one part type with a route of length `4`. -/
abbrev Ex1Buffer : Type := Buffer 1 (fun _ => 4)

/-- Buffer `k + 1` of Example 1 (paper numbering `1, 2, 3, 4`; Lean index `k = 0, 1, 2, 3`). -/
def ex1Buf (k : Fin 4) : Ex1Buffer := ⟨0, k⟩

/-- The system of Example 1 (p. 291, Fig. 1). A single part type, with input rate `d = 1`,
visits machine 1, machine 2, machine 2 again and machine 1 again; its successive buffers are
`1, 2, 3, 4`, so `B_1 = {1, 4}` and `B_2 = {2, 3}` (Lean machines `0` and `1`). The processing
time at buffer `k + 1` is `τ k`, and `δ k` is the time for setting up *to* buffer `k + 1`:
`δ_{b, b'} = δ_{b'}` for `b ≠ b'`, and no set-up for staying on the same buffer. -/
def ex1 (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k) (δ : Fin 4 → ℝ) (hδ : ∀ k, 0 ≤ δ k) :
    System 1 2 (fun _ => 4) where
  n_pos _ := by norm_num
  route b := ![0, 1, 1, 0] b.2
  d _ := 1
  d_pos _ := one_pos
  τ b := τ b.2
  τ_pos b := hτ b.2
  δ b b' := if b = b' then 0 else δ b'.2
  δ_nonneg b b' := by
    by_cases h : b = b'
    · simp [h]
    · simp [h, hδ b'.2]
  δ_self b := by simp

/-- The initial state of Example 1 (Case 1, p. 291; Case 2, p. 292):
`x(0) = (ξ, 0, 0, 0)`, machine 1 set up for buffer 4 and machine 2 set up for buffer 3. -/
def Ex1Initial {S : System 1 2 (fun _ => 4)} (T : Trajectory S) (ξ : ℝ) : Prop :=
  T.x (ex1Buf 0) 0 = ξ ∧ T.x (ex1Buf 1) 0 = 0 ∧ T.x (ex1Buf 2) 0 = 0 ∧ T.x (ex1Buf 3) 0 = 0 ∧
  T.β 0 0 = ex1Buf 3 ∧ T.β 1 0 = ex1Buf 2

/-- `λ := τ₄ / (1 - τ₂)` (p. 292). -/
noncomputable def ex1Lambda (τ : Fin 4 → ℝ) : ℝ := τ 3 / (1 - τ 1)

/-- `α := (τ₄ + 1)(δ₁ + δ₂)/(1 - τ₂) + δ₃(τ₄ + 1) + δ₄` (p. 292). -/
noncomputable def ex1Alpha (τ δ : Fin 4 → ℝ) : ℝ :=
  (τ 3 + 1) * (δ 0 + δ 1) / (1 - τ 1) + δ 2 * (τ 3 + 1) + δ 3

/-- `β := τ₄(δ₁ + δ₂)/(1 - τ₂) + τ₄δ₃ + δ₄` (p. 292). -/
noncomputable def ex1Beta (τ δ : Fin 4 → ℝ) : ℝ :=
  τ 3 * (δ 0 + δ 1) / (1 - τ 1) + τ 3 * δ 2 + δ 3

end KumarSeidman.Reentrant


