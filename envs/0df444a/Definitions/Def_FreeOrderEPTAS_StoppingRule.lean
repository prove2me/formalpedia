-- Prove2me | Definitions.Def_FreeOrderEPTAS_StoppingRule
-- name    : FreeOrderEPTAS_StoppingRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:34.744475+00:00
-- url     : https://prove2.me/theorems/02c53c91-d4e9-430b-a3c0-f73bdfb464a2
-- title:
--   Stopping rules and their reward
-- statement:
--   Fix a permutation $\sigma$. A **stopping rule** decides at each time $t$, measurably in the values $X_{\sigma(1)},\dots,X_{\sigma(t)}$ observed so far, whether to stop. Its **reward** is $X_{\sigma(\tau)}$ at the first time $\tau$ at which it stops, and $0$ if it never stops; this is the $0$ in $V^*_n=\mathbb E[\max\{X_{\sigma^*(n)},0\}]$.
--
--   This object makes the operational value $V(\sigma)$ precise.
--
--   **Formalization Note** Time is 0-based. `observed σ x t` is the vector of the first $t+1$ values.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §3.1, p.16; the term $0$ of $V^*_n$, p.17

import Mathlib

namespace FreeOrderEPTAS

/-- A stopping rule on a permutation (arXiv:2007.13121v3, §3.1, p.16): at each time `t` (0-based)
a measurable decision depending on the `t + 1` values observed so far. -/
structure StoppingRule (n : ℕ) where
  /-- Stop at time `t`, given the first `t + 1` observed values? -/
  stop : (t : Fin n) → (Fin (t.val + 1) → ℝ) → Bool
  /-- Each decision is measurable. -/
  measurable_stop : ∀ t, Measurable (stop t)

/-- The values observed up to time `t` when the variables are inspected in the order `σ`:
`X_{σ(0)}, …, X_{σ(t)}` (0-based). -/
def observed {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (t : Fin n) :
    Fin (t.val + 1) → ℝ :=
  fun s => x (σ ⟨s.val, by omega⟩)

/-- The first time at which the rule stops, if any. -/
def stopTime {n : ℕ} (τ : StoppingRule n) (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    Option (Fin n) :=
  (List.finRange n).find? (fun t => τ.stop t (observed σ x t))

/-- The reward `X_{σ(τ)}`, and `0` if the rule never stops (the `0` in
`V*_n = E[max{X_{σ*(n)}, 0}]`, p.17). -/
def reward {n : ℕ} (τ : StoppingRule n) (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : ℝ :=
  match stopTime τ σ x with
  | some t => x (σ t)
  | none => 0

end FreeOrderEPTAS


