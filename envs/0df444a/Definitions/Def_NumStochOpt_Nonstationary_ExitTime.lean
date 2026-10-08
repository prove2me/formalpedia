-- Prove2me | Definitions.Def_NumStochOpt_Nonstationary_ExitTime
-- name    : NumStochOpt_Nonstationary_ExitTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T05:32:20.832514+00:00
-- url     : https://prove2.me/theorems/6b6ac26a-a1e1-4cf2-b588-c683df91d2c3
-- title:
--   The exit time $\tau = \min\{s \ge s_0 : \|x^s - x^{s_0}\| > \varepsilon\}$
-- statement:
--   Let $(x^s)_{s \ge 0}$ be a sequence in $\mathbb R^n$, $s_0 \in \mathbb N$ and $\varepsilon \in \mathbb R$. The **exit time** of the sequence from the closed $\varepsilon$-ball around $x^{s_0}$ is
--   $$
--   \tau = \min\{s \in \mathbb N : s \ge s_0,\ \|x^s - x^{s_0}\| > \varepsilon\},
--   $$
--   the first index from $s_0$ on at which the sequence is farther than $\varepsilon$ from $x^{s_0}$.
--
--   In Theorem 6.4 the exit times $\tau_k$ taken from the indices $s_k$ of a subsequence measure whether the sequence leaves a neighbourhood of a limit point, and with which value of a Lyapunov function it leaves.
--
--   **Formalization Note** The book prints the set as $\{s \mid s \ge s_k, \|x^{s_k} - x^s\| < \varepsilon\}$; the proof of Theorem 6.3 (pp. 155–156) shows that the exit condition $\|x^s - x^{s_k}\| > \varepsilon$ is meant, and that is the reading used. Lean's minimum of an empty set of natural numbers is $0$; Theorem 6.4 evaluates $\tau$ only where the set is nonempty.
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 155, Theorem 6.4 (2)(b); reading from the proof of Theorem 6.3, p. 156

import Mathlib

namespace NumStochOpt.Nonstationary

/-- The exit time `τ = min {s | s ≥ s₀, ‖x^s - x^{s₀}‖ > ε}` of a sequence `x` from the closed
`ε`-ball around `x^{s₀}` (Theorem 6.4 (2)(b), p. 155, in the reading fixed by the proof of
Theorem 6.3, p. 156). When the sequence never leaves the ball the set is empty and the value is
the junk value `0`; Theorem 6.4 only evaluates it where the set is nonempty. -/
noncomputable def exitTime {n : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin n)) (s₀ : ℕ) (ε : ℝ) : ℕ :=
  sInf {s : ℕ | s₀ ≤ s ∧ ε < ‖x s - x s₀‖}

end NumStochOpt.Nonstationary


