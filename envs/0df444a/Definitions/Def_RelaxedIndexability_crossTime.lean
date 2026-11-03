-- Prove2me | Definitions.Def_RelaxedIndexability_crossTime
-- name    : RelaxedIndexability_crossTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:28.319126+00:00
-- url     : https://prove2.me/theorems/7dcbda94-2a43-4e1b-a658-0245cd5aad75
-- title:
--   First-crossing time $L(\omega_1, \omega)$ of the linear threshold (34)
-- statement:
--   Fix an arm with transition matrix $\mathbf P$ and reward vector $B$, and a belief $\omega$ as a point in the threshold. For a belief $\omega_1$, write $\mathcal T^k(\omega_1) = \omega_1 \mathbf P^k$ for the belief after $k$ passive steps. The **first-crossing time** is
--   $$
--   L(\omega_1, \omega) = \min\{k \ge 0 : \mathcal T^k(\omega_1) B' > \omega B'\},
--   $$
--   and $L(\omega_1, \omega) = +\infty$ if $\mathcal T^k(\omega_1) B' \le \omega B'$ for all $k \ge 0$.
--
--   It is the number of slots the threshold policy with threshold $\omega$ stays passive when started at $\omega_1$. Note $L(\omega,\omega) \ge 1$, since the crossing is strict.
--
--   **Formalization Note** The threshold $\omega$ is the third argument and the starting belief $\omega_1$ the fourth; $+\infty$ is `⊤ : ℕ∞`. The crossing is strict and $k$ starts at $0$.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, (34), p.20

import Mathlib

open Matrix

namespace RelaxedIndexability

variable {K : ℕ}

/-- **First-crossing time** (Liu, arXiv:2107.11939v4, (34), p.20): with `ω` fixed as the threshold,
`crossTime P B ω x = L(x, ω) = min {k ≥ 0 : T^k(x) B′ > ω B′}` where `T^k(x) = x P^k`, and
`L(x, ω) = +∞` if `T^k(x) B′ ≤ ω B′` for all `k ≥ 0`.

**Formalization Note.** The threshold `ω` is the third argument and the starting belief `x` the
fourth (the paper writes `L(x, ω)`). The crossing is strict and `k` starts at `0`; `+∞` is `⊤ : ℕ∞`. -/
noncomputable def crossTime (P : Matrix (Fin K) (Fin K) ℝ) (B ω x : Fin K → ℝ) : ℕ∞ := by
  classical
  exact if h : ∃ k : ℕ, ω ⬝ᵥ B < (x ᵥ* P ^ k) ⬝ᵥ B then ((Nat.find h : ℕ) : ℕ∞) else ⊤

end RelaxedIndexability


