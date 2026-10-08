-- Prove2me | Definitions.Def_SuttonTD_Convergence_PerSequenceChanges
-- name    : SuttonTD_Convergence_PerSequenceChanges
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:06:35.294629+00:00
-- url     : https://prove2.me/theorems/59fc6d15-1e87-4766-a8a6-7bd9bb73d007
-- title:
--   Per-sequence weight changes of Widrow–Hoff and linear TD(1)
-- statement:
--   Let $x_1,\dots,x_m\in\mathbb R^K$ be the observation vectors of one sequence, $z$ its outcome, $w$ a weight vector held fixed during the sequence and $\alpha$ a step size. The **Widrow–Hoff** per-sequence weight change is
--
--   $$\sum_{t=1}^m\alpha\,(z-w^\top x_t)\,x_t .$$
--
--   With linear predictions $P_t=w^\top x_t$ ($t\le m$) and $P_{m+1}=z$, the **linear TD(1)** per-sequence weight change, from rule (3), is
--
--   $$\sum_{t=1}^m\alpha\,(P_{t+1}-P_t)\sum_{k=1}^t x_k .$$
--
--   These are the two procedures compared in Theorem 1.
--
--   **Formalization Note** Time is indexed from $0$: `xs t` for $t<m$ is the paper's $x_{t+1}$ and `linearPrediction … t` is $P_{t+1}$.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §2.2, pp. 14–15 (PDF pp. 6–7), (3)

import Mathlib

namespace SuttonTD.Convergence

variable {K : ℕ}

/-- The per-sequence weight change of the **Widrow–Hoff** procedure (Sutton 1988, §2.2, p. 14,
PDF p. 6): for observation vectors `x_1, …, x_m`, outcome `z`, a weight vector `w` held fixed
during the sequence and step size `α`, `∑_{t=1}^m α (z − wᵀx_t) x_t`.

Formalization Note: time is indexed from `0`, so `xs t` for `t < m` is the paper's `x_{t+1}`. -/
def widrowHoffChange (m : ℕ) (xs : ℕ → Fin K → ℝ) (z α : ℝ) (w : Fin K → ℝ) : Fin K → ℝ :=
  ∑ t ∈ Finset.range m, (α * (z - w ⬝ᵥ xs t)) • xs t

/-- The linear prediction sequence of §2.2 (p. 15): `P_t = wᵀx_t` for the `m` observations and
`P_{m+1} = z` (pp. 14–15), indexed from `0` (`linearPrediction … t` is the paper's `P_{t+1}`). -/
def linearPrediction (m : ℕ) (xs : ℕ → Fin K → ℝ) (z : ℝ) (w : Fin K → ℝ) (t : ℕ) : ℝ :=
  if t < m then w ⬝ᵥ xs t else z

/-- The per-sequence weight change of the **linear TD(1)** procedure (3) (§2.2, p. 15):
`∑_{t=1}^m α (P_{t+1} − P_t) ∑_{k=1}^t ∇_w P_k`, with `∇_w P_k = x_k` for linear predictions. -/
def tdOneChange (m : ℕ) (xs : ℕ → Fin K → ℝ) (z α : ℝ) (w : Fin K → ℝ) : Fin K → ℝ :=
  ∑ t ∈ Finset.range m,
    (α * (linearPrediction m xs z w (t + 1) - linearPrediction m xs z w t)) •
      ∑ k ∈ Finset.range (t + 1), xs k

end SuttonTD.Convergence


