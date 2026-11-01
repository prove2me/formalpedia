-- Prove2me | Definitions.Def_RobustMultiStop_doob
-- name    : RobustMultiStop_doob
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:55.137985+00:00
-- url     : https://prove2.me/theorems/285e37ce-f4a3-48e2-9d54-1058853716da
-- title:
--   The $\rho$-Doob martingale $M^{*}$ of a process: $M_{r+1}-M_r=V_{r+1}-\rho_r(V_{r+1})$
-- statement:
--   For a process $V$ and a last date $n$, the **$\rho$-Doob martingale** $M=M^{*}$ of $V$ is defined by $M_0=0$ and
--
--   $$M_{r+1}-M_r=\begin{cases}V_{r+1}-\rho_r(V_{r+1}), & r<n,\\ 0, & r\ge n.\end{cases}$$
--
--   For $V=Y^{*}$ this is the martingale part of the $\rho$-Doob decomposition (2.4)–(2.5); for $V=Y^{*,l}$ with $n=N+1-l$ it is the martingale $M^{*,l}$ of (3.4), which is the optimal dual martingale in Theorem 3.1.
--
--   **Formalization Note** $Y^{*,l}$ is defined on the dates $r$ with $r+l\le N+1$, so $M^{*,l}$ follows (3.4) for $r+l\le N$ and stays constant afterwards.
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, (2.5), p.6, and (3.4), p.8

import Mathlib

open MeasureTheory

namespace RobustMultiStop

/-- The `ρ`-Doob martingale of a process `V` on the dates `0, …, n`, Laeven, Schoenmakers,
Schweizer & Stadje, *Robust Multiple Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2,
(2.5), p.6, and (3.4), p.8: `M_0 = 0` and

`M_{r+1} − M_r = V_{r+1} − ρ_r(V_{r+1})` for `r < n`, `M_{r+1} = M_r` for `r ≥ n`.

**Formalization Note** With `V = Y^{*,l}`, which is defined on the dates `r` with `r + l ≤ N + 1`,
the paper's `M^{*,l}` is `doob ρ (Y l) (N + 1 - l)`: its increments are (3.4) for `r + l ≤ N`, and
after the last date on which `l` rights still fit it stays constant. -/
def doob {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ)) (V : ℕ → Ω →ₘ[P] ℝ) (n : ℕ) : ℕ → Ω →ₘ[P] ℝ
  | 0 => 0
  | r + 1 => if r < n then doob ρ V n r + V (r + 1) - ρ r (V (r + 1)) else doob ρ V n r

end RobustMultiStop


