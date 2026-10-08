-- Prove2me | Definitions.Def_TamedEuler_Convergence_Scheme
-- name    : TamedEuler_Convergence_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:45.155182+00:00
-- url     : https://prove2.me/theorems/84cef1ba-cde8-4ed2-b831-ed7d6658b4a7
-- title:
--   (8) and (10), pp. 4–5 — the tamed Euler scheme Y^N_n and its time-continuous interpolation Ȳ^N
-- statement:
--   Let $T>0$, $N\in\mathbb N$, $\mu:\mathbb R^d\to\mathbb R^d$, $\sigma:\mathbb R^d\to\mathbb R^{d\times m}$, $\xi:\Omega\to\mathbb R^d$ and $W:[0,\infty)\times\Omega\to\mathbb R^m$.
--
--   1. **Brownian increments** (p. 6): $\Delta W^N_k := W_{(k+1)T/N}-W_{kT/N}$.
--   2. **Tamed Euler scheme** (8), p. 4: $Y^N_0=\xi$ and
--   $$Y^N_{n+1}=Y^N_n+\frac{\tfrac TN\,\mu(Y^N_n)}{1+\tfrac TN\,\|\mu(Y^N_n)\|}+\sigma(Y^N_n)\,\Delta W^N_n .$$
--   Only the drift is tamed; the step size is $T/N$.
--   3. **Interpolation** (10), p. 5: for $t\in[nT/N,(n+1)T/N]$, $n\in\{0,\dots,N-1\}$,
--   $$\bar Y^N_t=Y^N_n+\frac{(t-nT/N)\,\mu(Y^N_n)}{1+\tfrac TN\,\|\mu(Y^N_n)\|}+\sigma(Y^N_n)\,(W_t-W_{nT/N}).$$
--
--   The scheme differs from the explicit Euler method only by a term of order $(T/N)^2$, yet it has bounded moments for superlinear drifts; $\bar Y^N$ is the process whose distance to the exact solution Theorem 1.1 bounds.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$. The recursion is defined for every $n$; every statement uses $n\le N$ and $N\ge1$. The cell index in (10) is $n=\min(\lfloor tN/T\rfloor,N-1)$: an interior grid point $t=nT/N$ takes the cell to its right (both formulas of (10) agree there by (8)), and $t=T$ takes the last cell $n=N-1$. $\bar Y^N_t$ is meaningful for $t\in[0,T]$.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 4, (8); p. 5, (10); p. 6 (ΔW^N_k)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_TamedEuler_Convergence_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TamedEuler.Convergence

open EthierKurtz

variable {d m : ℕ} {Ω : Type*}

/-- Hutzenthaler–Jentzen–Kloeden, p. 6: the Brownian increment
`ΔW^N_k := W_{(k+1)T/N} − W_{kT/N}` (used for `N ≥ 1`, `k ∈ {0, …, N − 1}`). -/
noncomputable def dW (T : ℝ≥0) (W : ℝ≥0 → Ω → SDEState m) (N k : ℕ) (ω : Ω) : SDEState m :=
  W (((k + 1 : ℕ) : ℝ≥0) * T / N) ω - W ((k : ℝ≥0) * T / N) ω

/-- Hutzenthaler–Jentzen–Kloeden, p. 4, (8): the tamed drift increment
`(T/N) µ(y) / (1 + (T/N) ‖µ(y)‖)`. Only the drift is tamed. -/
noncomputable def tamedDrift (T : ℝ≥0) (N : ℕ) (mu : SDEState d → SDEState d) (y : SDEState d) :
    SDEState d :=
  (((T : ℝ) / N) / (1 + ((T : ℝ) / N) * ‖mu y‖)) • mu y

/-- Hutzenthaler–Jentzen–Kloeden, p. 4, (8): the tamed Euler scheme `Y^N_0 = ξ`,
`Y^N_{n+1} = Y^N_n + (T/N) µ(Y^N_n) / (1 + (T/N) ‖µ(Y^N_n)‖) + σ(Y^N_n) ΔW^N_n`.
The recursion is defined for every `n`; the paper (and every statement of the mission) uses
`n ∈ {0, …, N}` and `N ≥ 1`. -/
noncomputable def Y (T : ℝ≥0) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ) (ξ : Ω → SDEState d)
    (W : ℝ≥0 → Ω → SDEState m) (N : ℕ) : ℕ → Ω → SDEState d
  | 0 => ξ
  | n + 1 => fun ω =>
      Y T mu σ ξ W N n ω + tamedDrift T N mu (Y T mu σ ξ W N n ω)
        + matVec (σ (Y T mu σ ξ W N n ω)) (dW T W N n ω)

/-- The index `n ∈ {0, …, N − 1}` of the grid cell `[nT/N, (n+1)T/N]` used for time `t` in
(10): `n = min(⌊tN/T⌋, N − 1)`. Interior grid points `t = nT/N` get the cell to their right
(both adjacent formulas of (10) agree there by (8)), and `t = T` gets the last cell
`n = N − 1`. -/
noncomputable def cell (T : ℝ≥0) (N : ℕ) (t : ℝ≥0) : ℕ :=
  min ⌊(t : ℝ) * N / T⌋₊ (N - 1)

/-- Hutzenthaler–Jentzen–Kloeden, p. 5, (10): the time-continuous interpolation
`Ȳ^N_t = Y^N_n + (t − nT/N) µ(Y^N_n) / (1 + (T/N) ‖µ(Y^N_n)‖) + σ(Y^N_n)(W_t − W_{nT/N})`
for `t ∈ [nT/N, (n+1)T/N]`, `n ∈ {0, …, N − 1}`, with `n = cell T N t`. Meaningful for
`N ≥ 1` and `t ∈ [0, T]`. -/
noncomputable def Ybar (T : ℝ≥0) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ) (ξ : Ω → SDEState d)
    (W : ℝ≥0 → Ω → SDEState m) (N : ℕ) (t : ℝ≥0) (ω : Ω) : SDEState d :=
  Y T mu σ ξ W N (cell T N t) ω
    + (((t : ℝ) - (cell T N t : ℝ) * T / N)
        / (1 + ((T : ℝ) / N) * ‖mu (Y T mu σ ξ W N (cell T N t) ω)‖))
      • mu (Y T mu σ ξ W N (cell T N t) ω)
    + matVec (σ (Y T mu σ ξ W N (cell T N t) ω))
        (W t ω - W ((cell T N t : ℝ≥0) * T / N) ω)

end TamedEuler.Convergence


