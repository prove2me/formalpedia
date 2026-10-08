-- Prove2me | Definitions.Def_NonlinFPE_Main_SDE
-- name    : NonlinFPE_Main_SDE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:59.289657+00:00
-- url     : https://prove2.me/theorems/1d9b1ab0-bee6-4f94-98fc-4095042f4f2b
-- title:
--   §2 and §4 — diffusion and drift coefficients switched off after time T, the inputs of a weak SDE solution on [0, T]
-- statement:
--   Fix $T > 0$. For a time-dependent diffusion matrix $s(t,x) = (s_{ij}(t,x))$ and drift $\beta(t,x) = (\beta_i(t,x))$ on $[0,\infty)\times\mathbb R^d$, the **coefficients switched off after $T$** are
--   $$s^T(t,x) = \begin{cases} s(t,x), & t \le T,\\ 0, & t > T,\end{cases} \qquad \beta^T(t,x) = \begin{cases} \beta(t,x), & t \le T,\\ 0, & t > T.\end{cases}$$
--   A weak solution on $[0,\infty)$ of $dX = \beta^T(t,X)\,dt + s^T(t,X)\,dW$ is constant after $T$, and on $[0,T]$ it is a weak solution of $dX = \beta(t,X)\,dt + s(t,X)\,dW$.
--
--   The McKean–Vlasov SDE (4.1) and the SDE (2.2) are posed on $[0,T]$, while the published notion `EthierKurtz.IsWeakSDESolution` is on $[0,\infty)$; these cut coefficients are the bridge.
--
--   **Formalization Note** The diffusion matrix takes values in `EthierKurtz.SDEDiffusion d` (entry $(i,j)$), the drift in `EthierKurtz.SDEState d`, both built with `WithLp.toLp 2`.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, §2, pp. 5–6, (2.2); §4, p. 23, (4.1), 0 ≤ t ≤ T

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion

open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz

/-- A time-dependent diffusion matrix `s(t, x)` (entry `(i, j)` = `s t x i j`) switched off after
time `T`, as the coefficient `ℝ≥0 × ℝᵈ → ℝ^{d×d}` of `EthierKurtz.IsWeakSDESolution`: it equals
`s(t, x)` for `t ≤ T` and `0` for `t > T`, so a solution is constant after `T`. -/
noncomputable def cutDiff {d : ℕ} (T : ℝ≥0) (s : ℝ≥0 → SDEState d → Fin d → Fin d → ℝ) :
    ℝ≥0 × SDEState d → SDEDiffusion d :=
  fun p => WithLp.toLp 2 (fun q : Fin d × Fin d => if p.1 ≤ T then s p.1 p.2 q.1 q.2 else 0)

/-- A time-dependent drift `β(t, x)` (component `i` = `β t x i`) switched off after time `T`: it
equals `β(t, x)` for `t ≤ T` and `0` for `t > T`. -/
noncomputable def cutDrift {d : ℕ} (T : ℝ≥0) (β : ℝ≥0 → SDEState d → Fin d → ℝ) :
    ℝ≥0 × SDEState d → SDEState d :=
  fun p => WithLp.toLp 2 (fun i : Fin d => if p.1 ≤ T then β p.1 p.2 i else 0)

end NonlinFPE.Main


