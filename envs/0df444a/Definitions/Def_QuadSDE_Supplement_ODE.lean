-- Prove2me | Definitions.Def_QuadSDE_Supplement_ODE
-- name    : QuadSDE_Supplement_ODE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:13:05.030495+00:00
-- url     : https://prove2.me/theorems/4a1f0953-437c-4f8d-80c1-c6f461c1e945
-- title:
--   Solutions of the ODE $dX/dt=f(X)$, $X(0)=Y$, on $[0,T]$
-- statement:
--   For a vector field $f:\mathbb R^N\to\mathbb R^N$, an initial condition $Y$ and a final time $T$, a function $X:[0,T]\to\mathbb R^N$ **solves the ODE** (1) if it is continuous on $[0,T]$ and
--   $$X(t)=Y+\int_0^tf(X(s))\,ds\qquad\text{for every }t\in[0,T].$$
--
--   This is the noise-free dynamics of Problem 1 (APX-ODE), used in Theorem 6.
--
--   **Formalization Note** The integral form; for a continuous $f$ it is equivalent to $dX/dt=f(X)$ with one-sided derivatives at the endpoints.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), Eq. (1) and Problem 1, p. 2

import Mathlib

noncomputable section

namespace QuadSDE.Supplement

/-- Bravyi, Byrne, Zayats, Zhuk, Zlokapa, *Quantum algorithms for stochastic nonlinear differential
equations*, arXiv:2606.08349 (sha256 29bd9b01…), Problem 1 and Eq. (1), p. 2: `X` solves the ODE
`dX(t)/dt = f(X(t))`, `X(0) = Y`, on `[0, T]`: `X` is continuous on `[0, T]` and
`X(t) = Y + ∫₀ᵗ f(X(s)) ds` for every `t ∈ [0, T]`.

**Formalization Note.** The integral form; for a continuous `f` it is equivalent to the
differential form with one-sided derivatives at the endpoints. -/
def IsODESol {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (Y : Fin N → ℝ) (T : ℝ)
    (X : ℝ → Fin N → ℝ) : Prop :=
  ContinuousOn X (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T, X t = Y + ∫ s in (0 : ℝ)..t, f (X s)

end QuadSDE.Supplement


