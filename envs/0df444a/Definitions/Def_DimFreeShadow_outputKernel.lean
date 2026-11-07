-- Prove2me | Definitions.Def_DimFreeShadow_outputKernel
-- name    : DimFreeShadow_outputKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:45.406736+00:00
-- url     : https://prove2.me/theorems/212bdb8e-26aa-4730-95b4-fb9383567dfb
-- title:
--   Eq. (17) — the output kernels $K_t(y\mid x)$ and $K(y\mid x)$
-- statement:
--   For $0\le t<N$,
--
--   $$
--   K_t(y\mid x)=\operatorname{Tr}(D_{y,t}\rho_x^{\otimes t}),\qquad K(y\mid x)=\frac1N\sum_{t=0}^{N-1}K_t(y\mid x).
--   $$
--
--   $K_t(y\mid x)$ is the probability of outcome $y$ in the $t$-copy measurement given $X=x$, and $K(y\mid x)$ is the probability that Algorithm 2 with budget $N$ returns $y$ given $X=x$.
--
--   **Formalization Note** Real part of the trace. The arguments come in the printed order, $y$ then $x$. The condition $N\ge1$ is a hypothesis of the statements that use $K$.
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), §4.1, Eq. (17), p.16

import Mathlib
import Definitions.Def_DimFreeShadow_recoveryEffect

namespace DimFreeShadow

open ShadowTomography.UpperBound (tensorPow)

/-- **The `t`-copy output kernel** `K_t(y | x) := Tr(D_{y,t} ρ_x^{⊗t})` (arXiv:2608.06345,
sha256 a1a42249…, Eq. (17), p.16): the probability of outcome `y` in the `t`-copy recovery
measurement, conditional on `X = x`.

**Formalization Note** Real part of the trace (it is real). Argument order `y` then `x`, as in
`K_t(y | x)`. -/
noncomputable def outputKernelT {X d : Type} [Fintype X] [Fintype d] [DecidableEq d]
    (p : X → ℝ) (ρ : X → Matrix d d ℂ) (t : ℕ) (y x : X) : ℝ :=
  (Matrix.trace (recoveryEffect p ρ t y * tensorPow (ρ x) t)).re

/-- **The output kernel of Algorithm 2** `K(y | x) := (1/N) Σ_{t=0}^{N−1} K_t(y | x)`
(arXiv:2608.06345, sha256 a1a42249…, Eq. (17), p.16): the probability of `Y = y` in Algorithm 2
(the recovery PGM with budget `N`, which draws `t` uniformly from `{0, …, N−1}`), conditional on
`X = x`.

**Formalization Note** `t` runs over `Finset.range N` (0-based, as in the paper). The budget
condition `N ≥ 1` is a hypothesis of the statements. -/
noncomputable def outputKernel {X d : Type} [Fintype X] [Fintype d] [DecidableEq d]
    (p : X → ℝ) (ρ : X → Matrix d d ℂ) (N : ℕ) (y x : X) : ℝ :=
  (1 / (N : ℝ)) * ∑ t ∈ Finset.range N, outputKernelT p ρ t y x

end DimFreeShadow


