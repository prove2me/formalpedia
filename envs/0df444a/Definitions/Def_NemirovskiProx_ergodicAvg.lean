-- Prove2me | Definitions.Def_NemirovskiProx_ergodicAvg
-- name    : NemirovskiProx_ergodicAvg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:45:52.315242+00:00
-- url     : https://prove2.me/theorems/c21a4c77-ed67-4674-bcf0-40c7dfb35b82
-- title:
--   Ergodic average $z^N$
-- statement:
--   Given stepsizes $\gamma_1,\dots,\gamma_N$ and points $w_1,\dots,w_N$, the **approximate solution built in the course of $N$ steps** is
--   $$z^N=\Big(\sum_{t=1}^N\gamma_t\Big)^{-1}\sum_{t=1}^N\gamma_t w_t .$$
--
--   It is the output of the conceptual prox-method and of its basic implementation; the error bounds of Proposition 2.2 and Theorem 3.2 are stated for it. Note that it averages the points $w_t$, not the prox points $z_t$.
--
--   **Formalization Note** Indices are the paper's ($t=1,\dots,N$); in every run of the mission $\gamma_t>0$.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, CPM, §2.3, p. 233 (definition of z^t)

import Mathlib

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **The approximate solution `z^N` built in the course of `N` steps.**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), CPM, §2.3, p. 233: "z^t = (Σ_{τ=1}^t γτ)^{−1} Σ_{τ=1}^t γτ wτ".

`ergodicAvg γs w n = (Σ_{t=1}^n γs t)⁻¹ • Σ_{t=1}^n γs t • w t`.

**Formalization Note.** Indices are the paper's: `γs t`, `w t` for `t = 1, …, n`; index `0` is
unused. In every run of this mission `γs t > 0`, so the inverted sum is positive for `n ≥ 1`. -/
noncomputable def ergodicAvg {E : Type*} [AddCommGroup E] [Module ℝ E]
    (γs : ℕ → ℝ) (w : ℕ → E) (n : ℕ) : E :=
  (∑ t ∈ Finset.Icc 1 n, γs t)⁻¹ • ∑ t ∈ Finset.Icc 1 n, γs t • w t

end NemirovskiProx


