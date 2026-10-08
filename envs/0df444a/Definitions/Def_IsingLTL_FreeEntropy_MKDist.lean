-- Prove2me | Definitions.Def_IsingLTL_FreeEntropy_MKDist
-- name    : IsingLTL_FreeEntropy_MKDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:33.146225+00:00
-- url     : https://prove2.me/theorems/85e5235f-5789-4e00-925d-aba23f2623b5
-- title:
--   Monge–Kantorovich–Wasserstein distance $\|X-Y\|_{\mathrm{MK}}$ (Lemma 4.6)
-- statement:
--   For laws $\mu$ of $X$ and $\nu$ of $Y$ on $\mathbb R$, the **Monge–Kantorovich–Wasserstein distance** is
--   $$\|X-Y\|_{\mathrm{MK}}=\inf\big\{\mathbb E|X'-Y'| : X'\overset{d}{=}X,\ Y'\overset{d}{=}Y\big\},$$
--   the infimum of $\mathbb E|X-Y|$ over all couplings of $X$ and $Y$. It may be $+\infty$. It is the optimal transport cost $D_c(\mu,\nu)$ for the cost $c(u,w)=|u-w|$.
--
--   **Formalization Note** Built on the published general optimal transport cost `RWPI.SqrtLasso.transportCost` (infimum over probability couplings of the lower integral of a $[0,\infty]$-valued cost); the value lies in $[0,\infty]$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 18, Lemma 4.6; p. 22, proof of Lemma 6.1

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost

namespace IsingLTL.FreeEntropy

open MeasureTheory

/-- The **Monge–Kantorovich–Wasserstein distance** `‖X − Y‖_MK` between laws `μ` of `X` and `ν`
of `Y` on `ℝ` (Dembo–Montanari, *Ising Models on Locally Tree-Like Graphs*, arXiv:0804.4726v3,
Lemma 4.6, p. 18): "the infimum of `E|X − Y|` over all couplings of `X` and `Y`". It is the optimal
transport cost `D_c(μ, ν)` (the published `RWPI.SqrtLasso.transportCost`) for the cost
`c(u, w) = |u − w|`.

Formalization Note: the value is in `ℝ≥0∞`: a coupling is a probability measure on `ℝ × ℝ` with
marginals `μ` and `ν`, and `E|X − Y|` is a lower integral, so `‖X − Y‖_MK = ∞` is possible (the
proof of Lemma 6.1 uses that case). For probability laws a coupling (the product) always
exists. -/
noncomputable def mkDist (μ ν : Measure ℝ) : ENNReal :=
  RWPI.SqrtLasso.transportCost (fun u w : ℝ => ENNReal.ofReal |u - w|) μ ν

end IsingLTL.FreeEntropy


