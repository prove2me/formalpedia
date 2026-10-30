-- Prove2me | Definitions.Def_CompOT_SinkhornConv_gibbsKernel
-- name    : CompOT_SinkhornConv_gibbsKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:20:56.637167+00:00
-- url     : https://prove2.me/theorems/6dae9bd8-c81c-4d73-825c-efa4b1abace9
-- title:
--   Gibbs kernel $K = e^{-C/\varepsilon}$
-- statement:
--   For a cost matrix $C\in\mathbb R^{n\times m}$ and $\varepsilon>0$, the **Gibbs kernel** is the matrix
--   $$K_{i,j} = e^{-C_{i,j}/\varepsilon}.$$
--
--   Its entries are positive for every real cost. The solution of entropic optimal transport is a diagonal scaling $\mathrm{diag}(u)K\mathrm{diag}(v)$ of this kernel, and Sinkhorn's algorithm computes the scalings.
-- source:
--   Peyré, Cuturi, Computational Optimal Transport, Found. Trends Mach. Learn. 11(5–6) (2019), doi:10.1561/2200000073, §4.1, p. 428 (definition of the Gibbs kernel)

import Mathlib

namespace CompOT.SinkhornConv

/-- **Gibbs kernel `K_{i,j} = exp(−C_{i,j}/ε)`.**
Peyré, Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11(5–6) (2019), §4.1, p. 428: "the Gibbs kernel associated to the cost matrix C as Ki,j := e^{−Ci,j/ε}".

`gibbsKernel C ε` is the `n × m` matrix with entries `exp (−C i j / ε)`. For every real cost
`C` and every `ε`, its entries are positive. -/
noncomputable def gibbsKernel {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ) :
    Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun i j => Real.exp (-C i j / ε)

end CompOT.SinkhornConv


