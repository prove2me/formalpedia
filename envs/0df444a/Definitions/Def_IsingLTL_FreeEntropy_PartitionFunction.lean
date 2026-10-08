-- Prove2me | Definitions.Def_IsingLTL_FreeEntropy_PartitionFunction
-- name    : IsingLTL_FreeEntropy_PartitionFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:08.922127+00:00
-- url     : https://prove2.me/theorems/a1f0f55d-3914-4354-80be-e7786952a51d
-- title:
--   Partition function $Z_n(\beta,B)$ and free entropy density $\phi_n(\beta,B)$ ((1.1), (1.2))
-- statement:
--   For a finite graph $G=(V,E)$ with $n=|V|$ vertices, inverse temperature $\beta$ and constant magnetic field $B$, the **partition function** is
--   $$Z(\beta,B)=\sum_{\underline x\in\{+1,-1\}^V}\exp\Big\{\beta\sum_{(i,j)\in E}x_ix_j+B\sum_{i\in V}x_i\Big\},$$
--   the normalizing constant of the Ising measure (1.1), with every edge counted once. The **free entropy density** is
--   $$\phi_n(\beta,B)=\frac1n\log Z_n(\beta,B).$$
--   For a sequence of graphs $G_n=(V_n=[n],E_n)$, the asymptotic free entropy density (1.2) is the limit of $\phi_n(\beta,B)$ as $n\to\infty$; Theorem 2.4 is about this limit.
--
--   **Formalization Note** $Z>0$, so the logarithm is the genuine one. At $n=0$ the value is the junk $0$, which does not affect limits as $n\to\infty$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 1, (1.1)-(1.2); p. 6 (definition of $\phi_n$)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_IsingModel

namespace IsingLTL.FreeEntropy

/-- The **partition function** `Z(β, B) = ∑ₓ exp{β ∑_{(i,j)∈E} x_i x_j + B ∑_{i∈V} x_i}` of the
Ising model (1.1) on a finite graph `G = (V, E)` with constant field `B` (Dembo–Montanari,
*Ising Models on Locally Tree-Like Graphs*, arXiv:0804.4726v3, p. 1, (1.1)). Every unordered edge
is counted once. It is the normalizing constant of `isingOn G β (fun _ => B) ∅ Finset.univ`. -/
noncomputable def partitionFn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (β B : ℝ) : ℝ :=
  ∑ x, isingWeight G β (fun _ => B) ∅ Finset.univ x

/-- The **free entropy density** `φ_n(β, B) = (1/n) log Z_n(β, B)` of the Ising model on a finite
graph with `n = |V|` vertices (arXiv:0804.4726v3, p. 1, (1.2), and p. 6). For the graphs
`G_n` on `V_n = [n]` of the paper, take `V = Fin n`.

Formalization Note: `Z > 0`, so the logarithm is the true one; at `n = 0` the value is the junk
`log 1 / 0 = 0`, which is irrelevant for limits `n → ∞`. -/
noncomputable def freeEntropyDensity {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (β B : ℝ) : ℝ :=
  Real.log (partitionFn G β B) / Fintype.card V

end IsingLTL.FreeEntropy


