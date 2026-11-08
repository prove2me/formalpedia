-- Prove2me | Definitions.Def_AFIsingKS_partitionFn
-- name    : AFIsingKS_partitionFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:14:20.564452+00:00
-- url     : https://prove2.me/theorems/9f197abc-f083-4589-9e13-3b716932e06c
-- title:
--   The Ising partition function $Z_G(\beta)$ of a simple graph
-- statement:
--   For a simple graph $G=(V,E)$ on $n$ vertices and $\sigma\in\{\pm1\}^V$, the Hamiltonian
--   $$\mathcal H_G(\sigma)=\sum_{uv\in E}\frac{1-\sigma_u\sigma_v}{2}$$
--   counts the edges cut by the bipartition of $\sigma$. The **partition function** at $\beta\in\mathbb C$ is
--   $$Z_G(\beta)=\sum_{\sigma\in\{\pm1\}^V}\exp(\beta\,\mathcal H_G(\sigma)).$$
--   The model is antiferromagnetic for $\beta\ge0$. The goal theorem concerns the complex zeros of this function.
--
--   **Formalization Note** The Hamiltonian is defined as the number of cut edges, which is what the sum equals.
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 1, p.3

import Mathlib
import Definitions.Def_AFIsingKS_overlap

open scoped Classical

namespace AFIsingKS

/-- The Ising Hamiltonian `H_G(σ) = ∑_{uv ∈ E} (1 − σ_u σ_v)/2` of a simple graph on `Fin n`, as the
number of edges cut by the bipartition of `σ` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 1, p.3).

**Formalization Note.** The term `(1 − σ_u σ_v)/2` is `1` on an edge with different spins and `0`
otherwise, so the sum is this count, as the page says. -/
noncomputable def cut {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Spin n) : ℕ :=
  (G.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ σ u ≠ σ v)).card

/-- The partition function `Z_G(β) = ∑_{σ ∈ {±1}^V} exp(β · H_G(σ))` at a complex `β`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 1, p.3). -/
noncomputable def partitionFn {n : ℕ} (G : SimpleGraph (Fin n)) (β : ℂ) : ℂ :=
  ∑ σ : Spin n, Complex.exp (β * (cut G σ : ℂ))

end AFIsingKS


