-- Prove2me | Definitions.Def_MWMSLagrange_relaxedCost
-- name    : MWMSLagrange_relaxedCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:04:31.215987+00:00
-- url     : https://prove2.me/theorems/d0d82235-ebe3-4879-99ac-8047583f141e
-- title:
--   Lagrangian objective (3.3) at multipliers $\lambda$
-- statement:
--   For multipliers $\lambda=(\lambda_1,\dots,\lambda_M)$ and shipments $z$, the objective of the Lagrangian relaxation problem (3.3) is
--
--   $$\sum_{j=1}^M w_jC_j+\sum_{i=1}^N\sum_{t=1}^T\Big(\mathbb E\big[h_i(y_{i,t}-D_{i,t})^+ + b_i(D_{i,t}-y_{i,t})^+\big]+\sum_{j\in\mathcal M_i}c'_{i,j}\,\mathbb E[z_{i,j,t}]\Big)+\sum_{j=1}^M\lambda_j\Big(\sum_{i\in\mathcal N_j}\sum_{t=1}^T\mathbb E[z_{i,j,t}]-C_j\Big),$$
--
--   with $c'_{i,j}=c_{i,j}-w_j$. It equals $V^\pi$ plus the penalty $\sum_j\lambda_j(\text{expected shipments of } j-C_j)$.
--
--   **Formalization Note** The paper writes $\mathbb E[\rho^\pi_{i,j,t}(y^\pi_{i,t}-I^\pi_{i,t})]$, which is $\mathbb E[z_{i,j,t}]$.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), (3.3), p.10; c'_{i,j} = c_{i,j} − w_j, p.8

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Mset
import Definitions.Def_MWMSLagrange_Instance_Nset
import Definitions.Def_MWMSLagrange_demandMeasure
import Definitions.Def_MWMSLagrange_postLevel

open MeasureTheory

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), (3.3), p.10: the objective
of the Lagrangian relaxation problem with multipliers `λ = (λ_1, …, λ_M)`, evaluated at the
shipments `z`:
`∑_j w_j C_j + ∑_i ∑_t ( E[h_i(y_{i,t} − D_{i,t})^+ + b_i(D_{i,t} − y_{i,t})^+]
  + ∑_{j∈𝓜_i} c'_{i,j} E[z_{i,j,t}] ) + ∑_j λ_j ( ∑_{i∈𝓝_j} ∑_t E[z_{i,j,t}] − C_j )`,
where `c'_{i,j} = c_{i,j} − w_j` (p.8) and `z_{i,j,t} = ρ^π_{i,j,t}(y^π_{i,t} − I^π_{i,t})`.

**Formalization Note.** Written with shipments `z` instead of `(y^π, ρ^π)` (same quantity).
It equals `cost I μ z + ∑_j λ_j (∑_{i∈𝓝_j} ∑_t E[z_{i,j,t}] − C_j)` by the rearrangement
the paper states on p.8 ("(2.1) can be equivalently formulated"). -/
noncomputable def relaxedCost {M N T : ℕ} (I : Instance M N) (μ : Fin N → Fin T → Measure ℝ)
    (lam : Fin M → ℝ) (z : Fin T → (Fin N × Fin T → ℝ) → Fin N → Fin M → ℝ) : ℝ :=
  ∑ j, I.w j * I.C j
    + (∑ i, ∑ t : Fin T,
        ((∫ ω, (I.h i * max (postLevel I z ω i t - ω (i, t)) 0
                + I.b i * max (ω (i, t) - postLevel I z ω i t) 0) ∂demandMeasure μ)
          + ∑ j ∈ I.Mset i, (I.c i j - I.w j) * ∫ ω, z t ω i j ∂demandMeasure μ))
    + ∑ j, lam j * (∑ i ∈ I.Nset j, ∑ t : Fin T, (∫ ω, z t ω i j ∂demandMeasure μ) - I.C j)

end MWMSLagrange


