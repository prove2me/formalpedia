-- Prove2me | Definitions.Def_RankOneSK_muInner
-- name    : RankOneSK_muInner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:30.36826+00:00
-- url     : https://prove2.me/theorems/8413c912-4802-49fb-a835-134d5fb6ede0
-- title:
--   Inner product $\langle u,v\rangle_\mu$ of the SK Gibbs measure
-- statement:
--   For the SK Gibbs measure $\mu_J(x)=Z_n^{-1}\exp(\tfrac12x^\top Jx)$ on $\{\pm1\}^n$ (no external field),
--   $$\langle u,v\rangle_\mu=\mathbb E_{X\sim\mu_J}[u(X)v(X)].$$
--
--   The operators $P_i$, $L_i$ and $L_J$ are self-adjoint for this inner product, and $\langle L_Jf,f\rangle_\mu=\mathcal E(f)$ is the Dirichlet form (1).
--
--   **Formalization Note** Configurations are the published `OAI.SKGap.Spin n` (maps $[n]\to\{\text{true},\text{false}\}$ read as $\pm1$), sites are indexed from $0$, and the interaction matrix $J$ is the published `OAI.SKGap.Disorder n` (its entries above the diagonal; the full matrix `coupling J` is symmetric with zero diagonal). The expectation is the published `OAI.SKGap.expectation J 0`.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, §1, p.2 (inner product) and (4), p.4

import Mathlib
import Definitions.Def_SKHighTemperature

open OAI.SKGap

namespace RankOneSK

/-- The inner product `⟨u, v⟩_µ = E_{X∼µ_J}[u(X) v(X)]` for the SK Gibbs measure
`µ_J(x) = Z⁻¹ exp(½ xᵀJx)` with no external field.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §1, p.2 (inner product) and (4), p.4 (the measure `µ_J`).

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (read as ±1 through `spinValue`), sites are
0-based `Fin n`, and the interaction matrix `J` is the published `OAI.SKGap.Disorder n` (entries
above the diagonal; `coupling J` is symmetric with zero diagonal). The expectation is the published
`OAI.SKGap.expectation J 0` (zero external field). -/
noncomputable def muInner {n : ℕ} (J : Disorder n) (u v : Spin n → ℝ) : ℝ :=
  expectation J 0 (fun x => u x * v x)

end RankOneSK


