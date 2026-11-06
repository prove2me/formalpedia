-- Prove2me | Definitions.Def_RankOneSK_siteLap
-- name    : RankOneSK_siteLap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:34.090192+00:00
-- url     : https://prove2.me/theorems/e700b439-3d37-4ef5-9baf-892183b15825
-- title:
--   Single-site operator $L_i=I-P_i$ of SK Glauber dynamics
-- statement:
--   Let $\mu_J(x)=Z_n^{-1}\exp(\tfrac12 x^\top Jx)$ be the Sherrington–Kirkpatrick Gibbs measure on $\{\pm1\}^n$ with symmetric, zero-diagonal interaction matrix $J$ and no external field. For a site $i$ and $f:\{\pm1\}^n\to\mathbb R$, the heat-bath average is
--   $$P_if(x)=\mathbb E_{\mu_J}\big[f(X)\,\big|\,X_j=x_j\ \forall j\neq i\big],$$
--   and the single-site operator is
--   $$L_if(x)=f(x)-P_if(x).$$
--
--   $P_i$ is the update of Glauber dynamics at site $i$; $L_i$ is the complementary projection.
--
--   **Formalization Note** Configurations are the published `OAI.SKGap.Spin n` (maps $[n]\to\{\text{true},\text{false}\}$ read as $\pm1$), sites are indexed from $0$, and the interaction matrix $J$ is the published `OAI.SKGap.Disorder n` (its entries above the diagonal; the full matrix `coupling J` is symmetric with zero diagonal). $P_i$ is the published `conditionalExpectation J 0 i` (zero field).
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, §1, p.2 (operators $P_i$, $L_i$) and (4), p.4

import Mathlib
import Definitions.Def_SKHighTemperature

open OAI.SKGap

namespace RankOneSK

/-- The single-site operator `L_i = I − P_i` of the Glauber dynamics of the SK Gibbs measure
`µ_J(x) ∝ exp(½ xᵀJx)` (no external field): `L_i f(x) = f(x) − E_µ[f(X) | X_j = x_j, ∀ j ≠ i]`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §1, p.2 (`P_i`, `L_i = I − P_i`) and (4), p.4.

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (read as ±1 through `spinValue`), sites are
0-based `Fin n`, and the interaction matrix `J` is the published `OAI.SKGap.Disorder n` (entries
above the diagonal; `coupling J` is symmetric with zero diagonal). `P_i` is the published heat-bath
`conditionalExpectation J 0 i` at zero field, which averages `f` over the two values of spin `i`
with the Gibbs weights. -/
noncomputable def siteLap {n : ℕ} (J : Disorder n) (i : Fin n) (f : Spin n → ℝ) (x : Spin n) : ℝ :=
  f x - conditionalExpectation J 0 i f x

end RankOneSK


