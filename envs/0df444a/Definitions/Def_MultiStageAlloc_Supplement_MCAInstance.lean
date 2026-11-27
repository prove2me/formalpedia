-- Prove2me | Definitions.Def_MultiStageAlloc_Supplement_MCAInstance
-- name    : MultiStageAlloc_Supplement_MCAInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:16:37.828811+00:00
-- url     : https://prove2.me/theorems/c1af7632-51e3-4492-9ffb-7275237fd69d
-- title:
--   Instance of multi-stage configuration allocation with its price grid (§2.2, §4.1)
-- statement:
--   An instance of the $K$-stage configuration allocation model consists of finite sets $U$ (users), $C$ (configurations) and $V$ (advertisers), together with:
--
--   1. a stage $\mathrm{batch}(i)\in\{1,\dots,K\}$ for each user $i$, so that the batches $U_k=\{i:\mathrm{batch}(i)=k\}$ are disjoint and cover $U$;
--   2. impression numbers $\xi_{i,c,j}\ge 0$: choosing configuration $c$ for user $i$ gives advertiser $j$ exactly $\xi_{i,c,j}$ impressions;
--   3. a price grid $0=\hat w_0<\hat w_1<\dots<\hat w_T$ with $T\in\mathbb N$;
--   4. per-impression prices $w_{i,c,j}$, each equal to $\hat w_\tau$ for some $\tau\in[T]=\{1,\dots,T\}$.
--
--   Every advertiser demands $n_j=1$ impressions. Free disposal applies: an advertiser that receives more impressions pays only for its most expensive ones, up to its demand.
--
--   This is the model of Theorem 2 and of the stage programs of Algorithm 2.
--
--   **Formalization Note** The demand $n_j=1$ and the finite price grid are the paper's own normalizations, which it states without loss of generality (p.13, footnote 13; §4.1, p.25). The grid is part of the data, so statements hold for every admissible grid. Batches and the sets $U,C,V$ may be empty.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, §2.2, pp.12–13, and §4.1, p.25

import Mathlib

namespace MultiStageAlloc.Supplement

/-- **An instance of the multi-stage configuration allocation model, with its price grid.**
Feng & Niazadeh, *Batching and Optimal Multi-stage Bipartite Allocations*, arXiv:2211.16581v1,
§2.2, pp.12–13, and §4.1, p.25. `U` is the set of users, `C` the set of configurations and `V` the
set of advertisers. User `i` arrives at stage `batch i ∈ {1, …, K}`, so the batches
`U_k = {i | batch i = k}` are disjoint and cover `U`. Choosing configuration `c` for user `i`
allocates `ξ i c j ≥ 0` impressions to advertiser `j` at the per-impression price `price i c j`.
Every advertiser demands `n_j = 1` impressions in total (free disposal: it pays only for its top
`n_j` impressions).

The price universe of §4.1 is `0 = ŵ_0 < ŵ_1 < ⋯ < ŵ_T` (`wgrid`, `T ∈ ℕ`), and every price equals
`ŵ_τ` for some `τ ∈ [T] = {1, …, T}`.

**Formalization Note.** Capacities are `n_j = 1`, as the paper assumes "without loss of
generality" (p.13, footnote 13), and Algorithm 2 is printed only for that case. The grid is part of
the data, so every statement quantifies over every admissible grid. Only `wgrid 0, …, wgrid T`
matter; values of `wgrid` beyond `T` enter no definition. Batches, `U`, `C` and `V` may be empty;
finiteness is a `Fintype` hypothesis of each statement. -/
structure MCAInstance (U C V : Type*) (K : ℕ) where
  /-- The stage at which a user arrives. -/
  batch : U → ℕ
  /-- Stages are numbered `1, …, K`. -/
  batch_mem : ∀ i, batch i ∈ Finset.Icc 1 K
  /-- The number `ξ_{i,c,j}` of impressions configuration `c` of user `i` gives advertiser `j`. -/
  ξ : U → C → V → ℝ
  /-- Impression numbers are non-negative. -/
  ξ_nonneg : ∀ i c j, 0 ≤ ξ i c j
  /-- The number `T` of positive price levels. -/
  T : ℕ
  /-- The price grid `ŵ_0, ŵ_1, …, ŵ_T`. -/
  wgrid : ℕ → ℝ
  /-- `ŵ_0 = 0`. -/
  wgrid_zero : wgrid 0 = 0
  /-- `ŵ_0 < ŵ_1 < ⋯ < ŵ_T`. -/
  wgrid_lt : ∀ τ, τ < T → wgrid τ < wgrid (τ + 1)
  /-- The per-impression price `w_{i,c,j}`. -/
  price : U → C → V → ℝ
  /-- Every price is on the grid at a positive level: `w_{i,c,j} = ŵ_τ` for some `τ ∈ [T]`. -/
  price_mem : ∀ i c j, ∃ τ ∈ Finset.Icc 1 T, price i c j = wgrid τ

end MultiStageAlloc.Supplement


