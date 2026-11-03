-- Prove2me | Definitions.Def_RankRobustAssort_Problem
-- name    : RankRobustAssort_Problem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:12.793373+00:00
-- url     : https://prove2.me/theorems/afe96d22-3294-4433-b01a-c6444195d28e
-- title:
--   Problem instance: revenues, past assortments, sales data, radius and norm
-- statement:
--   A problem instance with $n$ products and $M$ past assortments consists of:
--
--   1. revenues $r_0,\dots,r_n$ of the products $\mathcal N_0=\{0,1,\dots,n\}$, where $0$ is the no-purchase option, with $r_0=0$ and $0<r_1<\dots<r_n$ (unique revenues sorted ascending);
--   2. past assortments $S_1,\dots,S_M\subseteq\mathcal N_0$ (not required to contain $0$);
--   3. historical purchase frequencies $v_{m,i}\in[0,1]$ with $\sum_{i\in\mathcal N_0}v_{m,i}=1$ for each $m$ and $v_{m,i}=0$ whenever $i\notin S_m$;
--   4. a radius $\eta\ge0$;
--   5. a norm $\|\cdot\|$, either $\ell_1$ or $\ell_\infty$.
--
--   These are exactly the standing assumptions of §2, on which every result of the mission is stated.
--
--   **Formalization Note.** Products are $\mathrm{Fin}(n+1)$; past assortments are indexed by $\mathrm{Fin}\,M$, so the paper's $S_m$ is entry $m-1$. "$r$ strictly increasing with $r_0=0$" encodes $0=r_0<r_1<\dots<r_n$. No lower bound on $n$ or $M$ is imposed, as in the paper.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, §2, p.7–8 and Notation p.6

import Mathlib
import Definitions.Def_RankRobustAssort_NormChoice

namespace RankRobustAssort

/-- A problem instance of robust assortment optimization under ranking-based choice models, with
`n` products and `M` past assortments, carrying the standing assumptions of §2.

* `r` — revenues of the products `𝒩₀ = {0,…,n}`, with `r₀ = 0` and `0 < r₁ < ⋯ < r_n`
  (unique revenues, sorted ascending);
* `S m` — the past assortment `S_{m+1} ⊆ 𝒩₀` (not required to contain `0`);
* `v m i` — the historical purchase frequency `v_{m+1,i} ∈ [0,1]`, normalized so that
  `∑_{i∈𝒩₀} v_{m,i} = 1`, and equal to zero for products not offered (`i ∉ S_m`);
* `η ≥ 0` — the radius of the consistent set `𝒰`;
* `norm` — the norm of the error vector, `ℓ₁` or `ℓ∞`.

Sturt, arXiv:2112.05010v4, §2, p.7 (products, revenues, past assortments, data), p.8 (radius
`η ≥ 0`), Notation p.6 (norm).

Formalization Note: products are `Fin (n+1)`, `0` the no-purchase option. Past assortments are
indexed by `Fin M`: the paper's `S_m` (`m ∈ {1,…,M}`) is `S ⟨m-1, _⟩`. `StrictMono r` together with
`r 0 = 0` is exactly `0 = r₀ < r₁ < ⋯ < r_n`. The paper writes "ℳ ≜ {S₁,…,S_M} ⊆ 𝒩₀" for "each
`S_m ⊆ 𝒩₀`"; past assortments need not contain `0`. `n = 0` and `M = 0` are allowed (the paper
states no lower bound). -/
structure Problem (n M : ℕ) where
  /-- revenue `r_i` of product `i` -/
  r : Fin (n + 1) → ℝ
  /-- the no-purchase option earns nothing, `r₀ = 0` -/
  r_zero : r 0 = 0
  /-- revenues are unique and sorted ascending, `r₀ < r₁ < ⋯ < r_n` -/
  r_strictMono : StrictMono r
  /-- the past assortments `S_1, …, S_M` -/
  S : Fin M → Finset (Fin (n + 1))
  /-- the historical purchase frequencies `v_{m,i}` -/
  v : Fin M → Fin (n + 1) → ℝ
  v_nonneg : ∀ m i, 0 ≤ v m i
  v_le_one : ∀ m i, v m i ≤ 1
  v_sum : ∀ m, ∑ i, v m i = 1
  v_off : ∀ m i, i ∉ S m → v m i = 0
  /-- the radius `η` of the consistent set -/
  η : ℝ
  η_nonneg : 0 ≤ η
  /-- the norm (`ℓ₁` or `ℓ∞`) of the estimation error -/
  norm : NormChoice

end RankRobustAssort


