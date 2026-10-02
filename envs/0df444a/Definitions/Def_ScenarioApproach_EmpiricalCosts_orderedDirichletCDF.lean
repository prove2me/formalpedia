-- Prove2me | Definitions.Def_ScenarioApproach_EmpiricalCosts_orderedDirichletCDF
-- name    : ScenarioApproach_EmpiricalCosts_orderedDirichletCDF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T18:09:08.836234+00:00
-- url     : https://prove2.me/theorems/ee8a8255-4fd7-48e7-92ef-79ba8ea0a6e6
-- title:
--   Theorem 8.4 — ordered Dirichlet distribution function with parameters (d, 1, …, 1)
-- statement:
--   Let $1\le d\le N$. The **ordered Dirichlet distribution with parameters $(d,1,\dots,1)$** (with $N-d$ ones) is the law on $\mathbb R^{N-d+1}$ of a vector $(\alpha_d,\dots,\alpha_N)$ with density $\frac{N!}{(d-1)!}\,\alpha_d^{d-1}$ on the ordered simplex $\{0\le\alpha_d\le\cdots\le\alpha_N\le1\}$. Its joint distribution function at $(\varepsilon_d,\dots,\varepsilon_N)$ is
--
--   $$
--   F(\varepsilon_d,\dots,\varepsilon_N)=\frac{N!}{(d-1)!}\int_0^{\varepsilon_d}\alpha_d^{d-1}\int_0^{\varepsilon_{d+1}}\cdots\int_0^{\varepsilon_N}\mathbf 1_{\{0\le\alpha_d\le\cdots\le\alpha_N\le1\}}\,\mathrm d\alpha_N\cdots\mathrm d\alpha_{d+1}\,\mathrm d\alpha_d .
--   $$
--
--   For $d=1$ it is the joint distribution of the order statistics of $N$ independent uniform variables on $[0,1]$; its first marginal is the beta distribution $B(d,N-d+1)$.
--
--   **Formalization Note** The variables $\alpha_d,\dots,\alpha_N$ are `α 0, …, α (N - d)` and `ε` is indexed by the book's indices $d,\dots,N$. The iterated integral is the Lebesgue integral over the box $\prod_j[0,\varepsilon_{d+j}]$ intersected with $\{\alpha\ \text{nondecreasing},\ 0\le\alpha_j\le1\}$. For $\varepsilon_j\ge0$ this equals the book's iterated integral; if some $\varepsilon_j<0$ the box is empty and the value is $0$ (the distribution function of a law on $[0,1]^{N-d+1}$). For $d=0$ or $d>N$ the value is the junk $0$.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 90, Theorem 8.4 (right-hand side)

import Mathlib

namespace ScenarioApproach.EmpiricalCosts

/-- The joint distribution function of the ordered Dirichlet distribution with parameters
`(d, 1, 1, …, 1)` (`N - d` ones), `1 ≤ d ≤ N`, evaluated at `(ε_d, ε_{d+1}, …, ε_N)`:
`N!/(d-1)! ∫_0^{ε_d} α_d^{d-1} ∫_0^{ε_{d+1}} ⋯ ∫_0^{ε_N} 1_{0 ≤ α_d ≤ ⋯ ≤ α_N ≤ 1} dα_N ⋯ dα_d`.
The variables `α_d, …, α_N` are `α 0, …, α (N - d)`, and `ε` is indexed by the book's indices
`d, …, N`. The iterated integral is the Lebesgue integral over the box `∏ⱼ [0, ε_{d+j}]` (empty,
hence contributing `0`, when some `ε_{d+j} < 0`). For `d = 0` or `d > N` the value is `0` (junk). -/
noncomputable def orderedDirichletCDF (d N : ℕ) (ε : ℕ → ℝ) : ℝ :=
  if h : 1 ≤ d ∧ d ≤ N then
    ((N.factorial : ℝ) / ((d - 1).factorial : ℝ)) *
      ∫ α in (Set.univ.pi fun j : Fin (N - d + 1) => Set.Icc (0 : ℝ) (ε (d + j))) ∩
          {α : Fin (N - d + 1) → ℝ | Monotone α ∧ ∀ j, α j ∈ Set.Icc (0 : ℝ) 1},
        (α ⟨0, by omega⟩) ^ (d - 1)
  else 0

end ScenarioApproach.EmpiricalCosts


