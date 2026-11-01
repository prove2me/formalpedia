-- Prove2me | Definitions.Def_NonstatNV_demandVariation
-- name    : NonstatNV_demandVariation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:01:53.755619+00:00
-- url     : https://prove2.me/theorems/fea938f2-62be-4119-ae63-3966cb5ff676
-- title:
--   Demand variation $V_\mu$ (2.2)
-- statement:
--   A **partition** of $\{1,\dots,T\}$ is a set of periods $1\le t_0<t_1<\dots<t_K\le T$, $0\le K\le T-1$. The **demand variation** of a sequence of means $\mu_1,\dots,\mu_T$ is
--
--   $$
--   V_\mu=\max_{0\le K\le T-1}\ \max_{\{t_0,\dots,t_K\}}\ \sum_{k=1}^{K}\big(\mu_{t_k}-\mu_{t_{k-1}}\big)^2 .
--   $$
--
--   It is a deterministic analogue of quadratic variation that penalizes trends; the instance class $\mathcal D(v)$ consists of sequences with $V_\mu\le T^v$.
--
--   **Formalization Note** A partition is a finite subset of $\{1,\dots,T\}$ listed in increasing order. The empty set is also admitted; like a one-point partition it has value $0$, so the maximum is unchanged (and $V_\mu=0$ for $T=0$).
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, §2.2, (2.2), p.12; $\mathcal D(v)$, p.13

import Mathlib

namespace NonstatNV

/-- The demand variation `V_μ` of a sequence of means over the horizon `{1, …, T}` ((2.2), p.12,
of An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4): the maximum, over all partitions `1 ≤ t₀ < ⋯ < t_K ≤ T` (`0 ≤ K ≤ T − 1`), of
`Σ_{k=1}^K (μ_{t_k} − μ_{t_{k−1}})²`.

**Formalization Note** A partition is a finite subset `S ⊆ {1, …, T}`, listed in increasing order
(`S.sort`); its value is the sum of the squared increments between consecutive elements. A one-point
partition (`K = 0`) and the empty set both have value `0`, so admitting the empty set changes
nothing (and makes `V_μ = 0` for `T = 0`). The maximum is a `Finset.sup'` over the power set. -/
noncomputable def demandVariation (μ : ℕ → ℝ) (T : ℕ) : ℝ :=
  (Finset.Icc 1 T).powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩ fun S =>
    (((S.sort).zip (S.sort).tail).map fun p => (μ p.2 - μ p.1) ^ 2).sum

end NonstatNV


