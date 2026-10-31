-- Prove2me | Definitions.Def_ShapleyNV_Data
-- name    : ShapleyNV_Data
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:06.302+00:00
-- url     : https://prove2.me/theorems/8403d81d-213f-439c-b464-50de2a8ba08b
-- title:
--   Historical data: distinct features $\hat x_k$ with demand samples $\hat z_{ki}$
-- statement:
--   The historical data consist of $n$ observations, grouped by their distinct feature values. There are $K \ge 1$ groups; group $k$ has feature value $\hat x_k$ in the feature space $\mathcal X$ and $n_k \ge 1$ demand observations $\hat z_{k1}, \dots, \hat z_{kn_k} \in \mathcal Z = \mathbb R_+$. The feature values $\hat x_1, \dots, \hat x_K$ are pairwise distinct; the demands need not be. The total sample size is $n = \sum_k n_k$.
--
--   The empirical distribution, the in-sample feature set $\widehat{\mathcal X} = \{\hat x_k\}$ and the Shapley extension are all built from these data.
--
--   **Formalization Note** Groups are indexed by $\{0,\dots,K-1\}$ and the observations of group $k$ by $\{0,\dots,n_k-1\}$. The fields record $K>0$, injectivity of $k \mapsto \hat x_k$, and $n_k > 0$. Two auxiliary facts say that the two index sets are nonempty, so that finite minima and maxima over them are defined.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), §2.2, p.5 (grouping into K groups by distinct feature values x̂_k, observations ẑ_ki, Σ n_k = n)

import Mathlib

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Historical data** of the feature-based newsvendor.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), §2.2, p.5: "Suppose the historical data contains n observations. We first group them into
K groups according to distinct feature values x̂_k, k = 1, …, K. Each x̂_k is associated with
demand observations ẑ_ki, i = 1, …, n_k, where Σ_k n_k = n."

Fields:
* `K` is the number of distinct observed feature values, and `K_pos : 0 < K` (there is data);
* `xhat k ∈ X` is the k-th observed feature value, and `xhat_inj` says the x̂_k are **distinct**
  ("distinct feature values", p.5);
* `m k = n_k` is the number of demand observations attached to `x̂_k`, and `m_pos : 0 < n_k`
  (each group is nonempty: a group is formed by observations having that feature value);
* `zhat k i = ẑ_ki ∈ 𝒵 = ℝ₊` is the i-th demand observed with feature `x̂_k` (not necessarily
  distinct).

**Formalization Note.** Groups are indexed by `Fin K` (the paper's `[K]`, shifted to start at 0)
and observations in group `k` by `Fin (n_k)`. The total sample size is `n = Σ_k m k`. The two
lemmas below only record that the index sets are nonempty, so that finite `min`/`max` over them
make sense. -/
structure Data (X : Type*) where
  /-- number of distinct observed feature values -/
  K : ℕ
  /-- there is at least one observation -/
  K_pos : 0 < K
  /-- the distinct observed feature values `x̂_k` -/
  xhat : Fin K → X
  /-- the `x̂_k` are distinct -/
  xhat_inj : Function.Injective xhat
  /-- `n_k`, the number of demand observations attached to `x̂_k` -/
  m : Fin K → ℕ
  /-- every group is nonempty -/
  m_pos : ∀ k, 0 < m k
  /-- the demand observations `ẑ_ki ∈ ℝ₊` -/
  zhat : (k : Fin K) → Fin (m k) → ℝ≥0

/-- The index set `[K]` is nonempty. -/
theorem Data.univ_nonempty {X : Type*} (D : Data X) : (Finset.univ : Finset (Fin D.K)).Nonempty :=
  ⟨⟨0, D.K_pos⟩, Finset.mem_univ _⟩

/-- The set of observation indices `(k, i)` is nonempty. -/
theorem Data.obs_nonempty {X : Type*} (D : Data X) :
    (Finset.univ : Finset (Σ k : Fin D.K, Fin (D.m k))).Nonempty :=
  ⟨⟨⟨0, D.K_pos⟩, ⟨0, D.m_pos _⟩⟩, Finset.mem_univ _⟩

end ShapleyNV


