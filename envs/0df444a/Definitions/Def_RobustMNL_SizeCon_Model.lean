-- Prove2me | Definitions.Def_RobustMNL_SizeCon_Model
-- name    : RobustMNL_SizeCon_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:20:41.246997+00:00
-- url     : https://prove2.me/theorems/61481919-cc31-4ede-8b6d-b755306f83ca
-- title:
--   Sec. 3, 3.2 and Example 3.4, pp. 5–11 — MNL revenue f(S, v), worst case min_{v∈V} f(S, v), Z*(V), Y*(V) (Size-Constrained Robust), the box ∏[l_i, u_i] and the parametric value
-- statement:
--   This file sets up the size-constrained robust assortment problem under the multinomial logit (MNL) model of Rusmevichientong and Topaloglu.
--
--   There are $n$ products $\mathcal A=\{1,\dots,n\}$ with revenues $r_1,\dots,r_n\in\mathbb R$. A **parameter vector** $v=(v_0,v_1,\dots,v_n)$ collects the no-purchase weight $v_0$ and the preference weights $v_i$ of the products; it is **positive**, $v\in\mathbb R^{n+1}_{++}$, when every component is strictly positive. Offering an **assortment** $S\subseteq\mathcal A$ yields the expected revenue
--
--   $$
--   f(S,v)=\frac{\sum_{i\in S} r_i v_i}{v_0+\sum_{i\in S} v_i}.
--   $$
--
--   For an uncertainty set $\mathcal V$ of parameter vectors, the **worst-case revenue** of $S$ is $\min_{v\in\mathcal V} f(S,v)$, and
--
--   $$
--   Z^*(\mathcal V)=\max_{S\subseteq\mathcal A}\ \min_{v\in\mathcal V} f(S,v),\qquad
--   Y^*(\mathcal V)=\max_{S\subseteq\mathcal A:\ |S|\le K}\ \min_{v\in\mathcal V} f(S,v)
--   $$
--
--   are the optimal values of the (Robust Logit) and the (Size-Constrained Robust) problems, where $K\in\mathbb N$ is the largest allowable assortment size. Both maxima range over **all** subsets (of size at most $K$ for $Y^*$), and both minima over the whole set $\mathcal V$.
--
--   The file also defines:
--
--   1. the **rectangular uncertainty set** $\prod_{i=0}^n [l_i,u_i]$ of Example 3.4, in which $v_0\in[l_0,u_0]$ and $v_i\in[l_i,u_i]$ for each product;
--   2. the **parametric value** of the proof of Theorem 3.8, for a real parameter $\lambda$,
--   $$
--   g_{\mathcal V}(\lambda)=\max_{S:\ |S|\le K}\ \min_{v\in\mathcal V}\ \frac{1}{v_0}\sum_{i\in S} v_i\,(r_i-\lambda);
--   $$
--   3. the **known-weights optimum** $\max_{S:\ |S|\le K} f(S,q)$ for a fixed parameter vector $q$.
--
--   These are the objects of Section 3.2 of the paper: Theorem 3.8 says that over a rectangular set, $Y^*$ equals the known-weights optimum at $q=(u_0,l_1,\dots,l_n)$.
--
--   **Formalization Note** Products are `Fin n`, so Lean index $i$ is the paper's product $i+1$. A parameter vector is a pair `p : ℝ × (Fin n → ℝ)` with `p.1` $=v_0$ and `p.2 i` the weight of product $i+1$. The revenue $f(S,v)$ is the published `ChoiceCDLP.MNL.mnlObjective`. Every minimum over $\mathcal V$ is a real infimum `sInf`, which is the attained minimum when $\mathcal V$ is compact, nonempty and positive (the theorems carry these hypotheses; Lean's `sInf` is $0$ on an empty set). Every maximum over assortments is a `Finset.sup'` over the finite, nonempty family of subsets of size at most $K$ (it contains $\emptyset$, for every $K$, $K=0$ included). Revenues are arbitrary reals, without the paper's ordering $r_1\ge\dots\ge r_n>0$, which no proof uses. The parameter $\lambda$ is named `lam` in Lean.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Sec. 3, pp. 5–6 (f(S, v), Robust Logit); Example 3.4, p. 8 (rectangular set); Sec. 3.2, p. 11 (Size-Constrained Robust); proof of Theorem 3.8, p. 12 (parametric value)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_RobustMNL_Static_Model

namespace RobustMNL.SizeCon

/-- The assortments of size at most `K`, `{S ⊆ 𝒜 : |S| ≤ K}` (Sec. 3.2, p. 11). -/
def sizeFeasible (n K : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun S => S.card ≤ K)

/-- The empty assortment has size `0 ≤ K`, so `sizeFeasible n K` is nonempty for every `K`. -/
theorem sizeFeasible_nonempty (n K : ℕ) : (sizeFeasible n K).Nonempty :=
  ⟨∅, by simp [sizeFeasible]⟩

/-- The optimal value of the (Size-Constrained Robust) problem,
`Y*(V) = max_{S ⊆ 𝒜 : |S| ≤ K} min_{v ∈ V} f(S, v)` (Sec. 3.2, p. 11): the maximum over **all**
assortments of size at most `K` of the RobustMNL.Static.worst-case revenue over the whole set `V`. -/
noncomputable def Ystar {n : ℕ} (V : Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ) (K : ℕ) : ℝ :=
  (sizeFeasible n K).sup' (sizeFeasible_nonempty n K) (RobustMNL.Static.worst V r)

/-- The parametric value
`max_{S : |S| ≤ K} min_{v ∈ V} (1/v₀) ∑_{i ∈ S} v_i (r_i − λ)` of the proof of Theorem 3.8
(p. 12), as a function of the real parameter `λ` (named `lam` in Lean). The inner minimum is a
real infimum over the whole set `V`, attained when `V` is compact, nonempty and positive. -/
noncomputable def paramValue {n : ℕ} (V : Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ) (K : ℕ)
    (lam : ℝ) : ℝ :=
  (sizeFeasible n K).sup' (sizeFeasible_nonempty n K)
    (fun S => sInf ((fun p : ℝ × (Fin n → ℝ) => (1 / p.1) * ∑ i ∈ S, p.2 i * (r i - lam)) '' V))

/-- The rectangular uncertainty set `∏_{i=0}^n [l_i, u_i]` of Example 3.4 (p. 8): the
no-purchase weight `v₀` ranges over `[l₀, u₀]` and the weight of each product `i` over
`[l i, u i]` (componentwise interval `Set.Icc l u` in `Fin n → ℝ`). -/
def box {n : ℕ} (l₀ u₀ : ℝ) (l u : Fin n → ℝ) : Set (ℝ × (Fin n → ℝ)) :=
  Set.Icc l₀ u₀ ×ˢ Set.Icc l u

/-- The size-constrained optimal revenue under a **known** parameter vector `q`,
`max_{S ⊆ 𝒜 : |S| ≤ K} f(S, q)` (Theorem 3.8, p. 11, right-hand side with
`q = (u₀, l₁, …, lₙ)`). -/
noncomputable def knownMax {n : ℕ} (r : Fin n → ℝ) (K : ℕ) (q : ℝ × (Fin n → ℝ)) : ℝ :=
  (sizeFeasible n K).sup' (sizeFeasible_nonempty n K) (fun S => RobustMNL.Static.rev r S q)

end RobustMNL.SizeCon


