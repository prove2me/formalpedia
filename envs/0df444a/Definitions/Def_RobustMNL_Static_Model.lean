-- Prove2me | Definitions.Def_RobustMNL_Static_Model
-- name    : RobustMNL_Static_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:47.57208+00:00
-- url     : https://prove2.me/theorems/916952ac-c48a-484a-93fc-870884d1c431
-- title:
--   Sec. 3, pp. 5–6 — MNL parameters v ∈ ℝⁿ⁺¹₊₊, revenue f(S, v), worst-case revenue, Z*(V) (Robust Logit) and the smallest-cardinality optimal assortment S*(V)
-- statement:
--   A seller has $n$ products $\mathcal A = \{1, \dots, n\}$; product $i$ earns revenue $r_i$. Customers choose according to a **multinomial logit model** with parameter vector $v = (v_0, v_1, \dots, v_n) \in \mathbb R^{n+1}_{++}$: $v_0$ is the weight of the no-purchase option and $v_i$ the preference weight of product $i$, all strictly positive. If the assortment $S \subseteq \mathcal A$ is offered, a customer buys $i \in S$ with probability $\phi_i(S,v) = v_i/(v_0 + \sum_{\ell \in S} v_\ell)$, and the expected revenue is
--   $$f(S, v) = \sum_{i \in S} r_i\,\phi_i(S,v) = \frac{\sum_{i\in S} r_i v_i}{v_0 + \sum_{i \in S} v_i}.$$
--
--   The parameters are uncertain and range over an **uncertainty set** $\mathcal V \subseteq \mathbb R^{n+1}_{++}$, compact and nonempty. The **worst-case revenue** of $S$ is $\min_{v \in \mathcal V} f(S, v)$, and the **Robust Logit** problem is
--   $$Z^*(\mathcal V) = \max_{S \subseteq \mathcal A}\ \min_{v \in \mathcal V} f(S, v).$$
--   $S^*(\mathcal V)$ denotes an optimal assortment of this problem with the **smallest cardinality** among all optimal assortments. For a single parameter vector, $S^*_v = S^*(\{v\})$ and $Z^*_v = Z^*(\{v\})$.
--
--   This file defines the objects every statement of the mission is written in: positivity of a parameter vector, $f$, the worst-case revenue, $Z^*(\mathcal V)$, and the predicate "$S$ is an optimal assortment of smallest cardinality".
--
--   **Formalization Note** Products are `Fin n`, so Lean index $i$ is the paper's product $i+1$. A parameter vector is a pair `p : ℝ × (Fin n → ℝ)` with `p.1` $= v_0$ and `p.2 i` $= v_{i+1}$; `IsPos p` is $v \in \mathbb R^{n+1}_{++}$. $f(S,v)$ is the published `ChoiceCDLP.MNL.mnlObjective` (`rev r S p`); the choice probabilities $\phi_i$ are described above only to explain $f$ and are not declared in this file. The minimum over $\mathcal V$ is a real infimum (`sInf`), which equals the attained minimum exactly when $\mathcal V$ is compact, nonempty and positive; every theorem of the mission carries these three hypotheses. $Z^*$ is a maximum over **all** $2^n$ subsets. $S^*(\mathcal V)$ is not a choice function but the predicate `IsSmallestOptimal V r S`, so a theorem about $S^*(\mathcal V)$ holds for every optimal assortment of smallest cardinality. Revenues are arbitrary real numbers (the paper's ordering $r_1 \ge \dots \ge r_n > 0$ is assumed "without loss of generality" and used by no statement here).
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Sec. 3, pp. 5–6 (the definition of φ_i and f, p. 5; (Robust Logit), S*(V) with footnote 1, S*_v and Z*_v, p. 6)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective

namespace RobustMNL.Static

/-- A multinomial logit parameter vector `v = (v₀, v₁, …, vₙ)` is encoded as
`p : ℝ × (Fin n → ℝ)`: `p.1` is the no-purchase weight `v₀` and `p.2 i` is the preference
weight of product `i + 1` of the paper (Lean products are `Fin n`, 0-based).
`IsPos p` says `v ∈ ℝⁿ⁺¹₊₊`, i.e. every component is strictly positive (Sec. 3, p. 5). -/
def IsPos {n : ℕ} (p : ℝ × (Fin n → ℝ)) : Prop :=
  0 < p.1 ∧ ∀ i, 0 < p.2 i

/-- The expected revenue `f(S, v) = ∑_{i ∈ S} r_i v_i / (v₀ + ∑_{i ∈ S} v_i)` of offering the
assortment `S` under parameters `p = (v₀, v)` (Sec. 3, p. 5). This is the published
`ChoiceCDLP.MNL.mnlObjective` with scores `r`, weights `p.2` and no-purchase weight `p.1`. -/
noncomputable def rev {n : ℕ} (r : Fin n → ℝ) (S : Finset (Fin n)) (p : ℝ × (Fin n → ℝ)) : ℝ :=
  ChoiceCDLP.MNL.mnlObjective p.2 r p.1 S

/-- The worst-case expected revenue `min_{v ∈ V} f(S, v)` of the assortment `S` over the
uncertainty set `V` (Sec. 3, p. 6), written as a real infimum. Real `sInf` is `0` on an empty or
unbounded-below set; every theorem using it assumes, as the paper does, that `V` is compact,
nonempty and contained in `ℝⁿ⁺¹₊₊`, and then `v ↦ f(S, v)` is continuous on `V`, so this
infimum is the attained minimum. -/
noncomputable def worst {n : ℕ} (V : Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  sInf ((fun p => rev r S p) '' V)

/-- The optimal value of the (Robust Logit) problem,
`Z*(V) = max_{S ⊆ 𝒜} min_{v ∈ V} f(S, v)` (Sec. 3, p. 6), the maximum over **all** subsets
of the product set. -/
noncomputable def Zstar {n : ℕ} (V : Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty (worst V r)

/-- `S` is an optimal assortment of the (Robust Logit) problem with the smallest cardinality
among all optimal assortments: the paper's `S*(V)` with its tie-breaking rule (Sec. 3, p. 6,
footnote 1). With `V = {v}` this is `S*_v`, and `Zstar {v} r` is `Z*_v`. -/
def IsSmallestOptimal {n : ℕ} (V : Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ)
    (S : Finset (Fin n)) : Prop :=
  worst V r S = Zstar V r ∧ ∀ S' : Finset (Fin n), worst V r S' = Zstar V r → S.card ≤ S'.card

end RobustMNL.Static


