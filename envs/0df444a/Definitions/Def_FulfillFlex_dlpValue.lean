-- Prove2me | Definitions.Def_FulfillFlex_dlpValue
-- name    : FulfillFlex_dlpValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:20.016104+00:00
-- url     : https://prove2.me/theorems/576c009a-0907-4aed-9ee1-a325ccfa38fe
-- title:
--   The deterministic LP (5) and its value $f(\mathbf r)$
-- statement:
--   Given a right side $m\in\mathbb R^{N+1}$ (in the paper $m=T\mu$, the mean demand over the horizon), inventories $r$ and abandonment probabilities $\alpha_j$, the **deterministic linear program** (DLP) is
--
--   $$
--   \begin{aligned}
--   f(r)=\min_{f,l\ge 0}\ &\sum_j\Bigl(p_jl_j+\sum_{j'}c_{jj'}f_{jj'}\Bigr)\\
--   \text{s.t. }&l_j+\sum_{0\le j'\le N}f_{j'j}\ge m_j &&\forall j,\\
--   &\sum_{j'\ne j}f_{j'j}\le(1-\alpha_j)(m_j-f_{jj}) &&\forall j,\\
--   &\sum_{0\le j'\le N}f_{jj'}\le r_j &&\forall j,\\
--   &f_{jj'}=0 &&\forall (j,j')\notin A.
--   \end{aligned}
--   $$
--
--   Here $f_{jj'}$ is the flow from DC $j$ to DC $j'$ and $l_j$ the lost sales at DC $j$. The second constraint says that a fraction $\alpha_j$ of the demand not filled locally abandons. The DLP replaces demand by its mean, and its value is the benchmark of Proposition 3.
--
--   **Formalization Note** `DLPFeasible` is the feasible set, `dlpObjective` the objective, and `dlpValue` the real infimum of the objective over the feasible set. Under Assumption 1 the objective is nonnegative on the feasible set, and for $m,r\ge0$ the pair $(f,l)=(0,m)$ is feasible, so that infimum is genuine. The right side $m$ is a parameter: the paper's $f(r)$ at horizon $T$ is `dlpValue A c p α (T • μ) r`.
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), display (5), p.16, restated p.49

import Mathlib
import Definitions.Def_FulfillFlex_DC

namespace FulfillFlex

/-- **Feasible set of the DLP (5).**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), display (5), p.16, restated with the
sign constraints on p.49. A pair `(f, l)` is feasible when

* `l_j + ∑_{0≤j'≤N} f_{j'j} ≥ m_j` for all `j`;
* `∑_{j'≠j} f_{j'j} ≤ (1 - α_j)(m_j - f_jj)` for all `j`;
* `∑_{0≤j'≤N} f_{jj'} ≤ r_j` for all `j`;
* `f_{jj'} = 0` for `(j, j') ∉ A`;
* `f ≥ 0` and `l ≥ 0`.

**Formalization Note** The right side `m` stands for the paper's `Tμ`: the paper's DLP at horizon
`T` is this one at `m = T • μ`. `f j j'` is the flow from DC `j` to DC `j'`. -/
structure DLPFeasible {N : ℕ} (A : Set (DC N × DC N)) (α : DC N → unitInterval)
    (m r : DC N → ℝ) (f : DC N → DC N → ℝ) (l : DC N → ℝ) : Prop where
  /-- First constraint of (5). -/
  demand : ∀ j, m j ≤ l j + ∑ j', f j' j
  /-- Second constraint of (5): the abandonment constraint. -/
  spillover : ∀ j, ∑ j' ∈ Finset.univ.erase j, f j' j ≤ (1 - (α j : ℝ)) * (m j - f j j)
  /-- Third constraint of (5): inventory. -/
  capacity : ∀ j, ∑ j', f j j' ≤ r j
  /-- Fourth constraint of (5): no flow off the links. -/
  link : ∀ j j', (j, j') ∉ A → f j j' = 0
  /-- Sign constraint on the flows, p.49. -/
  flow_nonneg : ∀ j j', 0 ≤ f j j'
  /-- Sign constraint on the lost sales, p.49. -/
  lost_nonneg : ∀ j, 0 ≤ l j

/-- The objective of the DLP (5), p.16: `∑_j (p_j l_j + ∑_{j'} c_{jj'} f_{jj'})`. -/
def dlpObjective {N : ℕ} (c : DC N → DC N → ℝ) (p : DC N → ℝ) (f : DC N → DC N → ℝ)
    (l : DC N → ℝ) : ℝ :=
  ∑ j, (p j * l j + ∑ j', c j j' * f j j')

/-- **The DLP value `f(r)`.**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), display (5), p.16: the minimum of the
objective over the feasible set.

**Formalization Note** The value is the real infimum of the objective values of feasible pairs.
Under Assumption 1 the objective is nonnegative on the feasible set, and for `m, r ≥ 0` the pair
`(0, m)` is feasible, so that set of values is nonempty and bounded below and the infimum is
genuine. The paper's `f(r)` at horizon `T` is `dlpValue A c p α (T • μ) r`. -/
noncomputable def dlpValue {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ) (p : DC N → ℝ)
    (α : DC N → unitInterval) (m r : DC N → ℝ) : ℝ :=
  sInf {v | ∃ f l, DLPFeasible A α m r f l ∧ v = dlpObjective c p f l}

end FulfillFlex


