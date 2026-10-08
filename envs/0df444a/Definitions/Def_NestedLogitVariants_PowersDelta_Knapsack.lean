-- Prove2me | Definitions.Def_NestedLogitVariants_PowersDelta_Knapsack
-- name    : NestedLogitVariants_PowersDelta_Knapsack
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:47:57.618987+00:00
-- url     : https://prove2.me/theorems/de118153-4479-4efb-96c0-13c74935f3bd
-- title:
--   Appendix A.5, pp. 49–51 — large and small products, q, ℘_L, ℘_S, the continuous knapsack (33), ẑ(J_L, J_S) and Ŝ(J_L, J_S)
-- statement:
--   Fix a nest $i$ (subscripts omitted: $v_0 = v_{i0}$, $v_j = v_{ij}$, $r_j = r_{ij}$), a constant $\delta > 1$ and a level $l \in \mathbb Z$. A product $j$ is **large** if $v_j > (\delta - 1)\delta^{l-1}$ and **small** if $v_j \le (\delta - 1)\delta^{l-1}$; $N_L$ and $N_S$ are the sets of large and small products. Let $q = \lceil \delta/(\delta - 1) \rceil$, and let $\wp_L$ ($\wp_S$) be the collection of subsets of $N_L$ ($N_S$) with at most $q$ elements.
--
--   For $J_L \subseteq N_L$ and $J_S \subseteq N_S$, the continuous knapsack (33) is
--   $$\max \sum_{j=1}^n r_j v_j z_j \quad \text{s.t.} \quad v_0 + \sum_{j=1}^n v_j z_j \le \delta^l,\ z_j = 1\ (j \in J_L \cup J_S),\ z_j = 0\ (j \in N_L \setminus J_L),\ 0 \le z_j \le \mathbf 1\big(r_j v_j \le \min_{k \in J_S} r_k v_k\big)\ (j \in N_S \setminus J_S).$$
--   Its solution $\hat z(J_L, J_S)$ is the greedy one described on p. 50: the products of $J_L \cup J_S$ are put in, the large products outside $J_L$ and the small products whose variable is fixed at zero are left out, and the remaining small products are added in nonincreasing order of $r_j$ into the capacity that is left, the first that does not fit taking a fractional value. Finally
--   $$\hat S(J_L, J_S) = \{ j \in N : \hat z_j(J_L, J_S) = 1 \}.$$
--
--   These are the objects of Proposition 15, which shows that one of the assortments $\hat S(J_L, J_S)$ solves problem (32), the single-nest form of (15), within a factor $\delta$.
--
--   **Formalization Note** The capacity row of (33) is stated as $v_0 + \sum_j v_j z_j \le \delta^l$. The page prints $\sum_j v_j z_j \le \delta^l$, without $v_0$; its own proof of Proposition 15 concludes that $\hat S(\tilde J_L, A_S)$ satisfies the upper bound of (32), $v_0 + \sum_j v_j z_j \le \delta^l$, which needs $v_0$ in the row. When $J_S = \emptyset$ the minimum over $J_S$ is $+\infty$ and every small product is free. The greedy order is the index order, which is nonincreasing in $r_j$ by the standing ordering $r_1 \ge \dots \ge r_n$. When the products forced to one overflow the capacity, (33) is infeasible and the definition simply keeps them; no statement uses such a pair.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 49–51, Appendix A.5, displays (32), (33) and the definitions of N_L, N_S, q, ℘_L, ℘_S, ẑ(J_L, J_S), Ŝ(J_L, J_S)

import Mathlib
import Definitions.Def_NestedLogitVariants_PowersDelta_Levels

namespace NestedLogitVariants.PowersDelta

/-! Appendix A.5 (pp. 49–51): the objects of Proposition 15 for a single nest `i` of an instance
(`v_0 = v_{i0}`, `v_j = v_{ij}`, `r_j = r_{ij}`), a level `l ∈ ℤ` and `δ > 1`. -/

variable {ι : Type*} {n : ℕ}

/-- The large products `N_L = {j : v_j > (δ − 1) δ^{l−1}}` (p. 49). -/
noncomputable def largeSet (I : Instance ι n) (i : ι) (δ : ℝ) (l : ℤ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (δ - 1) * δ ^ (l - 1) < I.v i j)

/-- The small products `N_S = {j : v_j ≤ (δ − 1) δ^{l−1}}` (p. 49). -/
noncomputable def smallSet (I : Instance ι n) (i : ι) (δ : ℝ) (l : ℤ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => I.v i j ≤ (δ - 1) * δ ^ (l - 1))

/-- `q = ⌈δ/(δ − 1)⌉` (p. 50). -/
noncomputable def qParam (δ : ℝ) : ℕ := ⌈δ / (δ - 1)⌉₊

/-- `℘_L`: the subsets of `N_L` of cardinality at most `q` (p. 51). -/
def wpL (I : Instance ι n) (i : ι) (δ : ℝ) (l : ℤ) : Set (Finset (Fin n)) :=
  {J | J ⊆ largeSet I i δ l ∧ J.card ≤ qParam δ}

/-- `℘_S`: the subsets of `N_S` of cardinality at most `q` (p. 51). -/
def wpS (I : Instance ι n) (i : ι) (δ : ℝ) (l : ℤ) : Set (Finset (Fin n)) :=
  {J | J ⊆ smallSet I i δ l ∧ J.card ≤ qParam δ}

/-- The small products of `N_S ∖ J_S` whose variable is free in (33): those with
`r_j v_j ≤ min_{k ∈ J_S} r_k v_k` (all of `N_S` when `J_S = ∅`). -/
noncomputable def eligible (I : Instance ι n) (i : ι) (δ : ℝ) (l : ℤ) (JS : Finset (Fin n)) :
    Finset (Fin n) :=
  (smallSet I i δ l \ JS).filter (fun j => ∀ k ∈ JS, I.r i j * I.v i j ≤ I.r i k * I.v i k)

/-- The capacity left in (33) after the products of `J_L ∪ J_S` are put in, with the capacity
row read as `v_0 + ∑_j v_j z_j ≤ δ^l` (see `zhat`). -/
noncomputable def residual (I : Instance ι n) (i : ι) (δ : ℝ) (l : ℤ) (JL JS : Finset (Fin n)) :
    ℝ :=
  δ ^ l - (I.vnp i + ∑ j ∈ JL ∪ JS, I.v i j)

/-- `ẑ(J_L, J_S)`, the greedy solution of the continuous knapsack (33) described on p. 50:
`z_j = 1` on `J_L ∪ J_S`, `z_j = 0` on `N_L ∖ J_L` and on the small products that are not free,
and the free small products filled in index order (which is nonincreasing order of the ratio
`r_j`) into the remaining capacity, the first that does not fit taking a fractional value.
The capacity row is `v_0 + ∑_j v_j z_j ≤ δ^l`: the page prints `∑_j v_j z_j ≤ δ^l`, a slip
against its own proof, which needs the upper bound of (32). -/
noncomputable def zhat (I : Instance ι n) (i : ι) (δ : ℝ) (l : ℤ) (JL JS : Finset (Fin n))
    (j : Fin n) : ℝ :=
  if j ∈ JL ∪ JS then 1
  else if j ∈ eligible I i δ l JS then
    max 0 (min 1 ((residual I i δ l JL JS -
      ∑ k ∈ (eligible I i δ l JS).filter (fun k => k < j), I.v i k) / I.v i j))
  else 0

/-- `Ŝ(J_L, J_S) = {j ∈ N : ẑ_j(J_L, J_S) = 1}` (p. 50). -/
noncomputable def Shat (I : Instance ι n) (i : ι) (δ : ℝ) (l : ℤ) (JL JS : Finset (Fin n)) :
    Finset (Fin n) :=
  Finset.univ.filter (fun j => zhat I i δ l JL JS j = 1)

end NestedLogitVariants.PowersDelta


