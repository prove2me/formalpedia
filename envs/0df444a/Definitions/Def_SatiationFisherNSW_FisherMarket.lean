-- Prove2me | Definitions.Def_SatiationFisherNSW_FisherMarket
-- name    : SatiationFisherNSW_FisherMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:00.621033+00:00
-- url     : https://prove2.me/theorems/3872f368-1ecb-4ae1-add8-3d1bf93432bd
-- title:
--   Fisher market with utility and earning limits; thrifty and modest equilibrium; money clearing
-- statement:
--   A **Fisher market with utility and earning limits** has a finite set $B$ of buyers and a finite set $G$ of divisible goods, each in unit supply and sold by its own seller. Buyer $i$ has values $u_{ij}\ge 0$, an endowment $m_i\ge 0$ of money and a utility cap $c_i>0$; seller $j$ has an earning cap $d_j>0$. The **budget-additive utility** of a bundle $y=(y_j)_{j\in G}$ is
--   $$
--   u_i(y)=\min\Bigl(c_i,\ \sum_{j\in G}u_{ij}y_j\Bigr).
--   $$
--
--   Given prices $p$, good $j$ is a **maximum bang-per-buck (MBB) good** of buyer $i$ if $u_{ij}>0$ and $u_{ij}/p_j\ge u_{ik}/p_k$ for every $k$ (a zero price counts as an infinite ratio). The **MBB ratio** is $\alpha_i=\max_k u_{ik}/p_k$, and the **active budget** is $m^a_i=\min(m_i,c_i/\alpha_i)$. A bundle $y\ge 0$ is a **demand bundle** of $i$ if $\sum_j p_jy_j\le m_i$ and $u_i(y)\ge u_i(z)$ for every $z\ge0$ with $\sum_j p_jz_j\le m_i$; it is **thrifty** if $y_j>0$ only for MBB goods, and **modest** if $\sum_j u_{ij}y_j\le c_i$. The **modest supply** of seller $j$ is $e_j=\min(1,d_j/p_j)$, read as $1$ when $p_j=0$.
--
--   A **thrifty and modest equilibrium** (Definition 2.1) is a pair $(x,p)$ with
--
--   1. $p\ge 0$;
--   2. $x_j=\sum_i x_{ij}\le e_j$ for every good $j$;
--   3. every $x_i$ a thrifty and modest demand bundle of buyer $i$;
--   4. Walras' law $p_j(e_j-x_j)=0$ for every good $j$.
--
--   Buyer $i$ is **capped** if $u_i(x_i)=c_i$. The set $B_0$ consists of the buyers with $u_{ij}>0$ for some good of price $0$. The market is **money clearing** (Definition 2.2) if
--   $$
--   \sum_{i\in\hat B}m_i\le\sum_{j\in N(\hat B)}d_j\qquad\text{for every }\hat B\subseteq B,
--   $$
--   where $N(\hat B)=\{j\in G\mid u_{ij}>0\text{ for some }i\in\hat B\}$.
--
--   These are the market objects of the whole mission: the rounding algorithm for Nash social welfare starts from a thrifty and modest equilibrium of such a market.
--
--   **Formalization Note** The MBB condition is cross-multiplied, $u_{ik}p_j\le u_{ij}p_k$, so zero prices need no $\infty$. The demand problem has no box $y_j\le 1$; unit supply enters only through $x_j\le e_j$. The MBB ratio is a supremum over the finite set $G$, with $0/0=0$ as in the paper; it is used only for buyers outside $B_0$.
-- source:
--   Garg, Hoefer, Mehlhorn, Satiation in Fisher markets and approximation of Nash social welfare, arXiv:1707.04428v3 (31 Jul 2019), https://arxiv.org/abs/1707.04428v3, §2, pp.6–7 (Definitions 2.1, 2.2), Definition 3.1, p.9, and p.24 ($G_0$, $B_0$)

import Mathlib
open scoped Classical

namespace SatiationFisherNSW

/-- A linear Fisher market with utility and earning limits (Garg, Hoefer, Mehlhorn,
arXiv:1707.04428v3, §2, "Fisher Markets with Earning and Utility Limits", p.6).

There is a set `B` of buyers and a set `G` of divisible goods, each good in unit supply and owned
by its own seller. Buyer `i` has a value `u i j ≥ 0` for a unit of good `j`, an endowment
`m i ≥ 0` of money and a utility cap `c i > 0`; seller `j` has an earning cap `d j > 0`.

**Formalization Note** Buyers and goods are arbitrary finite types (`Fintype` where sums are
taken); the data are real numbers. p.6 additionally assumes integer data "for the algorithms";
nothing in §4 uses it, and real data is the §4 setting (p.7). -/
structure FisherMarket (B G : Type*) where
  /-- The value `u_{ij}` of buyer `i` for a unit of good `j`. -/
  u : B → G → ℝ
  /-- The endowment (budget) `m_i` of buyer `i`. -/
  m : B → ℝ
  /-- The utility cap `c_i` of buyer `i`. -/
  c : B → ℝ
  /-- The earning cap `d_j` of the seller of good `j`. -/
  d : G → ℝ
  u_nonneg : ∀ i j, 0 ≤ u i j
  m_nonneg : ∀ i, 0 ≤ m i
  c_pos : ∀ i, 0 < c i
  d_pos : ∀ j, 0 < d j

namespace FisherMarket

variable {B G : Type*} [Fintype B] [Fintype G] (M : FisherMarket B G)

/-- The budget-additive utility `u_i(y) = min(c_i, Σ_j u_{ij} y_j)` of buyer `i` for a bundle
`y` (arXiv:1707.04428v3, p.6). -/
noncomputable def utility (i : B) (y : G → ℝ) : ℝ :=
  min (M.c i) (∑ j, M.u i j * y j)

/-- Good `j` is a maximum bang-per-buck (MBB) good of buyer `i` at prices `p`
(arXiv:1707.04428v3, p.6: `u_{ij}/p_j = α_i`, where `α_i = 1/λ_i`, `λ_i = min_k p_k/u_{ik}`).

**Formalization Note** The ratio `u_{ij}/p_j` is compared with every `u_{ik}/p_k` after
cross-multiplication, `u_{ik} p_j ≤ u_{ij} p_k`, so that a zero price gives an infinite ratio
(the paper's `α_i = ∞` for buyers interested in a zero-price good) instead of Lean's `x/0 = 0`.
`u_{ij} > 0` is required: a good of value `0` is never an MBB good of a buyer who values some
good. -/
def IsMBB (p : G → ℝ) (i : B) (j : G) : Prop :=
  0 < M.u i j ∧ ∀ k, M.u i k * p j ≤ M.u i j * p k

/-- `y` is a demand bundle of buyer `i` at prices `p` (arXiv:1707.04428v3, p.6): a bundle
`y ≥ 0` within the budget, `Σ_j p_j y_j ≤ m_i`, that maximizes `u_i` among all such bundles.

**Formalization Note** The competing bundles range over all `z ≥ 0` with `Σ_j p_j z_j ≤ m_i`,
without a box `z_j ≤ 1`: this is the reading under which an uncapped buyer spends its whole
budget (Lemma 4.3(a), p.24) and the maximal utility is `min{c_i, m_i α_i}` (proof of Lemma 3.5,
p.14). Unit supply is enforced by the market condition `x_j ≤ e_j` of the equilibrium. -/
def IsDemandBundle (p : G → ℝ) (i : B) (y : G → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ ∑ j, p j * y j ≤ M.m i ∧
    ∀ z : G → ℝ, (∀ j, 0 ≤ z j) → ∑ j, p j * z j ≤ M.m i → M.utility i z ≤ M.utility i y

/-- A bundle is thrifty (MBB) if it consists only of MBB goods: `y_j > 0` only if `j` is an MBB
good of `i` (arXiv:1707.04428v3, p.6, item 2). -/
def IsThrifty (p : G → ℝ) (i : B) (y : G → ℝ) : Prop :=
  ∀ j, 0 < y j → M.IsMBB p i j

/-- A bundle is modest if `Σ_j u_{ij} y_j ≤ c_i` (arXiv:1707.04428v3, p.6, item 1). -/
def IsModest (i : B) (y : G → ℝ) : Prop :=
  ∑ j, M.u i j * y j ≤ M.c i

/-- The modest supply `e_j = min(1, d_j/p_j)` of seller `j` (arXiv:1707.04428v3, p.6, item 3).

**Formalization Note** At `p_j = 0` the paper's `d_j/p_j` is `+∞`, so `e_j = 1`; this case is
written out because Lean's `d_j/0` is `0`. -/
noncomputable def modestSupply (p : G → ℝ) (j : G) : ℝ :=
  if p j = 0 then 1 else min 1 (M.d j / p j)

/-- A thrifty and modest (market) equilibrium `(x, p)` (arXiv:1707.04428v3, Definition 2.1,
p.6): (1) `p ≥ 0`; (2) `e_j` is the modest supply; (3) `x_j = Σ_i x_{ij} ≤ e_j` (no
overallocation); (4) every `x_i` is a thrifty and modest demand bundle; (5) Walras' law
`p_j (e_j − x_j) = 0`.

**Formalization Note** `x i j` is the amount of good `j` bought by buyer `i`; `x_{ij} ≥ 0` is
part of the demand-bundle condition. p.6 writes `Σ_i x_{ij} = 1` for an allocation, which
conditions (3) and (5) contradict whenever `p_j > d_j`; the allocation is therefore only required
to satisfy (3). -/
def IsEquilibrium (x : B → G → ℝ) (p : G → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧
  (∀ j, ∑ i, x i j ≤ M.modestSupply p j) ∧
  (∀ i, M.IsDemandBundle p i (x i) ∧ M.IsThrifty p i (x i) ∧ M.IsModest i (x i)) ∧
  (∀ j, p j * (M.modestSupply p j - ∑ i, x i j) = 0)

/-- Buyer `i` is capped in the allocation `x` if `u_i(x_i) = c_i` (arXiv:1707.04428v3, p.6). -/
def IsCapped (x : B → G → ℝ) (i : B) : Prop :=
  M.utility i (x i) = M.c i

/-- The goods `N(B̂) = {j ∈ G | u_{ij} > 0 for some i ∈ B̂}` that some buyer of `B̂` values
(arXiv:1707.04428v3, p.6). -/
noncomputable def N (S : Finset B) : Finset G :=
  Finset.univ.filter (fun j => ∃ i ∈ S, 0 < M.u i j)

/-- The market is money clearing (arXiv:1707.04428v3, Definition 2.2, eq. (1), p.7):
`∀ B̂ ⊆ B, Σ_{i∈B̂} m_i ≤ Σ_{j∈N(B̂)} d_j`. -/
def IsMoneyClearing : Prop :=
  ∀ S : Finset B, ∑ i ∈ S, M.m i ≤ ∑ j ∈ M.N S, M.d j

/-- Buyer `i` belongs to `B₀ = {i | u_{ij} > 0 for some j ∈ G₀}`, where `G₀ = {j | p_j = 0}`
(arXiv:1707.04428v3, p.24). These are the buyers with infinite MBB ratio. -/
def InB0 (p : G → ℝ) (i : B) : Prop :=
  ∃ j, p j = 0 ∧ 0 < M.u i j

/-- The MBB ratio `α_i = max_k u_{ik}/p_k` of buyer `i` (arXiv:1707.04428v3, p.6, and proof of
Lemma 3.5, p.14).

**Formalization Note** It is used only for buyers `i ∉ B₀`. For such a buyer every good with
`p_k = 0` has `u_{ik} = 0`, and the term `0/0` is `0`, the paper's own convention (p.6); the
maximum over the finite type `G` is a `⨆`. For `i ∈ B₀` the paper's `α_i` is `+∞` and this
value is not used: the procedure treats zero-price goods by the rule of Appendix B. -/
noncomputable def mbbRatio (p : G → ℝ) (i : B) : ℝ :=
  ⨆ k, M.u i k / p k

/-- The active budget `m^a_i = min(m_i, c_i/α_i)` of buyer `i` (arXiv:1707.04428v3,
Definition 3.1, p.9).

**Formalization Note** Used only for buyers `i ∉ B₀` who buy some good, for whom `α_i` is
finite and positive. -/
noncomputable def activeBudget (p : G → ℝ) (i : B) : ℝ :=
  min (M.m i) (M.c i / M.mbbRatio p i)

end FisherMarket

end SatiationFisherNSW


