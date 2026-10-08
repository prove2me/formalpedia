-- Prove2me | Definitions.Def_ConstrNestedLogit_Pricing_Model
-- name    : ConstrNestedLogit_Pricing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:13.268985+00:00
-- url     : https://prove2.me/theorems/67bb7d1f-0969-48aa-bbbf-4ff4ad59c48a
-- title:
--   §6, pp. 23–24 — virtual products, the pricing feasible set $\mathcal C_i$, problem (7) and the coefficients $f_{ij}(u)$
-- statement:
--   This module sets up the joint assortment and pricing problem of §6 of Gallego and Topaloglu as a constrained assortment problem over **virtual products**.
--
--   Each nest $i$ has $p$ products $P=\{1,\dots,p\}$, and each product can be offered at one of $b$ price levels $B=\{1,\dots,b\}$. Offering product $k$ at price level $l$ in nest $i$ earns the price $\rho_{ik}^l$ and gives the product the preference weight $\nu_{ik}^l$; the relation between $\rho_{ik}^l$ and $\nu_{ik}^l$ is arbitrary. Every pair (product, price level) is a virtual product, so there are $n=pb$ virtual products $N=\{1,\dots,n\}$, and $N_k\subseteq N$ denotes the $b$ virtual products of product $k$. A virtual product $j\in N_k$ for price level $l$ has revenue $r_{ij}=\rho_{ik}^l$ and preference weight $v_{ij}=\nu_{ik}^l$.
--
--   The module defines:
--
--   1. **Virtual product map.** A map $\pi:N\to P$ sending each virtual product to its product, with fibers $N_k=\pi^{-1}(k)$ of size $|N_k|=b$ for every $k\in P$. The fibers are disjoint and cover $N$.
--   2. **Feasible set.** The feasible assortments of nest $i$ are
--   $$
--   \mathcal C_i=\Big\{S_i\in\{0,1\}^n:\ \sum_{j\in N_k}S_{ij}\le 1\ \ \forall k\in P\Big\},
--   $$
--   so each product is offered at no more than one price level (and possibly not at all).
--   3. **Problem (7).** For $u\in\mathbb R$, the objective $V_i(S_i)\,(R_i(S_i)-u)$, where $V_i(S_i)=\sum_{j\in S_i}v_{ij}$ and $R_i(S_i)=\sum_{j\in S_i}r_{ij}v_{ij}/V_i(S_i)$ are the published nested logit quantities. An assortment $S_i$ is an *optimal solution of (7) at $u$* if $S_i\in\mathcal C_i$ and $V_i(S_i)(R_i(S_i)-u)\ge V_i(S_i')(R_i(S_i')-u)$ for every $S_i'\in\mathcal C_i$.
--   4. **Coefficients.** The linear functions $f_{ij}(u)=v_{ij}\,(r_{ij}-u)$, the objective coefficients of problem (12).
--
--   These are the objects of the paper's joint assortment and pricing result: a small collection of candidate assortments per nest that contains an optimal solution of (7) for every $u\ge 0$.
--
--   **Formalization Note** The virtual products are `Fin n` (0-based) and the products `Fin p`; $N_k$ is the fiber of a map `prod : Fin n → Fin p`, and the price level of a virtual product is left implicit (the fiber of size $b$ is in bijection with $B$). The prices and weights are the published instance's `r i j` and `v i j`. Assortments are `Finset (Fin n)`. The published `V` is $v_{i0}+\sum_{j\in S}v_{ij}$; the theorems of this mission assume $v_{i0}=0$, which gives the paper's $V_i(S_i)$.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, pp. 23–24, §6 (virtual products, C_i), p. 14, problem (7), p. 24, problem (12)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

namespace ConstrNestedLogit.Pricing

open NestedLogitVariants.LP

variable {ι : Type*} {n p : ℕ}

/-- Virtual products (§6, p. 23). `prod : Fin n → Fin p` sends virtual product `j` to the product
`k ∈ P = Fin p` it is a copy of; the fiber `N_k = {j | prod j = k}` is the set of virtual products of
product `k`, one per price level. `IsVirtualProductMap prod b` says `|N_k| = b` for every `k`
(the fibers are automatically pairwise disjoint and cover `Fin n`, so `n = p b`). -/
def IsVirtualProductMap (prod : Fin n → Fin p) (b : ℕ) : Prop :=
  ∀ k : Fin p, (Finset.univ.filter (fun j => prod j = k)).card = b

/-- The feasible set `C_i` of §6 (p. 24): `S_i ∈ {0,1}^n` with `∑_{j ∈ N_k} S_ij ≤ 1` for every
product `k`, i.e. at most one virtual product (one price level) of each product is offered. -/
def PricingFeasible (prod : Fin n → Fin p) (S : Finset (Fin n)) : Prop :=
  ∀ k : Fin p, (S.filter (fun j => prod j = k)).card ≤ 1

/-- The objective of problem (7) (p. 14) in nest `i` at `u`: `V_i(S_i) (R_i(S_i) − u)`. -/
noncomputable def obj7 (I : Instance ι n) (i : ι) (u : ℝ) (S : Finset (Fin n)) : ℝ :=
  V I i S * (R I i S - u)

/-- `S` is an optimal solution of problem (7) in nest `i` at `u` when the feasible set is the
pricing set `C_i` of §6: `S ∈ C_i` and `V_i(S)(R_i(S) − u) ≥ V_i(S')(R_i(S') − u)` for every
`S' ∈ C_i`. -/
def IsOptimal7 (I : Instance ι n) (prod : Fin n → Fin p) (i : ι) (u : ℝ)
    (S : Finset (Fin n)) : Prop :=
  PricingFeasible prod S ∧ ∀ S' : Finset (Fin n), PricingFeasible prod S' → obj7 I i u S' ≤ obj7 I i u S

/-- The linear function `f_ij(u) = v_ij (r_ij − u)` of p. 24: the objective coefficient of virtual
product `j` in problem (12). (The paper's `f_i0(u) = 0` is the constant `0`.) -/
def coeff (I : Instance ι n) (i : ι) (u : ℝ) (j : Fin n) : ℝ :=
  I.v i j * (I.r i j - u)

end ConstrNestedLogit.Pricing


