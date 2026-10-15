-- Prove2me | Definitions.Def_VehicleSharePricing_DemandFree_ProductFormNetwork
-- name    : VehicleSharePricing_DemandFree_ProductFormNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:29:39.703924+00:00
-- url     : https://prove2.me/theorems/af068ee9-6c40-4989-aea2-2f082e425c5c
-- title:
--   Closed product-form network with single-server and infinite-server stations: states, weights, normalizing constant, busy probability
-- statement:
--   This file defines the stationary law of a **closed product-form (BCMP) network** with two kinds of stations: single-server stations indexed by a finite set $\iota$ and infinite-server stations indexed by a finite set $\kappa$.
--
--   The network is described by relative loads: $\rho_i$ for each single-server station $i\in\iota$ (visit rate divided by service rate) and $\sigma_k$ for each infinite-server station $k\in\kappa$. With population $K\in\mathbb N$, a **state** assigns a count $x_s\in\mathbb N$ to every station $s\in\iota\sqcup\kappa$ with $\sum_s x_s=K$. Its **weight** is
--
--   $$
--   w(x)=\prod_{i\in\iota}\rho_i^{\,x_i}\;\prod_{k\in\kappa}\frac{\sigma_k^{\,x_k}}{x_k!},
--   $$
--
--   with the convention $0^0=1$. The **normalizing constant** is $G(K)=\sum_{x}w(x)$, the sum over all states with population $K$, and the stationary probability that single-server station $i$ is busy is
--
--   $$
--   \mathbb P_K(x_i\ge 1)=\frac{1}{G(K)}\sum_{x:\,x_i\ge 1}w(x).
--   $$
--
--   This is the product form of Baskett, Chandy, Muntz and Palacios (1975) for exponential single-server stations and infinite-server stations (where, by insensitivity, only the mean service time matters). It is used here as a definition, not as a theorem: the vehicle-sharing model builds its availabilities on it.
--
--   **Formalization Note** States are functions $\iota\oplus\kappa\to\mathbb N$ in the finite set of those with entries at most $K$ and total $K$. The busy probability is a quotient in $\mathbb R$; it is meaningful when $G(K)>0$, which holds for positive loads.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 5 (closed queueing network with single-server pick-up queues and infinite-server transit queues) and p. 6 (BCMP networks, Baskett et al. 1975)

import Mathlib

namespace VehicleSharePricing.DemandFree

open Finset

/-- A closed queueing network with single-server stations indexed by `ι` and infinite-server
stations indexed by `κ`, described by the relative loads of its stations: `ssLoad i` is the
relative load (visit rate divided by service rate) of single-server station `i`, and `isLoad k`
the relative load of infinite-server station `k`. -/
structure ProductFormNetwork (ι κ : Type*) where
  ssLoad : ι → ℝ
  isLoad : κ → ℝ

namespace ProductFormNetwork

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The states with population `K`: a count `x s ∈ ℕ` at every station `s`, with total `K`. -/
def stateSpace (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (K : ℕ) :
    Finset (ι ⊕ κ → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (K + 1)).filter fun x => ∑ s, x s = K

/-- The (unnormalized) product-form weight of a state `x`:
`∏_i ρ_i^{x_i} · ∏_k σ_k^{x_k} / x_k!`, with `ρ = ssLoad` and `σ = isLoad` (and `0^0 = 1`). -/
noncomputable def weight (net : ProductFormNetwork ι κ) (x : ι ⊕ κ → ℕ) : ℝ :=
  (∏ i, net.ssLoad i ^ x (Sum.inl i)) *
    ∏ k, net.isLoad k ^ x (Sum.inr k) / ((x (Sum.inr k)).factorial : ℝ)

/-- The normalizing constant `G(K)`: the total weight of the states with population `K`. -/
noncomputable def normConst (net : ProductFormNetwork ι κ) (K : ℕ) : ℝ :=
  ∑ x ∈ stateSpace ι κ K, net.weight x

/-- The stationary probability, with population `K`, that single-server station `i` is busy
(holds at least one customer): the weight share of the states with `x_i ≥ 1`. -/
noncomputable def busyProb (net : ProductFormNetwork ι κ) (K : ℕ) (i : ι) : ℝ :=
  (∑ x ∈ (stateSpace ι κ K).filter (fun x => 1 ≤ x (Sum.inl i)), net.weight x) /
    net.normConst K

end ProductFormNetwork

end VehicleSharePricing.DemandFree


