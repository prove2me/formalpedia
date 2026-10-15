-- Prove2me | Definitions.Def_VehicleSharePricing_MultiNet_ClosedNet
-- name    : VehicleSharePricing_MultiNet_ClosedNet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:29:41.298306+00:00
-- url     : https://prove2.me/theorems/37323925-8627-4d36-9fd3-dedde991aa5e
-- title:
--   Closed product-form network of single-server and infinite-server stations: states, weights, $G(K)$ and availability
-- statement:
--   This file defines the stationary availability of a closed queueing network in **product form** (Baskett, Chandy, Muntz and Palacios, 1975), for networks made of two kinds of stations.
--
--   Let $S$ be a finite set of **single-server** stations and $T$ a finite set of **infinite-server** stations, and let $K\in\mathbb N$ identical items circulate among them. Each station carries a **load**: $a_s\in\mathbb R$ for $s\in S$ and $b_t\in\mathbb R$ for $t\in T$ (in a queueing network, the load of a station is its visit ratio divided by its service rate).
--
--   1. A **state** is a vector $x=(x_k)_{k\in S\sqcup T}$ of nonnegative integers with $\sum_k x_k=K$.
--   2. The **weight** of a state is
--   $$w(x)=\prod_{s\in S}a_s^{x_s}\cdot\prod_{t\in T}\frac{b_t^{x_t}}{x_t!},$$
--   with the convention $0^0=1$.
--   3. The **normalising constant** is $G(K)=\sum_{x}w(x)$, the sum over all states with $K$ items.
--   4. The **availability** of a single-server station $s$ is the stationary probability that $s$ holds at least one item,
--   $$\alpha_s(K)=\frac{1}{G(K)}\sum_{x:\,x_s\ge1}w(x).$$
--   With $K=0$ the only state is $x=0$, so $\alpha_s(0)=0$.
--
--   When the loads are positive, $w/G(K)$ is the stationary distribution of the closed network with exponential single-server stations and general infinite-server stations (by insensitivity only the mean service time of an infinite-server station matters). In the vehicle-sharing model of Benjaafar and Shen the single-server stations are the pick-up queues at the locations and the infinite-server stations are the transit queues on the origin–destination pairs.
--
--   **Formalization Note** This is a definition, not a theorem: the paper invokes the BCMP class (p. 6) without writing the stationary law, and this file writes it. States are functions on the disjoint union $S\oplus T$; every coordinate of a state is at most $K$, so the state space is a finite set. The availability is a quotient by $G(K)$; the model file only uses it with positive loads, for which $G(K)>0$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 5 (pick-up and transit queues), p. 6 (availability α_i, BCMP networks); Baskett, Chandy, Muntz, Palacios, J. ACM 22 (1975) 248–260

import Mathlib

namespace VehicleSharePricing.MultiNet

open Finset

/-! # Closed product-form network of single-server and infinite-server stations

A closed network with a finite set `S` of single-server stations and a finite set `T` of
infinite-server stations, circulating `K` identical items. In the BCMP product form
(Baskett, Chandy, Muntz and Palacios, 1975), a state `x : S ⊕ T → ℕ` with `∑ x = K` has
unnormalised weight `∏_{s ∈ S} a_s^{x_s} · ∏_{t ∈ T} b_t^{x_t} / x_t!`, where the load `a_s`
(resp. `b_t`) is the visit ratio of the station divided by its service rate. -/

/-- The state space: all `x : S ⊕ T → ℕ` with `∑_k x_k = K` (every coordinate is then `≤ K`). -/
def states (S T : Type*) [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T] (K : ℕ) :
    Finset (S ⊕ T → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (K + 1)).filter fun x => ∑ k, x k = K

/-- Product-form weight `∏_s a_s^{x_s} · ∏_t b_t^{x_t} / x_t!` of a state `x`
(with `0^0 = 1`, so a station of load `0` only contributes through the states that leave it empty). -/
noncomputable def weight {S T : Type*} [Fintype S] [Fintype T] (a : S → ℝ) (b : T → ℝ)
    (x : S ⊕ T → ℕ) : ℝ :=
  (∏ s, a s ^ x (Sum.inl s)) * ∏ t, b t ^ x (Sum.inr t) / ((x (Sum.inr t)).factorial : ℝ)

/-- Normalising constant `G(K) = ∑_{x ∈ states K} weight x`. -/
noncomputable def normConst {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (a : S → ℝ) (b : T → ℝ) (K : ℕ) : ℝ :=
  ∑ x ∈ states S T K, weight a b x

/-- Availability of the single-server station `s` with `K` items: the stationary probability
that `s` holds at least one item, `∑_{x : x_s ≥ 1} weight x / G(K)`. With `K = 0` it is `0`. -/
noncomputable def availability {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S]
    [DecidableEq T] (a : S → ℝ) (b : T → ℝ) (K : ℕ) (s : S) : ℝ :=
  (∑ x ∈ (states S T K).filter (fun x => 1 ≤ x (Sum.inl s)), weight a b x) / normConst a b K

end VehicleSharePricing.MultiNet


