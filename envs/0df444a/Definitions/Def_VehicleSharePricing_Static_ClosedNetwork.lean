-- Prove2me | Definitions.Def_VehicleSharePricing_Static_ClosedNetwork
-- name    : VehicleSharePricing_Static_ClosedNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:29:42.620823+00:00
-- url     : https://prove2.me/theorems/89a4bf63-1a3c-4d46-81bf-05c5be877421
-- title:
--   Product-form closed network with single-server and infinite-server stations: states, weights, $G(K)$, busy probabilities
-- statement:
--   This file sets up the **product-form distribution** of a closed queueing network with a finite set $S$ of stations, each of which is either a single-server station or an infinite-server station, and $K$ circulating customers.
--
--   1. A **population vector** is $x=(x_s)_{s\in S}\in\mathbb N^S$ with $\sum_{s\in S}x_s=K$; these vectors form the finite state space.
--   2. Every station $s$ carries a **relative load** $\rho_s$ (its visit ratio divided by its service rate). The **product-form weight** of $x$ is
--   $$w(x)=\prod_{s\ \text{single-server}}\rho_s^{\,x_s}\;\prod_{s\ \text{infinite-server}}\frac{\rho_s^{\,x_s}}{x_s!}.$$
--   3. The **normalizing constant** is $G(K)=\sum_{x:\,\sum_s x_s=K}w(x)$, and the **product-form probability** of $x$ is $\pi(x)=w(x)/G(K)$.
--   4. The **busy probability** of station $s$ is $\Pr\{x_s\ge 1\}=\sum_{x:\,\sum_s x_s=K,\ x_s\ge 1}\pi(x)$.
--
--   This is the stationary law of the closed BCMP networks of Baskett, Chandy, Muntz and Palacios (1975) with one customer class, single-server stations and infinite-server stations; by insensitivity only the mean service times enter. The vehicle-sharing network of Benjaafar and Shen (pp. 5–6 of their paper) is an instance. Here the product form is a **definition**, not a theorem.
--
--   **Formalization Note** Stations form an arbitrary finite type; a station is infinite-server when the Boolean flag `isIS s` is true. A station with load $0$ contributes $0^0=1$ when empty and $0$ when occupied, so it is occupied with probability $0$. The quotient $w(x)/G(K)$ uses Lean's convention $a/0=0$; every use in this mission has $G(K)>0$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), pp. 5–6 (closed queueing network with pick-up and transit queues; "belongs to the class of BCMP networks"); Baskett, Chandy, Muntz & Palacios, Open, Closed, and Mixed Networks of Queues with Different Classes of Customers, J. ACM 22 (1975), product form

import Mathlib

namespace VehicleSharePricing.Static

open Finset

/-- Population vectors of a closed network with finite station set `S` and `K` customers:
all `x : S → ℕ` with `∑ s, x s = K`. -/
def popStates (S : Type*) [Fintype S] [DecidableEq S] (K : ℕ) : Finset (S → ℕ) :=
  (Fintype.piFinset fun _ : S => Finset.range (K + 1)).filter fun x => ∑ s, x s = K

/-- Product-form weight of a population vector `x` of a closed network whose station `s` has
relative load `ρ s` (visit ratio divided by service rate) and is an infinite-server station when
`isIS s = true`, a single-server station otherwise:
`∏_{s single-server} ρ_s^{x_s} · ∏_{s infinite-server} ρ_s^{x_s} / x_s!`.
A station with load `0` contributes `0^0 = 1` when empty and `0` when occupied. -/
noncomputable def pfWeight {S : Type*} [Fintype S] (ρ : S → ℝ) (isIS : S → Bool)
    (x : S → ℕ) : ℝ :=
  ∏ s, if isIS s then ρ s ^ x s / ((x s).factorial : ℝ) else ρ s ^ x s

/-- Normalizing constant `G(K) = ∑_{x : ∑ x = K} weight(x)`. -/
noncomputable def pfNormConst {S : Type*} [Fintype S] [DecidableEq S] (ρ : S → ℝ)
    (isIS : S → Bool) (K : ℕ) : ℝ :=
  ∑ x ∈ popStates S K, pfWeight ρ isIS x

/-- Product-form stationary probability `π(x) = weight(x) / G(K)` of the population vector `x`
in the closed network with `K` customers. -/
noncomputable def pfProb {S : Type*} [Fintype S] [DecidableEq S] (ρ : S → ℝ)
    (isIS : S → Bool) (K : ℕ) (x : S → ℕ) : ℝ :=
  pfWeight ρ isIS x / pfNormConst ρ isIS K

/-- Probability, under the product form with `K` customers, that station `s` holds at least one
customer: `∑_{x : ∑ x = K, x_s ≥ 1} π(x)`. -/
noncomputable def pfBusyProb {S : Type*} [Fintype S] [DecidableEq S] (ρ : S → ℝ)
    (isIS : S → Bool) (K : ℕ) (s : S) : ℝ :=
  ∑ x ∈ (popStates S K).filter (fun x => 1 ≤ x s), pfProb ρ isIS K x

end VehicleSharePricing.Static


