-- Prove2me | Definitions.Def_SharedVehicleApprox_Pricing_Supplement_StationaryLaw
-- name    : SharedVehicleApprox_Pricing_Supplement_StationaryLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:25:23.325608+00:00
-- url     : https://prove2.me/theorems/fe292c62-a02b-40e1-a201-eb265ec59131
-- title:
--   Stationary law of a finite-state continuous-time Markov chain given by its transition rates
-- statement:
--   Let $\mathcal S$ be a finite set of states and let $Q(s,t)$ be the transition rate from $s$ to $t$. A **stationary law** of the chain is a function $\pi\ge0$ that vanishes outside $\mathcal S$, has total mass $\sum_{s\in\mathcal S}\pi(s)=1$, and satisfies the global balance equations
--
--   $$\pi(s)\sum_{t\in\mathcal S}Q(s,t)=\sum_{t\in\mathcal S}\pi(t)\,Q(t,s)\qquad(s\in\mathcal S).$$
--
--   This is the paper's description of a steady-state distribution (p. 7), for an arbitrary finite state space. The models with travel times use it.
--
--   **Formalization Note** The balance equations are the published full-balance predicate of Kelly and Yudovina, applied on the subtype of $\mathcal S$, where its unconditional sums are finite sums. A rate $Q(s,s)$ appears on both sides and cancels.
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 7 (PDF 8), §2.2, balance equation (1)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

namespace SharedVehicleApprox.Pricing.Supplement

open Finset

/-- A stationary law of the continuous-time Markov chain with transition rates `rate` on the finite
state space `St`: a probability vector on `St`, zero off `St`, satisfying the equilibrium (global
balance) equations `π s ∑_t rate s t = ∑_t π t · rate t s` at every `s ∈ St`. -/
def IsStationaryLaw {S : Type*} (St : Finset S) (rate : S → S → ℝ) (π : S → ℝ) : Prop :=
  (∀ s, 0 ≤ π s) ∧ (∀ s, s ∉ St → π s = 0) ∧ (∑ s ∈ St, π s) = 1 ∧
    KellyStochasticNetworks.FullBalance (fun s : {s // s ∈ St} => π s)
      (fun s t : {s // s ∈ St} => rate s t)

end SharedVehicleApprox.Pricing.Supplement


