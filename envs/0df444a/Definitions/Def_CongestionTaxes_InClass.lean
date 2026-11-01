-- Prove2me | Definitions.Def_CongestionTaxes_InClass
-- name    : CongestionTaxes_InClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:01.564992+00:00
-- url     : https://prove2.me/theorems/5d94da77-c8a8-46d4-b544-9999f965e65c
-- title:
--   Congestion games with resource costs in $\mathcal L$
-- statement:
--   A congestion game $G$ **belongs to the class $\mathcal G$ for the cost set $\mathcal L$** if every resource cost $\ell_r$ lies in $\mathcal L$ and every agent has a nonempty set of feasible allocations. The number of agents and the finite set of resources are arbitrary. Strategies may contain the empty set.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, p.4 and Theorem 3, p.19

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

namespace CongestionTaxes

/-- The game `G` **belongs to the class 𝒢 of congestion games with costs in `𝓛`** (Paccagnan,
Gairing, arXiv:2105.07480v2, p.4 and Theorem 3, p.19): every resource cost `ℓ_r` lies in `𝓛`, and
every agent has a nonempty set of feasible allocations (p.1, "endowed with a set of feasible
allocations"; the simplex `Δ(s_i)` of (12) is empty otherwise).

**Formalization Note** Strategies may contain `∅`, as `𝓐_i ⊆ 2^𝓡` allows. -/
def InClass {ι E : Type*} (L : Set (ℕ → ℝ)) (G : CongestionPoA.AsymSum.CongestionGame ι E) :
    Prop :=
  (∀ r, G.latency r ∈ L) ∧ ∀ i, (G.strategies i).Nonempty

end CongestionTaxes


