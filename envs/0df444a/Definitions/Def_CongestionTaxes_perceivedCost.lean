-- Prove2me | Definitions.Def_CongestionTaxes_perceivedCost
-- name    : CongestionTaxes_perceivedCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:40.199005+00:00
-- url     : https://prove2.me/theorems/65dc1f6e-03c9-43ce-bd16-417d1de5ba09
-- title:
--   Perceived cost $\bar C_i$ on strategy profiles
-- statement:
--   The perceived cost $\bar C_i(a)=\sum_{r\in a_i}f_r(|a|_r,v_r)$ of agent $i$ under the taxes with parameters $(v_r)_r$, as a function of a profile in which every agent plays one of its own strategies. It is the player cost with respect to which correlated and coarse correlated equilibria of the taxed game are defined.
--
--   **Formalization Note** A profile is a choice of an element of each agent's strategy set; its underlying allocation is the family of chosen resource sets.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (2), p.4; Definition 4, p.18; p.19

import Mathlib
import Definitions.Def_CongestionTaxes_taxedGame

namespace CongestionTaxes

/-- The **perceived cost** `C̄_i(a) = ∑_{r ∈ a_i} f_r(|a|_r, v_r)` of agent `i` (Paccagnan, Gairing,
arXiv:2105.07480v2, display (2), p.4, with Definition 4, p.18, and p.19), as a function of a profile
in which every agent plays one of its own strategies.

**Formalization Note** A profile is `s : ∀ i, ↥(G.strategies i)`, the form used by the
(coarse) correlated equilibria; its underlying allocation is `j ↦ (s j).1`. The value is the
published player cost of the taxed game `taxedGame G v`. -/
noncomputable def perceivedCost {ι E : Type*} [Fintype ι] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (v : E → ℝ) :
    ι → (∀ i, ↥(G.strategies i)) → ℝ :=
  fun i s => CongestionPoA.AsymSum.cost (taxedGame G v) (fun j => (s j).1) i

end CongestionTaxes


