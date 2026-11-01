-- Prove2me | Definitions.Def_RedundancyHT_cocChain
-- name    : RedundancyHT_cocChain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:33.573171+00:00
-- url     : https://prove2.me/theorems/3cad3cc9-f5d0-4add-b54e-bc9b0d075eb2
-- title:
--   The redundancy c.o.c. Markov chain
-- statement:
--   The cancel-on-completion system with Poisson arrivals and exponential replica sizes is the Markov chain on job sequences driven by one clock per job type (rate $N\lambda p_S$) and one clock per server (rate $\mu_n$), each acting through the event map of `cocStep`.
--
--   **Formalization Note** The chain is a published `EventChain` with the same rates as the published c.o.s. `queueChain`, taken as a function of the load $\rho=\lambda/\mu$. Clock rings without effect are null events: the chain is the uniformization of the continuous-time process and has the same stationary laws.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §2.1, p.4, and §2.3.1, p.7

import Definitions.Def_RedundancyHT_cocStep

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The c.o.c. Markov chain** as a published `EventChain`: one Poisson clock per job type, at rate
`ρ * nominal i`, and one per server, at rate `µ_j`, acting through `cocStep`
(arXiv:2005.14566v5, §2.1, p.4, and §2.3.1, p.7).

**Formalization Note.** These are the rates of the published `queueChain`. For `ρ = λ/µ` the class
rate is `N λ p_i`. Events without effect are null events of the uniformized chain, which does not
change the stationary laws. -/
def cocChain {n m : ℕ} (D : Model n m) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    EventChain (List (Fin n)) (Event n m) where
  rate := Sum.elim (fun i => ρ * D.nominal i) D.service
  nonneg := (queueChain D ρ hρ).nonneg
  total_pos := (queueChain D ρ hρ).total_pos
  step := cocStep D

end RedundancyHT


