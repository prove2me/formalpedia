-- Prove2me | Definitions.Def_BCMPNetworks_Core_Aggregate
-- name    : BCMPNetworks_Core_Aggregate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:41:58.524984+00:00
-- url     : https://prove2.me/theorems/35b668dd-2c87-4098-b085-c9257cdd7634
-- title:
--   Mean service times $1/\mu_{ir}$ and aggregate-state factors $g_i(y_i)$
-- statement:
--   For a class-$r$ customer at a type 2, 3 or 4 center $i$, the **mean service time** of its Coxian service time is
--   $$\frac{1}{\mu_{ir}} = \sum_{l} \frac{A_{irl}}{\mu_{irl}}, \qquad A_{irl} = \prod_{j<l} a_{irj}.$$
--
--   For class counts $y_i = (n_{i1},\dots,n_{iR})$ at center $i$ with $n_i = \sum_r n_{ir}$, the **aggregate factor** $g_i(y_i)$ of §4.1 is
--
--   1. type 1: $g_i(y_i) = n_i!\,\Big\{\prod_{r} \frac{1}{n_{ir}!} e_{ir}^{n_{ir}}\Big\}(1/\mu_i)^{n_i}$;
--   2. types 2 and 4: $g_i(y_i) = n_i!\,\prod_{r} \frac{1}{n_{ir}!}\,(e_{ir}/\mu_{ir})^{n_{ir}}$;
--   3. type 3: $g_i(y_i) = \prod_{r} \frac{1}{n_{ir}!}\,(e_{ir}/\mu_{ir})^{n_{ir}}$.
--
--   The factors $g_i$ give the equilibrium law of the numbers of customers of each class at each center; they depend on the service time distributions only through their means.
--
--   **Formalization Note** The paper introduces $1/\mu_{ir}$ as "the mean service time"; here it is computed from the stage data rather than taken as a free parameter.
-- source:
--   Baskett, Chandy, Muntz, Palacios, Open, Closed, and Mixed Networks of Queues with Different Classes of Customers, J. ACM 22 (1975), p. 254, Section 4.1

import Mathlib
import Definitions.Def_BCMPNetworks_Core_Network

namespace BCMPNetworks.Core

namespace Network

variable {N R m : ℕ} (net : Network N R m)

/-- The mean service time `1/μ_{ir}` of a class-`r` customer at a type-2, -3 or -4 center
`i` (§4.1, p. 254), computed from its Coxian stages: `∑_l A_{irl} / μ_{irl}`, with the
corrected `A_{irl}` (the probability of reaching stage `l`). -/
noncomputable def meanServiceTime (i : Fin N) (r : Fin R) : ℝ :=
  ∑ l, net.A i r l / net.μs i r l

/-- The factor `g_i(y_i)` of the aggregate-state probabilities (§4.1, p. 254), for the class
counts `y = (n_{i1}, …, n_{iR})` at center `i` and `n_i = ∑_r n_{ir}`:

* type 1: `n_i! {∏_r (1/n_{ir}!) e_{ir}^{n_{ir}}} (1/μ_i)^{n_i}`;
* types 2 and 4: `n_i! ∏_r (1/n_{ir}!) (e_{ir}/μ_{ir})^{n_{ir}}`;
* type 3: `∏_r (1/n_{ir}!) (e_{ir}/μ_{ir})^{n_{ir}}`,

where `1/μ_{ir}` is `meanServiceTime i r`. -/
noncomputable def g (e : Fin N → Fin R → ℝ) (i : Fin N) (y : Fin R → ℕ) : ℝ :=
  match net.type i with
  | .fcfs => ((∑ r, y r).factorial : ℝ) *
      (∏ r, (1 / ((y r).factorial : ℝ)) * e i r ^ (y r)) * (1 / net.μ i) ^ (∑ r, y r)
  | .ps => ((∑ r, y r).factorial : ℝ) *
      ∏ r, (1 / ((y r).factorial : ℝ)) * (e i r * net.meanServiceTime i r) ^ (y r)
  | .lcfs => ((∑ r, y r).factorial : ℝ) *
      ∏ r, (1 / ((y r).factorial : ℝ)) * (e i r * net.meanServiceTime i r) ^ (y r)
  | .is => ∏ r, (1 / ((y r).factorial : ℝ)) * (e i r * net.meanServiceTime i r) ^ (y r)

end Network

end BCMPNetworks.Core


