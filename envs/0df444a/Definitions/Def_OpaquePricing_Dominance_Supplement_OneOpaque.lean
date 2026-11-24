-- Prove2me | Definitions.Def_OpaquePricing_Dominance_Supplement_OneOpaque
-- name    : OpaquePricing_Dominance_Supplement_OneOpaque
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:30:19.767594+00:00
-- url     : https://prove2.me/theorems/3d566acd-8b3a-4c82-95be-d486f82de534
-- title:
--   One full-set opaque product: menu, expected revenue and optimum
-- statement:
--   A seller offers $N\ge2$ items, each at price $p\ge0$, and one opaque option containing all items at price $r\ge0$. Pessimistic customers value that option at $\min_i v_i$ and risk-neutral customers at $N^{-1}\sum_i v_i$. A fraction $\alpha\in[0,1]$ is pessimistic, independently of valuations. Define
--   $$R_{1OPQ}(\mu,\alpha;p,r)=\alpha\,\mathbb E_\mu[\operatorname{rev}_{pess}(p,r;v)]+(1-\alpha)\,\mathbb E_\mu[\operatorname{rev}_{rn}(p,r;v)],\qquad R_{1OPQ}(\mu,\alpha)=\sup_{p,r\ge0}R_{1OPQ}(\mu,\alpha;p,r).$$
--   The offered menu consists exactly of all singleton items and the full item set. Revenue uses the published rule: maximize nonnegative utility and then price. This definition adds no intermediate opaque subsets, and agrees with general opaque selling for two items. Supremum and expectation use extended nonnegative reals; no attainment or integrability is assumed.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), §2.2, pp. 11–12

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

/-- Exactly the singletons and the full set, with no intermediate opaque products. -/
def oneOptions (N : ℕ) : Finset (Finset (Fin N)) :=
  (opqOptions N).filter (fun S => S.card = 1 ∨ S = Finset.univ)

noncomputable def oneRevenue {N : ℕ}
    (val : (Fin N → ℝ) → Finset (Fin N) → ℝ)
    (p r : ℝ) (v : Fin N → ℝ) : ℝ :=
  menuRevenue (oneOptions N)
    (fun S => val v S - opqPrice p (fun _ => r) S) (opqPrice p (fun _ => r))

noncomputable def expOne {N : ℕ} (μ : Measure (Fin N → ℝ)) (α p r : ℝ) : ENNReal :=
  ENNReal.ofReal α * (∫⁻ v, ENNReal.ofReal (oneRevenue pessValue p r v) ∂μ) +
  ENNReal.ofReal (1 - α) * (∫⁻ v, ENNReal.ofReal (oneRevenue rnValue p r v) ∂μ)

noncomputable def optOne {N : ℕ} (μ : Measure (Fin N → ℝ)) (α : ℝ) : ENNReal :=
  ⨆ (p : ℝ) (r : ℝ) (_ : 0 ≤ p ∧ 0 ≤ r), expOne μ α p r

end OpaquePricing.Dominance.Supplement


