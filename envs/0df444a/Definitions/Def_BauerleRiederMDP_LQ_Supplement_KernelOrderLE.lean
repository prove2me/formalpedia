-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_KernelOrderLE
-- name    : BauerleRiederMDP_LQ_Supplement_KernelOrderLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:20:55.77439+00:00
-- url     : https://prove2.me/theorems/135b075b-55b2-4a04-bfd8-701053c75295
-- title:
--   Integral stochastic orders on a state space
-- statement:
--   **Integral stochastic orders on a state space** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §2.4.5, p.38, PDF 53, with Appendix B.3, Theorem B.3.3 (ii) and Definition B.3.9, pp.359–361, PDF 365–367): for a class $P$ of functions $v : E \to  [-\infty , \infty ]$, $\mu  \le _P \nu $ if $\int  v d\mu  \le  \int  v d\nu $ for every measurable $v$ in the class for which both integrals exist. With $P$ = increasing, concave or convex functions this is $\le _st$, $\le _cv$, $\le _cx$.
--
--   **Formalization Note.** The integral of an extended-real function is `erealIntegral` ($\int  v^+ - \int  v^-$); it "exists" when $\int  v^+$ and $\int  v^-$ are not both infinite, which is required for both measures. The class is a parameter, so the three orders of §2.4.5 are one definition.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §2.4.5, p.38, PDF 53, with Appendix B.3, Theorem B.3.3 (ii) and Definition B.3.9, pp.359–361, PDF 365–367

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators

open MeasureTheory
open MDPFinance.Bellman (erealIntegral)

namespace BauerleRiederMDP.LQ.Supplement

/-- **Integral stochastic orders on a state space** (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), §2.4.5, p.38, PDF 53, with Appendix B.3, Theorem B.3.3 (ii)
and Definition B.3.9, pp.359–361, PDF 365–367): for a class `P` of functions `v : E → [−∞, ∞]`,
`μ ≤_P ν` if `∫ v dμ ≤ ∫ v dν` for every measurable `v` in the class for which both integrals
exist. With `P` = increasing, concave or convex functions this is `≤_st`, `≤_cv`, `≤_cx`.

**Formalization Note.** The integral of an extended-real function is `erealIntegral`
(`∫ v⁺ − ∫ v⁻`); it "exists" when `∫ v⁺` and `∫ v⁻` are not both infinite, which is required for
both measures. The class is a parameter, so the three orders of §2.4.5 are one definition. -/
def KernelOrderLE {E : Type*} [MeasurableSpace E] (P : (E → EReal) → Prop) (μ ν : Measure E) :
    Prop :=
  ∀ v : E → EReal, Measurable v → P v →
    (∫⁻ x, (v x ⊔ 0).toENNReal ∂μ < ⊤ ∨ ∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ < ⊤) →
    (∫⁻ x, (v x ⊔ 0).toENNReal ∂ν < ⊤ ∨ ∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂ν < ⊤) →
    erealIntegral μ v ≤ erealIntegral ν v

end BauerleRiederMDP.LQ.Supplement


