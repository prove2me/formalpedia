-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_ConvergenceAssumptionCNeg
-- name    : BauerleRiederMDP_LQ_Supplement_ConvergenceAssumptionCNeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:08:15.233714+00:00
-- url     : https://prove2.me/theorems/dd294ee1-5575-575a-bb4d-585e75984455
-- title:
--   The Convergence Assumption (C−)
-- statement:
--   **The Convergence Assumption (C−)** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §7.4, p.208, PDF 219): for every $x \in  E$, $\lim _{n\to \infty } \sup _\pi  \mathbb E ^\pi _x [\sum _{k=n}^\infty  \beta ^k r^-(X_k, f_k(X_k))] = 0$, the supremum over all Markov policies $\pi  \in  F^\infty $.
--
--   **Formalization Note.** Mirrors the published `BauerleRiederMDP.Contracting.ConvergenceAssumptionC` with $r^- = \max (-r, 0)$ in place of $r^+$: the tail expectation $\mathbb E ^\pi _x [\sum _{k\ge n} \beta ^k r^-]$ is `Jinfpi M r⁻ π x − Jnpi M r⁻ π n x`, which under the Integrability Assumption (A) of §7.4 (`IntegrabilityAssumptionNeg`, assumed alongside) is a difference of finite nonnegative numbers. The convergence is in `EReal`.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §7.4, p.208, PDF 219

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value

open MeasureTheory ProbabilityTheory Filter Topology
open MDPFinance.Contracting

namespace BauerleRiederMDP.LQ.Supplement

/-- **The Convergence Assumption (C−)** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), §7.4, p.208, PDF 219): for every `x ∈ E`,
`lim_{n→∞} sup_π 𝔼^π_x [∑_{k=n}^∞ β^k r^−(X_k, f_k(X_k))] = 0`, the supremum over all Markov
policies `π ∈ F^∞`.

**Formalization Note.** Mirrors the published `BauerleRiederMDP.Contracting.ConvergenceAssumptionC`
with `r^− = max(−r, 0)` in place of `r^+`: the tail expectation `𝔼^π_x [∑_{k≥n} β^k r^−]` is
`Jinfpi M r⁻ π x − Jnpi M r⁻ π n x`, which under the Integrability Assumption (A) of §7.4
(`IntegrabilityAssumptionNeg`, assumed alongside) is a difference of finite nonnegative numbers.
The convergence is in `EReal`. -/
def ConvergenceAssumptionCNeg {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) : Prop :=
  ∀ x : E, Tendsto
    (fun n : ℕ => ⨆ π ∈ {π : ℕ → E → A | IsPolicyOf M π},
      Jinfpi M (fun p => max (-M.r p) 0) π x - Jnpi M (fun p => max (-M.r p) 0) π n x)
    atTop (𝓝 0)

end BauerleRiederMDP.LQ.Supplement


