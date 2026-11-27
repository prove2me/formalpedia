-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_PDIntegrabilityA
-- name    : BauerleRiederMDP_LQ_Supplement_PDIntegrabilityA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:21:52.002659+00:00
-- url     : https://prove2.me/theorems/46b3e475-f7ab-535a-8fa1-60983da937a2
-- title:
--   The Integrability Assumption (A) of a Piecewise Deterministic Markov Decision Model
-- statement:
--   **The Integrability Assumption (A) of a Piecewise Deterministic Markov Decision Model** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §8.1, p.245, PDF 256): $\sup _\pi  \mathbb E ^\pi _x [\int _0^\infty  e^{-\beta t} r^+(X_t, \pi _t) dt] < \infty $ for all $x \in  E$, the supremum over all Markov policies.
--
--   **Formalization Note.** The law $\mathbb E ^\pi _x$, the process $X_t$ and the control process $\pi _t$ are the published `PDMDP.JumpModel.law`, $X$, `control`, exactly as in the published `JumpModel.Vpi`, with $r^+ = \max (r, 0)$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §8.1, p.245, PDF 256

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_Vinf
import Definitions.Def_MDPFinance_PDMDP_Core

open MeasureTheory ProbabilityTheory
open MDPFinance.PDMDP (erealIntegral)
open BauerleRiederMDP.PDMDP

namespace BauerleRiederMDP.LQ.Supplement

/-- **The Integrability Assumption (A) of a Piecewise Deterministic Markov Decision Model**
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §8.1, p.245,
PDF 256): `sup_π 𝔼^π_x [∫_0^∞ e^{−βt} r⁺(X_t, π_t) dt] < ∞` for all `x ∈ E`, the supremum over
all Markov policies.

**Formalization Note.** The law `𝔼^π_x`, the process `X_t` and the control process `π_t` are the
published `PDMDP.JumpModel.law`, `X`, `control`, exactly as in the published `JumpModel.Vpi`, with
`r⁺ = max(r, 0)`. -/
def PDIntegrabilityA {E U : Type*} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace U]
    (M : JumpModel E U) : Prop :=
  ∀ x : E, (⨆ π : ℕ → DecisionRule E U, erealIntegral (M.law π x) fun ω =>
    erealIntegral (volume.restrict (Set.Ioi (0 : ℝ))) fun t =>
      ((Real.exp (-M.β * t) * max (M.r (M.X π ω t, M.control π ω t)) 0 : ℝ) : EReal)) < ⊤

end BauerleRiederMDP.LQ.Supplement


