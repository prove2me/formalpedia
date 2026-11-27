-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_finiteChainIntegrabilityA
-- name    : BauerleRiederMDP_LQ_Supplement_finiteChainIntegrabilityA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:44:08.898162+00:00
-- url     : https://prove2.me/theorems/aee0b94a-12d0-4b4d-850b-05d250132a99
-- title:
--   The Integrability Assumption (A) of a finite-horizon Markov Decision Chain
-- statement:
--   **The Integrability Assumption (A) of a finite-horizon Markov Decision Chain** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §8.3, p.258, PDF 269): $\sup _\pi  \mathbb E ^\pi _x [\int _0^T r^+(X_s, \pi _s) ds + g^+(X_T)] < \infty $, $x \in  E$, the supremum over Markov policies.
--
--   **Formalization Note.** The expectation is the published `FiniteChain.Vpi` at $t = 0$ with $r^+$, $g^+$ in place of $r$, $g$ (same path law `pathLaw` of $(T_n, Z_n)$ started at $(0, x)$, same process and controls).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §8.3, p.258, PDF 269

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Core
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_PDMDP_pathLaw
import Definitions.Def_BauerleRiederMDP_PDMDP_FiniteChain

open MeasureTheory ProbabilityTheory
open MDPFinance.PDMDP (erealIntegral)
open BauerleRiederMDP.PDMDP

namespace BauerleRiederMDP.LQ.Supplement

/-- **The Integrability Assumption (A) of a finite-horizon Markov Decision Chain** (Bäuerle &
Rieder, *Markov Decision Processes with Applications to Finance* (2011), §8.3, p.258, PDF 269):
`sup_π 𝔼^π_x [∫_0^T r⁺(X_s, π_s) ds + g⁺(X_T)] < ∞`, `x ∈ E`, the supremum over Markov policies.

**Formalization Note.** The expectation is the published `FiniteChain.Vpi` at `t = 0` with `r⁺`,
`g⁺` in place of `r`, `g` (same path law `pathLaw` of `(T_n, Z_n)` started at `(0, x)`, same
process and controls). -/
def finiteChainIntegrabilityA {E U : Type*} [MeasurableSpace E] [Countable E]
    [MeasurableSingletonClass E] [MeasurableSpace U] (C : FiniteChain E U) : Prop :=
  ∀ x : E, (⨆ π : ℕ → DecisionRule (ℝ × E) U,
    erealIntegral (pathLaw (fun n => C.step (π n)) (0, x)) fun ω =>
      erealIntegral (volume.restrict (Set.Ioc 0 C.horizon)) (fun s =>
        ((max (C.r ((ω (jumpIndex ω s)).2,
          (π (jumpIndex ω s)).1 (s - (ω (jumpIndex ω s)).1, ω (jumpIndex ω s)))) 0 : ℝ) : EReal)) +
        ((max (C.g (ω (jumpIndex ω C.horizon)).2) 0 : ℝ) : EReal)) < ⊤

end BauerleRiederMDP.LQ.Supplement


