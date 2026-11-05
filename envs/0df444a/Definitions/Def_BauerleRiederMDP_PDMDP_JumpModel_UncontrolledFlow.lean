-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_UncontrolledFlow
-- name    : BauerleRiederMDP_PDMDP_JumpModel_UncontrolledFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:32.800589+00:00
-- url     : https://prove2.me/theorems/d307108e-6ed5-4cb9-b34f-48e0b8079fa1
-- title:
--   Uncontrolled flow
-- statement:
--   The flow is **uncontrolled** when $\varphi^\alpha_t(x)$ is independent of $\alpha$. This is the first alternative of Theorem 8.2.7.
--
--   **Formalization Note** The independence is required for $\alpha\in A$ only, the weaker hypothesis; independence over $\mathcal R$ follows from it.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.2.7, p.253

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel

namespace BauerleRiederMDP.PDMDP

/-- "`φ^α_t(x)` is independent of `α` (uncontrolled flow)" (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.2.7, p.253, PDF 264),
for `α ∈ A`. -/
def JumpModel.UncontrolledFlow {E U : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [MeasurableSpace U] (M : JumpModel E U) : Prop :=
  ∀ (α α' : ControlFn U) x t, 0 ≤ t → M.flow α.toRelaxed x t = M.flow α'.toRelaxed x t

end BauerleRiederMDP.PDMDP


