-- Prove2me | Definitions.Def_AlgoTransparency_IsOpaqueOutcome
-- name    : AlgoTransparency_IsOpaqueOutcome
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:53:35.117664+00:00
-- url     : https://prove2.me/theorems/4c29b9bb-2848-41ae-93ea-90ab67d24f6f
-- title:
--   Selected (payoff-dominant) opaque equilibrium outcome
-- statement:
--   An opaque Nash equilibrium $(q_H,q_L,P)$ is the **selected outcome** when its equilibrium utility for a type-H agent, $\max(u^H_{\mathrm{imp}},u^H_{\mathrm{not}})$, and for a type-L agent, $\max(u^L_{\mathrm{imp}},u^L_{\mathrm{not}})$, are each at least as large as at every opaque Nash equilibrium with the same parameters and costs.
--
--   This is the paper's rule: agents move first in the opaque game, so the outcome is "the equilibrium outcome that maximizes the utilities for both agent types (i.e., payoff dominant)".
--
--   **Formalization Note** The comparison runs over all opaque equilibria (pure, one type mixing, both types mixing), not over the paper's five cases. A selected outcome need not exist in general; the mission's theorems assert its existence where they use it.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §4.1, p.19 (PDF 20); App. A.1, "Dealing with multiple equilibria", p.45 (PDF 46)

import Mathlib
import Definitions.Def_AlgoTransparency_IsOpaqueEq

namespace AlgoTransparency

/-- **The selected (payoff-dominant) equilibrium outcome of the opaque game**, Wang, Huang, Jasin
& Singh, arXiv:2008.09283v1, §4.1, p.19 (PDF 20), and App. A.1, "Dealing with multiple
equilibria", p.45 (PDF 46).

`IsOpaqueOutcome p CH CL qH qL P` says that `(qH, qL, P)` is an opaque Nash equilibrium
(`IsOpaqueEq`) whose equilibrium utility for a type-H agent, `max(u^H_imp, u^H_not)`, and for a
type-L agent, `max(u^L_imp, u^L_not)`, are each at least the corresponding utility at **every**
opaque Nash equilibrium with the same parameters and costs. This is the paper's "equilibrium
outcome that maximizes the utilities for both agent types (i.e., payoff dominant)" (p.19).

**Formalization Note.** In an equilibrium a type that mixes is indifferent and a type that plays
a pure strategy plays a best response, so `max(u_imp, u_not)` is that type's equilibrium utility.
The comparison is with all equilibria of the game (pure, one type mixing, both types mixing), not
with the paper's list of five cases; such an outcome need not exist, which is why the mission's
statements assert existence separately. -/
def IsOpaqueOutcome (p : Params) (CH CL qH qL : ℝ) (P : OState → ℝ) : Prop :=
  IsOpaqueEq p CH CL qH qL P ∧
  ∀ (qH' qL' : ℝ) (P' : OState → ℝ), IsOpaqueEq p CH CL qH' qL' P' →
    max (uHImpO p CH P') (uHNotO p P') ≤ max (uHImpO p CH P) (uHNotO p P) ∧
    max (uLImpO p CL P') (uLNotO p P') ≤ max (uLImpO p CL P) (uLNotO p P)

end AlgoTransparency


