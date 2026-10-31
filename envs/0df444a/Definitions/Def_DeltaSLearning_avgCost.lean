-- Prove2me | Definitions.Def_DeltaSLearning_avgCost
-- name    : DeltaSLearning_avgCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:33.029755+00:00
-- url     : https://prove2.me/theorems/cda689bd-8ea5-4d95-bac3-f667a2cb9b44
-- title:
--   Long-run average pseudo cost $V(\delta,S)=\mathbb E[G]/\mathbb E[L]$
-- statement:
--   For a demand process $D$ on $(\Omega,P)$, the objective of the $(\delta,S)$ policy is
--   $$V(\delta,S) := \frac{\mathbb E[G(\delta,S)]}{\mathbb E[L(\delta)]},$$
--   where $G$ and $L$ are evaluated on the demand path $t\mapsto D_t(\omega)$. By the renewal-reward theorem it is the long-run average pseudo cost of the policy (8), which the paper uses as the definition.
--
--   **Formalization Note** The expectations are Bochner integrals. Under Assumption 1, $L$ is integrable (Lemma 2) and $|G|\le\gamma L$ (Lemma 1), so both are finite; the milestones state the needed integrability as conclusions.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), p.11, after (9)

import Mathlib
import Definitions.Def_DeltaSLearning_cycleCost

open MeasureTheory

namespace DeltaSLearning

/-- The objective `V(δ, S) := E[G(δ, S)] / E[L(δ)]`, the long-run average pseudo cost of the
`(δ, S)` policy, for the demand process `D` on `(Ω, P)`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), p.11 (after (9)).

**Formalization Note** `G` and `L` are evaluated on the demand path `t ↦ D t ω`, i.e. on a
cycle started at period 1; under Assumption 1 every cycle has this law. The expectations are
Bochner integrals: `L` and `G` are integrable under Assumption 1 (Lemma 2, and `|G| ≤ γ L`
by Lemma 1), which the milestones state as conclusions. -/
noncomputable def avgCost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℕ → Ω → ℝ)
    (cp : Params) (δ S : ℝ) : ℝ :=
  (∫ ω, cycleCost cp δ S (fun t => D t ω) ∂P) /
    ∫ ω, (cycleLength δ (fun t => D t ω) : ℝ) ∂P

end DeltaSLearning


