-- Prove2me | Definitions.Def_LearnManip_IsAdmissible
-- name    : LearnManip_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:08.401679+00:00
-- url     : https://prove2.me/theorems/5e89fb58-5e9c-46ef-8660-a6d7584f76f2
-- title:
--   Integrable belief process
-- statement:
--   Each posterior mean $\mu_{n+1}$ is integrable under the law of the belief process, so that the expected payoff of each period in (8) is a real number.
--
--   **Formalization Note.** The paper does not say when the expectation in (8) is defined. This is the reading that makes the payoff term meaningful. It is a condition on the pair (policy, initial mean).
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (8), p.11

import Mathlib
import Definitions.Def_LearnManip_Policy
import Definitions.Def_LearnManip_pathLaw

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The expectations `E_π[μ_t]` in (8), p.11, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04) exist:
each `μ_{n+1}` is integrable under the path law. The paper does not say when the expectation is
defined; this is the reading that makes its first term a real number. -/
def IsAdmissible {s₀ : ℝ≥0} (M : Policy s₀) (μ₀ : ℝ) : Prop :=
  ∀ n, Integrable (fun ω : ℕ → ℝ => ω (n + 1)) (pathLaw M μ₀)

end LearnManip


