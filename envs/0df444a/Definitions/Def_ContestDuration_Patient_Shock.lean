-- Prove2me | Definitions.Def_ContestDuration_Patient_Shock
-- name    : ContestDuration_Patient_Shock
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:12.336756+00:00
-- url     : https://prove2.me/theorems/09b99b9a-4c7b-4a19-a21d-26911a6e6ac5
-- title:
--   Mean-zero shock condition and scale transformation
-- statement:
--   Let $h$ be a real probability density with finite first moment. The contest's output shock has mean zero and $h$ is log-concave. For a positive scale $\alpha$, the transformed shock $\alpha\tilde\xi$ has density
--
--   $$h_\alpha(s)=\frac{h(s/\alpha)}{\alpha}.$$
--
--   This definition supplies the paper-specific shock condition and scaling operation used in the comparative static. The general real-density, cumulative-distribution, and expected-maximum definitions come from the referenced published density module.
--
--   **Formalization Note** The published density predicate's condition that a nonnegative measurable $h$ integrates to one implies integrability. Its CDF and expected-maximum formulas have the same domain and normalization as the source paper; its symmetry-specific predicate is not used here.
-- source:
--   Korpeoglu, Körpeoğlu & Tunç, Optimal Duration of Innovation Contests, SSRN 3064763 (authors' version, forthcoming at M&SOM; PDF of 2020-07-23), p. 9, §2, output-shock density, order-statistic density, and scale transformation

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density

open MeasureTheory

namespace ContestDuration.Patient

/-- §2 p. 9: a mean-zero log-concave shock density. -/
def ShockOK (h : ℝ → ℝ) : Prop :=
  CrowdContest.Pooling.IsDensity h ∧ Integrable (fun s => s * h s) ∧
    ∫ s, s * h s = 0 ∧
    ConvexOptimization.LogConcaveOn Set.univ h

/-- The density of the shock scaled by a positive parameter α. -/
noncomputable def scaled (h : ℝ → ℝ) (α : ℝ) : ℝ → ℝ :=
  fun s => h (s / α) / α

end ContestDuration.Patient


