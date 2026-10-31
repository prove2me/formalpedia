-- Prove2me | Definitions.Def_LearnManip_IsDistortion
-- name    : LearnManip_IsDistortion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:59.314079+00:00
-- url     : https://prove2.me/theorems/2fcbc385-7010-4e3e-80c2-932f635efc8a
-- title:
--   Distortion rules $\Lambda\in\mathcal D_{\mu^q}$, encoded by the distorted law
-- statement:
--   A distortion rule with respect to the posterior mean $\mu^q$ is a nonnegative measurable $\Lambda$ with $E[\Lambda]=1$, inducing the law $P^\Lambda(B)=E[\Lambda 1_B]$, such that $\mu^q$ is integrable under $P^\Lambda$. This predicate describes the induced law $G=P^\Lambda$: a probability measure, absolutely continuous with respect to $N(\mu,\sigma^2_{\mu^q})$, with the identity function $G$-integrable.
--
--   **Formalization Note.** (4) is a bijection between such $\Lambda$ and such $G$, with $\Lambda=dG/dN$, so nothing is lost by working with $G$. The distortion cost (6) is $\gamma$ times the relative entropy of $G$ from $N(\mu,\sigma^2_{\mu^q})$.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (4), p.8, and (6), p.9

import Mathlib
import Definitions.Def_LearnManip_baseLaw

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- `G` is the law of the posterior mean under a distortion rule `Λ ∈ D_{μ^q}`: (4) and the
definition of `D_X`, p.8, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04).

**Formalization Note.** The paper's `Λ` is a nonnegative `F_X`-measurable variable with `E[Λ] = 1`, and
(4) makes `Λ ↦ P^Λ` a bijection onto the probability measures `≪ P`, with `Λ = dP^Λ/dP`. So the
distortion is encoded by the distorted law `G = P^Λ`. The requirement "`X` integrable with respect to
`P^Λ`" is the field `integrable`. The cost `E[Λ log Λ]` of (6) is `klDiv G (baseLaw μ s q)`. -/
structure IsDistortion (μ : ℝ) (s q : ℝ≥0) (G : Measure ℝ) : Prop where
  isProb : IsProbabilityMeasure G
  absCont : G ≪ baseLaw μ s q
  integrable : Integrable (fun y : ℝ => y) G

end LearnManip


