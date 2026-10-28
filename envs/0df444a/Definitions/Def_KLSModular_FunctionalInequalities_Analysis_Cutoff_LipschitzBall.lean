-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
-- name    : KLSModular_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:33:10.001214+00:00
-- url     : https://prove2.me/theorems/ff179ecc-cd31-4939-9396-b1ea0665ce64
-- title:
--   Lipschitz cutoff on a norm ball
-- statement:
--   `Probability.Diffusion.ballCutoff R p` is the scalar cutoff $\max(0,\min(1,R+1-\|p\|))$ on a finite-dimensional real normed space. It is the piecewise-linear norm-ball cutoff taking values between $0$ and $1$, although this bundle only supplies the definition.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Topology.EMetricSpace.Lipschitz
--   import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
--   import Mathlib.Analysis.Normed.Module.FiniteDimension
--   import Mathlib.Topology.Algebra.Support
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def ballCutoff (R : ℝ) (p : V) : ℝ := max 0 (min 1 (R + 1 - ‖p‖))
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`exists_lipschitzWith_smul_of_locallyLipschitz`](https://prove2.me/theorems/a69c5efc-cc10-4d88-8cc4-a8588fa667cb)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Cutoff/LipschitzBall.lean) · `FunctionalInequalities.Analysis.Cutoff.LipschitzBall` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/LipschitzBall.lean#L22-L23 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.LipschitzBall`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Cutoff_LipschitzBall`; the repository is private at upload time).

import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support

noncomputable section
open scoped NNReal
namespace FunctionalInequalities
namespace Probability
namespace Diffusion
section Cutoff
variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
/-- The norm-ball cutoff `γ_R = clamp₀¹(R + 1 − ‖p‖)`. -/
noncomputable def ballCutoff (R : ℝ) (p : V) : ℝ := max 0 (min 1 (R + 1 - ‖p‖))
end Cutoff
end Diffusion
end Probability
end FunctionalInequalities


