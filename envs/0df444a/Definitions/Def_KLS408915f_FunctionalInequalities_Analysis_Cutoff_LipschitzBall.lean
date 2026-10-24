-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
-- name    : KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:51:42.900168+00:00
-- url     : https://prove2.me/theorems/89bafc33-9a3e-477b-a907-f55efeba2b97
-- title:
--   Lipschitz cutoff on a norm ball
-- statement:
--   `Probability.Diffusion.ballCutoff R p` is the scalar cutoff $\max(0,\min(1,R+1-\|p\|))$ on a finite-dimensional real normed space. It is the piecewise-linear norm-ball cutoff taking values between $0$ and $1$, although this bundle only supplies the definition.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/LipschitzBall.lean#L22-L23 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.LipschitzBall`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall`; the repository is private at upload time).

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz

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


