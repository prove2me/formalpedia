-- Prove2me | Definitions.Def_GaussianBandit
-- name    : GaussianBandit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-19T18:21:30.423817+00:00
-- url     : https://prove2.me/theorems/75da52a7-23f0-45e1-bfe9-43792e3a15db
-- statement:
--   The unit-variance Gaussian bandit $\nu_\mu$ with mean vector $\mu$ (the class $\mathcal{E}^k_{\mathcal{N}(1)}$ of the lower-bound chapters; the Ch 17 class is parameterized by $\mu \in [0,1]^k$ per the box on p.216).
-- source:
--   L&S Ch 13-17 (class defined p.180 and p.216)

import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_StochasticBandit

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapters 13-17:
the unit-variance Gaussian bandit `ν_μ` with mean vector `μ`
(the environment class `𝓔^k_𝒩(1)` of the lower-bound chapters; the
high-probability chapter's class `𝓔^k` is parameterized by `μ ∈ [0,1]^k`,
see the box on p.216).
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The unit-variance Gaussian bandit with mean vector `μvec`
(L&S `ν_μ ∈ 𝓔^k_𝒩(1)`). -/
noncomputable def gaussianBandit {k : ℕ} (μvec : Fin k → ℝ) : StochasticBandit k where
  P := fun i ↦ gaussianReal (μvec i) 1
  prob := fun _ ↦ inferInstance

end BanditAlgorithm


