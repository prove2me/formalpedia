-- Prove2me | Definitions.Def_GevreyGibbsSep_outputLaw
-- name    : GevreyGibbsSep_outputLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:39:24.831225+00:00
-- url     : https://prove2.me/theorems/ef7a472b-66dd-4a3c-95b6-e2be52c1f669
-- title:
--   Output law $\widehat p_n$ of a sampling algorithm
-- statement:
--   The **output law** $\widehat p_n$ is the distribution, over the seed $\omega\sim P$, of the output $\widehat X_n=\Psi_n(\omega,O_1,\dots,O_n)$ after $n$ queries to the order-$k$ oracle on the instance.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition B.3, p.35

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus
import Definitions.Def_GevreyGibbsSep_SamplingAlg
import Definitions.Def_GevreyGibbsSep_runAnswers

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The output law `p̂ₙ`: the law over the seed of the output `X̂ₙ = Ψₙ(ω, O₁, …, Oₙ)` after `n`
queries (arXiv:2608.24527 (sha256 d4fd40eb…), Definition B.3, p.35). -/
noncomputable def outputLaw {d : ℕ} (A : SamplingAlg d) (k : ℕ∞) (V : (Fin d → ℝ) → ℝ)
    (n : ℕ) : Measure (Torus d) :=
  A.P.map (fun ω => A.Ψ n ω (runAnswers A k V ω n))

end GevreyGibbsSep


