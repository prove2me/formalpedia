-- Prove2me | Definitions.Def_ReplicableOL_covF
-- name    : ReplicableOL_covF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:48:44.000836+00:00
-- url     : https://prove2.me/theorems/fda9793b-fce9-4a10-a7d3-30d42e33039f
-- title:
--   $\mathrm{Cov}_f$
-- statement:
--   For a fixed function $f$ of a block, $\mathrm{Cov}_f=\mathbb E[\mu f(S)]=\mathbb E[\mu q_f(\mu)]$, which equals $\mathrm{Cov}(\mu,f(S))$ since $\mathbb E\mu=0$.
--
--   **Formalization Note** An integral of a polynomial against the uniform law.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Appendix A.3, p.28

import Mathlib
import Definitions.Def_ReplicableOL_qf
import Definitions.Def_ReplicableOL_uniformPrior
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **$\mathrm{Cov}_f$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Appendix A.3, p.28. `Cov_f := E[μ f(S)] = E[μ q_f(μ)]`.

**Formalization Note.** An integral of a polynomial against the uniform law. -/
noncomputable def covF {L : ℕ} (Δ : ℝ) (f : Block L → ℝ) : ℝ :=
  ∫ μ, μ * qf f μ ∂(uniformPrior Δ)

end ReplicableOL


