-- Prove2me | Definitions.Def_ReplicableOL_varF
-- name    : ReplicableOL_varF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:48:34.151744+00:00
-- url     : https://prove2.me/theorems/a1a9e8e3-4bf3-4002-a470-b588eadd27fe
-- title:
--   Variance $\mathrm{Var}(f(S))$
-- statement:
--   The variance of $f(S)$ when $\mu\sim U[-\Delta,\Delta]$ and $S\sim\nu_\mu$ given $\mu$.
--
--   **Formalization Note** `E f(S)² − (E f(S))²`, with both expectations written explicitly.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Appendix A.3, p.29

import Mathlib
import Definitions.Def_ReplicableOL_blockWeight
import Definitions.Def_ReplicableOL_qf
import Definitions.Def_ReplicableOL_uniformPrior
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Variance $\mathrm{Var}(f(S))$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Appendix A.3, p.29. `Var(f(S))`, over `(μ, S)`.

**Formalization Note.** `E f(S)² − (E f(S))²`, with both expectations written explicitly. -/
noncomputable def varF {L : ℕ} (Δ : ℝ) (f : Block L → ℝ) : ℝ :=
  ∫ μ, ∑ s : Block L, blockWeight μ s * f s ^ 2 ∂(uniformPrior Δ) - (∫ μ, qf f μ ∂(uniformPrior Δ)) ^ 2

end ReplicableOL


