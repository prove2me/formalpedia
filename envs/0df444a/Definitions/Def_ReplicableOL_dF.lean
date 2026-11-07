-- Prove2me | Definitions.Def_ReplicableOL_dF
-- name    : ReplicableOL_dF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:52.372403+00:00
-- url     : https://prove2.me/theorems/53d83bb0-bf2a-4bc7-be23-8e47dd218cb2
-- title:
--   Disagreement $d_f$
-- statement:
--   The **disagreement** $d_f=\mathbb E|f(S)-f(S')|$ of a fixed function $f$ on two blocks that are conditionally independent given $\mu$.
--
--   **Formalization Note** An integral against the uniform law of a finite sum over the two blocks.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Appendix A.3, p.28

import Mathlib
import Definitions.Def_ReplicableOL_blockWeight
import Definitions.Def_ReplicableOL_uniformPrior
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Disagreement $d_f$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Appendix A.3, p.28. `d_f := E|f(S) − f(S′)|`, over `(μ, S, S′)`.

**Formalization Note.** An integral against the uniform law of a finite sum over the two blocks. -/
noncomputable def dF {L : ℕ} (Δ : ℝ) (f : Block L → ℝ) : ℝ :=
  ∫ μ, ∑ s : Block L, ∑ s' : Block L, blockWeight μ s * blockWeight μ s' * |f s - f s'| ∂(uniformPrior Δ)

end ReplicableOL


