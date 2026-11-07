-- Prove2me | Definitions.Def_ReplicableOL_uniformPrior
-- name    : ReplicableOL_uniformPrior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:50.423983+00:00
-- url     : https://prove2.me/theorems/d28bf178-be1a-4a80-86cc-caa5578db09f
-- title:
--   Uniform law $U[-\Delta,\Delta]$
-- statement:
--   The uniform law on $[-\Delta,\Delta]$, for $\Delta>0$. It is the law of each epoch mean in Construction C. The continuity of this prior is essential: on the two-point prior $\mu_j\in\{\pm\Delta\}$ the main theorem fails (Remark A.16(2)).
--
--   **Formalization Note** Lebesgue measure conditioned on `[−Δ, Δ]`; it is a probability measure when `0 < Δ`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.7

import Mathlib
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Uniform law $U[-\Delta,\Delta]$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.7. `μ_j` is uniform on `[−Δ, Δ]`.

**Formalization Note.** Lebesgue measure conditioned on `[−Δ, Δ]`; it is a probability measure when `0 < Δ`. -/
noncomputable def uniformPrior (Δ : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc (-Δ) Δ)

end ReplicableOL


