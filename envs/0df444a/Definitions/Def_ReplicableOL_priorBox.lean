-- Prove2me | Definitions.Def_ReplicableOL_priorBox
-- name    : ReplicableOL_priorBox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:52.46319+00:00
-- url     : https://prove2.me/theorems/df3ef198-9a8b-423c-af13-c2289b2882c3
-- title:
--   The support box of the prior
-- statement:
--   The set $[-\Delta,\Delta]^k$ of epoch-mean vectors, on which the prior is carried. "Each law $P_\theta$" in the paper refers to $\theta$ in this box.
--
--   **Formalization Note** The laws `P_θ` are probability measures for `θ` in this box and `Δ ≤ 1/2`; hypotheses on `θ` are stated only on it.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.7

import Mathlib

namespace ReplicableOL

/-- **The support box of the prior.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.7. The values `θ` that Construction C draws: `θ ∈ [−Δ, Δ]^k`.

**Formalization Note.** The laws `P_θ` are probability measures for `θ` in this box and `Δ ≤ 1/2`; hypotheses on `θ` are stated only on it. -/
def priorBox (k : ℕ) (Δ : ℝ) : Set (Fin k → ℝ) :=
  {θ | ∀ j, θ j ∈ Set.Icc (-Δ) Δ}

end ReplicableOL


