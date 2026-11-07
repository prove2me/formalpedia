-- Prove2me | Definitions.Def_ReplicableOL_IsReplicableUnder
-- name    : ReplicableOL_IsReplicableUnder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:37.745202+00:00
-- url     : https://prove2.me/theorems/114cab0c-66f6-45a4-8685-857f99184402
-- title:
--   $\rho$-replicability under a law $Q$
-- statement:
--   A learner with seed law $P_R$ is **$\rho$-replicable under the law $Q$** of the losses if $\mathbb E_R\,\rho_\tau(Q,R)\le\rho$: two runs on independent samples from $Q$, sharing the seed, produce different trajectories with probability at most $\rho$.
--
--   The main theorem assumes this only for the laws $P_\theta$ of Construction C.
--
--   **Formalization Note** The expectation over the seed is a `lintegral` in `ℝ≥0∞` and `ρ` enters through `ENNReal.ofReal`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.7

import Mathlib
import Definitions.Def_ReplicableOL_disagreeProb
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **$\rho$-replicability under a law $Q$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.7. "for a single law Q of S, product or not, we say that the learner is ρ-replicable under Q if E_R ρ_τ(Q, R) ≤ ρ".

**Formalization Note.** The expectation over the seed is a `lintegral` in `ℝ≥0∞` and `ρ` enters through `ENNReal.ofReal`. -/
def IsReplicableUnder {n T : ℕ} {R : Type*} [MeasurableSpace R] (𝓛 : Learner n T R)
    (PR : Measure R) (ρ : ℝ) (Q : Measure (Fin T → Fin n → ℝ)) : Prop :=
  ∫⁻ r, disagreeProb 𝓛 Q r ∂PR ≤ ENNReal.ofReal ρ

end ReplicableOL


