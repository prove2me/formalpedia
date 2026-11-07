-- Prove2me | Definitions.Def_ReplicableOL_disagreeProb
-- name    : ReplicableOL_disagreeProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:26.076552+00:00
-- url     : https://prove2.me/theorems/3d5fb7b6-c346-472b-86bb-c8f6215f6b88
-- title:
--   Per-seed disagreement $\rho_\tau(Q,r)$
-- statement:
--   For a seed value $r$ and a law $Q$ of $S$, the **per-seed disagreement** is
--   $$
--   \rho_\tau(Q,r)=\mathbb P_{S,S'\sim Q}[\tau(S,r)\ne\tau(S',r)],
--   $$
--   with $S,S'$ independent and both runs using the same seed $r$.
--
--   **Formalization Note** A value in `ℝ≥0∞`, the mass under `Q ⊗ Q` of the set of pairs with different trajectories.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.7

import Mathlib
import Definitions.Def_ReplicableOL_traj
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Per-seed disagreement $\rho_\tau(Q,r)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.7. `ρ_τ(Q, r) := P_{S,S′∼Q}[τ(S, r) ≠ τ(S′, r)]`.

**Formalization Note.** A value in `ℝ≥0∞`, the mass under `Q ⊗ Q` of the set of pairs with different trajectories. -/
noncomputable def disagreeProb {n T : ℕ} {R : Type*} [MeasurableSpace R] (𝓛 : Learner n T R)
    (Q : Measure (Fin T → Fin n → ℝ)) (r : R) : ℝ≥0∞ :=
  (Q.prod Q) {p | traj 𝓛 p.1 r ≠ traj 𝓛 p.2 r}

end ReplicableOL


