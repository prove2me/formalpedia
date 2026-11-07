-- Prove2me | Definitions.Def_ReplicableOL_IsAdvReplicable
-- name    : ReplicableOL_IsAdvReplicable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:53.666494+00:00
-- url     : https://prove2.me/theorems/b7469329-69ea-4bb5-8973-e27f04dc06f0
-- title:
--   Adversarial $\rho$-replicability
-- statement:
--   A learner is **adversarially $\rho$-replicable** if for every product law $P$ on $([0,1]^n)^T$, point masses included,
--   $$
--   \mathbb P_{S,S'\sim P,\,R}[\tau(S,R)=\tau(S',R)]\ge 1-\rho,
--   $$
--   where $S,S'$ are independent and the two runs share $R$. Equivalently, the learner is $\rho$-replicable under every product law.
--
--   **Formalization Note** This is the form of p.7; by Fubini it is Definition 2.1's `P_{S,S′∼P, R}[τ(S, R) = τ(S′, R)] ≥ 1 − ρ`, which the verification file proves.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Definition 2.1, p.6; Sec. 2.1, p.7

import Mathlib
import Definitions.Def_ReplicableOL_IsProductLaw
import Definitions.Def_ReplicableOL_IsReplicableUnder
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Adversarial $\rho$-replicability.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Definition 2.1, p.6; Sec. 2.1, p.7. "adversarial ρ-replicability is ρ-replicability under every product law".

**Formalization Note.** This is the form of p.7; by Fubini it is Definition 2.1's `P_{S,S′∼P, R}[τ(S, R) = τ(S′, R)] ≥ 1 − ρ`, which the verification file proves. -/
def IsAdvReplicable {n T : ℕ} {R : Type*} [MeasurableSpace R] (𝓛 : Learner n T R)
    (PR : Measure R) (ρ : ℝ) : Prop :=
  ∀ P : Measure (Fin T → Fin n → ℝ), IsProductLaw P → IsReplicableUnder 𝓛 PR ρ P

end ReplicableOL


