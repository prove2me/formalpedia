-- Prove2me | Definitions.Def_SparseBatchBandit_Assumption2
-- name    : SparseBatchBandit_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:57.762122+00:00
-- url     : https://prove2.me/theorems/c473f26a-878f-42e5-b2bc-7c1c98eb3ebd
-- title:
--   Assumption 2 (Diverse covariate)
-- statement:
--   **Assumption 2.** There are positive $\gamma(K),\rho(K)$ such that for any $\theta\in\mathbb R^d$ and any unit vector $v$,
--
--   $$
--   \mathbb P\big((v^\top x_{t,a^\star})^2\ge\gamma(K)\big)\ge\rho(K),\qquad a^\star=\operatorname*{argmax}_{a\in[K]}x_{t,a}^\top\theta .
--   $$
--
--   It guarantees exploration without any explicit exploration step: whatever the current estimate, the greedy arm's context has variation in every direction.
--
--   **Formalization Note** The argmax uses the tie-break of Algorithm 1 (lowest index). The proof applies the assumption at $\hat\theta_0=0$, where all arms tie, so the rule is part of the content.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Assumption 2, p.5

import Mathlib
import Definitions.Def_SparseBatchBandit_greedyArm
open MeasureTheory Matrix

namespace SparseBatchBandit

/-- **Assumption 2** (Diverse covariate), Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, p.5 (PDF 5): for any `θ ∈ ℝ^d` and any unit vector `v`,
`P((v⊤x_{t,a*})² ≥ γ) ≥ ρ`, where `a* = argmax_a x_{t,a}⊤θ`.

**Formalization Note.** The argmax is the one of Algorithm 1, lowest index on ties. The proof
applies the assumption at `θ̂₀ = 0`, where every arm ties, so the tie-break is part of the content. -/
def Assumption2 {Ω : Type*} [MeasurableSpace Ω] {T K d : ℕ} [NeZero K] (P : Measure Ω)
    (x : Ω → Fin T → Fin K → Fin d → ℝ) (γ ρ : ℝ) : Prop :=
  ∀ (t : Fin T) (θ v : Fin d → ℝ), ∑ j, v j ^ 2 = 1 →
    ρ ≤ P.real {ω | γ ≤ (v ⬝ᵥ x ω t (greedyArm (x ω t) θ)) ^ 2}

end SparseBatchBandit


