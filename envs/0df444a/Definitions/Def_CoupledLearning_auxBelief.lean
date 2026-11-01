-- Prove2me | Definitions.Def_CoupledLearning_auxBelief
-- name    : CoupledLearning_auxBelief
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:00.268437+00:00
-- url     : https://prove2.me/theorems/0e1582b2-ec4e-4227-90fe-fd2c55d80ea1
-- title:
--   The auxiliary belief $\tilde\theta^k$ of (6), updated at every stage
-- statement:
--   The auxiliary belief starts at $\tilde\theta^1=\theta^1$ and is updated at every stage by Bayes' rule:
--
--   $$\tilde\theta^{k+1}(s)=\frac{\tilde\theta^k(s)\,\varphi^s(y^k|q^k)}{\sum_{s'\in S}\tilde\theta^k(s')\,\varphi^{s'}(y^k|q^k)},\qquad s\in S .$$
--
--   The proofs of Lemmas 1, 2 and 4 work with it, and (7) relates it to the belief $\theta^k$.
--
--   **Formalization Note** Stages are indexed from $0$.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, eq. (6), p.22

import Mathlib
import Definitions.Def_CoupledLearning_Prof
import Definitions.Def_CoupledLearning_belief

namespace CoupledLearning

/-- The auxiliary belief `θ̃^k` of (6), arXiv:2206.05637v2, p.22, updated at every stage:
`θ̃^1 = θ^1` and `θ̃^{k+1}(s) = θ̃^k(s) φ^s(y^k|q^k) / ∑_{s'} θ̃^k(s') φ^{s'}(y^k|q^k)`.

**Formalization Note.** Stages are indexed from `0`. -/
noncomputable def auxBelief {I S : Type*} [Fintype S] {d : I → ℕ} (θ₁ : S → ℝ)
    (φ : S → Prof d → (I → ℝ) → ℝ) (qs : ℕ → Prof d) (ys : ℕ → I → ℝ) : ℕ → S → ℝ
  | 0 => θ₁
  | k + 1 => bayesStep (auxBelief θ₁ φ qs ys k) (fun s => φ s (qs k) (ys k))

end CoupledLearning


