-- Prove2me | Definitions.Def_LatentMixDRO_empObj
-- name    : LatentMixDRO_empObj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:46.853912+00:00
-- url     : https://prove2.me/theorems/354c0389-ce7b-4a56-b71f-d3f9242ab56a
-- title:
--   Objective of the marginal DRO estimator (16)
-- statement:
--   For $\theta\in\Theta$, with $q=p/(p-1)$,
--
--   $$
--   \inf_{\eta\in[0,M],\ B\in\mathbb R_+^{n\times n}}\Big\{\frac1{\alpha_0}\big(\widehat R_{p,\epsilon,L}(\theta,\eta,B)\vee\epsilon^{q-1}\big)+\eta\Big\}.
--   $$
--
--   The marginal DRO estimator minimizes this quantity over $\theta$.
--
--   **Formalization Note** $\widehat R_{p,\epsilon,L}(\theta,\eta,B)$ is the corrected (15). For $M\ge0$ and $\alpha_0>0$ the set of values is nonempty and bounded below by $0$, so the real infimum is the true one.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, display (16), p.11

import Mathlib
import Definitions.Def_LatentMixDRO_empRB

namespace LatentMixDRO

/-- The objective of the marginal DRO estimator (16) at `θ`:
`inf_{η ∈ [0,M], B ∈ ℝ₊^{n×n}} {(1/α₀)(R̂_{p,ε,L}(θ, η, B) ∨ ε^{q-1}) + η}`, with `q = p/(p - 1)`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, display (16), p.11.

**Formalization Note.** `R̂_{p,ε,L}(θ, η, B)` is the corrected (15), see `empRB`. For `M ≥ 0`, `α₀ > 0`
the set is nonempty and bounded below by `0`, so `sInf` is the true infimum. -/
noncomputable def empObj {d n : ℕ} {Θ : Type*} (ω : Fin n → EuclideanSpace ℝ (Fin d) × ℝ)
    (ℓ : Θ → EuclideanSpace ℝ (Fin d) × ℝ → ℝ) (p ε L α₀ M : ℝ) (θ : Θ) : ℝ :=
  sInf {v | ∃ η ∈ Set.Icc (0 : ℝ) M, ∃ B : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ B i j) ∧
    v = (1 / α₀) * max (empRB ω ℓ p ε L θ η B) (ε ^ (p / (p - 1) - 1)) + η}

end LatentMixDRO


