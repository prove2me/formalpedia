-- Prove2me | Definitions.Def_RouzeFranca_LearnGibbs_SatisfiesTC
-- name    : RouzeFranca_LearnGibbs_SatisfiesTC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:01.228289+00:00
-- url     : https://prove2.me/theorems/e7c3eb4e-217b-485d-8f2e-4664224ba878
-- title:
--   Transportation cost inequality with constant $\alpha$
-- statement:
--   A state $\sigma$ satisfies a **transportation cost (TC) inequality** with constant $\alpha$, with respect to a Lipschitz constant $\|\cdot\|_{\mathrm{Lip}}$ and its Wasserstein distance $W_1$, if for every state $\rho$
--   $$
--   W_1(\rho,\sigma)\le\sqrt{\frac{D(\rho\|\sigma)}{2\alpha}} .
--   $$
--
--   TC inequalities are known for several classes of Gibbs states of commuting Hamiltonians (Theorem B.1); they are the hypothesis under which the paper's sample complexity is logarithmic in the system size.
--
--   **Formalization Note** States are positive semidefinite matrices of trace one. The inequality is required whenever $D(\rho\|\sigma)$ is finite; when $D(\rho\|\sigma)=+\infty$ it holds trivially. $D$ is the natural-log relative entropy. The condition $\alpha>0$ is a hypothesis of the theorems.
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, §B.3, Eq. (44), p. 25

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_RouzeFranca_LearnGibbs_relEnt
import Definitions.Def_RouzeFranca_LearnGibbs_W1Le

namespace RouzeFranca.LearnGibbs

/-- A state `σ` satisfies a **transportation cost inequality** with constant `α` (for the
Wasserstein distance induced by `lip`) if for every state `ρ`,
`W₁(ρ, σ) ≤ √(D(ρ‖σ) / (2α))`.

Rouzé, Stilck França, arXiv:2107.03333v4, §B.3, Eq. (44), p. 25: "A quantum state σ satisfies a
transportation cost inequality with constant α > 0 if for any other state ρ it holds that:
W1(ρ, σ) ≤ sqrt((1/(2α)) D(ρ∥σ))".

**Formalization Note.** States are `WildeQIT.IsDensityOperator` (PSD, trace one). The relative
entropy is the natural-log `relEnt` in `EReal`; the inequality is required only when
`D(ρ‖σ)` is a real number `d`, because `W₁ ≤ +∞` holds trivially. `W₁ ≤ w` is `W1Le`. The
positivity `α > 0` is a hypothesis of the theorems. -/
def SatisfiesTC {n : ℕ} (lip : Mat n → ℝ) (α : ℝ) (σ : Mat n) : Prop :=
  ∀ ρ : Mat n, WildeQIT.IsDensityOperator ρ → ∀ d : ℝ, relEnt ρ σ = (d : EReal) →
    W1Le lip ρ σ (Real.sqrt (d / (2 * α)))

end RouzeFranca.LearnGibbs


