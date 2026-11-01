-- Prove2me | Definitions.Def_MarkovSA_T1
-- name    : MarkovSA_T1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:15.433998+00:00
-- url     : https://prove2.me/theorems/07d4470c-fdca-42c2-b1c1-986fa7765cf1
-- title:
--   $T_1=\alpha_k\langle\nabla M(x_k-x^*),\bar F(x_k)-x_k\rangle$
-- statement:
--   The expected-update term of the one-step expansion (17):
--
--   $$
--   T_1=\alpha_k\langle\nabla M(x_k-x^*),\bar F(x_k)-x_k\rangle.
--   $$
--
--   **Formalization Note** $\langle\nabla M(z),v\rangle$ is the Fréchet derivative of $M$ at $z$ applied to $v$.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Eq. (17), p.25

import Mathlib
import Definitions.Def_MarkovSA_moreauM
import Definitions.Def_MarkovSA_Fbar

namespace MarkovSA

/-- `T₁ = α_k ⟨∇M(x_k − x*), F̄(x_k) − x_k⟩`, the expected-update term of Eq. (17) (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.25), along a process `x`.
`⟨∇M(z), v⟩` is `fderiv ℝ M z v`. -/
noncomputable def T1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴] {Ω : Type*} (s : E → ℝ) (θ : ℝ)
    (F : E → 𝒴 → E) (μ : 𝒴 → ℝ) (α : ℕ → ℝ) (x : ℕ → Ω → E) (xstar : E) (k : ℕ) (ω : Ω) : ℝ :=
  α k * fderiv ℝ (moreauM s θ) (x k ω - xstar) (Fbar F μ (x k ω) - x k ω)

end MarkovSA


