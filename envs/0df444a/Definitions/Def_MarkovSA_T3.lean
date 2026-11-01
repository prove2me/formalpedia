-- Prove2me | Definitions.Def_MarkovSA_T3
-- name    : MarkovSA_T3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:38.328036+00:00
-- url     : https://prove2.me/theorems/f7ab15b5-8e3d-430f-9311-aef5c221e8ad
-- title:
--   $T_3=\alpha_k\langle\nabla M(x_k-x^*),F(x_k,Y_k)-\bar F(x_k)\rangle$
-- statement:
--   The Markovian-noise term of (17):
--
--   $$
--   T_3=\alpha_k\langle\nabla M(x_k-x^*),F(x_k,Y_k)-\bar F(x_k)\rangle.
--   $$
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Eq. (17), p.25

import Mathlib
import Definitions.Def_MarkovSA_moreauM
import Definitions.Def_MarkovSA_Fbar

namespace MarkovSA

/-- `T₃ = α_k ⟨∇M(x_k − x*), F(x_k, Y_k) − F̄(x_k)⟩`, the Markovian-noise term of Eq. (17) (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.25). -/
noncomputable def T3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴] {Ω : Type*} (s : E → ℝ) (θ : ℝ)
    (F : E → 𝒴 → E) (μ : 𝒴 → ℝ) (α : ℕ → ℝ) (x : ℕ → Ω → E) (Y : ℕ → Ω → 𝒴) (xstar : E)
    (k : ℕ) (ω : Ω) : ℝ :=
  α k * fderiv ℝ (moreauM s θ) (x k ω - xstar) (F (x k ω) (Y k ω) - Fbar F μ (x k ω))

end MarkovSA


