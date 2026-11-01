-- Prove2me | Definitions.Def_MarkovSA_T2
-- name    : MarkovSA_T2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:21.369286+00:00
-- url     : https://prove2.me/theorems/65fb84fa-5777-4ac9-9fc9-7c5b68a02d7c
-- title:
--   $T_2=\alpha_k\langle\nabla M(x_k-x^*),w_k\rangle$
-- statement:
--   The martingale-noise term of (17):
--
--   $$
--   T_2=\alpha_k\langle\nabla M(x_k-x^*),w_k\rangle.
--   $$
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Eq. (17), p.25

import Mathlib
import Definitions.Def_MarkovSA_moreauM

namespace MarkovSA

/-- `T₂ = α_k ⟨∇M(x_k − x*), w_k⟩`, the martingale-noise term of Eq. (17) (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.25). -/
noncomputable def T2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Ω : Type*} (s : E → ℝ) (θ : ℝ)
    (α : ℕ → ℝ) (x : ℕ → Ω → E) (w : ℕ → Ω → E) (xstar : E) (k : ℕ) (ω : Ω) : ℝ :=
  α k * fderiv ℝ (moreauM s θ) (x k ω - xstar) (w k ω)

end MarkovSA


