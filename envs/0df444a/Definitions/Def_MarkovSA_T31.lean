-- Prove2me | Definitions.Def_MarkovSA_T31
-- name    : MarkovSA_T31
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:33.476649+00:00
-- url     : https://prove2.me/theorems/96e24fbb-20da-4633-a33f-c01a6f43acf2
-- title:
--   $T_{31}=\langle\nabla M(x_k-x^*)-\nabla M(x_{k-t_k}-x^*),F(x_k,Y_k)-\bar F(x_k)\rangle$
-- statement:
--   The first piece of the decomposition (18) of $T_3$:
--
--   $$
--   T_{31}=\langle\nabla M(x_k-x^*)-\nabla M(x_{k-t_k}-x^*),\,F(x_k,Y_k)-\bar F(x_k)\rangle.
--   $$
--
--   As printed in (18), $T_3=\alpha_k(T_{31}+T_{32}+T_{33})$: the three terms do not carry the factor $\alpha_k$. The lagged index $j$ is $k-t_k$.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Eq. (18), p.26

import Mathlib
import Definitions.Def_MarkovSA_moreauM
import Definitions.Def_MarkovSA_Fbar

namespace MarkovSA

/-- `T₃₁ = ⟨∇M(x_k − x*) − ∇M(x_j − x*), F(x_k, Y_k) − F̄(x_k)⟩`, Eq. (18) (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.26). The lagged index `j` is `k − t_k`. As printed, `T₃ = α_k(T₃₁ + T₃₂ + T₃₃)`: `T₃₁, T₃₂, T₃₃` do **not** carry the factor `α_k`. -/
noncomputable def T31 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴] {Ω : Type*} (s : E → ℝ) (θ : ℝ)
    (F : E → 𝒴 → E) (μ : 𝒴 → ℝ) (x : ℕ → Ω → E) (Y : ℕ → Ω → 𝒴) (xstar : E)
    (k j : ℕ) (ω : Ω) : ℝ :=
  fderiv ℝ (moreauM s θ) (x k ω - xstar) (F (x k ω) (Y k ω) - Fbar F μ (x k ω)) -
    fderiv ℝ (moreauM s θ) (x j ω - xstar) (F (x k ω) (Y k ω) - Fbar F μ (x k ω))

end MarkovSA


