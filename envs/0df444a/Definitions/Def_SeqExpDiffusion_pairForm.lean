-- Prove2me | Definitions.Def_SeqExpDiffusion_pairForm
-- name    : SeqExpDiffusion_pairForm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:10:58.442037+00:00
-- url     : https://prove2.me/theorems/4df5ee18-854d-4cfc-92fa-701734ef611b
-- title:
--   The closed form (18) of the two-action value $\tilde{\mathcal G}_{ij}$
-- statement:
--   Given thresholds $\underline\delta,\bar\delta$ and constants $C^0,C^1$, the function
--
--   $$\tilde{\mathcal G}_{ij}(\delta)=\begin{cases}\tilde G_{ij}(\delta) & 0\le\delta\le\underline\delta,\\ C^0(1-\delta)^\gamma\delta^{1-\gamma}+C^1(1-\delta)^{1-\gamma}\delta^\gamma & \underline\delta<\delta<\bar\delta,\\ \tilde G_{ij}(\delta)&\bar\delta\le\delta\le1,\end{cases}$$
--
--   with $\gamma=(1+\sqrt{1+8r/\tilde\sigma^2})/2$ and $\tilde G_{ij}=\max\{\tilde R_i,\tilde R_j\}$. With the admissible quadruple it is the value of the two-action problem.
--
--   **Formalization Note** The middle branch is used on the open interval only; at the thresholds the page's branches agree by value matching, and the power $0^{1-\gamma}$ would be a default value when $\underline\delta=0$.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, Proposition 5, display (18), p.20

import Mathlib
import Definitions.Def_SeqExpDiffusion_pairPayoff
import Definitions.Def_SeqExpDiffusion_gammaOf
import Definitions.Def_SeqExpDiffusion_contValue

namespace SeqExpDiffusion

/-- The closed form (18) of the two-action value `𝒢̃_ij`, Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, Proposition 5, p.20:
`G̃_ij(δ)` for `δ ∉ (δ̲, δ̄)`, and `C⁰ (1 − δ)^γ δ^{1−γ} + C¹ (1 − δ)^{1−γ} δ^γ` for
`δ ∈ (δ̲, δ̄)`, with `δ̲ = a`, `δ̄ = b`.

**Formalization Note** The middle branch is used on the open interval `(a, b)` only; at the
thresholds the page's branches agree by value matching (17), and `0^{1−γ}` would be a junk value
when `a = 0`. -/
noncomputable def pairForm {ι : Type*} (r σ : ℝ) (α β : ι → ℝ) (i j : ι) (a b C₀ C₁ : ℝ)
    (δ : ℝ) : ℝ :=
  if δ ∈ Set.Ioo a b then contValue (gammaOf r σ) C₀ C₁ δ else pairPayoff α β i j δ

end SeqExpDiffusion


