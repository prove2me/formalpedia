-- Prove2me | Definitions.Def_SeqExpDiffusion_payoff
-- name    : SeqExpDiffusion_payoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:40.759991+00:00
-- url     : https://prove2.me/theorems/54cb3b70-5968-4714-a39a-a60da6e3142a
-- title:
--   The payoff $G(\delta)=\max_{a}\mathbb E_\delta[\mathcal R(a,\Theta)]$
-- statement:
--   For a nonempty finite action set $\mathscr A$ with affine expected rewards $\tilde R_a(\delta)=\tilde\alpha_a+\tilde\beta_a\delta$, the payoff of stopping at belief $\delta$ and choosing the best action is
--
--   $$G(\delta)=\max_{a\in\mathscr A}\tilde R_a(\delta).$$
--
--   It is the reward collected at the stopping time in the optimal stopping problem (12); it is convex and piecewise linear in $\delta$.
--
--   **Formalization Note** The maximum is taken over all elements of a finite nonempty type.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, display (1), p.7

import Mathlib
import Definitions.Def_SeqExpDiffusion_reward

namespace SeqExpDiffusion

/-- The payoff `G(δ) = max_{a ∈ 𝒜} E_δ[R(a, Θ)]` of stopping at belief `δ`: Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, display (1),
p.7.

**Formalization Note** The action set `𝒜` is a nonempty finite type `ι`, and the maximum is
`Finset.sup'` over all of `ι`. -/
noncomputable def payoff {ι : Type*} [Fintype ι] [Nonempty ι] (α β : ι → ℝ) (δ : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => reward α β a δ)

end SeqExpDiffusion


