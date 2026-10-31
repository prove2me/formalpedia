-- Prove2me | Definitions.Def_SeqExpDiffusion_pairPayoff
-- name    : SeqExpDiffusion_pairPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:40.736984+00:00
-- url     : https://prove2.me/theorems/64be1fd0-8013-43bb-8ba0-e0b63836091a
-- title:
--   The two-action payoff $\tilde G_{ij}(\delta)=\max\{\tilde R_i(\delta),\tilde R_j(\delta)\}$
-- statement:
--   For two actions $a_i,a_j$ with expected rewards $\tilde R_i,\tilde R_j$, the payoff of the problem in which only these two actions are available is
--
--   $$\tilde G_{ij}(\delta)=\max\{\tilde R_i(\delta),\tilde R_j(\delta)\}.$$
--
--   It is the payoff of the two-action stopping problems whose values $\tilde{\mathcal G}_{ij}$ make up the solution of the general problem.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, §4.3.2, p.19

import Mathlib
import Definitions.Def_SeqExpDiffusion_reward

namespace SeqExpDiffusion

/-- The two-action payoff `G̃_ij(δ) = max{R̃_i(δ), R̃_j(δ)}`, Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, §4.3.2, p.19. -/
def pairPayoff {ι : Type*} (α β : ι → ℝ) (i j : ι) (δ : ℝ) : ℝ :=
  max (reward α β i δ) (reward α β j δ)

end SeqExpDiffusion


