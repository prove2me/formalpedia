-- Prove2me | Definitions.Def_TBSGStrategyIteration_modCost
-- name    : TBSGStrategyIteration_modCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T00:16:26.483259+00:00
-- url     : https://prove2.me/theorems/3fe5dfa3-e6a6-48f4-b59e-8dee5e51454b
-- title:
--   Modified cost vector $c^\pi$ and modified value vectors $v^\pi_{\pi'}$ (Definitions 3.3, 3.5)
-- statement:
--   Let $J \in \mathbb{R}^{m\times n}$ be the matrix with $J_{a,i} = 1$ iff $a \in A_i$. The **modified cost vector** of a profile $\pi$ is $c^\pi = c - (J - \gamma P) v_\pi \in \mathbb{R}^m$, that is, for every action $a$,
--   $$(c^\pi)_a = c(a) - (v_\pi)_{s(a)} + \gamma \sum_{j \in S} P_{a,j} (v_\pi)_j .$$
--   It must not be confused with $c_\pi \in \mathbb{R}^n$, the costs of the actions of $\pi$. For two profiles $\pi, \pi'$, the **modified value vector** $v^\pi_{\pi'}$ is the value vector of $\pi'$ when the costs $c$ are replaced by $c^\pi$.
--
--   **Formalization Note.** `modCost G π a` is $(c^\pi)_a$ and `modValue G π π'` is $v^\pi_{\pi'}$ = `valueWith G (modCost G π) π'`.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 5, Definitions 3.3 and 3.5

import Mathlib
import Definitions.Def_TBSGStrategyIteration_value

namespace TBSGStrategyIteration

variable {S A : Type*} [Fintype S] [DecidableEq S]

/-- Def. 3.3: the modified cost vector `c^π = c − (J − γP) v_π ∈ ℝ^m`. Since `J_{a,i} = 1`
iff `s(a) = i`, its entry at the action `a` is
`(c^π)_a = c(a) − (v_π)_{s(a)} + γ ∑_j P_{a,j} (v_π)_j`. -/
noncomputable def modCost (G : Game S A) (π : Profile G) (a : A) : ℝ :=
  G.c a - (value G π (G.src a) - G.γ * ∑ j, G.P a j * value G π j)

/-- Def. 3.5: the modified value vector `v^π_{π'}`, the value vector of `π'` for the modified
cost vector `c^π` in place of `c`. -/
noncomputable def modValue (G : Game S A) (π π' : Profile G) : S → ℝ :=
  valueWith G (modCost G π) π'

end TBSGStrategyIteration


