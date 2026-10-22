-- Prove2me | Definitions.Def_TBSGStrategyIteration_flux
-- name    : TBSGStrategyIteration_flux
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T00:21:25.015035+00:00
-- url     : https://prove2.me/theorems/9ac80fd9-c042-4304-88cd-9bd5d268de35
-- title:
--   Flux vector $x_\pi$ (Definition 3.8)
-- statement:
--   For a profile $\pi$ the **flux vector** $x_\pi \in \mathbb{R}^{1 \times n}$ is the row vector whose entry $(x_\pi)_i$ is the sum, over all initial states, of the expected total discounted cost when the players use $\pi$, the cost of the action $\pi(i)$ is $1$, and the cost of every other action is $0$:
--   $$(x_\pi)_i = \sum_{j \in S} \big(\text{value vector of } \pi \text{ for the costs } \mathbf 1_{\{\pi(i)\}}\big)_j .$$
--   (Lemma 3.9 of the paper identifies it with $e^T (I - \gamma P_\pi)^{-1}$.)
--
--   **Formalization Note.** `flux G π i` is defined literally as in Definition 3.8, through `valueWith` with the indicator cost of the action `π.act i`.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 5, Definition 3.8

import Mathlib
import Definitions.Def_TBSGStrategyIteration_value

namespace TBSGStrategyIteration

variable {S A : Type*} [Fintype S] [DecidableEq S] [DecidableEq A]

/-- Def. 3.8: the flux vector `x_π ∈ ℝ^{1×n}`: `(x_π)_i` is the sum, over all initial states
`j`, of the expected total discounted cost when the cost of the action `π(i)` is `1`, the cost
of every other action is `0`, and the players use `π`. -/
noncomputable def flux (G : Game S A) (π : Profile G) (i : S) : ℝ :=
  ∑ j, valueWith G (fun a => if a = π.act i then 1 else 0) π j

end TBSGStrategyIteration


