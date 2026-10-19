-- Prove2me | Definitions.Def_DynSetValue_DPP_SetValue
-- name    : DynSetValue_DPP_SetValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:18.05902+00:00
-- url     : https://prove2.me/theorems/de876977-630b-47e7-b674-b778351fe362
-- title:
--   Relaxed equilibrium set value and open lower envelope
-- statement:
--   For each history $(t,\omega)$ and radius $\varepsilon>0$, the relaxed value set is the union of open Euclidean balls around the cost vectors of all $\varepsilon$-equilibria:
--
--   $$
--   \mathbb V_\varepsilon(t,\omega)=\bigcup_{\alpha\in NE_\varepsilon(t,\omega)}
--   O_\varepsilon(J(t,\omega,\alpha)),\qquad
--   \mathbb V(t,\omega)=\bigcap_{\varepsilon>0}\mathbb V_\varepsilon(t,\omega).
--   $$
--
--   The open lower envelope is $\widehat{\mathbb V}_\varepsilon(t,\omega)=\bigcup_{0<\varepsilon'<\varepsilon}\mathbb V_{\varepsilon'}(t,\omega)$. The envelope is the random set whose membership event occurs in the dynamic programming principle.
--
--   **Formalization Note** For nonpositive radii, the ball is empty, so restricting the envelope's union to positive $\varepsilon'$ is equivalent to the displayed definition in the paper.
-- source:
--   Feinstein, Rudloff, Zhang, Dynamic set values for nonzero sum games with multiple equilibriums, arXiv:2002.00449v2, p. 23, first display and Proposition 3.4; p. 26, last display

import Mathlib
import Definitions.Def_DynSetValue_DPP_Game

open MeasureTheory
open scoped Topology BigOperators

namespace DynSetValue.DPP

variable {T : ℝ} (hT : 0 < T) {d N : ℕ}

/-- Values within an open ε-ball of the cost of an ε-equilibrium. -/
def Vε (G : Game T hT d N) (P0 : Measure (Ω T d))
    (t : ℝ) (ω : Ω T d) (ε : ℝ) : Set (Payoff N) :=
  {y | ∃ α : Profile hT G, NEε hT G P0 t ω ε α ∧ y ∈ Metric.ball (J hT G P0 t ω α) ε}

/-- The relaxed set value (p. 23). -/
def V (G : Game T hT d N) (P0 : Measure (Ω T d))
    (t : ℝ) (ω : Ω T d) : Set (Payoff N) :=
  ⋂ ε > 0, Vε hT G P0 t ω ε

/-- The open lower envelope of ε-set values (p. 26). -/
def Vhat (G : Game T hT d N) (P0 : Measure (Ω T d))
    (t : ℝ) (ω : Ω T d) (ε : ℝ) : Set (Payoff N) :=
  ⋃ ε' ∈ Set.Ioo (0 : ℝ) ε, Vε hT G P0 t ω ε'

end DynSetValue.DPP


