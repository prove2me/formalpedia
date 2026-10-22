-- Prove2me | Definitions.Def_StrategyproofMinimax_Circle_mech31
-- name    : StrategyproofMinimax_Circle_mech31
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T20:52:39.853734+00:00
-- url     : https://prove2.me/theorems/62315921-3060-4488-8ab5-9c46a5a5701a
-- title:
--   Mechanism 3.1: LRM on one semicircle, random center otherwise
-- statement:
--   **Mechanism 3.1.** Given a location profile $x\in G^n$ on the circle $G$ of circumference one:
--
--   1. if the agents are located on one semicircle, execute the LRM mechanism on that semicircle, treating it as an interval: $\operatorname{mech31}(x)=\operatorname{lrm}(x)$;
--   2. otherwise execute the random center mechanism: $\operatorname{mech31}(x)=\operatorname{rc}(x)$.
--
--   $$\operatorname{mech31}(x)=\begin{cases}\operatorname{lrm}(x) & \text{if the agents are on one semicircle},\\ \operatorname{rc}(x) & \text{otherwise.}\end{cases}$$
--
--   This hybrid is the mechanism that Theorem 3.1 proves strategyproof with approximation ratio $3/2$ for the maximum cost.
--
--   **Formalization Note.** `mech31 x = if OnSemicircle x then lrm x else rc x`, with the definitions `OnSemicircle`, `lrm` and `rc` of this mission. The tie-break of `lrm` for agents occupying exactly one antipodal pair is part of `lrm`.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 517, Mechanism 3.1

import Mathlib
import Definitions.Def_StrategyproofMinimax_Circle_lrm
import Definitions.Def_StrategyproofMinimax_Circle_rc

namespace StrategyproofMinimax.Circle

open MeasureTheory

/-- Mechanism 3.1 (p. 517): if the agents are located on one semicircle, run the LRM mechanism
on that semicircle, treated as an interval; otherwise run the random center (RC) mechanism. -/
noncomputable def mech31 {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) :
    Measure (AddCircle (1 : ℝ)) := by
  classical
  exact if OnSemicircle x then lrm x else rc x

end StrategyproofMinimax.Circle


