-- Prove2me | Definitions.Def_HartSchmeidler_FinStrat_Peleg
-- name    : HartSchmeidler_FinStrat_Peleg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:08:46.312088+00:00
-- url     : https://prove2.me/theorems/51b92f40-d84e-444f-9214-5b2e187663b8
-- title:
--   Examples 1–2 — Peleg's infinite-player binary games
-- statement:
--   The players are the positive integers $N=\{1,2,\ldots\}$, and each chooses $s^i\in\{0,1\}$. **Case 1** consists of profiles with only finitely many $1$'s; its complement is Case 0. Example 1 pays player $i$ the amount $s^i$ in Case 1 and $-s^i$ in Case 0. Example 2 changes only the Case 1 payoff:
--
--   $$h^i_2(s)=\begin{cases}s^i/i^2,&s\in\mathrm{Case\ 1},\\-s^i,&s\in\mathrm{Case\ 0}.\end{cases}$$
--
--   The Example 2 payoff is the object of the paper's nonexistence result for countably additive correlated equilibria.
--
--   **Formalization Note.** Players are positive naturals, so $i=0$ never occurs in the denominator $i^2$. Case 1 is finite support of the set of coordinates equal to $1$, exactly the convergence case of the paper's binary sum. Both payoff functions are bounded and measurable for the countable product σ-algebra, although they are discontinuous.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), pp. 21–22, Examples 1–2

import Definitions.Def_HartSchmeidler_FinStrat_Game

/-! Peleg's examples in Hart and Schmeidler (1989), pp. 21–22. -/

namespace HartSchmeidler.FinStrat

open MeasureTheory

/-- Case 1: only finitely many positive-integer players choose action 1. -/
def pelegCase1 : Set (PNat → Fin 2) :=
  {s | {i : PNat | s i = 1}.Finite}

/-- Example 1 payoff: action 1 earns +1 in Case 1 and −1 otherwise. -/
noncomputable def pelegPayoff (i : PNat) (s : PNat → Fin 2) : ℝ := by
  classical
  exact if s ∈ pelegCase1 then (s i : ℕ) else -((s i : ℕ) : ℝ)

/-- Example 2 payoff: Case 1's reward for action 1 is 1/i². -/
noncomputable def peleg2Payoff (i : PNat) (s : PNat → Fin 2) : ℝ := by
  classical
  exact if s ∈ pelegCase1 then ((s i : ℕ) : ℝ) / ((i : ℕ) : ℝ) ^ 2
    else -((s i : ℕ) : ℝ)

end HartSchmeidler.FinStrat


