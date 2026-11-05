-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_Policy
-- name    : BauerleRiederMDP_FiniteHorizon_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:08.961387+00:00
-- url     : https://prove2.me/theorems/8006043a-5a51-4140-9181-e930aa2a5d89
-- title:
--   $N$-stage Markov policy $\pi=(f_0,\dots,f_{N-1})$
-- statement:
--   An **$N$-stage policy** is a sequence $\pi=(f_0,\dots,f_{N-1})$ of decision rules, $f_n\in F_n$, where a decision rule at time $n$ is a measurable map $f:E\to A$ with $f(x)\in D_n(x)$ for all $x\in E$.
--
--   This is the class over which the value function $V_n$ takes its supremum.
--
--   **Formalization Note.** The index set is `Fin N`, so a policy has no component at a time $n\ge N$. For $N=0$ there is exactly one policy, the empty one, even when $A$ is empty.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.1.5 b), p.16

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel IsDecisionRule)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- An `N`-stage (Markov) policy `π = (f_0, …, f_{N-1})`, `f_n ∈ F_n` (Bäuerle & Rieder, Markov
Decision Processes with Applications to Finance (2011), Definition 2.1.5 b), p.16, PDF 31).

**Formalization Note.** The index set is `Fin N`, so a policy has no component at any time
`n ≥ N`. In particular for `N = 0` there is exactly one policy, the empty one, for every action
space, even an empty one. The retired `MDPFinance.Bellman.Policy` asks for a measurable map
`E → A` at *every* `n : ℕ`; for `N = 0`, `E` nonempty and `A` empty it has no element, its
supremum `V` is `⊥` and `V_N = g_N` fails. -/
def Policy {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) : Type u :=
  {f : Fin N → E → A // ∀ n : Fin N, IsDecisionRule M n (f n)}

end BauerleRiederMDP.FiniteHorizon


