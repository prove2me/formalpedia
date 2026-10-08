-- Prove2me | Definitions.Def_SchedComplexity_Tardiness_Knapsack
-- name    : SchedComplexity_Tardiness_Knapsack
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:42:28.889003+00:00
-- url     : https://prove2.me/theorems/5ec9036b-303a-4a77-9408-7bb059147389
-- title:
--   KNAPSACK (Theorem 2(b)) as a predicate on a finite family of sizes $a:T\to\mathbb N$
-- statement:
--   **KNAPSACK** (Theorem 2(b) of the paper): given positive integers $a_1,\dots,a_t,b$, does there exist a subset $S\subseteq T=\{1,\dots,t\}$ such that
--
--   $$\sum_{j\in S}a_j=b\,?$$
--
--   The predicate $\mathrm{KnapsackYes}(a,b)$ says that such an $S$ exists, for sizes given as a function $a:T\to\mathbb N$ (rather than as a list). It holds exactly when the list form $\mathrm{KnapsackYes}((a_1,\dots,a_t),b)$ of `SchedComplexity.OneMachine.Knapsack` holds. Positivity of $a_1,\dots,a_t,b$ is not part of the predicate: it is a membership condition of the KNAPSACK language $\mathsf{KNAPSACK}$ of `SchedComplexity.OneMachine.Knapsack`, which this file imports so that the missions using the function form also have the language.
--
--   The function form is the one in which the constructions of Theorem 4(a) and 4(d) of the paper are written: they index jobs by $T$ and refer to $a_j$ for $j\in T$.
--
--   **Formalization Note** Indices are 0-based: $T$ is `Fin t`. "$S\subset T$" in the paper is an arbitrary subset (possibly empty or all of $T$); with $b>0$ the empty set is never a solution.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 14, Theorem 2(b)

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_SchedComplexity_OneMachine_Knapsack

namespace SchedComplexity.Tardiness

open CookPvsNP ProjSchedTW.Complexity

/-- KNAPSACK (Brucker, Lenstra & Rinnooy Kan 1975, Theorem 2(b), p. 14): given sizes
`a_1, …, a_t` (here `a : Fin t → ℕ`, 0-based) and `b`, is there a subset `S` of
`T = {1, …, t}` with `Σ_{j ∈ S} a_j = b`? The positivity of the data is not part of this
predicate. The KNAPSACK language, with positivity as a membership condition, is
`SchedComplexity.OneMachine.knapsackLang` (imported above), stated with the list form
`SchedComplexity.OneMachine.KnapsackYes`; `KnapsackYes a b` holds iff
`SchedComplexity.OneMachine.KnapsackYes (List.ofFn a) b` does. -/
def KnapsackYes {t : ℕ} (a : Fin t → ℕ) (b : ℕ) : Prop :=
  ∃ S : Finset (Fin t), ∑ j ∈ S, a j = b

end SchedComplexity.Tardiness


