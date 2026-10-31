-- Prove2me | Definitions.Def_CombOpt_MatroidPolytope_GreedyStep
-- name    : CombOpt_MatroidPolytope_GreedyStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:57.061025+00:00
-- url     : https://prove2.me/theorems/75264a84-0646-4c1c-83c7-87f986be52ae
-- title:
--   One iteration of the Greedy Algorithm
-- statement:
--   The **Greedy Algorithm** for a family $\mathcal I$ and weights $c\in\mathbb R^S$ is:
--
--   Set $J=\emptyset$; while there exists $e\notin J$ with $c_e>0$ and $J\cup\{e\}\in\mathcal I$: choose such $e$ with $c_e$ maximum and replace $J$ by $J\cup\{e\}$.
--
--   One iteration takes $J$ to $J\cup\{e\}$, where $e\notin J$, $c_e>0$, $J\cup\{e\}\in\mathcal I$, and $c_e\ge c_f$ for every $f\notin J$ with $c_f>0$ and $J\cup\{f\}\in\mathcal I$.
--
--   **Formalization Note** Ties are broken arbitrarily, so one iteration is a relation between the current set and the next one: every admissible choice of $e$ is a possible step.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, p. 274 (PDF p. 281), the box "Greedy Algorithm"

import Mathlib

namespace CombOpt.MatroidPolytope

/-- **One iteration of the Greedy Algorithm.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, p. 274 (PDF p. 281), the box *Greedy Algorithm*: "Set J = ∅; While there exists
e ∉ J with c_e > 0 and J ∪ {e} ∈ I: Choose such e with c_e maximum; Replace J by J ∪ {e}."

`GreedyStep I c J J'` says that one pass of the while loop can take the current set `J` to
`J'`: there is an element `e ∉ J` with `c_e > 0` and `J ∪ {e} ∈ I` whose weight is maximum
among all such elements, and `J' = J ∪ {e}`.

**Formalization Note.** Ties are broken arbitrarily in the book, so this is a relation (every
admissible choice is a possible step), not a function. -/
def GreedyStep {α : Type*} [DecidableEq α] (I : Finset α → Prop) (c : α → ℝ)
    (J J' : Finset α) : Prop :=
  ∃ e : α, e ∉ J ∧ 0 < c e ∧ I (insert e J) ∧
    (∀ f : α, f ∉ J → 0 < c f → I (insert f J) → c f ≤ c e) ∧ J' = insert e J

end CombOpt.MatroidPolytope


