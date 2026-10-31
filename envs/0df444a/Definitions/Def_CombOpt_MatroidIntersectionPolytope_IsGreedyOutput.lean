-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsGreedyOutput
-- name    : CombOpt_MatroidIntersectionPolytope_IsGreedyOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:33.519122+00:00
-- url     : https://prove2.me/theorems/d5261fb7-fcb1-4a6e-8684-571cb24bc109
-- title:
--   $J$ is a set found by the Greedy Algorithm
-- statement:
--   For a matroid $M=(S,\mathcal I)$ and weights $c\in\mathbb R^S$, the **Greedy Algorithm** is:
--
--   > Set $J=\emptyset$. While there exists $e\notin J$ with $c_e>0$ and $J\cup\{e\}\in\mathcal I$, choose such $e$ with $c_e$ maximum and replace $J$ by $J\cup\{e\}$.
--
--   A set $J$ is *found by the Greedy Algorithm* if some run of the algorithm returns it: there is a sequence $e_1,\dots,e_k$ of distinct elements with $J=\{e_1,\dots,e_k\}$ such that each $e_{i+1}$ is, among the elements $e\notin\{e_1,\dots,e_i\}$ with $c_e>0$ and $\{e_1,\dots,e_i,e\}\in\mathcal I$, one of maximum weight, and at the end no $e\notin J$ has $c_e>0$ and $J\cup\{e\}\in\mathcal I$.
--
--   **Formalization Note** The algorithm leaves ties open ("choose such $e$"); the predicate accepts every run, i.e. every way of breaking ties.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, Greedy Algorithm, p. 274 (PDF p. 281)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid

namespace CombOpt.MatroidIntersectionPolytope

/-- **A set found by the Greedy Algorithm.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, p. 274 (PDF p. 281):

    Greedy Algorithm
    Set J = ∅;
    While there exists e ∉ J with c_e > 0 and J ∪ {e} ∈ I
        Choose such e with c_e maximum;
        Replace J by J ∪ {e}.

`IsGreedyOutput M c J` holds when some run of this algorithm returns `J`: there is a list
`[e₁, …, e_k]` of distinct elements with `J = {e₁, …, e_k}` such that, writing
`J_{i} = {e₁, …, e_i}`, each `e_{i+1}` is an element `e ∉ J_i` with `c_e > 0` and
`J_i ∪ {e} ∈ I` whose weight is maximum among all such elements, and at the end no `e ∉ J` has
`c_e > 0` and `J ∪ {e} ∈ I`.

**Formalization Note.** The algorithm leaves ties unresolved ("choose such e"); the predicate
accepts every run, i.e. every tie-breaking. `J_i` is `(l.take i).toFinset`. -/
def IsGreedyOutput {S : Type*} [Fintype S] [DecidableEq S] (M : FinMatroid S) (c : S → ℝ)
    (J : Finset S) : Prop :=
  ∃ l : List S, l.Nodup ∧ J = l.toFinset ∧
    (∀ (i : ℕ) (hi : i < l.length),
      l[i] ∉ (l.take i).toFinset ∧ 0 < c l[i] ∧ M.Indep (insert l[i] (l.take i).toFinset) ∧
      ∀ f : S, f ∉ (l.take i).toFinset → 0 < c f → M.Indep (insert f (l.take i).toFinset) →
        c f ≤ c l[i]) ∧
    ∀ f : S, f ∉ J → 0 < c f → ¬ M.Indep (insert f J)

end CombOpt.MatroidIntersectionPolytope


