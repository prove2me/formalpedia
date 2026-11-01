-- Prove2me | Definitions.Def_ProcNetStab_ValidChoice
-- name    : ProcNetStab_ValidChoice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:41.209244+00:00
-- url     : https://prove2.me/theorems/f85b28e0-ebdf-46d0-bd98-968906dbbd97
-- title:
--   Profiles of revealed preference relations $\mathcal R(g)$
-- statement:
--   Let $g$ be the observed network. When a link $ab \in g$ is observed, both endpoints reveal that they weakly prefer $g$ to $g - ab$; when $ab \notin g$, at least one endpoint reveals that it strictly prefers $g$ to $g + ab$. A **choice of revealing endpoints** is a relation $C$ on $V$ ($C(a, b)$: "agent $a$ reveals $g \succ_a g + ab$") such that every non-link $ab \notin g$ has $C(a, b)$ or $C(b, a)$. The **profile of revealed preference relations** of $C$ is $\langle R_a, P_a\rangle_{a \in V}$ with
--   $$
--   R_a = \{(g, g - ab) : ab \in g\} \cup \{(g, g + ab) : ab \notin g,\ C(a, b)\}, \qquad P_a = \{(g, g + ab) : ab \notin g,\ C(a, b)\}.
--   $$
--   The set $\mathcal R(g)$ of the paper is the set of these profiles over all valid choices $C$.
--
--   **Formalization Note** Definition A.5 asks for "the smallest profile" satisfying a clause that is a disjunction, so no unique smallest profile exists; the profiles are therefore parametrized by the nonempty sets of revealing endpoints of each non-link (`ValidChoice`, `revR`, `revP`).
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Definition A.5, pp.OA-2–OA-3

import Mathlib
import Definitions.Def_ProcNetStab_IsAdjacentNet

namespace ProcNetStab

/-- A **choice of revealing endpoints** for the observed network `g` (reading of Chiong, Qi,
*Stability of Procurement Networks* (authors' manuscript, 2025), Definition A.5, pp.OA-2–OA-3):
`C a b` means "agent `a` reveals `g ≻_a g + ab`". It is valid if every non-link `ab ∉ g`
(`a ≠ b`) has at least one revealing endpoint, as clause 2 of Definition A.5 requires. -/
def ValidChoice {V : Type*} (g : SimpleGraph V) (C : V → V → Prop) : Prop :=
  ∀ a b : V, a ≠ b → ¬ g.Adj a b → C a b ∨ C b a

/-- The relation `R_a` of the **profile of revealed preference relations** determined by the
choice `C` (Chiong, Qi, *Stability of Procurement Networks* (authors' manuscript, 2025),
Definition A.5, pp.OA-2–OA-3): the smallest relation containing `(g, g − ab)` for every link
`ab ∈ g`, and `(g, g + ab)` for every non-link `ab ∉ g` that `a` reveals (`C a b`).

**Formalization Note** Clause 2 of Definition A.5 is a disjunction, so there is no unique smallest
profile; the set `R(g)` of revealed preference profiles is parametrized by the valid choices `C`
of which endpoints reveal each non-link (a nonempty subset of `{a, b}`). -/
def revR {V : Type*} (g : SimpleGraph V) (C : V → V → Prop) (a : V)
    (x y : SimpleGraph V) : Prop :=
  (∃ b, g.Adj a b ∧ x = g ∧ y = delLink g a b) ∨
    (∃ b, a ≠ b ∧ ¬ g.Adj a b ∧ C a b ∧ x = g ∧ y = addLink g a b)

/-- The relation `P_a` of the profile of revealed preference relations determined by the choice
`C` (Chiong, Qi, *Stability of Procurement Networks* (authors' manuscript, 2025), Definition A.5,
pp.OA-2–OA-3): the pairs `(g, g + ab)` for the non-links `ab ∉ g` that `a` reveals. -/
def revP {V : Type*} (g : SimpleGraph V) (C : V → V → Prop) (a : V)
    (x y : SimpleGraph V) : Prop :=
  ∃ b, a ≠ b ∧ ¬ g.Adj a b ∧ C a b ∧ x = g ∧ y = addLink g a b

end ProcNetStab


