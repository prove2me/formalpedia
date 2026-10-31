-- Prove2me | Definitions.Def_FASTournament_oneSum
-- name    : FASTournament_oneSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:48.620992+00:00
-- url     : https://prove2.me/theorems/7ce3c6f8-428c-4c18-a003-63f73db7e39c
-- title:
--   The 1-sum construction
-- statement:
--   Let $T_1=(V_1,A_1)$ and $T_2=(V_2,A_2)$ be tournaments, $(a_1,b_1)$ an arc of $T_1$ and $(b_2,a_2)$ an arc of $T_2$. The **1-sum of $T_1$ and $T_2$ over $(a_1,b_1)$ and $(b_2,a_2)$** is the tournament arising from the disjoint union of $T_1\setminus a_1$ and $T_2\setminus a_2$ by identifying $b_1$ with $b_2$ (the resulting vertex $b$ is the **hub**) and adding all arcs from $T_1\setminus\{a_1,b_1\}$ to $T_2\setminus\{a_2,b_2\}$.
--
--   **Formalization Note** The vertex set is $(V_1\setminus\{a_1\})\sqcup(V_2\setminus\{a_2,b_2\})$, with the hub represented by $b_1$; the hub keeps the arcs of $b_1$ in $T_1$ and of $b_2$ in $T_2$. The conditions on the special arcs are imposed in `IsOneSum`.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.5

import Mathlib

namespace FASTournament

/-- **The 1-sum of `T₁` and `T₂` over `(a₁, b₁)` and `(b₂, a₂)`.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.5: "The 1-sum of T1 and T2 over (a1, b1) and (b2, a2) is the tournament arising from
the disjoint union of T1\a1 and T2\a2 by identifying b1 with b2 (the resulting vertex is
denoted by b) and adding all arcs from T1\{a1, b1} to T2\{a2, b2}. We call b the hub of the
1-sum."

The vertex set is `(V₁ ∖ {a₁}) ⊔ (V₂ ∖ {a₂, b₂})`; the hub `b` is the left copy of `b₁`, and it
carries the arcs of `b₁` in `T₁` and of `b₂` in `T₂`. Arcs inside each side are those of `T₁`,
`T₂`; every vertex of `T₁ ∖ {a₁, b₁}` sends an arc to every vertex of `T₂ ∖ {a₂, b₂}`.

**Formalization Note.** Only the construction is defined here; the conditions on the special
arcs are in `IsOneSum`. -/
def oneSum {V₁ V₂ : Type*} (T₁ : Digraph V₁) (a₁ b₁ : V₁) (T₂ : Digraph V₂) (b₂ a₂ : V₂) :
    Digraph ({v // v ≠ a₁} ⊕ {v // v ≠ a₂ ∧ v ≠ b₂}) where
  Adj
    | .inl x, .inl y => T₁.Adj x.1 y.1
    | .inr x, .inr y => T₂.Adj x.1 y.1
    | .inl x, .inr y => x.1 = b₁ → T₂.Adj b₂ y.1
    | .inr x, .inl y => y.1 = b₁ ∧ T₂.Adj x.1 b₂

end FASTournament


