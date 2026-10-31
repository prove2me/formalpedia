-- Prove2me | Definitions.Def_FASTournament_IsOneSum
-- name    : FASTournament_IsOneSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:29.561436+00:00
-- url     : https://prove2.me/theorems/4060c4df-cec6-4dcf-a587-f40a830b1b96
-- title:
--   $T$ is a 1-sum of $T_1$ and $T_2$
-- statement:
--   Let $T_1=(V_1,A_1)$ and $T_2=(V_2,A_2)$ be tournaments with $|V_i|\ge 3$. Suppose that $(a_1,b_1)$ is a special arc of $T_1$ with $d^+_{T_1}(a_1)=1$ and $(b_2,a_2)$ is a special arc of $T_2$ with $d^-_{T_2}(a_2)=1$. A tournament $T$ **is a 1-sum of $T_1$ and $T_2$** if it is (isomorphic to) the 1-sum of $T_1$ and $T_2$ over $(a_1,b_1)$ and $(b_2,a_2)$ for some such arcs.
--
--   **Formalization Note** An arc $(a_1,b_1)$ with $d^+(a_1)=1$ is special because $a_1$ is a near-sink, and likewise for $(b_2,a_2)$; degrees are cardinalities of out- and in-neighbourhoods.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.5

import Mathlib
import Definitions.Def_FASTournament_oneSum
import Definitions.Def_FASTournament_IsTournament
import Definitions.Def_FASTournament_Isomorphic

namespace FASTournament

/-- **`T` is a 1-sum of the tournaments `T₁` and `T₂`.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.5: "Let Ti = (Vi, Ai) be a tournament, with |Vi| ≥ 3 for i = 1, 2. … Suppose that
(a1, b1) is a special arc of T1 with d+T1(a1) = 1 and (b2, a2) is a special arc of T2 with
d−T2(a2) = 1. The 1-sum of T1 and T2 over (a1, b1) and (b2, a2) is …".

`T₁, T₂` are tournaments with at least three vertices, `a₁ → b₁` is an arc of `T₁` with
`a₁` of out-degree `1`, `b₂ → a₂` is an arc of `T₂` with `a₂` of in-degree `1`, and `T` is
isomorphic to `oneSum T₁ a₁ b₁ T₂ b₂ a₂`.

**Formalization Note.** Degrees are `Nat.card` of the out- and in-neighbourhoods; `3 ≤ Nat.card Vᵢ`
forces `Vᵢ` finite. An arc `(a₁, b₁)` with `d⁺(a₁) = 1` is automatically special (`a₁` is a
near-sink, p.5), and likewise `(b₂, a₂)` with `d⁻(a₂) = 1`. -/
def IsOneSum {V V₁ V₂ : Type*} (T : Digraph V) (T₁ : Digraph V₁) (T₂ : Digraph V₂) : Prop :=
  IsTournament T₁ ∧ IsTournament T₂ ∧ 3 ≤ Nat.card V₁ ∧ 3 ≤ Nat.card V₂ ∧
    ∃ (a₁ b₁ : V₁) (b₂ a₂ : V₂), T₁.Adj a₁ b₁ ∧ Nat.card {u // T₁.Adj a₁ u} = 1 ∧
      T₂.Adj b₂ a₂ ∧ Nat.card {u // T₂.Adj u a₂} = 1 ∧ Isomorphic T (oneSum T₁ a₁ b₁ T₂ b₂ a₂)

end FASTournament


