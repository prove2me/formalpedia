-- Prove2me | Definitions.Def_NashOrTriangle_IsTriangleAnswer
-- name    : NashOrTriangle_IsTriangleAnswer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:49:39.706676+00:00
-- url     : https://prove2.me/theorems/f9356f5f-15b0-4969-a987-731158d9b6b0
-- title:
--   Halted with a triangle of known strategies
-- statement:
--   The run has halted and its output is a list of $t$ row labels and $t$ column labels naming known strategies $a_1, \dots, a_t$ and $b_1, \dots, b_t$ that form a triangle of the required kind (a $t$-triangle, or a $(t, \gamma)$-triangle).
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Theorem 2.1, pp.4–5 (PDF pp.5–6)

import Mathlib
import Definitions.Def_NashOrTriangle_decode

namespace NashOrTriangle

/-- The state has halted with a triangle of the kind `Tri`: the output decodes to `t` row labels
and `t` column labels, all naming known strategies `a₁, …, a_t` and `b₁, …, b_t` (in order), and
`Tri a b` holds.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem 2.1, printed pp. 4–5 (PDF pp. 5–6): "… or a t-triangle" / "… or a
(t, c/k)-triangle". -/
def IsTriangleAnswer {A B : Type*} (t : ℕ) (Tri : (Fin t → A) → (Fin t → B) → Prop)
    (s : State A B) : Prop :=
  ∃ base : ℤ, ∃ rs cs : List ℕ, s.output = some base ∧
    decode s.core.mem base = some (Answer.triangle rs cs) ∧
    rs.length = t ∧ cs.length = t ∧
    ∃ a : Fin t → A, ∃ b : Fin t → B,
      (∀ i : Fin t, (rs[(i : ℕ)]?).bind (fun l => s.rows[l]?) = some (a i)) ∧
      (∀ j : Fin t, (cs[(j : ℕ)]?).bind (fun l => s.cols[l]?) = some (b j)) ∧
      Tri a b

end NashOrTriangle


