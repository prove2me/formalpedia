-- Prove2me | Definitions.Def_WildeQIT_Feedback_pastOutputs
-- name    : WildeQIT_Feedback_pastOutputs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:54.952333+00:00
-- url     : https://prove2.me/theorems/e58689e7-dda1-49ec-921f-3b80fdbf675a
-- title:
--   Fed-back outputs $y^{i-1}=(y_1,\dots,y_{i-1})$
-- statement:
--   For an output word $y^n=(y_1,\dots,y_n)\in\mathcal Y^n$ and a time $i$, the **fed-back outputs** at time $i$ are the prefix
--   $$
--   y^{i-1}=(y_1,\dots,y_{i-1}),
--   $$
--   the outputs the receiver has seen, and sent back to the sender, before the $i$-th channel use. They are the second argument of the feedback encoder $x_i(m,y^{i-1})$.
--
--   **Formalization Note** Times are 0-based: for `y : Fin n → β` and `i : Fin n`, `pastOutputs y i : Fin i → β` lists the outputs at times $0,\dots,i-1$; at time $0$ it is the empty word.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 21.5.1, p. 604 ("all of the previously received values Y_1, …, Y_{i−1}")

import Mathlib.Data.Fin.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §21.5.1, proof of
Theorem 21.5.1, p. 604: the outputs `Y₁, …, Y_{i−1}` fed back to the sender before time `i`.
-/

namespace WildeQIT.Feedback

/-- **The fed-back outputs `y^{i−1} = (y₁, …, y_{i−1})`.** Wilde, *From Classical to Quantum
Shannon Theory*, arXiv:1106.1445v8, proof of Theorem 21.5.1, p. 604: the symbol `xᵢ(m, Y^{i−1})`
depends on "all of the previously received values `Y₁, …, Y_{i−1}` from the receiver".

**Formalization Note.** Times are `Fin n`, 0-based: for an output word `y : Fin n → β` and a
time `i`, `pastOutputs y i : Fin i → β` is the word of the `i` outputs at times `0, …, i − 1`
(the empty word at time `0`). -/
def pastOutputs {β : Type} {n : ℕ} (y : Fin n → β) (i : Fin n) : Fin i → β :=
  fun j => y (Fin.castLE i.isLt.le j)

end WildeQIT.Feedback


