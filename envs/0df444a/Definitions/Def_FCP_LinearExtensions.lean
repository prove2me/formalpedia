-- Prove2me | Definitions.Def_FCP_LinearExtensions
-- name    : FCP_LinearExtensions
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T19:07:08.548967+00:00
-- url     : https://prove2.me/theorems/1a5f3d67-7bc6-49c1-86a4-053707acc00a
-- title:
--   Linear extensions of a finite partial order
-- statement:
--   For a finite partially ordered set $P$ with $|P| = N$ elements, a **linear extension** is recorded as a bijection $e : P \to \{0, 1, \dots, N-1\}$ that is order-preserving: $x \le y$ implies $e(x) \le e(y)$. The set of all such bijections is the sample space over which the probability $\Pr[\,x \text{ before } y\,]$ in the $1/3$--$2/3$ conjecture is computed.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/conjecture_1_3_to_2_3.lean); https://en.wikipedia.org/wiki/1/3%E2%80%932/3_conjecture

import Mathlib

namespace FCP.Order

/-- The set of linear extensions of a finite partial order `P`, represented as the
order-preserving bijections from `P` onto `Fin (card P)`. -/
def LinearExtensions (P : Type) [Fintype P] [PartialOrder P] :
    Set (P ≃ Fin (Fintype.card P)) :=
  {e | ∀ x y : P, x ≤ y → e x ≤ e y}

end FCP.Order


