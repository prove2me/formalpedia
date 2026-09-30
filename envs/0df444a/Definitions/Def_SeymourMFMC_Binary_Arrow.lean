-- Prove2me | Definitions.Def_SeymourMFMC_Binary_Arrow
-- name    : SeymourMFMC_Binary_Arrow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T03:17:32.854123+00:00
-- url     : https://prove2.me/theorems/6af4ab90-b042-4665-b64b-3a9b31567c2e
-- title:
--   x → y: every member of mb(L) containing x contains y, and y ∉ ⟨x⟩
-- statement:
--   Let $\mathbf L$ be a critical binary clutter and $x, y \in E(\mathbf L)$. We write $x \to y$ if every member of $mb(\mathbf L)$ containing $x$ contains $y$, and yet $y \notin \langle x \rangle$:
--
--   $$
--   x \to y \iff \bigl(\forall B \in mb(\mathbf L),\ x \in B \Rightarrow y \in B\bigr) \ \text{and}\ y \notin \langle x \rangle .
--   $$
--
--   The relation $\to$ organizes the structure theory of critical Mengerian binary clutters, via the initial elements.
--
--   **Formalization Note** The Lean predicate is defined for every clutter, and includes $x, y \in E(\mathbf L)$. The paper introduces it only for critical binary clutters, and every statement of the mission that uses it assumes criticality and binarity.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 203, Section 4

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_mb
import Definitions.Def_SeymourMFMC_Binary_point

namespace SeymourMFMC.Binary

/-- `Arrow L x y` is the relation `x → y` of Seymour 1977, p. 203: `x, y ∈ E(L)`, every member
of `mb(L)` containing `x` contains `y`, and yet `y ∉ ⟨x⟩`. The paper introduces it for critical
binary clutters `L`; every statement using it assumes those hypotheses. -/
def Arrow {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (x y : α) : Prop :=
  x ∈ ground L ∧ y ∈ ground L ∧ (∀ B ∈ mb L, x ∈ B → y ∈ B) ∧ y ∉ point L x

end SeymourMFMC.Binary


