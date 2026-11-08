-- Prove2me | Definitions.Def_OneOfManyCC_rectFn
-- name    : OneOfManyCC_rectFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:34.662705+00:00
-- url     : https://prove2.me/theorems/cb4a218d-6f89-4301-bac7-a0fd5ac94790
-- title:
--   A solvable rectangle as a function on $A\sqcup B$
-- statement:
--   Every solvable rectangle $A'\times B'$ is regarded as the function on $A\sqcup B$ that equals
--
--   $$\mathbf 1[x\notin A']\text{ at each }x\in A,\qquad \mathbf 1[y\in B']\text{ at each }y\in B.$$
--
--   A rectangle is thus correct at $x$ when it is zero there, and correct at $y$ when it is one there. The set $\mathcal F$ of these functions is the leaf set for the formula $\Psi$ of the proof of Theorem 1.2.
--
--   **Formalization Note** Formula leaves are typed as the rectangles themselves. A rectangle is determined by its function, so this is the same as leaves from $\mathcal F$.
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Theorem 1.2, p.12

import Mathlib
import Definitions.Def_OneOfManyCC_Solvable

namespace OneOfManyCC

open Classical in
/-- **A solvable rectangle as a function on `A ⊔ B`.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Theorem 1.2, p.12:
"Regard every solvable rectangle A′ × B′ as the function on A ⊔ B that equals 1[x ∉ A′] at each
x ∈ A and 1[y ∈ B′] at each y ∈ B, and let F be the set of these functions."

**Formalization Note.** A formula's leaves are typed as the rectangles themselves. The map from
rectangles to these functions is injective, so this is the same as leaves from `F`, and the walk
of the proof can read the rectangle at the leaf it reaches. -/
noncomputable def rectFn {A B O : Type} [Fintype O] {k : ℕ} {R : A → B → O → Prop}
    (r : SolvableRect k R) : A ⊕ B → Bool
  | Sum.inl x => decide (x ∉ r.1.1)
  | Sum.inr y => decide (y ∈ r.1.2)

end OneOfManyCC


