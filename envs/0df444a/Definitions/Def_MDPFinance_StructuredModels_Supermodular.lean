-- Prove2me | Definitions.Def_MDPFinance_StructuredModels_Supermodular
-- name    : MDPFinance_StructuredModels_Supermodular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:32:38.158141+00:00
-- url     : https://prove2.me/theorems/c2da4076-9764-4e68-9645-474964fd2719
-- title:
--   Supermodular functions (Definition A.3.1)
-- statement:
--   For a lattice $L$ and $D \subseteq L$, a function $f : L \to \overline{\mathbb{R}}$ is
--   **supermodular on $D$** if $f(x) + f(y) \leq f(x \wedge y) + f(x \vee y)$ for all $x, y \in D$.
--
--   **Formalization Note.** The book's Definition A.3.1 is for $f : \mathbb{R}^d \to \mathbb{R}$
--   (global, $D = \mathbb{R}^d$); this mission needs it for the `EReal`-valued operator $L_n v$
--   restricted to $D = D_n$, so both the codomain and the domain restriction are generalized
--   directly from the book's own inequality (see `MODERATION_NOTES.md`).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 352, Definition A.3.1

import Mathlib

namespace MDPFinance.StructuredModels

variable {L : Type*} [Lattice L]

/-- A function `f : L → EReal` is supermodular on `D ⊆ L` (Bäuerle–Rieder, Definition A.3.1,
p. 352, PDF 359: `f(x) + f(y) ≤ f(x ∧ y) + f(x ∨ y)` for `x, y ∈ ℝ^d`, restricted here to `x, y
∈ D` following the chapter's own phrase "`L_n v` is supermodular on `D_n`"). The book states
Def. A.3.1 for `f : ℝ^d → ℝ`; here `f` is generalized to `EReal`-valued, matching the type of the
operator `L_n v` this definition is applied to in Proposition 2.4.16 (see `MODERATION_NOTES.md`).
-/
def SupermodularOn (D : Set L) (f : L → EReal) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, f x + f y ≤ f (x ⊓ y) + f (x ⊔ y)

end MDPFinance.StructuredModels


