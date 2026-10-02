-- Prove2me | Definitions.Def_LeblSCV_Varieties_IsIrreducibleGerm
-- name    : LeblSCV_Varieties_IsIrreducibleGerm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:13:14.167406+00:00
-- url     : https://prove2.me/theorems/221c1ddd-08cc-44ba-be1c-154e030b3d2a
-- title:
--   Definition 6.7.1 — irreducible germ of a subvariety
-- statement:
--   A germ of a subvariety $(X, p)$ is **reducible at $p$** if there are two germs of subvarieties $(X_1, p)$ and $(X_2, p)$ with $(X_1, p) \not\subset (X_2, p)$ and $(X_2, p) \not\subset (X_1, p)$ such that
--   $$(X, p) = (X_1, p) \cup (X_2, p).$$
--   Otherwise the germ $(X, p)$ is **irreducible at $p$**.
--
--   Irreducible germs are the building blocks of every germ of a subvariety (Proposition 6.7.3).
--
--   **Formalization Note.** Irreducible means: $(X,p)$ is a germ of a subvariety and it is not reducible. The union of germs is the germ of the union of representatives (Definition 6.1.3). As in the book's literal wording, the empty germ is irreducible under this definition.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 193, Definition 6.7.1

import Mathlib
import Definitions.Def_LeblSCV_Varieties_IsSubvarietyGerm
import Definitions.Def_LeblSCV_Varieties_GermEq
import Definitions.Def_LeblSCV_Varieties_GermSubset

namespace LeblSCV.Varieties

/-- Lebl, Definition 6.7.1: a germ of a subvariety `(X, p)` is **reducible at `p`** if there are
two germs of subvarieties `(X₁, p)`, `(X₂, p)` with `(X₁, p) ⊄ (X₂, p)`, `(X₂, p) ⊄ (X₁, p)` and
`(X, p) = (X₁, p) ∪ (X₂, p)`; otherwise (and being a germ of a subvariety) it is
**irreducible at `p`**. -/
def IsIrreducibleGerm {n : ℕ} (p : Fin n → ℂ) (X : Set (Fin n → ℂ)) : Prop :=
  IsSubvarietyGerm p X ∧
    ¬ ∃ X₁ X₂ : Set (Fin n → ℂ), IsSubvarietyGerm p X₁ ∧ IsSubvarietyGerm p X₂ ∧
      ¬ GermSubset p X₁ X₂ ∧ ¬ GermSubset p X₂ X₁ ∧ GermEq p X (X₁ ∪ X₂)

end LeblSCV.Varieties


