-- Prove2me | Definitions.Def_LeblSCV_Varieties_GermSubset
-- name    : LeblSCV_Varieties_GermSubset
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:07:48.505099+00:00
-- url     : https://prove2.me/theorems/16f84a09-1b90-4475-ae4e-0c959f554fe1
-- title:
--   Definition 6.1.3 — inclusion of germs of sets $(A,p) \subset (B,p)$
-- statement:
--   Let $p \in \mathbb{C}^n$ and $A, B \subset \mathbb{C}^n$. The germ $(A, p)$ is **contained** in the germ $(B, p)$, written $(A,p) \subset (B,p)$, if there is a neighborhood $W$ of $p$ such that
--   $$A \cap W \subset B \cap W.$$
--
--   This is the inclusion used to define the vanishing ideal $I_p(X)$ and (ir)reducibility of germs of subvarieties.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`; "neighborhood" is membership in `nhds p`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 168, Definition 6.1.3

import Mathlib

namespace LeblSCV.Varieties

/-- Lebl, Definition 6.1.3: inclusion of germs of sets, `(A, p) ⊂ (B, p)`: there is a
neighborhood `W` of `p` with `A ∩ W ⊆ B ∩ W`. -/
def GermSubset {n : ℕ} (p : Fin n → ℂ) (A B : Set (Fin n → ℂ)) : Prop :=
  ∃ W ∈ nhds p, A ∩ W ⊆ B ∩ W

end LeblSCV.Varieties


