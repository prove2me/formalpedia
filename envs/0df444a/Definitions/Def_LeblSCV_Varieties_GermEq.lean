-- Prove2me | Definitions.Def_LeblSCV_Varieties_GermEq
-- name    : LeblSCV_Varieties_GermEq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:07:29.81295+00:00
-- url     : https://prove2.me/theorems/e0e4d809-51db-4fb2-8d37-d8b1fb9e7d48
-- title:
--   Definition 6.1.3 — equality of germs of sets $(A,p) = (B,p)$
-- statement:
--   Let $p \in \mathbb{C}^n$. Two sets $A, B \subset \mathbb{C}^n$ are **equivalent at $p$** if there is a neighborhood $W$ of $p$ with
--   $$A \cap W = B \cap W.$$
--   An equivalence class is a **germ of a set at $p$**, written $(A, p)$; so $(A,p) = (B,p)$ exactly when the displayed condition holds for some neighborhood $W$ of $p$.
--
--   Germs of sets record only the behaviour of a set arbitrarily close to $p$; they are the language of all local statements about subvarieties in this mission.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`; "neighborhood" is membership in the neighborhood filter `nhds p`. The germ is not built as a quotient: the relation is used directly.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 168, Definition 6.1.3

import Mathlib

namespace LeblSCV.Varieties

/-- Lebl, Definition 6.1.3: two sets `A, B ⊆ ℂⁿ` have the same **germ** at `p`, `(A, p) = (B, p)`,
if there is a neighborhood `W` of `p` with `A ∩ W = B ∩ W`. -/
def GermEq {n : ℕ} (p : Fin n → ℂ) (A B : Set (Fin n → ℂ)) : Prop :=
  ∃ W ∈ nhds p, A ∩ W = B ∩ W

end LeblSCV.Varieties


