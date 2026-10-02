-- Prove2me | Definitions.Def_LeblSCV_BallPolydisc_IsBiholomorphicMap
-- name    : LeblSCV_BallPolydisc_IsBiholomorphicMap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:18:17.992534+00:00
-- url     : https://prove2.me/theorems/adbe743f-8e4b-45a2-8f79-77d10feff818
-- title:
--   Definition 1.4.1 — biholomorphic map
-- statement:
--   Let $U, V \subset \mathbb{C}^n$. A map $f : U \to V$ is a **biholomorphic map** (a **biholomorphism**) if it is holomorphic, one-to-one and onto, and its inverse
--   $$f^{-1} : V \to U$$
--   is holomorphic. Two domains are biholomorphic (biholomorphically equivalent) if a biholomorphism between them exists.
--
--   Biholomorphic domains have the same function theory, and classifying domains up to biholomorphism is one of the main questions of complex analysis.
--
--   **Formalization Note.** Holomorphic is `DifferentiableOn ℂ` on the (in all uses, open) sets `U` and `V`; this is equivalent to the book's Definition 1.1.2 on open sets (Proposition 1.1.3 and Theorem 1.2.1). The inverse is an ambient function `g` with `Set.InvOn g f U V`, i.e. $g \circ f = \mathrm{id}$ on $U$ and $f \circ g = \mathrm{id}$ on $V$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 32, Definition 1.4.1

import Mathlib

namespace LeblSCV.BallPolydisc

/-- Definition 1.4.1 (Lebl, p. 32). `f : U → V` is a biholomorphic map (biholomorphism): it is
holomorphic on `U`, one-to-one from `U` onto `V`, and its inverse `f⁻¹ : V → U` is holomorphic
on `V`. Holomorphic is `DifferentiableOn ℂ` (equivalent to Definition 1.1.2 on open sets). -/
def IsBiholomorphicMap {n : ℕ} (f : (Fin n → ℂ) → (Fin n → ℂ)) (U V : Set (Fin n → ℂ)) : Prop :=
  DifferentiableOn ℂ f U ∧ Set.BijOn f U V ∧
    ∃ g : (Fin n → ℂ) → (Fin n → ℂ), DifferentiableOn ℂ g V ∧ Set.InvOn g f U V

end LeblSCV.BallPolydisc


