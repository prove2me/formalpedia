-- Prove2me | Definitions.Def_MatroidOptGame_weight
-- name    : MatroidOptGame_weight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:45.747517+00:00
-- url     : https://prove2.me/theorems/29f582c3-8381-451e-81b8-83ad24b942bd
-- title:
--   Weight of a set $w(F)=\sum_{e\in F} w(e)$
-- statement:
--   For a weight function $w : E \to \mathbb N$ and a finite set $F \subseteq E$, the **weight** of $F$ is
--   $$
--   w(F) = \sum_{e \in F} w(e).
--   $$
--   This extends the element weights of the matroid base minimization game to sets: MIN's payoff is the weight of the base it secures.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, p.20 (and w : E → ℕ, Section 2, p.3)

import Mathlib

namespace MatroidOptGame

/-- The weight of a finite set: `w(F) = ∑_{e ∈ F} w(e)`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, p.20 ("for F ⊆ E, w(F) = ∑_{e∈F} w(e)"); weights `w : E → ℕ`
as in Section 2, p.3. -/
def weight {α : Type*} (w : α → ℕ) (F : Finset α) : ℕ :=
  ∑ e ∈ F, w e

end MatroidOptGame


