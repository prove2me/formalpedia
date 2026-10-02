-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_DomZ
-- name    : DiscreteConvex_ConjugacyDuality_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:09:30.521018+00:00
-- url     : https://prove2.me/theorems/1523074f-f273-421d-a8d9-a81e9c74face
-- title:
--   Effective domain on the integer lattice
-- statement:
--   The effective domain $\operatorname{dom} f = \{x \in \mathbb Z^V : f(x) \ne +\infty\}$ of $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 8.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 8

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003: the effective domain of a function on the
integer lattice, in `DiscreteConvex.ConjugacyDuality`.
-/

namespace DiscreteConvex.ConjugacyDuality

/-- The effective domain `dom f = \{x ∈ Zⱽ : f(x) ≠ +∞\}` of `f : Zⱽ → R ∪ {+∞}`. -/
def DomZ {V : Type*} (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) :=
  {x | f x ≠ ⊤}

end DiscreteConvex.ConjugacyDuality


