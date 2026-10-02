-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
-- name    : DiscreteConvex_MConvexFunctions_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:51:49.952697+00:00
-- url     : https://prove2.me/theorems/180d7538-4195-4d6c-8c88-9d49f5a91e3c
-- title:
--   Effective domain on the integer lattice
-- statement:
--   The effective domain $\operatorname{dom} f = \{x \in \mathbb Z^V : f(x) \ne +\infty\}$ of $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133: the effective domain of a function on the
integer lattice, in `DiscreteConvex.MConvexFunctions`.
-/

namespace DiscreteConvex.MConvexFunctions

/-- The effective domain `dom f = \{x ∈ Zⱽ : f(x) ≠ +∞\}` of `f : Zⱽ → R ∪ {+∞}`. -/
def DomZ {V : Type*} (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) :=
  {x | f x ≠ ⊤}

end DiscreteConvex.MConvexFunctions


