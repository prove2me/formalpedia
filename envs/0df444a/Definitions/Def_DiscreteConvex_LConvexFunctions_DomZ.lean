-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ
-- name    : DiscreteConvex_LConvexFunctions_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:13:30.509985+00:00
-- url     : https://prove2.me/theorems/bf751ea8-c192-4273-bcbf-1d76b9ac06c9
-- title:
--   Effective domain on the integer lattice
-- statement:
--   The effective domain $\operatorname{dom} g = \{p \in \mathbb Z^V : g(p) \ne +\infty\}$ of $g : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.177: the effective domain of a function on the
integer lattice, in `DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- The effective domain `dom g = \{p ∈ Zⱽ : g(p) ≠ +∞\}` of `g : Zⱽ → R ∪ {+∞}`. -/
def DomZ {V : Type*} (g : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) :=
  {p | g p ≠ ⊤}

end DiscreteConvex.LConvexFunctions


