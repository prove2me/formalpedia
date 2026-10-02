-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexity_DomZ
-- name    : DiscreteConvex_IntegralConvexity_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:48:31.649136+00:00
-- url     : https://prove2.me/theorems/b2819d21-2002-457e-afd9-21636a85a9d2
-- title:
--   Effective domain on the integer lattice
-- statement:
--   The **effective domain** $\operatorname{dom}_{\mathbb Z} f = \{x \in \mathbb Z^n : f(x) \ne +\infty\}$ of a function $f : \mathbb Z^n \to \mathbb R \cup \{+\infty\}$, represented as `f : (Fin n → ℤ) → WithTop ℝ`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93: the effective domain `dom_Z f` of a
function `f : Zⁿ → R ∪ {+∞}`, in `DiscreteConvex.IntegralConvexity`.
-/

namespace DiscreteConvex.IntegralConvexity

/-- The effective domain `dom_Z f = {x ∈ Zⁿ : f(x) ≠ +∞}` of `f : Zⁿ → R ∪ {+∞}`, represented
as `f : (Fin n → ℤ) → WithTop ℝ`. -/
def DomZ {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) : Set (Fin n → ℤ) :=
  {x | f x ≠ ⊤}

end DiscreteConvex.IntegralConvexity


