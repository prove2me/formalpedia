-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
-- name    : DiscreteConvex_MConvexFunctionsB_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:05:55.25842+00:00
-- url     : https://prove2.me/theorems/9ce31edf-f128-4948-879c-09dfe6d7eeec
-- title:
--   DomZ
-- statement:
--   The effective domain $\operatorname{dom} f = \{x \in \mathbb Z^V : f(x) \ne +\infty\}$ of $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The effective domain `dom f = \{x ∈ Zⱽ : f(x) ≠ +∞\}` of `f : Zⱽ → R ∪ {+∞}`. -/
def DomZ {V : Type*} (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | f x ≠ ⊤}

end DiscreteConvex.MConvexFunctionsB


