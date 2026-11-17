-- Prove2me | Definitions.Def_AnchoredEP_Supplement_newtonUpperPasses
-- name    : AnchoredEP_Supplement_newtonUpperPasses
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:07:28.317823+00:00
-- url     : https://prove2.me/theorems/5a454cb3-0b72-441d-b8bf-e366628298d0
-- title:
--   Upper trial of Subroutine 1 terminates the method
-- statement:
--   In Subroutine 1 of the AEP Newton method, the **upper trial passes** when
--   $$
--   \varphi_k(\bar a_k)\le\sqrt2 .
--   $$
--   In that case the whole outer method terminates and returns the trial point $z_{k+1}(\bar a_k)$ together with $v_{k+1}(\bar a_k)$.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Subroutine 1 lines 4–5, p.25

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_Supplement_newtonPhi
import Definitions.Def_AnchoredEP_Supplement_newtonAbar

namespace AnchoredEP.Supplement

/-- **The upper trial of Subroutine 1 terminates the method.** Jiang–Yoon, arXiv:2609.30212,
Subroutine 1 lines 4–5, p.25: "if `φ_k(ā_k) ≤ √2` then terminate the outer method and return
`(z_{k+1}(ā_k), v_{k+1}(ā_k))`". -/
def newtonUpperPasses {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) : Prop :=
  newtonPhi F L sol z0 s (newtonAbar F L ε s) ≤ Real.sqrt 2

end AnchoredEP.Supplement


