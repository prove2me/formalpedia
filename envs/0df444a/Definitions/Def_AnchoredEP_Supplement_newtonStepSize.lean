-- Prove2me | Definitions.Def_AnchoredEP_Supplement_newtonStepSize
-- name    : AnchoredEP_Supplement_newtonStepSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:08:19.011329+00:00
-- url     : https://prove2.me/theorems/e3c5543c-354d-4837-9651-97b23906ad07
-- title:
--   Step size $a_k$ accepted by Subroutine 1
-- statement:
--   When the upper trial of Subroutine 1 fails, the step size $a_k$ selected at outer iteration $k$ of the AEP Newton method is the first bisection midpoint $a$ with $1\le\varphi_k(a)\le\sqrt2$.
--
--   **Formalization Note** If no bisection trial is ever accepted, the value $\bar a_k$ is used as a placeholder. The theorems about Algorithm 1 assert that the line search returns at every outer iteration the run reaches, so the placeholder never enters a run they describe.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Algorithm 1 line 7, p.8; Subroutine 1 line 16, p.25

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_Supplement_newtonAbar
import Definitions.Def_AnchoredEP_Supplement_newtonBisect
import Definitions.Def_AnchoredEP_Supplement_newtonAccepted

namespace AnchoredEP.Supplement

open Classical in
/-- **The step size `a_k` accepted by Subroutine 1.** Jiang–Yoon, arXiv:2609.30212, Algorithm 1
line 7, p.8, and Subroutine 1 line 16, p.25: the first bisection midpoint `a` with
`1 ≤ φ_k(a) ≤ √2`.

**Formalization Note.** If no bisection trial is ever accepted, the value `ā_k` is a placeholder.
The theorems about Algorithm 1 assert that the line search returns
(`NewtonLineSearchReturnsWithin`) at every outer iteration the run reaches, so the placeholder is
never used by a run they describe. The upper-trial branch is handled in `newtonOuterStep`, which
calls this step size only when the upper trial fails. -/
noncomputable def newtonStepSize {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) : ℝ :=
  if h : ∃ t, newtonAccepted F L ε sol z0 s t then
    ((newtonBisect F L ε sol z0 s (Nat.find h)).1 + (newtonBisect F L ε sol z0 s (Nat.find h)).2) / 2
  else newtonAbar F L ε s

end AnchoredEP.Supplement


