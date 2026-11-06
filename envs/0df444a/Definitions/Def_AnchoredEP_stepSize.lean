-- Prove2me | Definitions.Def_AnchoredEP_stepSize
-- name    : AnchoredEP_stepSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:43.025013+00:00
-- url     : https://prove2.me/theorems/feead962-30f1-4caf-bfcc-f58e245c219e
-- title:
--   Step size $a_k$ selected by the line search
-- statement:
--   The step size of outer iteration $k$ is $\bar a_k$ if the upper trial passes, and otherwise the midpoint of the first accepted bisection trial.
--
--   **Formalization Note** If the upper trial fails and no bisection trial is ever accepted, the value $\bar a_k$ is used as a placeholder. The complexity theorem asserts that the line search returns at every iteration the run reaches, so the placeholder never affects the runs it describes.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Algorithm 3, line 7, p.37, and Appendix G.2, p.38

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_abar
import Definitions.Def_AnchoredEP_bisect
import Definitions.Def_AnchoredEP_accepted
import Definitions.Def_AnchoredEP_upperPasses

namespace AnchoredEP

open Classical in
/-- **The step size `a_k` selected by the line search.** Jiang–Yoon, arXiv:2609.30212, Algorithm 3
line 7, p.37, and Appendix G.2, p.38: the upper trial `ā_k` if `ψ_k(ā_k) ≤ p!ρ`; otherwise the
first accepted bisection midpoint.

**Formalization Note.** If the upper trial fails and no bisection trial is ever accepted, the
value `ā_k` is a placeholder. The complexity theorem `theorem_5_1` asserts that the line search
returns (`LineSearchReturnsWithin`) at every outer iteration it reaches, so the placeholder is
never used by a run it describes. -/
noncomputable def stepSize {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℕ) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) : ℝ :=
  if upperPasses F p L ε sol z0 s then abar F p L ε s
  else if h : ∃ t, accepted F p L ε sol z0 s t then
    ((bisect F p L ε sol z0 s (Nat.find h)).1 + (bisect F p L ε sol z0 s (Nat.find h)).2) / 2
  else abar F p L ε s

end AnchoredEP


