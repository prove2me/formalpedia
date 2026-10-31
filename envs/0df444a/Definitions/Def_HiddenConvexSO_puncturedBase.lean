-- Prove2me | Definitions.Def_HiddenConvexSO_puncturedBase
-- name    : HiddenConvexSO_puncturedBase
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:35.730863+00:00
-- url     : https://prove2.me/theorems/9da1847d-fa06-4994-b142-3caa4f2ee224
-- title:
--   Base point $(0,-1)$ of the punctured plane $\mathbb R^2\setminus(0,0)$
-- statement:
--   The **punctured plane** $\mathbb R^2\setminus(0,0)$ carries the subspace topology of $\mathbb R^2$. Its base point is $p_0=(0,-1)$, the point where the loop $t\mapsto(\sin 2\pi t,-\cos 2\pi t)$ used in the proof of Theorem 3 starts and ends.
--
--   The fundamental group of the punctured plane is taken at this point.
--
--   **Formalization Note** $\mathbb R^2$ is `ℝ × ℝ` and the punctured plane is the subtype `{p : ℝ × ℝ // p ≠ 0}`. The paper fixes no base point; the punctured plane is path connected, so the fundamental group does not depend on the choice (p.13).
-- source:
--   Ramachandran, Shu & Wang, Hidden convexity, optimization, and algorithms on rotation matrices, arXiv:2304.08596v2, §4.1, p.13 ("The punctured plane R2 \ (0, 0) viewed as a subtopological space of R2") and proof of Theorem 3, p.16

import Mathlib

namespace HiddenConvexSO

/-- **The base point `(0, −1)` of the punctured plane `ℝ² ∖ (0, 0)`.**
Ramachandran, Shu & Wang, arXiv:2304.08596v2, §4.1, p.13 (PDF p.13): "The punctured plane
R2 \ (0, 0) viewed as a subtopological space of R2 with the standard topology"; the point `(0, −1)`
is where the loop `t ↦ (sin(2πt), −cos(2πt))` of the proof of Theorem 3 (p.16) starts and ends.

**Formalization Note.** `ℝ²` is `ℝ × ℝ` (product topology = standard topology) and the punctured plane
is the subtype `{p : ℝ × ℝ // p ≠ 0}` with the subspace topology. The paper fixes no base point; since
the punctured plane is path connected its fundamental group does not depend on it ("If X is path
connected, then the fundamental group is independent of the choice of basepoint", p.13). -/
def puncturedBase : {p : ℝ × ℝ // p ≠ 0} :=
  ⟨(0, -1), by simp⟩

end HiddenConvexSO


