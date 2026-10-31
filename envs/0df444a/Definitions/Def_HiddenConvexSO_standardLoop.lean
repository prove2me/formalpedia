-- Prove2me | Definitions.Def_HiddenConvexSO_standardLoop
-- name    : HiddenConvexSO_standardLoop
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:44.659806+00:00
-- url     : https://prove2.me/theorems/3728163f-569b-46ec-abc0-1fad69e34f97
-- title:
--   The anticlockwise unit loop $t\mapsto(\sin 2\pi t,-\cos 2\pi t)$ in $\mathbb R^2\setminus(0,0)$
-- statement:
--   The **standard loop** is
--
--   $$
--   \sigma(t)=\bigl(\sin(2\pi t),\,-\cos(2\pi t)\bigr),\qquad t\in[0,1],
--   $$
--
--   a loop in the punctured plane $\mathbb R^2\setminus(0,0)$ based at $(0,-1)$. It traverses the unit circle once anticlockwise: it passes $(1,0)$ at $t=1/4$ and $(0,1)$ at $t=1/2$.
--
--   The proof of Theorem 3 shows that the image of a loop in $\mathrm{SO}(n)$ is homotopic to $\sigma$ in the punctured plane; since $\sigma$ winds once around the origin, that image loop is not null-homotopic.
--
--   **Formalization Note** A Mathlib `Path` from `puncturedBase` to itself in `{p : ℝ × ℝ // p ≠ 0}`; its points are nonzero because $\sin^2+\cos^2=1$.
-- source:
--   Ramachandran, Shu & Wang, Hidden convexity, optimization, and algorithms on rotation matrices, arXiv:2304.08596v2, proof of Theorem 3, p.16 ("the loop (sin(2πt), −cos(2πt))")

import Mathlib
import Definitions.Def_HiddenConvexSO_puncturedBase

namespace HiddenConvexSO

/-- **The standard anticlockwise loop `t ↦ (sin(2πt), −cos(2πt))` in `ℝ² ∖ (0, 0)`.**
Ramachandran, Shu & Wang, arXiv:2304.08596v2, proof of Theorem 3, p.16 (PDF p.16): "we will exhibit
a homotopy from f∗(γ) to the loop (sin(2πt), −cos(2πt))". It runs once around the unit circle,
anticlockwise, starting and ending at `(0, −1)` (it passes `(1, 0)` at `t = 1/4`, `(0, 1)` at
`t = 1/2`).

**Formalization Note.** A Mathlib `Path` from `puncturedBase = (0, −1)` to itself in the subtype
`{p : ℝ × ℝ // p ≠ 0}`; the points never vanish because `sin² + cos² = 1`. -/
noncomputable def standardLoop : Path puncturedBase puncturedBase where
  toFun t := ⟨(Real.sin (2 * Real.pi * t), -Real.cos (2 * Real.pi * t)), by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at h1 h2
    have := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
    rw [h1, h2] at this
    norm_num at this⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := by
    simp [puncturedBase]
  target' := by
    simp [puncturedBase]

end HiddenConvexSO


