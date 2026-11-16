-- Prove2me | Definitions.Def_AgnHalfMem_Supplement_IsMarginSeparable
-- name    : AgnHalfMem_Supplement_IsMarginSeparable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:56:20.888737+00:00
-- url     : https://prove2.me/theorems/d6cc0549-a24a-43d0-85a9-98f4cc48d42c
-- title:
--   Linear separability with a $\gamma$-margin
-- statement:
--   A distribution $D$ on $\mathbb R^d\times\{-1,1\}$ is **linearly separable with a $\gamma$-margin** if there is a unit vector $w^*\in\mathbb R^d$, $\|w^*\|_2=1$, such that, almost surely for $(x,y)\sim D$, $x\ne0$ and
--   $$
--   y\,\Big\langle w^*,\frac{x}{\|x\|_2}\Big\rangle\ \ge\ \gamma ,
--   $$
--   stated as $y\langle w^*,x\rangle\ge\gamma\|x\|_2$ with the Euclidean norm.
--
--   This is the realizable margin setting of Theorem 5.1, where the paper normalizes the samples to $\|x_t\|_2\le1$ and $y_t\langle w^*,x_t\rangle\ge\gamma$.
--
--   **Formalization Note** The condition $x\ne0$ is what makes the normalization defined. Without it, a point $x=0$ with label $-1$ would satisfy the inequality, but no homogeneous halfspace classifies it, since $\mathrm{sign}(0)=+1$.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Theorem 5.1, p.19; App. A.2, p.26

import Mathlib
import Definitions.Def_AgnHalfMem_Supplement_marginErr

open MeasureTheory

namespace AgnHalfMem

namespace Supplement

/-- **Linear separability with a γ-margin.** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for
Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), Theorem 5.1, p.19 ("a distribution linearly separable with a γ-margin") and
App. A.2, p.26: "Let w* be the unit vector separating the data distribution D with margin γ. By
normalizing the samples, we can assume that ‖xₜ‖₂ ≤ 1 and yₜ⟨w*, xₜ⟩ ≥ γ."

`IsMarginSeparable D γ`: there is a unit vector `w*` (`Σᵢ w*ᵢ² = 1`) such that `D`-almost surely
`x ≠ 0` and `sgn(y)·⟨w*, x⟩ ≥ γ‖x‖₂`, i.e. `y⟨w*, x/‖x‖₂⟩ ≥ γ`.

**Formalization Note.** `x ≠ 0` is what makes the normalization `x/‖x‖₂` defined; without it an
atom at `x = 0` labelled `−1` would satisfy the inequality while no homogeneous halfspace
(`sign(0) = +1`) classifies it. `‖·‖₂` is the Euclidean norm `eNorm`. -/
def IsMarginSeparable {d : ℕ} (D : Measure ((Fin d → ℝ) × Bool)) (γ : ℝ) : Prop :=
  ∃ w : Fin d → ℝ, ∑ i, w i ^ 2 = 1 ∧
    ∀ᵐ p ∂D, p.1 ≠ 0 ∧ γ * eNorm p.1 ≤ sgn p.2 * dot w p.1

end Supplement

end AgnHalfMem


