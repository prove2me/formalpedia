-- Prove2me | Definitions.Def_AgnHalfMem_halfspace
-- name    : AgnHalfMem_halfspace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:43.496313+00:00
-- url     : https://prove2.me/theorems/f11f4bc2-b125-4a2f-be58-fbe5c8665af5
-- title:
--   Homogeneous halfspaces $\mathcal H_d$
-- statement:
--   For $w,x\in\mathbb R^d$ write $\langle w,x\rangle=\sum_{i=1}^d w_ix_i$ for the (non-normalized) Euclidean inner product. The **homogeneous halfspace** with normal $w$ is the classifier $x\mapsto \mathrm{sign}(\langle w,x\rangle)$, and the class of $d$-dimensional homogeneous halfspaces is
--   $$
--   \mathcal H_d=\{\,x\mapsto \mathrm{sign}(\langle w,x\rangle)\;:\;\|w\|_2=1\,\}.
--   $$
--   This is the hypothesis class whose agnostic learnability the mission studies.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ` with the product σ-algebra, so that the product law $\mu^{\otimes d}$ is `Measure.pi`. The unit condition is written $\sum_i w_i^2=1$; classifiers output Boolean labels.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), §1, p.2; §4.3, p.13

import Mathlib
import Definitions.Def_AgnHalfMem_sgn

namespace AgnHalfMem

/-- **Homogeneous halfspaces `H_d`.** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for
Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), §1, p.2: "`H_d = {x ↦ sign(⟨w, x⟩) | ‖w‖₂ = 1}`"; §4.3, p.13: `⟨·,·⟩` and
`‖·‖` on vectors are the non-normalized ones, `⟨v, v′⟩ = Σᵢ vᵢ v′ᵢ`.

`dot w x = Σᵢ wᵢ xᵢ`, `halfspace w` is the classifier `x ↦ sign(⟨w, x⟩)`, and `halfspaces d` is
the class `H_d` of these classifiers over unit vectors `w`.

**Formalization Note.** Features are `Fin d → ℝ` (coordinates `0, …, d−1`, the product
measurable space, so that `μ^{⊗d}` is `Measure.pi`). The unit condition `‖w‖₂ = 1` is written
`Σᵢ wᵢ² = 1`. Classifiers output labels in `Bool` (`true ↔ +1`), with `sign(0) = +1`. -/
def dot {d : ℕ} (w x : Fin d → ℝ) : ℝ := ∑ i, w i * x i

/-- The halfspace classifier `x ↦ sign(⟨w, x⟩)` (p.2). -/
noncomputable def halfspace {d : ℕ} (w : Fin d → ℝ) : (Fin d → ℝ) → Bool := fun x => signB (dot w x)

/-- The class `H_d` of homogeneous halfspaces with unit normal (p.2). -/
def halfspaces (d : ℕ) : Set ((Fin d → ℝ) → Bool) :=
  {f | ∃ w : Fin d → ℝ, ∑ i, w i ^ 2 = 1 ∧ f = halfspace w}

end AgnHalfMem


