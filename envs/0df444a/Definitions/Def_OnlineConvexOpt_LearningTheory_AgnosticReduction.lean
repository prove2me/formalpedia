-- Prove2me | Definitions.Def_OnlineConvexOpt_LearningTheory_AgnosticReduction
-- name    : OnlineConvexOpt_LearningTheory_AgnosticReduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:45:42.067579+00:00
-- url     : https://prove2.me/theorems/39bb9489-2a73-410c-826f-ed7490b50530
-- title:
--   Reduction: agnostic learning ⇒ OCO (Algorithm 29)
-- statement:
--   `IsAgnosticReductionRun Prob D pred ℓ A T samp h hbar` formalizes Algorithm 29 (p. 158),
--   the reduction from agnostic PAC learning to online convex optimization: an OCO algorithm
--   `A` is run on the sequence of loss functions $f_t(x) = \ell(\mathrm{pred}(x, x_t), y_t)$
--   built from i.i.d. labeled examples $(x_t,y_t)\sim D$; `h_0 \leftarrow A(\emptyset)`
--   (round-0 history modeled as the zero cost sequence); `h_{t+1} = A(f_0,\dots,f_t)`; and the
--   output is the running average $\bar h = \frac1T\sum_{t=0}^{T-1} h_t$.
--
--   **Formalization Note.** 0-indexed (`t \in \mathbb{N}` is the book's round `t+1`) to match
--   `OnlineConvexOpt.FirstOrder.RegretT`/`IsOnlineAlgorithm`'s convention, which the goal
--   theorem's non-anticipation hypothesis on `A` (`kind: reference`, reused from Chunk 03) is
--   stated against — see `MODERATION_NOTES.md`.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 158, Algorithm 29 (PDF p. 180)

import Mathlib

open MeasureTheory

namespace OnlineConvexOpt.LearningTheory

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `IsAgnosticReductionRun Prob D pred ℓ A T samp h hbar` formalizes Algorithm 29 (Hazan,
*Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 158, PDF p. 180),
the reduction from agnostic PAC learning to online convex optimization, 0-indexed to match
`OnlineConvexOpt.FirstOrder.RegretT`/`IsOnlineAlgorithm`'s convention (round `t`, `t ∈ ℕ`, is the
book's round `t + 1`) — required by the goal theorem's non-anticipation hypothesis, which is
stated against `A` using that same convention: `samp t ω` is round-`t`'s labeled example drawn
i.i.d. from `D` (line 4, book round `t + 1`); `h 0` is `A`'s initial play (line 2, `h_1 ← A(∅)`,
modeled as `A` applied to the identically-zero cost sequence, since a non-anticipating `A`'s
round-0 decision cannot depend on any cost function); at every round `t + 1` (`t + 1 < T`), the
next hypothesis is `h_{t+1} = A(f_0,...,f_t)` where each `f_τ(x) = ℓ(pred x, x_τ, y_τ)` is the
loss of hypothesis-parameter `x` on round-`τ`'s example (line 5-6, book rounds `1,...,t+1`); and
`hbar` is the running average `h̄ = (1/T)∑_{t=0}^{T-1} h_t` (line 8, book's
`(1/T)∑_{t=1}^T h_t`). -/
def IsAgnosticReductionRun {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    (D : Measure (X × Y)) (pred : E → X → ℝ) (ℓ : ℝ → Y → ℝ)
    (A : (ℕ → E → ℝ) → ℕ → E) (T : ℕ)
    (samp : ℕ → Ω → X × Y) (h : ℕ → Ω → E) (hbar : Ω → E) : Prop :=
  (∀ t : ℕ, t < T → Measure.map (samp t) Prob = D) ∧
  ProbabilityTheory.iIndepFun samp Prob ∧
  h 0 = (fun _ => A (fun _ _ => (0 : ℝ)) 0) ∧
  (∀ t : ℕ, t + 1 < T → ∀ ω : Ω,
    h (t + 1) ω =
      A (fun τ x => if τ ≤ t then ℓ (pred x (samp τ ω).1) (samp τ ω).2 else 0) (t + 1)) ∧
  (∀ ω : Ω, hbar ω = (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, h t ω)

end OnlineConvexOpt.LearningTheory


