-- Prove2me | Definitions.Def_ZOGlobalLB_ZOAlg
-- name    : ZOGlobalLB_ZOAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:46:39.276953+00:00
-- url     : https://prove2.me/theorems/dbf18c2f-0c5d-4707-8166-0fd339af92d8
-- title:
--   Randomized adaptive zeroth-order algorithms with reusable labels, their cost and success
-- statement:
--   A **randomized adaptive zeroth-order algorithm** on $\mathbb R^d$ with labels $\Xi=\{1,\dots,n\}$ has a random seed $\omega$ from a probability space $(\Omega,\mu)$. At each round $t=0,1,2,\dots$ it looks at its seed and the history of the previous rounds (label, query point, exact reply) and either
--
--   1. evaluates some label $\xi$ at some point $x\in\mathbb R^d$ and receives the exact value $f_\xi(x)$ (one query), or
--   2. stops and outputs a point $\hat x\in\mathbb R^d$ (not evaluated, no cost).
--
--   Any point, any label and any reuse of labels are allowed, and the rule may never stop; it is required to be measurable in the seed and the history. The **cost** of a run is its number of evaluations ($\infty$ if it never stops). The run **succeeds** at accuracy $\epsilon$ if it stops with $\|\nabla f(\hat x)\|\le\epsilon$, where $f$ is the population mean.
--
--   **Formalization Note.** Rounds are 0-based; the history is `none` after the run stops; the cost is the round at which the rule stops, in $\mathbb N\cup\{\infty\}$.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Section 2, p.4 (oracle model)

import Mathlib
import Definitions.Def_ZOGlobalLB_Admissible

open MeasureTheory
open scoped ENNReal

namespace ZOGlobalLB

/-- **A randomized adaptive zeroth-order algorithm** with reusable labels.
Xia, Yuan, arXiv:2610.19652, Section 2, p.4: "An algorithm may randomize, adaptively query any
`(ξ, x) ∈ Ξ × ℝᵈ`, reuse labels, and output any point. Each exact scalar evaluation costs one
query."

At round `t` (rounds `0, 1, 2, …`), given its random seed `ω ∈ Ω` and the history of the `t`
previous rounds (label, query point, exact reply `f_ξ(x)`), the rule `next t ω h` either stops and
outputs a point (`Sum.inl x`) or evaluates label `j` at point `x` (`Sum.inr (j, x)`).

**Formalization Note.** The label set is `Fin n`. The seed space `Ω` is an arbitrary measurable
space (the paper notes that seed spaces need not be standard Borel, Lemma C.5, p.52); the rule
is jointly measurable in the seed and the history. Nothing else is imposed: any point, any label,
any reuse, and the rule may never stop. The rule sees the instance only through replies. -/
structure ZOAlg (d n : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- The query/stopping rule at round `t`. -/
  next : (t : ℕ) → Ω → (Fin t → Fin n × E d × ℝ) → E d ⊕ (Fin n × E d)
  /-- The rule is jointly measurable in the seed and the history. -/
  measurable_next : ∀ t, Measurable (Function.uncurry (next t))

namespace ZOAlg

variable {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The history of the run of `A` on the family `F` at seed `ω` before round `t`:
`some h` with `h : Fin t → (label, point, reply)` if the run has not stopped before round `t`,
`none` once it has stopped. Each paid round appends the exact reply `F j x`. -/
noncomputable def hist (A : ZOAlg d n Ω) (F : Fin n → E d → ℝ) (ω : Ω) :
    (t : ℕ) → Option (Fin t → Fin n × E d × ℝ)
  | 0 => some Fin.elim0
  | t + 1 => (A.hist F ω t).bind fun h =>
      match A.next t ω h with
      | Sum.inl _ => none
      | Sum.inr q => some (Fin.snoc (α := fun _ => Fin n × E d × ℝ) h (q.1, q.2, F q.1 q.2))

/-- The output of the run if it stops exactly at round `t` (after `t` paid queries), else `none`.
The output point is free: it is not evaluated. -/
noncomputable def outputAt (A : ZOAlg d n Ω) (F : Fin n → E d → ℝ) (ω : Ω) (t : ℕ) :
    Option (E d) :=
  (A.hist F ω t).bind fun h =>
    match A.next t ω h with
    | Sum.inl x => some x
    | Sum.inr _ => none

/-- The query cost of the run: the number of paid evaluations before the rule stops, i.e. the
round at which it stops; `⊤` if it never stops. -/
noncomputable def cost (A : ZOAlg d n Ω) (F : Fin n → E d → ℝ) (ω : Ω) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : (A.outputAt F ω t).isSome), (t : ℕ∞)

/-- **Success**: the run stops and its output `x̂` satisfies `‖∇f(x̂)‖ ≤ ε`, where `f` is the
population mean of `F` (Theorem 2.1, p.4: "Finding `‖∇f(x̂)‖ ≤ ϵ`"). A run that never stops
fails. -/
def Succeeds (ε : ℝ) (A : ZOAlg d n Ω) (F : Fin n → E d → ℝ) (ω : Ω) : Prop :=
  ∃ t x, A.outputAt F ω t = some x ∧ ‖gradient (popMean F) x‖ ≤ ε

end ZOAlg

end ZOGlobalLB


