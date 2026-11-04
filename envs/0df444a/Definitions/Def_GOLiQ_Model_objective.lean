-- Prove2me | Definitions.Def_GOLiQ_Model_objective
-- name    : GOLiQ_Model_objective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:52.427915+00:00
-- url     : https://prove2.me/theorems/5f9544b5-88c7-4e8a-a845-0011a8ef0e3e
-- title:
--   Objective (5): $f(\mu,p)=h_0\lambda(p)(\mathbb E[W_\infty(\mu,p)]+1/\mu)+c(\mu)-p\lambda(p)$
-- statement:
--   For $(\mu,p)$, let $W_\infty(\mu,p)$ be the steady-state waiting time of the GI/GI/1 queue with service times $V_j/\mu$ and interarrival times $U_j/\lambda(p)$, realized by Loynes' construction on the primitives, and $X_\infty(\mu,p)$ the steady-state observed busy period. Write $w(\mu,p)=\mathbb E[W_\infty(\mu,p)]$. The **objective** is
--   $$f(\mu,p)=h_0\lambda(p)\Big(\mathbb E[W_\infty(\mu,p)]+\frac1\mu\Big)+c(\mu)-p\lambda(p).\tag{5}$$
--   It is the steady-state expected cost rate $h_0\mathbb E[Q_\infty]+c(\mu)-p\lambda(p)$ of (2), rewritten by Little's law; the provider minimizes it over $\mathcal B$.
--
--   **Formalization Note** $f$ is defined by (5) at every point of the plane; only its values on $\mathcal B$ are used. The module also defines $W_\infty$, $X_\infty$, $w$ and $\mathbb E[X_\infty]$.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, (2), p.10; (5), p.13; w(µ,p), p.22

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_loynesWait
import Definitions.Def_GOLiQ_loynesBusy

open MeasureTheory

namespace GOLiQ

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω)

/-- `W∞(µ, p)`: the steady-state waiting time of the GI/GI/1 queue with service times `Vⱼ/µ` and
interarrival times `Uⱼ/λ(p)`, realized by Loynes' construction on the primitives `(U, V)`
(Chen, Liu, Hong, arXiv:2009.02911v3, (5), p.13; coupling from the past, p.58). -/
noncomputable def stationaryWait (mu p : ℝ) (ω : Ω) : ℝ :=
  loynesWait (fun j => Pr.V j ω / mu) (fun j => Pr.U j ω / M.lam p)

/-- `X∞(µ, p)`: the steady-state observed busy period, realized on the same primitives
(Lemma 5, p.30). -/
noncomputable def stationaryBusy (mu p : ℝ) (ω : Ω) : ℝ :=
  loynesBusy (fun j => Pr.V j ω / mu) (fun j => Pr.U j ω / M.lam p)

/-- `w(µ, p) = E[W∞(µ, p)]` (p.22). -/
noncomputable def waitMean (mu p : ℝ) : ℝ := ∫ ω, M.stationaryWait Pr mu p ω ∂Pr.P

/-- `E[X∞(µ, p)]`. -/
noncomputable def busyMean (mu p : ℝ) : ℝ := ∫ ω, M.stationaryBusy Pr mu p ω ∂Pr.P

/-- **The objective (5)** (Chen, Liu, Hong, arXiv:2009.02911v3, p.13): for `x = (µ, p)`,

`f(µ, p) = h₀ λ(p) (E[W∞(µ, p)] + 1/µ) + c(µ) − p λ(p)`.

This is the steady-state expected cost (2), rewritten by Little's law; it is minimized over the box
`B`. **Formalization Note.** `f` is defined by (5) for every point of the plane; only its values on
`B` are used. -/
noncomputable def objective (x : Point) : ℝ :=
  M.h0 * M.lam (x 1) * (M.waitMean Pr (x 0) (x 1) + 1 / x 0) + M.c (x 0) - x 1 * M.lam (x 1)

end Model

end GOLiQ


