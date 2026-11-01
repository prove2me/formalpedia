-- Prove2me | Definitions.Def_LocalDOvS_SUS_tapeMeasure
-- name    : LocalDOvS_SUS_tapeMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:23.982092+00:00
-- url     : https://prove2.me/theorems/1699cb90-f251-4cd8-86eb-081d70b9797d
-- title:
--   Reward tape of a model
-- statement:
--   A **tape** is an array $\omega=(\omega(x,j))_{x,j\in\mathbb N}$ of real numbers; $\omega(x,j)$ is the output of the $(j+1)$-th simulation of decision $x$. The tape measure of a model is the product measure
--
--   $$
--   P_M=\bigotimes_{(x,j)\in\mathbb N\times\mathbb N}\nu_x ,
--   $$
--
--   under which all entries are independent and the entries of one decision are i.i.d. copies of $F(x,\xi_x)$. This is the paper's convention that the simulations $F(x,\xi_{x,1}),F(x,\xi_{x,2}),\dots$ are independent copies.
--
--   **Formalization Note** Mathlib's `Measure.infinitePi`; it is a probability measure because every $\nu_x$ is.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, §1.2, p.7

import Mathlib
import Definitions.Def_LocalDOvS_SUS_Model

open MeasureTheory

namespace LocalDOvS.SUS

/-- The reward tape of a model (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, §1.2, p.7: "We write
`ξ_{x,1}, ξ_{x,2}, …, ξ_{x,n}` as independent and identically distributed copies of `ξ_x`").
A tape is `ω : ℕ × ℕ → ℝ`; the entry `ω (x, j)` is the output of the `(j + 1)`-th simulation of
decision `x`. Under `tapeMeasure M` all entries are independent and `ω (x, j)` has law
`M.law x`, so the entries of one decision are i.i.d.

**Formalization Note.** This is Mathlib's infinite product `Measure.infinitePi` of the laws
`M.law x` over the index set `ℕ × ℕ`; it is a probability measure because every `M.law x` is.
Simulations are 0-indexed: the `j`-th entry (`j ≥ 0`) is the paper's `(j + 1)`-th copy. -/
noncomputable def tapeMeasure (M : Model) : Measure (ℕ × ℕ → ℝ) :=
  Measure.infinitePi (fun p : ℕ × ℕ => M.law p.1)

end LocalDOvS.SUS


