-- Prove2me | Definitions.Def_ActiveCtxSearch_Stream
-- name    : ActiveCtxSearch_Stream
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:40:04.554382+00:00
-- url     : https://prove2.me/theorems/025b70a9-bfb7-4b99-ace0-dbd91198700c
-- title:
--   The item stream and the binary feedback
-- statement:
--   Items arrive one at a time. Item $t$ carries a context $x_t$ and a noise $\xi_t$; the contexts are i.i.d. $P_X$, the noises are i.i.d. $P_\xi$, and the two sequences are independent. The **stream law** is the infinite product of $P_X\otimes P_\xi$ over $t\in\mathbb N$.
--
--   After seeing $x_t$, the decision-maker either lets the item pass, obtaining nothing, or **queries** it at an action $b\in\mathbb R$ and observes the binary feedback
--   $$y_t=\operatorname{sgn}(u_t-b)=\begin{cases}+1,& u_t\ge b,\\-1,& u_t<b,\end{cases}\qquad u_t=v(x_t)+\xi_t .$$
--
--   The algorithms of the mission are deterministic functions of the stream that use only the contexts they read and the feedback of the items they query.
--
--   **Formalization Note** $\operatorname{sgn}(0)=+1$, matching $y=1$ when $u=b$. Labels are the integers $\pm1$. The stream is a sequence of (context, noise) pairs; the noise of a passed item is never read.
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, §2, pp.7–8, Eq. (1) and the two actions on p.8

import Mathlib
import Definitions.Def_ActiveCtxSearch_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace ActiveCtxSearch

/-- The sign `sgn(t) ∈ {±1}` used for binary feedback and classifiers (arXiv:2110.01072v2, p.8,
"`yᵢ = 1` if `uᵢ ≥ bᵢ` or `yᵢ = −1` if `uᵢ < bᵢ`", and Eq. (3), p.12).

**Formalization Note** `sgn(0) = +1`, matching `yᵢ = 1` when `uᵢ = bᵢ`. Labels are the integers `±1`. -/
noncomputable def sgn (t : ℝ) : ℤ := if 0 ≤ t then 1 else -1

namespace Problem

variable {d : ℕ}

/-- The binary feedback of a query at action `b` on an item `z = (x, ξ)` (arXiv:2110.01072v2, p.8):
`y = sgn(u − b)` with `u = v(x) + ξ`, i.e. `y = 1` if `u ≥ b` and `y = −1` if `u < b`. -/
noncomputable def response (I : Problem d) (z : E d × ℝ) (b : ℝ) : ℤ := sgn (I.v z.1 + z.2 - b)

/-- The law of the item stream `((x_t, ξ_t))_{t ≥ 0}` (arXiv:2110.01072v2, §2, p.7): the contexts
`x_t` are i.i.d. `P_X`, the noises `ξ_t` are i.i.d. `P_ξ`, and the two sequences are independent.

**Formalization Note** The stream is a sequence `ω : ℕ → ℝᵈ × ℝ` of (context, noise) pairs under the
infinite product of `P_X ⊗ P_ξ`. An algorithm reads the items in order. It sees the context of every
item it reads and, for an item it queries at `b`, the feedback `response I (ω t) b`; the noise of an
item it lets pass is never used. -/
noncomputable def streamLaw (I : Problem d) : Measure (ℕ → E d × ℝ) :=
  Measure.infinitePi (fun _ : ℕ => I.PX.prod I.Pξ)

end Problem

end ActiveCtxSearch


