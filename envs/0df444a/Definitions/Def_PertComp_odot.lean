-- Prove2me | Definitions.Def_PertComp_odot
-- name    : PertComp_odot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:21.023383+00:00
-- url     : https://prove2.me/theorems/87bc54e2-9848-47a9-b325-ad76954f0df6
-- title:
--   The scaled function $\xi\odot f$
-- statement:
--   For $\xi\in[0,+\infty[$,
--   $$\xi\odot f=\begin{cases}\iota_{\overline{\operatorname{dom} f}}, & \xi=0;\\ \xi f, & \xi>0,\end{cases}$$
--   where $\overline{\operatorname{dom} f}$ is the **closure** of the domain of $f$. This is the function that multiplies $f$ inside the Lagrangian (3.2), (3.10) and the chain rule (2.15).
--
--   **Formalization Note** The closure is in the topology of the space (for functions on $X^*$, its norm topology). The paper defines $\xi\odot f$ only for $\xi\ge0$; the Lean definition returns $\xi f$ for $\xi<0$, a value no statement of the mission reaches (it uses $\xi\odot f$ only for $\xi\in\operatorname{dom}\varphi^*\subset[0,+\infty[$ or $\xi\in\partial\varphi(f(x))\subset[0,+\infty[$). At $\xi=0$ the value is the indicator, not $0\cdot f$.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, (2.8), p.5

import Mathlib
import Definitions.Def_PertComp_indicator

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, (2.8), p.5: for `ξ ∈ [0, +∞[`,
`ξ ⊙ f = ι_{cl(dom f)}` (the indicator of the **closure** of `dom f`) if `ξ = 0`, and `ξ f` if
`ξ > 0`.

**Formalization Note.** The closure is for the topology of `V` (for a function on a dual space,
the norm topology of the dual). The paper defines `ξ ⊙ f` only for `ξ ≥ 0`; the value returned
here for `ξ < 0` (`ξ f`) is never used by a statement of the mission, which applies `ξ ⊙ f` only
at `ξ ∈ dom φ* ⊂ [0, +∞[` or `ξ ∈ ∂φ(f(x)) ⊂ [0, +∞[`. At `ξ = 0` the indicator is not
`0 · f` (in `EReal`, `0 · ⊤ = 0`). -/
noncomputable def odot {V : Type*} [TopologicalSpace V] (ξ : ℝ) (f : V → EReal) : V → EReal :=
  if ξ = 0 then indicator (closure {x | f x ≠ ⊤}) else fun x => (ξ : EReal) * f x

end PertComp


