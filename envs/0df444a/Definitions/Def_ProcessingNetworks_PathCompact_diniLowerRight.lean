-- Prove2me | Definitions.Def_ProcessingNetworks_PathCompact_diniLowerRight
-- name    : ProcessingNetworks_PathCompact_diniLowerRight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:29:27.56259+00:00
-- url     : https://prove2.me/theorems/76f44f14-a925-478b-b576-b54c1b0e5372
-- title:
--   Eq. (A.10) — lower Dini derivative $D^-f(t)=\liminf_{h\downarrow0}(f(t+h)-f(t))/h$
-- statement:
--   For a function $f$ and a time $t\ge0$, the **lower Dini derivative** of $f$ at $t$ is
--
--   $$D^-f(t):=\liminf_{h\downarrow0}\frac{f(t+h)-f(t)}{h}\in[-\infty,\infty].$$
--
--   It is the companion of the upper Dini derivative $D^+f(t)=\limsup_{h\downarrow0}(f(t+h)-f(t))/h$ of eq. (A.9), published as `ProcessingNetworks.LyapunovCriteria.diniUpperRight`, and it is defined in exactly the same way. Dini derivatives replace ordinary derivatives in Lyapunov arguments for fluid models whose Lyapunov functions are only continuous.
--
--   **Formalization Note** The value lies in the extended reals `EReal`, so $\pm\infty$ are represented. The book's $f$ is defined on $\mathbb R_+$; here $f:\mathbb R\to\mathbb R$, as in the published `diniUpperRight`. At $t\ge0$ only the values of $f$ on $[t,\infty)$ enter, so a function on $\mathbb R_+$ and any extension of it have the same Dini derivatives there.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix A, §A.4, eq. (A.10), p.262 (PDF 278)

import Mathlib

open Filter Topology

namespace ProcessingNetworks.PathCompact

/-- The **lower (right) Dini derivative** `D₋f(t)`, Dai & Harrison, *Processing Networks*
(pre-publication draft 2020-4-2, spnbook.org), Appendix A, §A.4, eq. (A.10), p.262 (PDF 278):
`D₋f(t) := liminf_{h ↓ 0} (f(t + h) − f(t)) / h`.

It is the `liminf` companion of the published upper Dini derivative
`ProcessingNetworks.LyapunovCriteria.diniUpperRight` (eq. (A.9)), defined the same way.

**Formalization Note.** The value is taken in `EReal`, so `+∞` and `−∞` are represented as such.
The book's `f` is defined on `ℝ₊`; here `f : ℝ → ℝ`, as in `diniUpperRight`. At a time `t ≥ 0`
only the values of `f` on `[t, ∞)` enter, so a function on `ℝ₊` and any extension of it to `ℝ`
have the same Dini derivatives there. -/
noncomputable def diniLowerRight (f : ℝ → ℝ) (t : ℝ) : EReal :=
  Filter.liminf (fun h : ℝ => (((f (t + h) - f t) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

end ProcessingNetworks.PathCompact


