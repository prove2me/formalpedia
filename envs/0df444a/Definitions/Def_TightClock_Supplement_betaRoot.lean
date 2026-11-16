-- Prove2me | Definitions.Def_TightClock_Supplement_betaRoot
-- name    : TightClock_Supplement_betaRoot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:14:15.369917+00:00
-- url     : https://prove2.me/theorems/47bd0671-c80f-4f3c-a693-5dd313857dec
-- title:
--   Root $\beta>1$ of $\beta\log\beta-\beta+1=c$
-- statement:
--   For $c>0$, the equation
--
--   $$\beta\log\beta-\beta+1=c$$
--
--   has exactly one solution $\beta>1$: the left side is continuous, equals $0$ at $\beta=1$, increases strictly on $(1,\infty)$ (its derivative is $\log\beta$) and is unbounded. This root defines the parameter $\beta$ of Window, (5.2), with $c=\log(b/a)$, and $\beta_m$ of (5.1), with $c=\log(4m)$.
--
--   **Formalization Note** For $c\le0$ there is no root and the value is set to $1$; this happens only for $\beta_m$ with no bidders. Existence and uniqueness for $c>0$ are proved in the mission's verification file.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §5, (5.1), p.21 (PDF p.24); (5.2), p.24 (PDF p.27)

import Mathlib

set_option autoImplicit false

open Classical

namespace TightClock.Supplement

/-- The unique `β > 1` with `β log β − β + 1 = c` (natural log), for `c > 0`. It defines `β` of
Window, (5.2), with `c = log(b/a)`, and `β_m` of (5.1), with `c = log(4m)`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §5, (5.1) p.21
(PDF 24), (5.2) p.24 (PDF 27).

**Formalization Note** For `c > 0` a root exists and is unique (the left side increases strictly from
`0` on `(1, ∞)`; checked in `Solutions/verification/TightClock_Supplement_sanity.lean`). For `c ≤ 0`
there is none and the value is `1`; this happens only for `β_m` with no bidders. -/
noncomputable def betaRoot (c : ℝ) : ℝ :=
  if h : ∃ β : ℝ, 1 < β ∧ β * Real.log β - β + 1 = c then h.choose else 1

end TightClock.Supplement


