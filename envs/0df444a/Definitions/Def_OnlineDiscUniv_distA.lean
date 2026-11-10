-- Prove2me | Definitions.Def_OnlineDiscUniv_distA
-- name    : OnlineDiscUniv_distA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:05.596083+00:00
-- url     : https://prove2.me/theorems/cbd495a4-f293-454b-895c-d22214b35afe
-- title:
--   Distance $d_a(x)=\operatorname{dist}(x,[-a,a])=(|x|-a)_+$
-- statement:
--   For $x\in\mathbb R$ and $a>0$,
--   $$
--   d_a(x):=\operatorname{dist}(x,[-a,a])=(|x|-a)_+ .
--   $$
--   It measures how far a terminal value lies outside the target interval $[-a,a]$ (Proposition 4.5).
--
--   **Formalization Note** Written as $\max(|x|-a,0)$, which equals the distance for $a\ge0$.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), (4.7), p.14 (PDF p.15)

import Mathlib

set_option autoImplicit false

namespace OnlineDiscUniv

/-- `d_a(x) := dist(x, [−a, a]) = (|x| − a)_+` (Jo–Lee, arXiv:2610.00103, artifact sha256
cb190f12…, (4.7), printed p.14, PDF p.15).

**Formalization Note** Written as `max (|x| − a) 0`, which equals the distance to `[−a, a]` for
`a ≥ 0` (the paper takes `a > 0`). -/
noncomputable def distA (a x : ℝ) : ℝ := max (|x| - a) 0

end OnlineDiscUniv


