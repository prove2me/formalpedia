-- Prove2me | Definitions.Def_HeilmanMax3Cut_jA
-- name    : HeilmanMax3Cut_jA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:02.995485+00:00
-- url     : https://prove2.me/theorems/7ee9743d-a7ca-4e0c-91fd-0861c5477f93
-- title:
--   $j(a)=P(a)-3k(a)$
-- statement:
--   With $b=1/3$, $k(a)=K_a(b,b)$ and $P(a)=\partial_1K_a(b,b)$,
--
--   $$j(a)=P(a)-3k(a).$$
--
--   $j(a)$ is the diagonal coefficient of the joint arc bound (Lemma 8.1); $j(0)=0$ and $j(a)>0$ for $a>0$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (65), p.23

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Karc
import Definitions.Def_HeilmanMax3Cut_PA

namespace HeilmanMax3Cut

/-- **`j(a) = P(a) − 3k(a)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (65), p.23, where `k(a) := K_a(b, b)` and `b = 1/3`. -/
noncomputable def jA (a : ℝ) : ℝ :=
  PA a - 3 * Karc a (1 / 3) (1 / 3)

end HeilmanMax3Cut


