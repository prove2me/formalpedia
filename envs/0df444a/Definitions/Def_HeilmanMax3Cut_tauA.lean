-- Prove2me | Definitions.Def_HeilmanMax3Cut_tauA
-- name    : HeilmanMax3Cut_tauA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:09.020508+00:00
-- url     : https://prove2.me/theorems/271fea44-436d-489a-8c52-0894b6a3c313
-- title:
--   $\tau(a)=4P(a)-3k(a)$
-- statement:
--   With $b=1/3$, $k(a)=K_a(b,b)$ and $P(a)=\partial_1K_a(b,b)$,
--
--   $$\tau(a)=4P(a)-3k(a).$$
--
--   $\tau(a)$ is the cross coefficient of the joint arc bound (Lemma 8.1); $\tau(0)=1$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (65), p.23

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Karc
import Definitions.Def_HeilmanMax3Cut_PA

namespace HeilmanMax3Cut

/-- **`τ(a) = 4P(a) − 3k(a)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (65), p.23, where `k(a) := K_a(b, b)` and `b = 1/3`. -/
noncomputable def tauA (a : ℝ) : ℝ :=
  4 * PA a - 3 * Karc a (1 / 3) (1 / 3)

end HeilmanMax3Cut


