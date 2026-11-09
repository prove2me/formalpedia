-- Prove2me | Definitions.Def_QMAvsQCIP_bernW
-- name    : QMAvsQCIP_bernW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:29.782141+00:00
-- url     : https://prove2.me/theorems/57ddca42-c2ba-46ce-ada8-911c9ad52f0a
-- title:
--   Independent Bernoulli weight
-- statement:
--   For a finite set $X$ and $p\in[0,1]$, the probability of $f:X\to\{0,1\}$ when the values $f(x)$ are independent Bernoulli$(p)$ is
--   $$
--   \prod_{x\in X}p^{f(x)}(1-p)^{1-f(x)} .
--   $$
--
--   **Formalization Note** A proved sanity check shows these weights sum to $1$.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Section 3.1, p.13; Definition 8, p.24

import Mathlib

set_option autoImplicit false

namespace QMAvsQCIP

/-- The probability weight of `f : X → {0,1}` under **independent Bernoulli(p) values**:
`∏_{x ∈ X} p^{f(x)} (1 − p)^{1 − f(x)}`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Section 3.1, p.13 (PDF p.16): "We write Bernoulli(p) for the distribution
that assigns probability p to one and 1 − p to zero"; Definition 8, p.24 (PDF p.27):
"H_i(a) ← Bernoulli(p)", "O(y, v) ←ind Bernoulli(δ)". -/
def bernW {X : Type} [Fintype X] (p : ℝ) (f : X → Bool) : ℝ :=
  ∏ x, if f x then p else 1 - p

end QMAvsQCIP


