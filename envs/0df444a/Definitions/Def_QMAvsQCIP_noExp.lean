-- Prove2me | Definitions.Def_QMAvsQCIP_noExp
-- name    : QMAvsQCIP_noExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:53:42.587943+00:00
-- url     : https://prove2.me/theorems/a5e85e2a-6621-462b-8c43-3ec5a9989144
-- title:
--   Expectation over $\mathrm{NO}_\lambda$
-- statement:
--   The **independent-marking distribution** $\mathrm{NO}_\lambda$ samples $O(y,v)\leftarrow\mathrm{Bernoulli}(\delta)$ independently for every $(y,v)\in Z_\lambda$, with $\delta=2^{-\lceil\lambda/12\rceil}$. This is the expectation $\mathbb E_{O\leftarrow\mathrm{NO}_\lambda}[F(O)]$; the probability of an event is the expectation of its indicator.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 8, Eq. (13), p.24

import Definitions.Def_QMAvsQCIP_Zdom
import Definitions.Def_QMAvsQCIP_bernExp
import Definitions.Def_QMAvsQCIP_delta

set_option autoImplicit false

namespace QMAvsQCIP

/-- Expectation over the **independent-marking distribution** `NO_λ` (Definition 8, item 2): the
values `O(y, v)`, `(y, v) ∈ Z_λ`, are independent Bernoulli(`δ`), `δ = 2^{−⌈λ/12⌉}`. The
probability of an event `E` is `noExp λ q (E.indicator 1)`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 8, p.24 (PDF p.27): "2. Independent-marking distribution
(NO_λ). Sample independently O(y, v) ←ind Bernoulli(δ) for every (y, v) ∈ Z_λ." -/
noncomputable def noExp (lam : ℕ) (q : ℕ+) (F : (Zdom lam q → Bool) → ℝ) : ℝ :=
  bernExp (delta lam) F

end QMAvsQCIP


