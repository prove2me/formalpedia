-- Prove2me | Definitions.Def_OnlineDiscUniv_Supplement_arrayLaw
-- name    : OnlineDiscUniv_Supplement_arrayLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:28:08.629713+00:00
-- url     : https://prove2.me/theorems/6a4d1735-434c-474a-a150-a7f49119b6a0
-- title:
--   Law of an input array with independent entries of different laws
-- statement:
--   Let $M,N\ge1$ and let $\nu_{k,i}$, $1\le k\le N$, $1\le i\le M$, be probability laws on $\mathbb R$. The **array law** $\bigotimes_{k=1}^N\bigotimes_{i=1}^M\nu_{k,i}$ is the law of an input $(\xi_1,\dots,\xi_N)$, $\xi_k=(\xi_{k,1},\dots,\xi_{k,M})\in\mathbb R^M$, whose $MN$ entries are mutually independent with $\xi_{k,i}\sim\nu_{k,i}$.
--
--   This is the input model of §6.2, in which the entry laws may differ across columns, rows and $N$. When every $\nu_{k,i}$ equals one law $\mu$ it is the i.i.d. input law of the main results.
--
--   **Formalization Note** Column $k$ and row $i$ are 0-based indices `Fin N`, `Fin M`, as in the published `OnlineDiscUniv.OnlineAlg`; the law is the iterated product measure `Measure.pi`.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), §6.2, Theorem 6.1, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_OnlineDiscUniv_OnlineAlg

set_option autoImplicit false

open MeasureTheory

namespace OnlineDiscUniv.Supplement

/-- The law of an input array with **independent entries whose laws may differ** (Jo–Lee,
*Exact Universality of Online Discrepancy*, arXiv:2610.00103, artifact sha256 cb190f12…,
§6.2, Theorem 6.1, printed p.25, PDF p.26): the `M·N` entries `ξ_{k,i}` are mutually
independent and `ξ_{k,i}` has law `ν k i`.

**Formalization Note** The input is `ξ : Fin N → Fin M → ℝ` as in the published
`OnlineDiscUniv.OnlineAlg`: column `k` (0-based) is the paper's vector `ξ_{k+1}` and coordinate
`i` (0-based) is row `i+1`. Mutual independence of all entries is the product measure
`⊗_k ⊗_i ν k i`. The published i.i.d. law `inputLaw μ M N` is the special case `ν k i = μ`
for all `k, i`. -/
noncomputable def arrayLaw {M N : ℕ} (ν : Fin N → Fin M → Measure ℝ) :
    Measure (Fin N → Fin M → ℝ) :=
  Measure.pi fun k : Fin N => Measure.pi fun i : Fin M => ν k i

end OnlineDiscUniv.Supplement


