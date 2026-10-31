-- Prove2me | Definitions.Def_MarketplaceScalability_Model
-- name    : MarketplaceScalability_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:34.793814+00:00
-- url     : https://prove2.me/theorems/0c5a1d83-2883-408d-a9d8-242c63dfa49e
-- title:
--   The model (corrected demand conditions, Assumption 1)
-- statement:
--   The conditions on the data.
--
--   1. The commission satisfies $0\le\alpha<1$.
--   2. $R'=D$ on $J=(0,\bar q)$, with $\bar q>0$.
--   3. On $J$, the demand $D$ is twice differentiable with $D>0$, $D'<0$ and $D''\le0$.
--   4. For every price $p\in(0,\bar c]$ the first-order condition $(1-\alpha)D(q)=p$ has a solution $q\in J$.
--   5. $0<\underline c<c<\bar c$ and $f<F$.
--   6. Assumption 1 holds:
--   $$
--   0<(1-\alpha)R(q(\bar c))-\bar c\,q(\bar c)-f<(1-\alpha)R(q(\underline c))-\underline c\,q(\underline c)-F.
--   $$
--
--   Every result of the mission is stated for such a model. Assumption 1 says that sellers enter under the market service and that, when they can scale, they prefer own service to the market service.
--
--   **Formalization Note** Conditions 2–4 correct p.4, which assumes $D>0$, $D'<0$, $D''\le0$ and $D(0)=\infty$. No function satisfies these: a positive concave function on $(0,\infty)$ cannot be strictly decreasing, and a concave function on $(0,b)$ cannot tend to $+\infty$ at $0$. The signs are kept on a bounded interval, and $D(0)=\infty$ is replaced by condition 4, which is the use the source makes of it. Linear demand $D(q)=a-bq$ on $(0,a/b)$ is an instance. The source's $\alpha$ has no stated range: $\alpha<1$ is forced by the first-order condition, and $\alpha=0$ is admitted. The condition $f<F$ is the investment $F-f$ of §2.2. Assumption 2 concerns low-type sellers, who are absent here.
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §2.1–§2.2, §2.4, Assumption 1, pp.4, 6

import Mathlib
import Definitions.Def_MarketplaceScalability_Params_J
import Definitions.Def_MarketplaceScalability_Params_sellerPayoff

namespace MarketplaceScalability

/-- **The model**: the conditions on the data of `Params`.
Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, §2.1–§2.2, §2.4 and Assumption 1, pp.4, 6.

The commission satisfies `0 ≤ α < 1`; `D = R′` on `J = (0, q̄)`, where `D` is twice differentiable
with `D > 0`, `D′ < 0`, `D″ ≤ 0`; the first-order condition `(1 − α) D(q) = p` has a solution in
`J` at every price `p ∈ (0, c̄]`; `0 < c̲ < c < c̄`; `f < F`; and Assumption 1 holds:
`0 < (1 − α) R(q(c̄)) − c̄ q(c̄) − f < (1 − α) R(q(c̲)) − c̲ q(c̲) − F`.

**Formalization Note**
* Correction: p.4 assumes `D > 0`, `D′ < 0`, `D″ ≤ 0` and `D(0) = ∞`, which no function satisfies.
  A positive concave function on `(0, ∞)` cannot be strictly decreasing, and a concave function on
  `(0, b)` cannot tend to `+∞` at `0`. So the signs are kept on the bounded interval `J`, and
  `D(0) = ∞` is replaced by `range_foc`, which is the use the source makes of it. The file
  `Solutions/verification/MarketplaceScalability_sanity.lean` proves both facts and exhibits an
  instance.
* `α < 1` is forced by the first-order condition with `D > 0` and `c̃ > 0`; `α = 0` is admitted.
* `0 < c̲` follows in the source from the first-order condition at `c̲`.
* `f < F` is the investment `F − f` of §2.2. Assumption 2 concerns low-type sellers, who are absent
  at μ = 1, so it is not a field. -/
structure Model extends Params where
  alpha_nonneg : 0 ≤ α
  alpha_lt_one : α < 1
  qbar_pos : 0 < qbar
  /-- `D = R′` on `J`. -/
  hasDerivAt_R : ∀ q ∈ toParams.J, HasDerivAt R (D q) q
  differentiableAt_D : ∀ q ∈ toParams.J, DifferentiableAt ℝ D q
  differentiableAt_deriv_D : ∀ q ∈ toParams.J, DifferentiableAt ℝ (deriv D) q
  D_pos : ∀ q ∈ toParams.J, 0 < D q
  deriv_D_neg : ∀ q ∈ toParams.J, deriv D q < 0
  deriv2_D_nonpos : ∀ q ∈ toParams.J, deriv (deriv D) q ≤ 0
  /-- The correction of `D(0) = ∞`: the first-order condition is solvable on `(0, c̄]`. -/
  range_foc : ∀ p ∈ Set.Ioc 0 cbar, ∃ q ∈ toParams.J, (1 - α) * D q = p
  cown_pos : 0 < cown
  cown_lt_c : cown < c
  c_lt_cbar : c < cbar
  f_lt_F : f < F
  /-- Assumption 1, first inequality. -/
  assumption1_left : 0 < toParams.sellerPayoff cbar f
  /-- Assumption 1, second inequality. -/
  assumption1_right : toParams.sellerPayoff cbar f < toParams.sellerPayoff cown F

end MarketplaceScalability


