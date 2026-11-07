-- Prove2me | Definitions.Def_EllipsoidFitting_mpCoeff
-- name    : EllipsoidFitting_mpCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:09.634189+00:00
-- url     : https://prove2.me/theorems/4a19a9de-53b6-4820-b2eb-05f05966e5ba
-- title:
--   The coefficients $c_t(k)$ of $Y^k$ in the MP basis
-- statement:
--   For a real $\gamma$, the numbers $c_t(k)$ ($t,k\ge0$) are defined by $c_0(0)=1$, $c_t(0)=0$ for $t>0$, and
--   $$
--   c_0(k+1)=\gamma c_1(k)-\gamma c_0(k),\qquad c_t(k+1)=c_{t-1}(k)+\gamma c_{t+1}(k)\quad(t\ge1).
--   $$
--   They are the coefficients of $(x-(1+\gamma))^k=\sum_{t=0}^kc_t(k)\,q_t(x)$, used for the centered matrix $Y=A-(1+\gamma)I_m$.
--
--   **Formalization Note** The two cases $t=1$ and $t\ge2$ printed on p.45 are the same formula and form one clause.
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), §4.2, proof of Lemma 4.10, p.45 (PDF p.47)

import Mathlib

set_option autoImplicit false

namespace EllipsoidFitting

/-- **The coefficients `c_t(k)` of `Y^k` in the MP basis.** de la Cerda, Potechin, Tulsiani, Xu,
*Sharp Phase Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), §4.2,
proof of Lemma 4.10, p.45: "Write Y^k = ∑_{t=0}^k ct(k) · qt(A)"; "with initial condition c0(0) =
1, ct(0) = 0 for any t > 0"; "c0(k + 1) = γc1(k) − γc0(k), c1(k + 1) = c0(k) + γc2(k), and, for
t ≥ 2, ct(k + 1) = ct−1(k) + γct+1(k)."

`mpCoeff γ k t` is `c_t(k)`, defined by this recurrence in `k`.

**Formalization Note** The cases `t = 1` and `t ≥ 2` of p.45 are the single clause
`c_{t+1}(k+1) = c_t(k) + γ c_{t+2}(k)`. These are the coefficients of `(x − (1 + γ))^k` in the
basis `q_t^{(γ)}` (Definition 2.14). -/
noncomputable def mpCoeff (γ : ℝ) : ℕ → ℕ → ℝ
  | 0, t => if t = 0 then 1 else 0
  | k + 1, 0 => γ * mpCoeff γ k 1 - γ * mpCoeff γ k 0
  | k + 1, t + 1 => mpCoeff γ k t + γ * mpCoeff γ k (t + 2)

end EllipsoidFitting


