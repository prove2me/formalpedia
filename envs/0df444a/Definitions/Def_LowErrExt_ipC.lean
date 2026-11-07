-- Prove2me | Definitions.Def_LowErrExt_ipC
-- name    : LowErrExt_ipC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:36.37931+00:00
-- url     : https://prove2.me/theorems/e31741d1-a249-438a-8be9-a7fafb3211fc
-- title:
--   The complex inner product $\mathrm{IP}$ on $\prod_i\mathbb Z_{q_i}\times\prod_i\mathbb Z_{p_i}$
-- statement:
--   For positive integers $d,q_1,\dots,q_d,p_1,\dots,p_d$ with $p_i\mid q_i$, the **inner product**
--   $$\mathrm{IP}:(\mathbb Z_{q_1}\times\cdots\times\mathbb Z_{q_d})\times(\mathbb Z_{p_1}\times\cdots\times\mathbb Z_{p_d})\to\mathbb C^\times$$
--   is
--   $$\mathrm{IP}((x_1,\dots,x_d),(y_1,\dots,y_d))=\omega_1^{x_1y_1}\cdots\omega_d^{x_dy_d},\qquad \omega_i=e^{2\pi\iota/p_i}.$$
--   It is a bihomomorphism (Claim 7.24).
--
--   **Formalization Note** $x_i$ and $y_i$ are lifted to $\{0,\dots,q_i-1\}$ and $\{0,\dots,p_i-1\}$; because $p_i\mid q_i$ the value does not depend on the lift. The divisibility is a hypothesis of each statement using $\mathrm{IP}$.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definition 7.11, p.54

import Mathlib

namespace LowErrExt

/-- **Complex inner product on products of cyclic groups.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 7.11, p.54: "For any positive integers d, q1, . . . , qd, and p1, . . . , pd such that each
pi|qi, we define IP : (Zq1 × · · · × Zqd) × (Zp1 × · · · × Zpd) → C× as
IP((x1, . . . , xd), (y1, . . . , yd)) := ω1^{x1y1} · · · ωd^{xdyd}, where each ωi := exp(2πι/pi)".

**Formalization Note.** `xᵢ` and `yᵢ` are lifted to their representatives in `[0, qᵢ)` and
`[0, pᵢ)` (`ZMod.val`) and the exponent is computed in `ℕ`. Since `pᵢ ∣ qᵢ`, the value does not
depend on the chosen lifts (Claim 7.24, p.68); the divisibility is a hypothesis of every statement
using `ipC`. -/
noncomputable def ipC {d : ℕ} (q p : Fin d → ℕ) (x : ∀ i, ZMod (q i)) (y : ∀ i, ZMod (p i)) : ℂ :=
  ∏ i, Complex.exp (2 * Real.pi * Complex.I * (((x i).val * (y i).val : ℕ) : ℂ) / (p i : ℂ))

end LowErrExt


