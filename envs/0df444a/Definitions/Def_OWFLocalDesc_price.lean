-- Prove2me | Definitions.Def_OWFLocalDesc_price
-- name    : OWFLocalDesc_price
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:02.968194+00:00
-- url     : https://prove2.me/theorems/e5cb00be-f9c9-44c9-9241-d56dfbd8cb36
-- title:
--   Charged length (price) of a certificate (Definition 2.5)
-- statement:
--   The **charged length**, or **price**, of a certificate $(A,a,\beta)$ with $k=|A|$ is
--   $$\lambda_m(k)+k+|\beta|,\qquad \lambda_m(k)=\lceil\log(m+1)\rceil+\Big\lceil\log\binom{m}{k}\Big\rceil ,$$
--   with logarithms to base $2$. The two terms of $\lambda_m(k)$ pay for the size and the rank of the retained set, $k$ pays for the tags and $|\beta|$ for the program.
--
--   **Formalization Note** $\lceil\log_2 N\rceil$ is `Nat.clog 2 N`; in particular $\lceil\log\binom m0\rceil=0$ and $\lceil\log(m+1)\rceil\ge1$ for $m\ge1$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.5, p.13

import Mathlib
import Definitions.Def_OWFLocalDesc_Certificate
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Charged length (price) of a certificate (Definition 2.5).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
Definition 2.5, p.13: "The certificate's charged length, also called its price, is
λ_m(k) + k + |β|, λ_m(k) = ⌈log(m+1)⌉ + ⌈log (m choose k)⌉, k = |A|."

**Formalization Note.** `Nat.clog 2 N` is `⌈log₂ N⌉` for `N ≥ 1` (and `Nat.clog 2 1 = 0`). -/
def price {m : ℕ} (c : Certificate m) : ℕ :=
  Nat.clog 2 (m + 1) + Nat.clog 2 (m.choose c.A.card) + c.A.card + c.prog.length

end OWFLocalDesc


