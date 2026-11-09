-- Prove2me | Definitions.Def_RecruitSmaller_sellerOrdExt
-- name    : RecruitSmaller_sellerOrdExt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:45.241075+00:00
-- url     : https://prove2.me/theorems/36480c2a-59c6-4cc3-ab5b-28affe573254
-- title:
--   Seller order statistics with the sentinel $s^{(k+1)}_k=+\infty$
-- statement:
--   The seller order statistics extended by the **sentinel cost**
--   $$
--   s^{(k+1)}_k := +\infty ,
--   $$
--   as values in $\mathbb R\cup\{+\infty\}$: for $1\le i\le k$ this is $s^{(i)}_k$, and for $i=k+1$ it is $+\infty$.
--
--   The sentinel makes the trade-reduction test of Definition 2.4 well defined when every seller is efficient: with $r'=k$ the test $b^{(k)}<s^{(k+1)}_k$ always holds, and the last pair is dropped.
--
--   **Formalization Note** Values in `WithTop ℝ`. The page defines only rank $k+1$; larger ranks also give $+\infty$ and are never used.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.1, p.10

import Mathlib
import Definitions.Def_RecruitSmaller_sellerOrd

namespace RecruitSmaller

/-- The seller order statistics **with the sentinel** `s⁽ᵏ⁺¹⁾ₖ := +∞` (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a),
Definition 2.1, p.10), valued in `WithTop ℝ`: `s⁽ⁱ⁾ₖ` for `i ≤ k` and `+∞` for `i ≥ k + 1`.

**Formalization Note** The page defines only the sentinel at `k + 1`; the value `⊤` for larger ranks
is never used. Rank `0` gives the junk `↑0`. -/
noncomputable def sellerOrdExt {k : ℕ} (s : Fin k → ℝ) (i : ℕ) : WithTop ℝ :=
  if i ≤ k then ((sellerOrd s i : ℝ) : WithTop ℝ) else ⊤

end RecruitSmaller


