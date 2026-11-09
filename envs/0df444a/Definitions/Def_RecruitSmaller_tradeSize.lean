-- Prove2me | Definitions.Def_RecruitSmaller_tradeSize
-- name    : RecruitSmaller_tradeSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:58.814463+00:00
-- url     : https://prove2.me/theorems/4fa390c2-3383-4524-bc7c-78fa24bd67bd
-- title:
--   Efficient trade size $r(b,s_k)$
-- statement:
--   For a buyer profile $b\in\mathbb R^m$ and a seller profile $s_k\in\mathbb R^k$, the **efficient trade size** is
--   $$
--   r(b,s_k) := \max\Bigl(\{0\}\cup\bigl\{\, i\in\{1,\dots,\min(m,k)\} : b^{(i)}\ge s^{(i)}_k \,\bigr\}\Bigr),
--   $$
--   the largest rank at which the $i$-th highest buyer value still weakly exceeds the $i$-th lowest seller cost.
--
--   It is the number of trades of the first-best (efficient) allocation, and the starting point of Seller Trade Reduction.
--
--   **Formalization Note** The maximum is `Finset.sup id` over the filtered rank set, which is $0$ on the empty set.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.3, p.11

import Mathlib
import Definitions.Def_RecruitSmaller_buyerOrd
import Definitions.Def_RecruitSmaller_sellerOrd

namespace RecruitSmaller

/-- The **efficient trade size** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.3, p.11):
`r(b, sₖ) := max({0} ∪ {i ∈ {1, …, min(m, k)} : b⁽ⁱ⁾ ≥ s⁽ⁱ⁾ₖ})`.

**Formalization Note** The maximum is `Finset.sup id` over the filtered rank set, which is `0` when
the set is empty, i.e. exactly the page's `max` with `0` adjoined. -/
noncomputable def tradeSize {m k : ℕ} (b : Fin m → ℝ) (s : Fin k → ℝ) : ℕ :=
  ((Finset.Icc 1 (min m k)).filter (fun i => sellerOrd s i ≤ buyerOrd b i)).sup id

end RecruitSmaller


