-- Prove2me | Definitions.Def_RecruitSmaller_sellerOrd
-- name    : RecruitSmaller_sellerOrd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:08:58.020227+00:00
-- url     : https://prove2.me/theorems/f8810084-3384-4175-a222-563e5060d006
-- title:
--   Seller order statistics $s^{(1)}_k\le\cdots\le s^{(k)}_k$
-- statement:
--   Given a seller cost profile $s_k=(s_1,\dots,s_k)\in\mathbb R^k$, the **seller order statistics** sort the costs in non-decreasing order,
--   $$
--   s^{(1)}_k\le s^{(2)}_k\le\cdots\le s^{(k)}_k ,
--   $$
--   so $s^{(i)}_k$ is the $i$-th smallest cost. The subscript $k$ records the number of sellers, which distinguishes the market before ($k=n$) and after ($k=n+2$) recruitment.
--
--   **Formalization Note** Ranks are natural numbers $i\in\{1,\dots,k\}$; $s^{(i)}_k$ is the entry at ascending position $i-1$ of `Tuple.sort`. Outside $1\le i\le k$ the value is a junk $0$; the sentinel $s^{(k+1)}_k=+\infty$ is the separate definition `sellerOrdExt`.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.1, p.10

import Mathlib

namespace RecruitSmaller

/-- The **seller order statistics** `s⁽¹⁾ₖ ≤ s⁽²⁾ₖ ≤ ⋯ ≤ s⁽ᵏ⁾ₖ` (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a),
Definition 2.1, p.10): `sellerOrd s i` is the `i`-th smallest entry of the cost profile `s ∈ ℝᵏ`.

**Formalization Note** Ranks are 1-based natural numbers `i ∈ {1, …, k}`; `Tuple.sort s` sorts
ascending, so `s⁽ⁱ⁾ₖ` is the entry at position `i − 1`. Outside `1 ≤ i ≤ k` the value is the junk
`0`; the sentinel `s⁽ᵏ⁺¹⁾ₖ = +∞` is the separate definition `sellerOrdExt`. -/
noncomputable def sellerOrd {k : ℕ} (s : Fin k → ℝ) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ k then s (Tuple.sort s ⟨i - 1, by omega⟩) else 0

end RecruitSmaller


