-- Prove2me | Definitions.Def_RecruitSmaller_buyerOrd
-- name    : RecruitSmaller_buyerOrd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:02.049238+00:00
-- url     : https://prove2.me/theorems/ab772cea-d419-4ab5-a7ad-52e972d17ee2
-- title:
--   Buyer order statistics $b^{(1)}\ge\cdots\ge b^{(m)}$
-- statement:
--   Given a buyer valuation profile $b=(b_1,\dots,b_m)\in\mathbb R^m$, the **buyer order statistics** sort the values in non-increasing order,
--   $$
--   b^{(1)}\ge b^{(2)}\ge\cdots\ge b^{(m)} ,
--   $$
--   so $b^{(i)}$ is the $i$-th largest value.
--
--   These are the buyers that the efficient allocation and Seller Trade Reduction match with the cheapest sellers, rank by rank.
--
--   **Formalization Note** Ranks are natural numbers $i\in\{1,\dots,m\}$ (1-based, as on the page). Mathlib's `Tuple.sort` sorts ascending, so $b^{(i)}$ is the entry at ascending position $m-i$. Outside $1\le i\le m$ the value is a junk $0$, never used.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.1, p.10

import Mathlib

namespace RecruitSmaller

/-- The **buyer order statistics** `b⁽¹⁾ ≥ b⁽²⁾ ≥ ⋯ ≥ b⁽ᵐ⁾` (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a),
Definition 2.1, p.10): `buyerOrd b i` is the `i`-th largest entry of the profile `b ∈ ℝᵐ`.

**Formalization Note** Ranks are 1-based natural numbers `i ∈ {1, …, m}`. `Tuple.sort b` sorts
ascending, so `b⁽ⁱ⁾` is the entry at ascending position `m − i`. Outside `1 ≤ i ≤ m` the value is
the junk `0`; every statement of the mission uses ranks inside that range. -/
noncomputable def buyerOrd {m : ℕ} (b : Fin m → ℝ) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ m then b (Tuple.sort b ⟨m - i, by omega⟩) else 0

end RecruitSmaller


