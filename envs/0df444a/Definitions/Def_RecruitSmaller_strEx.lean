-- Prove2me | Definitions.Def_RecruitSmaller_strEx
-- name    : RecruitSmaller_strEx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:05.643041+00:00
-- url     : https://prove2.me/theorems/0acb63c0-6100-4084-9d07-0fedabbf8ed9
-- title:
--   Ex-post Gains From Trade of Seller Trade Reduction $\mathrm{STR}(b,s_k)$
-- statement:
--   For $b\in\mathbb R^m$ and $s_k\in\mathbb R^k$, the **ex-post Gains From Trade of Seller Trade Reduction** is
--   $$
--   \mathrm{STR}(b,s_k) := \sum_{i=1}^{t(b,s_k)} \bigl(b^{(i)}-s^{(i)}_k\bigr),
--   $$
--   where $t(b,s_k)$ is the number of traded pairs.
--
--   **Formalization Note** Defined from $t$ exactly as in Definition 2.4, not from the rank-wise indicator sum of Lemma 3.2.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.4, p.11

import Mathlib
import Definitions.Def_RecruitSmaller_buyerOrd
import Definitions.Def_RecruitSmaller_sellerOrd
import Definitions.Def_RecruitSmaller_numTraded

namespace RecruitSmaller

/-- The **ex-post Gains From Trade of Seller Trade Reduction** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.4,
p.11): `STR(b, sₖ) := ∑_{i=1}^{t(b, sₖ)} (b⁽ⁱ⁾ − s⁽ⁱ⁾ₖ)`, the top `t(b, sₖ)` pairs trading.

**Formalization Note** Defined from `t` (Definition 2.4) exactly as printed, not from the rank-wise
indicator sum of Lemma 3.2. Prices do not enter the Gains From Trade and are not modelled. -/
noncomputable def strEx {m k : ℕ} (b : Fin m → ℝ) (s : Fin k → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (numTraded b s), (buyerOrd b i - sellerOrd s i)

end RecruitSmaller


