-- Prove2me | Definitions.Def_RecruitSmaller_Supplement_IsWBB
-- name    : RecruitSmaller_Supplement_IsWBB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:55:36.302985+00:00
-- url     : https://prove2.me/theorems/3ace04ba-a135-4ac2-869a-ed7a8c5c99d8
-- title:
--   Weak budget balance (WBB)
-- statement:
--   A mechanism is **weakly budget-balanced** if it never runs a deficit, in expectation over its internal randomness, at any profile:
--   $$
--   \sum_{j=1}^m p^B_j(b,s)\ge\sum_{\ell=1}^k p^S_\ell(b,s)\qquad\text{for all }(b,s)\in\mathbb R^m\times\mathbb R^k.
--   $$
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), §2.1, p.10 (PDF 12)

import Mathlib
import Definitions.Def_RecruitSmaller_Supplement_Mechanism

namespace RecruitSmaller.Supplement

/-- **Weak budget balance** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), §2.1, p.10): the mechanism never runs a deficit in expectation
over its internal randomness at any profile, `∑ⱼ pB_j(b, s) ≥ ∑ₗ pS_ℓ(b, s)` for all
`(b, s) ∈ ℝᵐ × ℝᵏ`. -/
def IsWBB {m k : ℕ} (M : Mechanism m k) : Prop :=
  ∀ (b : Fin m → ℝ) (s : Fin k → ℝ), ∑ l, M.pS l b s ≤ ∑ j, M.pB j b s

end RecruitSmaller.Supplement


