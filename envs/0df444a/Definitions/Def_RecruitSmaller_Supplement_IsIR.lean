-- Prove2me | Definitions.Def_RecruitSmaller_Supplement_IsIR
-- name    : RecruitSmaller_Supplement_IsIR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:54:51.34401+00:00
-- url     : https://prove2.me/theorems/107adec4-1e6f-4fb7-b24e-902f854337b5
-- title:
--   Individual rationality (IR)
-- statement:
--   A mechanism is **individually rational** if every agent obtains non-negative expected utility when reporting truthfully, no matter what the other agents report: for every profile $(b,s)\in\mathbb R^m\times\mathbb R^k$,
--   $$
--   b_j\,x^B_j(b,s)-p^B_j(b,s)\ge0\quad\text{for every buyer }j,\qquad p^S_\ell(b,s)-s_\ell\,x^S_\ell(b,s)\ge0\quad\text{for every seller }\ell.
--   $$
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), §2.1, p.10 (PDF 12)

import Mathlib
import Definitions.Def_RecruitSmaller_Supplement_Mechanism

namespace RecruitSmaller.Supplement

/-- **Individual rationality** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), §2.1, p.10): every agent obtains non-negative expected
utility when reporting truthfully, no matter what the other agents report: `b_j·xB_j(b, s) −
pB_j(b, s) ≥ 0` and `pS_ℓ(b, s) − s_ℓ·xS_ℓ(b, s) ≥ 0` at every profile `(b, s) ∈ ℝᵐ × ℝᵏ`. -/
def IsIR {m k : ℕ} (M : Mechanism m k) : Prop :=
  (∀ (b : Fin m → ℝ) (s : Fin k → ℝ) (j : Fin m), 0 ≤ b j * M.xB j b s - M.pB j b s) ∧
  (∀ (b : Fin m → ℝ) (s : Fin k → ℝ) (l : Fin k), 0 ≤ M.pS l b s - s l * M.xS l b s)

end RecruitSmaller.Supplement


