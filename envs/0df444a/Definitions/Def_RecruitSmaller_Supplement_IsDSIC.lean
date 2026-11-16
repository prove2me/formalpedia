-- Prove2me | Definitions.Def_RecruitSmaller_Supplement_IsDSIC
-- name    : RecruitSmaller_Supplement_IsDSIC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:54:19.42382+00:00
-- url     : https://prove2.me/theorems/30fb20e6-7904-4444-845b-8fbb0434b119
-- title:
--   Dominant-strategy incentive compatibility (DSIC)
-- statement:
--   With quasi-linear utilities, buyer $j$'s expected utility at profile $(b,s)$ is $b_j\,x^B_j(b,s)-p^B_j(b,s)$ and seller $\ell$'s is $p^S_\ell(b,s)-s_\ell\,x^S_\ell(b,s)$. A mechanism is **dominant-strategy incentive compatible** if every agent maximizes its expected utility by reporting truthfully, whatever the others report: for every profile $(b,s)$, every buyer $j$ and every misreport $b_j'\in\mathbb R$,
--   $$
--   b_j\,x^B_j(b_j',b_{-j},s)-p^B_j(b_j',b_{-j},s)\le b_j\,x^B_j(b,s)-p^B_j(b,s),
--   $$
--   and symmetrically for every seller $\ell$ and misreport $s_\ell'\in\mathbb R$,
--   $$
--   p^S_\ell(b,s_\ell',s_{-\ell})-s_\ell\,x^S_\ell(b,s_\ell',s_{-\ell})\le p^S_\ell(b,s)-s_\ell\,x^S_\ell(b,s).
--   $$
--
--   **Formalization Note** The misreport replaces one coordinate of the profile; true values, misreports and others' reports range over all of $\mathbb R$.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), §2.1, p.10 (PDF 12)

import Mathlib
import Definitions.Def_RecruitSmaller_Supplement_Mechanism

namespace RecruitSmaller.Supplement

/-- **Dominant-strategy incentive compatibility** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), §2.1, p.10): with quasi-linear expected
utilities `b_j·xB_j − pB_j` (buyer `j`) and `pS_ℓ − s_ℓ·xS_ℓ` (seller `ℓ`), every agent's expected
utility, evaluated at its true value, is at least as large when it reports truthfully as when it
reports any other value, whatever the other agents report.

**Formalization Note** `b` and `s` are the true value of the deviating agent together with
arbitrary reports of the others; the misreport replaces one coordinate (`Function.update`).
Misreports and the others' reports range over all of `ℝ`. -/
def IsDSIC {m k : ℕ} (M : Mechanism m k) : Prop :=
  (∀ (b : Fin m → ℝ) (s : Fin k → ℝ) (j : Fin m) (b' : ℝ),
      b j * M.xB j (Function.update b j b') s - M.pB j (Function.update b j b') s
        ≤ b j * M.xB j b s - M.pB j b s) ∧
  (∀ (b : Fin m → ℝ) (s : Fin k → ℝ) (l : Fin k) (s' : ℝ),
      M.pS l b (Function.update s l s') - s l * M.xS l b (Function.update s l s')
        ≤ M.pS l b s - s l * M.xS l b s)

end RecruitSmaller.Supplement


