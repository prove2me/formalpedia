-- Prove2me | Definitions.Def_AgnHalfMem_AppBConstants
-- name    : AgnHalfMem_AppBConstants
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:46.520955+00:00
-- url     : https://prove2.me/theorems/47d9e863-9fd8-4e06-8a3c-e44181ba1919
-- title:
--   The parameters $c,\gamma$ and $k,\ell,r$ of Appendix B
-- statement:
--   Fix $c,\gamma$ with $\tfrac1{100}<c<\tfrac23$, $\gamma>0$ and $\tfrac{3c}{2}<\gamma^2<1$. For extractor parameters $k',\ell',r'$, Appendix B uses
--   $$
--   k=\gamma k',\qquad \ell=\frac{\gamma\ell'}{3},\qquad r=\min\Big\{\frac{r'}2,\ \frac{(1-\gamma)k'}2,\ \frac{(1-\gamma)\ell'}2-1\Big\}.
--   $$
--   These are the thresholds of the truncated path and the exponents of all bounds in the proof of Theorem 2.2.
--
--   **Formalization Note** $\gamma$ is taken positive, since it scales exponents. The printed "$k:=\gamma k$" is a typo for $k=\gamma k'$ (p.37: "Recall that $k=\gamma k'$"). Theorem 2.2 itself states a slightly larger $r$ (p.8), written in that statement.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Theorem 2.2, p.7; App. B, p.29

import Mathlib

namespace AgnHalfMem

/-- **The constants of Theorem 2.2 and Appendix B.** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs
for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), Theorem 2.2, p.7: "Let 1/100 < c < 2/3. Fix γ to be such that 3c/2 < γ² < 1."
App. B, p.29: "Let n = log₂ |H|. Recall 1/100 < c < 2/3, and γ is such that 3c/2 < γ² < 1. M is a
(k′, ℓ′)-L2-Extractor with error 2^{−r′} and distribution μ, for sufficiently large k′, ℓ′ and r′.
Let k := γk and ℓ := γℓ′/3. Recall, r := min{r′/2, (1−γ)k′/2, (1−γ)ℓ′/2 − 1}."

`AppBConstants c γ` is `1/100 < c < 2/3`, `γ > 0` and `3c/2 < γ² < 1`.

**Formalization Note.** `γ` is taken positive: it scales the exponents `k = γk′` and
`ℓ = γℓ′/3`. The printed "k := γk" is a typo for `k = γk′` (p.37: "Recall that k = γk′"). -/
def AppBConstants (c γ : ℝ) : Prop :=
  1 / 100 < c ∧ c < 2 / 3 ∧ 0 < γ ∧ 3 * c / 2 < γ ^ 2 ∧ γ ^ 2 < 1

/-- `k = γ k′` (App. B, pp.29, 37). -/
def appBk (γ k' : ℝ) : ℝ := γ * k'

/-- `ℓ = γ ℓ′ / 3` (App. B, p.29). -/
noncomputable def appBl (γ l' : ℝ) : ℝ := γ * l' / 3

/-- `r = min{r′/2, (1−γ)k′/2, (1−γ)ℓ′/2 − 1}` (App. B, p.29). -/
noncomputable def appBr (γ k' l' r' : ℝ) : ℝ :=
  min (r' / 2) (min ((1 - γ) * k' / 2) ((1 - γ) * l' / 2 - 1))

end AgnHalfMem


