-- Prove2me | Definitions.Def_LowRankMisspec_RankOne_Divergences
-- name    : LowRankMisspec_RankOne_Divergences
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:15:54.036966+00:00
-- url     : https://prove2.me/theorems/d7d95453-8f9e-4b9d-bba0-12975f260958
-- title:
--   $\chi^2$ divergence (with value $+\infty$) and the bounded loss $f_{R,H}$
-- statement:
--   For laws $p,r$ on a finite set,
--   $$\chi^2(p\|r)=\sum_{x:r[x]>0}\frac{(p[x]-r[x])^2}{r[x]},$$
--   taken to be infinite unless $p$ is supported on the support of $r$. For laws $R,H$ on $[\sigma]^T$ the **bounded loss** is $f_{R,H}(x)=(1-H[x]/R[x])_+$ if $R[x]>0$ and $0$ if $R[x]=0$, where $(z)_+=\max\{z,0\}$.
--
--   **Formalization Note.** `chi2 p r` takes values in `ℝ≥0∞`; it is `⊤` exactly when some `x` has `r x = 0` and `p x ≠ 0`, and otherwise the finite sum above.
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 17 (PDF 18), §A.2 after Eq. (5); p. 32 (PDF 33), Appendix D before Eq. (10)

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws

set_option autoImplicit false

open scoped Classical ENNReal

noncomputable section

namespace LowRankMisspec.RankOne

/-!
# χ² divergence and the bounded loss `f_{R,H}`

Hasrati, Risteski, *Understanding Model Misspecification in Low-Rank Distributions: Tolerant
Testing and Agnostic Learning*, STOC 2027 submission (manuscript sha256 235f2a4f…), §A.2, p. 17
(PDF 18), after Eq. (5); Appendix D, p. 32 (PDF 33), before Eq. (10).

* `chi2 p r = χ²(p ‖ r) = Σ_{x : r[x] > 0} (p[x] − r[x])² / r[x]`, "taken to be infinite unless `p`
  is supported on the support of `r`": a value in `ℝ≥0∞`, equal to `⊤` exactly when some `x` has
  `r[x] = 0` and `p[x] ≠ 0`.
* `tvLoss R H x = f_{R,H}(x) = (1 − H[x]/R[x])₊` if `R[x] > 0`, and `0` if `R[x] = 0`
  (`(z)₊ = max{z, 0}`).
-/

/-- `χ²(p ‖ r) = Σ_{x : r[x] > 0} (p[x] − r[x])² / r[x]`, and `+∞` unless `p` is supported on the
support of `r`. -/
def chi2 {Ω : Type*} [Fintype Ω] (p r : Ω → ℝ) : ℝ≥0∞ :=
  if ∀ x, r x = 0 → p x = 0 then
    ENNReal.ofReal (∑ x, if 0 < r x then (p x - r x) ^ 2 / r x else 0)
  else ⊤

/-- The bounded loss `f_{R,H}(x) = (1 − H[x]/R[x])₊` if `R[x] > 0`, and `0` if `R[x] = 0`. -/
def tvLoss {Ω : Type*} (R H : Ω → ℝ) (x : Ω) : ℝ :=
  if 0 < R x then max (1 - H x / R x) 0 else 0

end LowRankMisspec.RankOne


