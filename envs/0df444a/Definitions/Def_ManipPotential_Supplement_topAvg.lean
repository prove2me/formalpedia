-- Prove2me | Definitions.Def_ManipPotential_Supplement_topAvg
-- name    : ManipPotential_Supplement_topAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:59:42.18477+00:00
-- url     : https://prove2.me/theorems/4edadef9-6fbc-4244-8b49-23ecee1957b3
-- title:
--   Top-$\ell$ average $\overline s(\ell)$
-- statement:
--   For $\ell \in [m]$, the average score of the top $\ell$ positions is
--   $$\overline{s}(\ell) := \frac{1}{\ell} \sum_{\ell' = 1}^{\ell} s_{\ell'} .$$
--
--   It appears in the bound $U_s(\ell)$ of Theorem 4.6.
--
--   **Formalization Note** At $\ell = 0$ Lean's division by zero gives $0$; the paper and the mission only use $\ell \ge 1$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.2, p.15

import Mathlib
import Definitions.Def_ManipPotential_Supplement_scoreAt

namespace ManipPotential.Supplement

/-- The average score of the top `ℓ` positions, `s̄(ℓ) := (1/ℓ) Σ_{ℓ'=1}^{ℓ} s_{ℓ'}` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…),
Section 4.2, p.15, the overlined `s(ℓ)`).

**Formalization Note** 1-based through `scoreAt`. At `ℓ = 0` Lean's `x / 0 = 0` gives `0`; the
paper defines `s̄(ℓ)` only for `ℓ ∈ [m]`, and the mission only uses `ℓ ≥ 1`. -/
noncomputable def topAvg {m : ℕ} (s : Fin m → ℝ) (ℓ : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 ℓ, scoreAt s j) / ℓ

end ManipPotential.Supplement


