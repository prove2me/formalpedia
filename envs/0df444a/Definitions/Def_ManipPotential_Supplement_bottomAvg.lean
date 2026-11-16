-- Prove2me | Definitions.Def_ManipPotential_Supplement_bottomAvg
-- name    : ManipPotential_Supplement_bottomAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:00:13.514747+00:00
-- url     : https://prove2.me/theorems/53d810a4-0949-4afc-a7d7-e062950a3525
-- title:
--   Bottom-$\ell$ average $\underline s(\ell)$
-- statement:
--   For $\ell \in [m]$, the average score of the bottom $\ell$ positions is
--   $$\underline{s}(\ell) := \frac{1}{\ell} \sum_{\ell' = m-\ell+1}^{m} s_{\ell'} .$$
--
--   It appears in the bound $U_s(\ell)$ of Theorem 4.6.
--
--   **Formalization Note** At $\ell = 0$ Lean's division by zero gives $0$; never used.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.2, p.15

import Mathlib
import Definitions.Def_ManipPotential_Supplement_scoreAt

namespace ManipPotential.Supplement

/-- The average score of the bottom `ℓ` positions, `s̲(ℓ) := (1/ℓ) Σ_{ℓ'=m−ℓ+1}^{m} s_{ℓ'}`
(Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.2, p.15, the underlined `s(ℓ)`).

**Formalization Note** 1-based through `scoreAt`; defined for `ℓ ∈ [m]` as in the paper (at `ℓ = 0`
Lean's `x / 0 = 0` gives `0`, never used). -/
noncomputable def bottomAvg {m : ℕ} (s : Fin m → ℝ) (ℓ : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc (m - ℓ + 1) m, scoreAt s j) / ℓ

end ManipPotential.Supplement


