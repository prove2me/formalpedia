-- Prove2me | Definitions.Def_ManipPotential_Supplement_alphaIdx
-- name    : ManipPotential_Supplement_alphaIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:00:41.972103+00:00
-- url     : https://prove2.me/theorems/7c3c1ffd-6f20-4484-a113-bdb3aa2a3e2c
-- title:
--   Index $\alpha^s_\ell$
-- statement:
--   For $\ell \in \{2, 3, \dots, m-1\}$ and a scoring vector with $s_1 > s_2$,
--   $$\alpha^s_\ell := \max\{\ell' \in [\ell - 1] : s_{\ell'} > s_{\ell+1}\},$$
--   which is well defined because $s_1 > s_2 \ge s_{\ell+1}$.
--
--   **Formalization Note** The maximum is taken in $\mathbb N$ with value $0$ on the empty set; under $s_1 > s_2$, the only case used (Theorem 4.6), the set contains $1$ and the value is the paper's maximum.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.2, p.15

import Mathlib
import Definitions.Def_ManipPotential_Supplement_scoreAt

namespace ManipPotential.Supplement

open Classical in
/-- `α^s_ℓ := max{ℓ' ∈ [ℓ − 1] : s_{ℓ'} > s_{ℓ+1}}` for `ℓ ∈ {2, …, m − 1}` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.2,
p.15), well defined when `s₁ > s₂`.

**Formalization Note** 1-based through `scoreAt`. The maximum is a `Finset.sup` in `ℕ`, which is
`0` on an empty set; under `s₁ > s₂ ≥ s_{ℓ+1}` (the only case used, Theorem 4.6) the set contains
`1` and the value is the paper's maximum. -/
noncomputable def alphaIdx {m : ℕ} (s : Fin m → ℝ) (ℓ : ℕ) : ℕ :=
  ((Finset.Icc 1 (ℓ - 1)).filter (fun j => scoreAt s (ℓ + 1) < scoreAt s j)).sup id

end ManipPotential.Supplement


