-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8NormalizedCoeff7
-- name    : CK_GeneralCK_Certificates_E8NormalizedCoeff7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:28:17.70998+00:00
-- url     : https://prove2.me/theorems/3f8ce3e1-d24f-442b-851c-23471f81a32a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8NormalizedCoeff7` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8NormalizedCoeff7` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8NormalizedCoeff7` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8NormalizedCoeff7 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8NormalizedCoeff7.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ElementaryCoeff5

-- ===== source module GeneralCK.Certificates.E8NormalizedCoeff7 =====
section

/-! Normalized product identities at the two additional orders needed for q7. -/

namespace GeneralCK.Certificates.E8NormalizedCoeff7

open E8AnalyticGerm E8NormalizedCoeff5

/-- Normalized Taylor coefficients turn analytic products into finite Cauchy
convolutions.  This is the reusable product rule for all higher orders. -/
theorem coeff_mul (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff (f * g) n =
      ∑ i ∈ Finset.range (n + 1), coeff f i * coeff g (n - i) := by
  rw [coeff, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by simpa using Finset.mem_range.mp hi
  rw [coeff, coeff, Nat.cast_choose ℂ hin]
  have hi0 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hni0 : ((n-i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n-i)
  have hn0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hi0, hni0, hn0]

theorem coeff_mul_six (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    coeff (f * g) 6 = coeff f 0 * coeff g 6 + coeff f 1 * coeff g 5 +
      coeff f 2 * coeff g 4 + coeff f 3 * coeff g 3 +
      coeff f 4 * coeff g 2 + coeff f 5 * coeff g 1 + coeff f 6 * coeff g 0 := by
  rw [coeff, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  simp [Finset.sum_range_succ, coeff]
  norm_num [Nat.choose]
  ring

theorem coeff_mul_seven (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    coeff (f * g) 7 = coeff f 0 * coeff g 7 + coeff f 1 * coeff g 6 +
      coeff f 2 * coeff g 5 + coeff f 3 * coeff g 4 +
      coeff f 4 * coeff g 3 + coeff f 5 * coeff g 2 +
      coeff f 6 * coeff g 1 + coeff f 7 * coeff g 0 := by
  rw [coeff, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  simp [Finset.sum_range_succ, coeff]
  norm_num [Nat.choose]
  ring

end GeneralCK.Certificates.E8NormalizedCoeff7

end


