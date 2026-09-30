-- Prove2me | Definitions.Def_CK_GeneralCK_PsiParentPolynomialBounds37
-- name    : CK_GeneralCK_PsiParentPolynomialBounds37
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:25:22.702911+00:00
-- url     : https://prove2.me/theorems/12d98eb7-d30b-457f-aca1-ed0f8dad439f
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiParentPolynomialBounds37` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiParentPolynomialBounds37` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiParentPolynomialBounds37` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiParentPolynomialBounds37 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiParentPolynomialBounds37.lean)

import Definitions.Def_CK_GeneralCK_PsiParentPolynomialBounds

-- ===== source module GeneralCK.PsiParentPolynomialBounds37 =====
section

/-! A sharper exact polynomial threshold for the opposite-parent
medium-bias entropy-ratio exclusion. -/

namespace GeneralCK.PsiParentPolynomialBounds

theorem log_P64_lt_five_halves37 {x : ℝ} (hx : 37 ≤ x) :
    Real.log (P64 x) < (5 / 2) * Real.log (1 + 2 * x / 7) := by
  have hy : 0 ≤ x - 37 := by linarith
  have he : (1 + 2 * x / 7) ^ 5 - (P64 x) ^ 2 =
      32 * (x - 37) ^ 5 / 16807 +
      26390817 * (x - 37) ^ 4 / 68841472 +
      2059604469 * (x - 37) ^ 3 / 68841472 +
      282639502389 * (x - 37) ^ 2 / 275365888 +
      1775061496323 * (x - 37) / 137682944 +
      235297239857 / 275365888 := by
    unfold P64
    ring
  have hdiff : 0 < (1 + 2 * x / 7) ^ 5 - (P64 x) ^ 2 := by
    rw [he]
    positivity
  have hP : 0 < P64 x := by
    unfold P64
    positivity
  have hh := Real.log_lt_log (pow_pos hP 2)
    (show (P64 x) ^ 2 < (1 + 2 * x / 7) ^ 5 by linarith)
  rw [Real.log_pow, Real.log_pow] at hh
  nlinarith

#print axioms log_P64_lt_five_halves37

end GeneralCK.PsiParentPolynomialBounds

end


