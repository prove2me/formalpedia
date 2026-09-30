-- Prove2me | Definitions.Def_CK_GeneralCK_PsiOuterEntropy37
-- name    : CK_GeneralCK_PsiOuterEntropy37
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:33:28.687977+00:00
-- url     : https://prove2.me/theorems/8797b8ca-5200-482b-a0b4-0d2edce7553d
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiOuterEntropy37` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiOuterEntropy37` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiOuterEntropy37` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiOuterEntropy37 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiOuterEntropy37.lean)

import Definitions.Def_CK_GeneralCK_PsiOuterEntropy200
import Definitions.Def_CK_GeneralCK_PsiParentPolynomialBounds37

-- ===== source module GeneralCK.PsiOuterEntropy37 =====
section

/-! Exact medium-bias parent exclusion at entropy ratio 37. -/

namespace GeneralCK.PsiOuterEntropy37

open GeneralCK.PsiOuterEntropy200

theorem parent_dominance_two_fifths37 {q E : ℝ}
    (hq : 0 < q) (hqu : q ≤ 2 / 5) (hE : 0 < E)
    (hr : 37 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let x := q / E
  have hx : 37 ≤ x := (le_div_iff₀ hE).mpr hr
  have hF := (le_div_iff₀ log_two_pos).mp
    (PsiParentContactEnvelope.F_le_logarithmic_polynomial64 hq hE (by linarith))
  have hp := mul_lt_mul_of_pos_left
    (PsiParentPolynomialBounds.log_P64_lt_five_halves37 hx) hq
  have hs := logarithmic_bias_scale (Q := (2 / 5 : ℝ)) hq.le
    (by norm_num) hqu (show 0 ≤ x by linarith)
  have hs' : (5 / 2) * q * Real.log (1 + 2 * x / 7) ≤
      Real.log (1 + 5 * q ^ 2 / (7 * E)) := by
    convert! hs using 1 <;> dsimp [x] <;> congr 1 <;> ring
  change q * Real.log (1 + (1347 / 128) * x + (3 / 64) * x ^ 2) <
    q * ((5 / 2) * Real.log (1 + 2 * x / 7)) at hp
  apply parent_dominance_of_cost_bound hq (by linarith) hE (by linarith)
  change F q E * Real.log 2 ≤
      q * Real.log (1 + (1347 / 128) * x + (3 / 64) * x ^ 2) at hF
  nlinarith only [hF, hp, hs', sq_nonneg q]

#print axioms parent_dominance_two_fifths37

end GeneralCK.PsiOuterEntropy37

end


