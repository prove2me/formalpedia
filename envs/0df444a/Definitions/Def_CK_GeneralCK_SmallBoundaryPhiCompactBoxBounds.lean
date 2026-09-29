-- Prove2me | Definitions.Def_CK_GeneralCK_SmallBoundaryPhiCompactBoxBounds
-- name    : CK_GeneralCK_SmallBoundaryPhiCompactBoxBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:20:49.129695+00:00
-- url     : https://prove2.me/theorems/0499c820-8338-4a49-84bd-4484fd16ef87
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallBoundaryPhiCompactBoxBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallBoundaryPhiCompactBoxBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallBoundaryPhiCompactBoxBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallBoundaryPhiCompactBoxBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallBoundaryPhiCompactBoxBounds.lean)

import Definitions.Def_CK_GeneralCK_SmallBoundaryPhiCompactBox

-- ===== source module GeneralCK.SmallBoundaryPhiCompactBoxBounds =====
section

namespace GeneralCK.SmallBoundaryPhiCompactBox

open GeneralCK.SmallBoundaryPhiTailBox

set_option maxHeartbeats 2000000

theorem factors_pos {t z b : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/9)
    (hb : 1 ≤ b) (hb' : b ≤ 10000/9999) :
    0 < 1-t ∧ 0 < 1-2*t ∧ 0 < cFactor t z b ∧
      0 < pFactor t z b ∧ 0 < mFactor t z b := by
  have hb0 : 0 ≤ b := by linarith
  have hc : 0 < 1-t := by linarith
  have hprod : t*b*z ≤ (1/10000 : ℝ)*(10000/9999)*(1/9) := by gcongr
  refine ⟨hc,by linarith,?_,?_,?_⟩
  · dsimp [cFactor]
    positivity
  · dsimp [pFactor]
    positivity
  · dsimp [mFactor]
    norm_num at hprod
    linarith

theorem rational_bounds {t z b : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/10000) (hz : 0 ≤ z) (hz' : z ≤ 1/9)
    (hb : 1 ≤ b) (hb' : b ≤ 10000/9999) :
    99/100 ≤ A t z b ∧ A t z b ≤ 6/5 ∧ K t z b ≤ 6/5 ∧
      A t z b-K t z b ≤ t/5 ∧ normalizedDerivative t z b ≤ EL t z b/10 := by
  obtain ⟨hc,hr,hC,hP,hM⟩ := factors_pos ht ht' hz hz' hb hb'
  have hAD : 0 < aDen t z b := by dsimp [aDen]; positivity
  have hKD : 0 < kDen t z b := by dsimp [kDen]; positivity
  have hDD : 0 < differenceDen t z b := by dsimp [differenceDen]; positivity
  have hFD : 0 < derivativeDen t z b := by dsimp [derivativeDen]; positivity
  have hbeta : 0 ≤ b-1 := by linarith
  have hbeta' : b-1 ≤ 1/9999 := by linarith
  have heB : 1+(b-1)=b := by ring
  have hAL := aLower_nonneg ht ht' hz hz' hbeta hbeta'
  have hAU := aUpper_nonneg ht ht' hz hz' hbeta hbeta'
  have hKU := kUpper_nonneg ht ht' hz hz' hbeta hbeta'
  have hDU := differenceUpper_nonneg ht ht' hz hz' hbeta hbeta'
  have hFU := derivativeUpper_nonneg ht ht' hz hz' hbeta hbeta'
  rw [heB] at hAL hAU hKU hDU hFU
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (le_div_iff₀ hAD).2 (by nlinarith only [hAL])
  · exact (div_le_iff₀ hAD).2 (by nlinarith only [hAU])
  · exact (div_le_iff₀ hKD).2 (by nlinarith only [hKU])
  · have he : A t z b-K t z b = t*differenceNum t z b/differenceDen t z b :=
      A_sub_K_identity hP.ne' hM.ne'
    have hbound : differenceNum t z b/differenceDen t z b ≤ 1/5 :=
      (div_le_iff₀ hDD).2 (by nlinarith only [hDU])
    rw [he, mul_div_assoc]
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hbound ht
  · dsimp only [normalizedDerivative, EL]
    rw [div_div]
    apply (div_le_div_iff₀ hFD (by positivity : 0 < (cFactor t z b*(1-2*t))*10)).2
    nlinarith only [hFU]

#print axioms factors_pos
#print axioms rational_bounds

end GeneralCK.SmallBoundaryPhiCompactBox

end


