-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:19.662161+00:00
-- url     : https://prove2.me/theorems/40eb33dc-d96c-40b1-9b8b-aad75fd3c0d4
-- title:
--   Init Part Zero XMul
-- statement:
--   Definitions and structural lemmas for Init Part Zero XMul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/InitPartZeroXMul.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_ShiftLastLetterThresholds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply


set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
noncomputable def resL (p : ℕ) [Fact p.Prime] (v : σ) (e : ℕ) :
    MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] where
  toFun := initPart v e
  map_add' x y := by
    ext m; simp only [coeff_initPart, coeff_add]; split_ifs <;> simp
  map_smul' a x := by
    ext m
    simp only [coeff_initPart, RingHom.id_apply, coeff_smul]
    split_ifs <;> simp
end Formalism.InvariantFactorPaths.L4


