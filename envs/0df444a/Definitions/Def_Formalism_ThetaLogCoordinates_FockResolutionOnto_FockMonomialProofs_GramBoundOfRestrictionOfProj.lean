-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:46:02.469774+00:00
-- url     : https://prove2.me/theorems/fd8f9ad8-5150-4cbd-ac58-47c8eeeae1dd
-- title:
--   Gram Bound Of Restriction Of Proj
-- statement:
--   Definitions and structural lemmas for Gram Bound Of Restriction Of Proj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundOfRestrictionOfProj.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_initPart_add
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_initPart_smul
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
section Gen
variable {p : ℕ} [Fact p.Prime] {σ : Type}
noncomputable def strip (p : ℕ) [Fact p.Prime] (v : σ) (e : ℕ) :
    MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] where
  toFun f := (initPart v e f).divMonomial (Finsupp.single v e)
  map_add' x y := by
    rw [initPart_add]; ext m; simp only [coeff_divMonomial, coeff_add]
  map_smul' a x := by
    rw [initPart_smul]; ext m; simp only [coeff_divMonomial, coeff_smul, RingHom.id_apply]
end Gen
section Last
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]
end Last
end Formalism.InvariantFactorPaths.L4


