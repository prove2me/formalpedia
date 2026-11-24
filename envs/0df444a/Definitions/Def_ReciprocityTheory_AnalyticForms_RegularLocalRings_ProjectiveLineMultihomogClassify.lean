-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjectiveLineMultihomogClassify
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjectiveLineMultihomogClassify
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:58.768819+00:00
-- url     : https://prove2.me/theorems/4d412ae1-4c72-4dbf-8f53-33eb1a347e50
-- title:
--   Projective Line Multihomog Classify
-- statement:
--   Definitions and structural lemmas for Projective Line Multihomog Classify, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjectiveLineMultihomogClassify.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial OnePoint Filter Topology
noncomputable section
def projectiveLineInvPoint (w : ℂ) : OnePoint ℂ := if w = 0 then ∞ else ((w⁻¹ : ℂ) : OnePoint ℂ)
def locRingBotEquivN {n : ℕ} (p : Fin n → ℂ) :
    locPt p ≃+* locRing (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) p :=
  (RingEquiv.quotientBot (locPt p)).symm.trans (Ideal.quotEquivOfEq Ideal.map_bot.symm)
end
end ReciprocityTheory.AnForm.R


