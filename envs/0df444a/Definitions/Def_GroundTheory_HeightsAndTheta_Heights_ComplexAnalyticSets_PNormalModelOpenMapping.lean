-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelOpenMapping
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelOpenMapping
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:05:21.935494+00:00
-- url     : https://prove2.me/theorems/41ee6bcd-6fb3-5841-9ff2-32ac6692b2e4
-- title:
--   PNormal Model Open Mapping
-- statement:
--   Definitions and structural lemmas for PNormal Model Open Mapping, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelOpenMapping.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelOpenMapping
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericProjectionFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscriminantCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Matrix
noncomputable section
theorem NormalModel.le_comap {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : NormalModel J) :
    J ≤ M.ideal.comap
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom :=
  fun q hq => by rw [← M.comap_eq] at hq; exact hq
def NormalModel.quotMap {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : NormalModel J) :
    MvPolynomial (Fin n) ℂ ⧸ J →+* MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal :=
  Ideal.quotientMap M.ideal
    (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom
    M.le_comap
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


