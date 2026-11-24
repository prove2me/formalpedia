-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTer
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:07.361879+00:00
-- url     : https://prove2.me/theorems/9172db31-21cd-4b5b-a43e-81924e24acf9
-- title:
--   Imports Bis Ter
-- statement:
--   Definitions and structural lemmas for Imports Bis Ter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsBisTer.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
def dividedDifferenceExpansion.Statement : Prop :=
  ∀ (r m : ℕ) (G : MvPolynomial (Fin r) ℤ), G.IsHomogeneous m →
    IsPairExpansion m G
      (fun l => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G))
end GroundTheory.Heights₂.Heights.NumbersDVR


