-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchPlace
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:48.251015+00:00
-- url     : https://prove2.me/theorems/1e4a62fd-bd48-44e6-b6bf-ef761329a3d8
-- title:
--   St Branch Place
-- statement:
--   Definitions and structural lemmas for St Branch Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchPlace.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Filter Topology
noncomputable section
def BranchPlace.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch I 1 q),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∃ P : MaximalSpectrum (curveNormalisation I q), ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) = branchOrder c f
end
end GroundTheory.Heights₂.Heights


