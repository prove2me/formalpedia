-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIrreducible
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIrreducible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:00.369829+00:00
-- url     : https://prove2.me/theorems/03335ee2-68f0-4104-8d11-4d74d416baa2
-- title:
--   St Normal Germ Irreducible
-- statement:
--   Definitions and structural lemmas for St Normal Germ Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalGermIrreducible.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
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
open MvPolynomial Topology
def NormalGermIrreducible.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I →
      GermIrreducibleAt (zeroSetIn I) w
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


