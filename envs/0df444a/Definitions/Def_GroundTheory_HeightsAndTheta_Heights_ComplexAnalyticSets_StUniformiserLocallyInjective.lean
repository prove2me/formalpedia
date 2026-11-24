-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUniformiserLocallyInjective
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUniformiserLocallyInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:07.266138+00:00
-- url     : https://prove2.me/theorems/05bd2474-9614-42ac-945e-a8b320327dcd
-- title:
--   St Uniformiser Locally Injective
-- statement:
--   Definitions and structural lemmas for St Uniformiser Locally Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StUniformiserLocallyInjective.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUniformiserBranchSimpleZero
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
open MvPolynomial Topology
noncomputable section
def UniformiserLocallyInjective.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) →
      ∃ U ∈ 𝓝 w, Set.InjOn (fun z : σ → ℂ ↦ eval z t) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I ∩ U)
end
end GroundTheory.Heights₂.Heights


