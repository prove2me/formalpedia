-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUniformiserBranchSimpleZero
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUniformiserBranchSimpleZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:22.169804+00:00
-- url     : https://prove2.me/theorems/14827d04-609b-4e0a-8550-ac4a24a35acb
-- title:
--   St Uniformiser Branch Simple Zero
-- statement:
--   Definitions and structural lemmas for St Uniformiser Branch Simple Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StUniformiserBranchSimpleZero.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurvePointDVR
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
open MvPolynomial
noncomputable section
def UniformiserBranchSimpleZero.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ)
    (r : ℝ) (φ : (Fin 1 → ℂ) → σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) → 0 < r →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) → φ 0 = w →
      analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 = 1
def UniformiserBranchSimpleZero.lineDisc : (Fin 1 → ℂ) → Fin 1 → ℂ :=
  fun t _ ↦ t 0
end
end GroundTheory.Heights₂.Heights


