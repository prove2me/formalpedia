-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUniformiserGradientIndependent
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUniformiserGradientIndependent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:02.487373+00:00
-- url     : https://prove2.me/theorems/b99fa2f3-dc15-47fe-a4a1-9effb089ac8a
-- title:
--   St Uniformiser Gradient Independent
-- statement:
--   Definitions and structural lemmas for St Uniformiser Gradient Independent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StUniformiserGradientIndependent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUniformiserLocallyInjective
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
def UniformiserGradientIndependent.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) →
      ∃ (k : ℕ) (f : Fin k → MvPolynomial σ ℂ), k + 1 = Fintype.card σ ∧ (∀ j, f j ∈ I) ∧
        LinearIndependent ℂ (Fin.cons (fun i ↦ eval w (pderiv i t)) (fun j i ↦ eval w (pderiv i (f j))) :
          Fin (k + 1) → σ → ℂ)
end
end GroundTheory.Heights₂.Heights


