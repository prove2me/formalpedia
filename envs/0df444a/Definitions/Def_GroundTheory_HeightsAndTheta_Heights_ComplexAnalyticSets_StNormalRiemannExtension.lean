-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalRiemannExtension
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalRiemannExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:22.079494+00:00
-- url     : https://prove2.me/theorems/5ffb4a00-809d-43d2-b0b1-45e27508775a
-- title:
--   St Normal Riemann Extension
-- statement:
--   Definitions and structural lemmas for St Normal Riemann Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalRiemannExtension.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicOnSubset
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
open MvPolynomial
def NormalRiemannExtension.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (U : Set (σ → ℂ))
    (f : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → IsOpen U →
    HolomorphicOnSubset f ((zeroSetIn I ∩ U) \ {z | eval z h = 0}) →
    Bornology.IsBounded (f '' ((zeroSetIn I ∩ U) \ {z | eval z h = 0})) →
    ∃ g : (σ → ℂ) → ℂ, HolomorphicOnSubset g (zeroSetIn I ∩ U) ∧
      Set.EqOn g f ((zeroSetIn I ∩ U) \ {z | eval z h = 0})
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


