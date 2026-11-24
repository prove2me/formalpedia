-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFramePlaneGraph
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFramePlaneGraph
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:05.187566+00:00
-- url     : https://prove2.me/theorems/e2ed47d4-a3c7-4a13-b98b-9124c4fa2710
-- title:
--   St Frame Plane Graph
-- statement:
--   Definitions and structural lemmas for St Frame Plane Graph, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StFramePlaneGraph.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
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
open MeasureTheory
noncomputable section
def FramePlaneGraph.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∃ (I₀ : Finset (Fin n)) (J' : Ideal (MvPolynomial (Fin n) ℂ)), I₀.card = d ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') < d ∧
        ∀ z ∈ zeroSetEuc J \ zeroSetEuc J', ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
          (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
            DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧
            (zeroSetEuc J \ zeroSetEuc J') ∩ V = g '' Ω
end
end GroundTheory.Heights₂.Heights


