-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:57.450904+00:00
-- url     : https://prove2.me/theorems/d13012e8-0548-48b1-870e-e8096496fac9
-- title:
--   St Frame Graph Generic
-- statement:
--   Definitions and structural lemmas for St Frame Graph Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StFrameGraphGeneric.lean

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
noncomputable section
open MvPolynomial
def FrameGraphGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∃ (I₀ : Finset (Fin n)) (q : MvPolynomial (Fin n) ℂ), I₀.card = d ∧ q ∉ J ∧
        ∀ z ∈ zeroSetEuc J, eval (fun i => z i) q ≠ 0 →
          ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
            (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
              DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧
              zeroSetEuc J ∩ V = g '' Ω
end
end GroundTheory.Heights₂.Heights


