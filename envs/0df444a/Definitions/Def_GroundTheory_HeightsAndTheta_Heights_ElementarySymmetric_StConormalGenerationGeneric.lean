-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StConormalGenerationGeneric
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StConormalGenerationGeneric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:38.008132+00:00
-- url     : https://prove2.me/theorems/c64793a7-1f57-4db0-82b9-886b64a3ac53
-- title:
--   St Conormal Generation Generic
-- statement:
--   Definitions and structural lemmas for St Conormal Generation Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StConormalGenerationGeneric.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StJacobianRankGeneric
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
def ConormalGenerationGeneric.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] (ι : Type) [Fintype ι]
    (f : ι → MvPolynomial (Fin n) ℂ),
    (∀ i, f i ∈ J) →
    Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) (Set.range (genericGradient J ∘ f)) =
      Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) (genericGradient J '' (J : Set _)) →
    ∃ s : MvPolynomial (Fin n) ℂ, s ∉ J ∧ ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)
end
end GroundTheory.Heights₂.Heights


