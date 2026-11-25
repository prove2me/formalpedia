-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:49:56.234046+00:00
-- url     : https://prove2.me/theorems/a785257c-7833-44e8-ac29-9e092bfa492e
-- title:
--   Statements Hyperbolic Pairs
-- statement:
--   Definitions and structural lemmas for Statements Hyperbolic Pairs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsHyperbolicPairs.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
section Transitive
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
def HyperbolicPairTransitive.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ v w v' w' : W, IsHyperbolicPair h v w → IsHyperbolicPair h v' w' →
    ∃ g : h.unitaryGroup, g • v = v' ∧ g • w = w'
end Transitive
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


