-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:48:20.073175+00:00
-- url     : https://prove2.me/theorems/c2e41fe0-6c3e-475d-a570-1eba08603f41
-- title:
--   Statements Complement Extension
-- statement:
--   Definitions and structural lemmas for Statements Complement Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsComplementExtension.lean

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
section Extension
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
def ComplementExtension.Statement (h : HermitianForm F E W) : Prop :=
  ∀ v w : W, IsHyperbolicPair h v w → ∀ h' : HermitianForm F E (hypComplement h v w),
    (∀ x y, h'.toSesq x y = h.toSesq x y) → ∀ m : h'.unitaryGroup,
    ∃ g : h.unitaryGroup, g • v = v ∧ g • w = w ∧
      ∀ x : hypComplement h v w, g • (x : W) = ((m • x : hypComplement h v w) : W)
end Extension
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


