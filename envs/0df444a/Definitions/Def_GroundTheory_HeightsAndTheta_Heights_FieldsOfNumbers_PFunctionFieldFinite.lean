-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFunctionFieldFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFunctionFieldFinite
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:35:53.072781+00:00
-- url     : https://prove2.me/theorems/d4ba8f91-88b7-443d-8886-e07f7c47d651
-- title:
--   PFunction Field Finite
-- statement:
--   Definitions and structural lemmas for PFunction Field Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PFunctionFieldFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFunctionFieldFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace FunctionFieldFinite
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
def chartGens (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    Set (FractionRing (MRing ι F ⧸ P)) :=
  Set.range fun v => algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X v)) /
    algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩))
end FunctionFieldFinite
end
end GroundTheory.Heights₂.Heights.FieldNumbers


