-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:51:39.818047+00:00
-- url     : https://prove2.me/theorems/eb6d7dd1-7312-4beb-ae74-baacbc9c9840
-- title:
--   Statements Adapted Reduction
-- statement:
--   Definitions and structural lemmas for Statements Adapted Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsAdaptedReduction.lean

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
section Reduction
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
def AdaptedReduction.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ v₀ w₀ : W, IsHyperbolicPair h v₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h v₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) → ∀ D : ℕ,
    ∃ KK : Set (AddSubgroup E × AddSubgroup E), KK.Finite ∧ ∃ n D' : ℕ, 0 < n ∧
      ∀ (La : AddSubgroup W) (l : Submodule E W), IsDIntegral h D La → IsIsotropicLine h l →
        ∃ (g : h.unitaryGroup) (La₁ : AddSubgroup W), g • La₁ = La ∧ g • v₀ ∈ l ∧
          (lineCoeffs (E := E) La₁ v₀, lineCoeffs (E := E) La₁ w₀) ∈ KK ∧
          (∀ x ∈ La₁, ∃ a ∈ lineCoeffs (E := E) La₁ v₀, ∃ b ∈ lineCoeffs (E := E) La₁ w₀,
            n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀) ∧
          IsDIntegral h' D' (La₁.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom)
end Reduction
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


