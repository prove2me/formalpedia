-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:40:57.292078+00:00
-- url     : https://prove2.me/theorems/e2989402-ba7a-45c8-b28f-177cbaf8902c
-- title:
--   St Rational Unipotent
-- statement:
--   Definitions and structural lemmas for St Rational Unipotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StRationalUnipotent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
def RationalUnipotent.Statement (h : HermitianForm F E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ w₀ : W), IsDIntegral h D La → x₀ ∈ La →
    IsHyperbolicPair h x₀ w₀ →
    ∃ m : ℕ, 0 < m ∧ ∀ (y : W) (c : E), y ∈ hypComplement h x₀ w₀ → (∃ z ∈ La, y = m • z) →
      (∃ a : 𝓞 E, c = (m : E) * a) → c + conj F E c = -h.toSesq y y →
      ∃ γ ∈ latticeStab h La, γ • x₀ = x₀ ∧ γ • w₀ = w₀ + y + c • x₀ ∧
        ∀ z ∈ hypComplement h x₀ w₀, γ • z = z - h.toSesq y z • x₀
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


