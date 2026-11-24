-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCodimOneUniformiser
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCodimOneUniformiser
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:39.940365+00:00
-- url     : https://prove2.me/theorems/ec1b2e59-3c8c-4464-9540-877c9fec93c8
-- title:
--   St Normal Codim One Uniformiser
-- statement:
--   Definitions and structural lemmas for St Normal Codim One Uniformiser, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalCodimOneUniformiser.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCodimOneCompleteIntersection
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
def NormalCodimOneUniformiser.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P Q : Ideal (MvPolynomial σ ℂ)) (e : ℕ) (x : MvPolynomial σ ℂ),
    P.IsPrime → Q.IsPrime → P ≤ Q → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ P) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ P) = (e + 1 : ℕ) → ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = (e : ℕ) →
    x ∈ Q → x ∉ P →
      ∃ (g a b t : MvPolynomial σ ℂ) (k : ℕ), g ∈ Q ∧ 0 < k ∧ a ∉ Q ∧ b ∉ Q ∧ t ∉ Q ∧
        b * x - a * g ^ k ∈ P ∧ ∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ P ⊔ Ideal.span {g}
end
end GroundTheory.Heights₂.Heights


