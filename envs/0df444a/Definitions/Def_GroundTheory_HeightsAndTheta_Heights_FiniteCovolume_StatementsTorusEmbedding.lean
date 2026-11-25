-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusEmbedding
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusEmbedding
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:40:22.943035+00:00
-- url     : https://prove2.me/theorems/47723c41-3e06-54d8-9be3-c9ca5aed7cb1
-- title:
--   Statements Torus Embedding
-- statement:
--   Definitions and structural lemmas for Statements Torus Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsTorusEmbedding.lean

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
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def TorusEmbedding.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ →
    ∃ τ : (InfinitePlace E → ℂˣ) →* archUnitary h v, Continuous τ ∧ ∀ a w,
      ((τ a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
          (a w : ℂ) • vecAt v x₀ w ∧
        ((τ a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w =
          (starRingEnd ℂ (a w : ℂ))⁻¹ • vecAt v w₀ w ∧
        ∀ z : ι → ℂ, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
          star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
          ((τ a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


