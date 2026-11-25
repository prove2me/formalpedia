-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescSt
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:44:06.457426+00:00
-- url     : https://prove2.me/theorems/040df1c0-b777-417b-aee3-32d623ca7f58
-- title:
--   Desc St
-- statement:
--   Definitions and structural lemmas for Desc St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DescSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
section Defs
variable {K K₂ : Type*} [Field K] [Field K₂] [Algebra K K₂] {V : Type*} [AddCommGroup V]
  [Module K V]
noncomputable def galAct (σ : K₂ ≃ₐ[K] K₂) : K₂ ⊗[K] V →ₗ[K] K₂ ⊗[K] V :=
  LinearMap.rTensor V σ.toLinearMap
def kPoints (W : Submodule K₂ (K₂ ⊗[K] V)) : Submodule K V :=
  (W.restrictScalars K).comap (TensorProduct.mk K K₂ V 1)
end Defs
def GaloisDescentStatement : Prop :=
  ∀ (K K₂ V : Type) [Field K] [Field K₂] [Algebra K K₂] [FiniteDimensional K K₂] [IsGalois K K₂]
    [AddCommGroup V] [Module K V] (W : Submodule K₂ (K₂ ⊗[K] V)),
    (∀ σ : K₂ ≃ₐ[K] K₂, ∀ x ∈ W, galAct σ x ∈ W) →
    W = baseSpan K₂ (kPoints W)
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


