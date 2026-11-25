-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerSt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:50:52.612875+00:00
-- url     : https://prove2.me/theorems/d1bf9487-9ff1-4818-b1df-d58273a3198d
-- title:
--   Fun Ker St
-- statement:
--   Definitions and structural lemmas for Fun Ker St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FunKerSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescSt
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
def FunKerStatement : Prop :=
  ∀ (K Ω V : Type) [Field K] [CharZero K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [AddCommGroup V]
    [Module K V] (U : Submodule K V) [FiniteDimensional K U]
    (Wc : Submodule Ω (Ω ⊗[K] V)) (FF : Set (Module.Dual Ω (Ω ⊗[K] V))),
    Wc ≤ baseSpan Ω U →
    (∀ c ∈ FF, ∃ K' : IntermediateField K Ω, FiniteDimensional K K' ∧ DefinedOver c K') →
    (∀ c ∈ FF, Wc ≤ LinearMap.ker c) →
    (∀ x ∈ baseSpan Ω U, x ∉ Wc → ∃ c ∈ FF, c x ≠ 0) →
    (∀ c ∈ FF, ∀ K₂ : IntermediateField K Ω, FiniteDimensional K K₂ → IsGalois K K₂ →
      DefinedOver c K₂ → ∀ σ : K₂ ≃ₐ[K] K₂, ∀ x ∈ descend K₂ Wc,
        c (inclT K₂ V (galAct σ x)) = 0) →
    ∃ W : Submodule K V, W ≤ U ∧ Submodule.span Ω ((fun v => (1 : Ω) ⊗ₜ[K] v) '' (W : Set V)) = Wc ∧
      ∃ K₁ : IntermediateField K Ω, FiniteDimensional K K₁ ∧
        ∃ (ρ : ℕ) (c : Fin ρ → Module.Dual Ω (Ω ⊗[K] V)),
          (∀ i, c i ∈ FF ∧ DefinedOver (c i) K₁) ∧
          (∀ x ∈ baseSpan K₁ U, (∀ i, c i (inclT K₁ V x) = 0) ↔ x ∈ baseSpan K₁ W) ∧
          Module.finrank K W + ρ = Module.finrank K U
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


