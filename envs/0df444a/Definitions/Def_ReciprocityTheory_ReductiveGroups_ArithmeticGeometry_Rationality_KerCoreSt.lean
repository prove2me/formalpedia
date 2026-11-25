-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_KerCoreSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_KerCoreSt
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:11:21.43006+00:00
-- url     : https://prove2.me/theorems/fce57edc-2c8f-4b27-959d-18c4b78f062c
-- title:
--   Ker Core St
-- statement:
--   Definitions and structural lemmas for Ker Core St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/KerCoreSt.lean

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
def KerCoreStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V)
    (Fam : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁], (V →ₗ[K] K₁) → Prop),
    (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (f : V →ₗ[K] K₁), Fam K₁ f →
      W ≤ LinearMap.ker f) →
    (∀ v : V, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (f : V →ₗ[K] K₁),
      Fam K₁ f → f v = 0) → v ∈ W) →
    (∀ (K' K₁ : Type) [Field K'] [NumberField K'] [Algebra K K'] [Field K₁] [NumberField K₁]
      [Algebra K K₁] (e : K' →ₐ[K] K₁) (f : V →ₗ[K] K'), Fam K' f →
      ∃ f₁ : V →ₗ[K] K₁, Fam K₁ f₁ ∧ ∀ v, f₁ v = e (f v)) →
    ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁) (ρ : ℕ)
      (g : Fin ρ → (V →ₗ[K] K₁)) (cfL : Fin ρ → Module.Dual K₁ (K₁ ⊗[K] V)),
      (∀ i, Fam K₁ (g i)) ∧ (∀ i v, cfL i ((1 : K₁) ⊗ₜ[K] v) = g i v) ∧
      (∀ x : K₁ ⊗[K] V, (∀ i, cfL i x = 0) ↔ x ∈ baseSpan K₁ W) ∧
      Module.finrank K W + ρ = Module.finrank K V
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


