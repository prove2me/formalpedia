-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:29.559178+00:00
-- url     : https://prove2.me/theorems/c6a12ebb-a8f0-42ec-92c8-e9251faa43f1
-- title:
--   Finite Detect Statement
-- statement:
--   Definitions and structural lemmas for Finite Detect Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDetectStatement.lean

import Mathlib
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
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
def baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    Submodule F (F ⊗[K] V) :=
  Submodule.span F ((fun u => (1 : F) ⊗ₜ[K] u) '' (U : Set V))
variable {Ω : Type*} [Field Ω] [Algebra K Ω]
noncomputable def inclT (K₁ : IntermediateField K Ω) (V : Type*) [AddCommGroup V] [Module K V] :
    K₁ ⊗[K] V →ₗ[K₁] Ω ⊗[K] V :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K₁ Ω) (LinearMap.id : V →ₗ[K] V)
def DefinedOver (c : Module.Dual Ω (Ω ⊗[K] V)) (K' : IntermediateField K Ω) : Prop :=
  ∀ x : K' ⊗[K] V, c (inclT K' V x) ∈ Set.range (algebraMap K' Ω)
noncomputable def descend (K₁ : IntermediateField K Ω) (W : Submodule Ω (Ω ⊗[K] V)) :
    Submodule K₁ (K₁ ⊗[K] V) :=
  (W.restrictScalars K₁).comap (inclT K₁ V)
end Defs
def FiniteDetectStatement : Prop :=
  ∀ (L E : Type) [Field L] [AddCommGroup E] [Module L E] [FiniteDimensional L E]
    (W : Submodule L E) (FF : Set (Module.Dual L E)),
    (∀ c ∈ FF, W ≤ LinearMap.ker c) →
    (∀ x : E, x ∉ W → ∃ c ∈ FF, c x ≠ 0) →
    ∃ s : Finset (Module.Dual L E), (↑s ⊆ FF) ∧ (⨅ c ∈ s, LinearMap.ker c) = W
def RationalityStatement : Prop :=
  ∀ (K Ω V : Type) [Field K] [Field Ω] [Algebra K Ω] [AddCommGroup V] [Module K V]
    (U : Submodule K V) [FiniteDimensional K U]
    (W : Submodule Ω (Ω ⊗[K] V)) (FF : Set (Module.Dual Ω (Ω ⊗[K] V))),
    W ≤ baseSpan Ω U →
    (∀ c ∈ FF, ∃ K' : IntermediateField K Ω, FiniteDimensional K K' ∧ DefinedOver c K') →
    (∀ c ∈ FF, W ≤ LinearMap.ker c) →
    (∀ x ∈ baseSpan Ω U, x ∉ W → ∃ c ∈ FF, c x ≠ 0) →
    ∃ K₁ : IntermediateField K Ω, FiniteDimensional K K₁ ∧
      ∃ (ρ : ℕ) (c : Fin ρ → Module.Dual Ω (Ω ⊗[K] V)),
        (∀ i, c i ∈ FF ∧ DefinedOver (c i) K₁) ∧
        descend K₁ W = baseSpan K₁ U ⊓
          ⨅ i, LinearMap.ker ((c i).restrictScalars K₁ ∘ₗ inclT K₁ V) ∧
        Submodule.span Ω (inclT K₁ V '' (descend K₁ W : Set (K₁ ⊗[K] V))) = W ∧
        Module.finrank K₁ (descend K₁ W) = Module.finrank Ω W ∧
        Module.finrank K₁ (descend K₁ W) + ρ = Module.finrank K U
def SelectStatement : Prop :=
  ∀ (L E ι : Type) [Field L] [AddCommGroup E] [Module L E] [FiniteDimensional L E]
    (ρ : ℕ) (c : Fin ρ → Module.Dual L E) (MD : Submodule L E),
    (⨅ i, LinearMap.ker (c i)) = MD →
    Module.finrank L MD + ρ = Module.finrank L E →
    ∀ th : ι → E, Submodule.span L (Set.range th) = ⊤ →
      ∃ sel : Fin ρ → ι, Function.Injective sel ∧
        (Matrix.of fun i j => c i (th (sel j))).det ≠ 0
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


