-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_BadStatement
-- name    : ReciprocityTheory_DualLattices_BadStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:05.741771+00:00
-- url     : https://prove2.me/theorems/db14d252-b36f-456e-aed7-d3f049e08360
-- title:
--   Bad Statement
-- statement:
--   Definitions and structural lemmas for Bad Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/BadStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.PGsh
open TensorProduct
universe u v w
def BadStatement : Prop :=
  ∀ (S : Type u) (A : Type v) [CommRing S] [CommRing A] [Algebra S A]
    (T₁ T₂ Q : Type w) [AddCommGroup T₁] [AddCommGroup T₂] [AddCommGroup Q]
    [Module S T₁] [Module S T₂] [Module S Q] [Module.Projective S Q]
    (ω₁ ω₂ Ω : Type w) [AddCommGroup ω₁] [AddCommGroup ω₂] [AddCommGroup Ω]
    [Module A ω₁] [Module A ω₂] [Module A Ω]
    (ι : T₁ →ₗ[S] T₂) (q : T₂ →ₗ[S] Q) (j : ω₁ →ₗ[A] ω₂) (p : ω₂ →ₗ[A] Ω)
    (α₁ : A ⊗[S] T₁ →ₗ[A] ω₁) (α₂ : A ⊗[S] T₂ →ₗ[A] ω₂) (β : A ⊗[S] Q →ₗ[A] Ω),
    Function.Injective ι → Function.Exact ι q → Function.Surjective q →
    Function.Injective j → Function.Exact j p →
    α₂ ∘ₗ ι.baseChange A = j ∘ₗ α₁ → p ∘ₗ α₂ = β ∘ₗ q.baseChange A → Function.Bijective β →
    (∀ c : A, (∀ x : ω₁, c • x ∈ LinearMap.range α₁) → ∀ x : ω₂, c • x ∈ LinearMap.range α₂) ∧
    Function.Injective (ι.baseChange A) ∧
    LinearMap.ker α₂ = (LinearMap.ker α₁).map (ι.baseChange A)
end ReciprocityTheory.PGsh


