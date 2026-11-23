-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DegeneratePrincipalSeriesUnitary_08b715622ebd4b27
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DegeneratePrincipalSeriesUnitary_08b715622ebd4b27
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:15.441322+00:00
-- url     : https://prove2.me/theorems/4976e0bd-208c-42a5-8d0d-9f936baad8e0
-- title:
--   Degenerate Principal Series Unitary
-- statement:
--   Definitions and structural lemmas for Degenerate Principal Series Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/DegeneratePrincipalSeriesUnitary.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SecMapApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.WeilM GlobalTheory.LinPair
open scoped Matrix
namespace GlobalTheory.Published
def DegeneratePrincipalSeriesUnitary : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JB : Matrix (Fin d) (Fin d) E) (Cy : Matrix (Fin d) (Fin n) E), ξ ≠ 0 →
    (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ (m : ℕ) (JA : Matrix (Fin m) (Fin m) E), IsHerm c JA →
  ∀ χ : Eˣ →* Circle, Continuous χ → ResEtaPow (R := k) ⊥ χ m →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ))
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ), IsLinPair c ψ ξ JA JB co χ Cy om → IsYForm c ψ co Cy l →
    (m < n → secSpace om l ≠ ⊥ ∧ ∀ N : Submodule ℂ (UG c JB → ℂ), N ≤ secSpace om l →
      (∀ h : UG c JB, ∀ f ∈ N, (fun x => f (x * h)) ∈ N) → N = ⊥ ∨ N = secSpace om l) ∧
    (n < m → ∀ (m' r : ℕ) (JA' : Matrix (Fin m') (Fin m') E), IsHerm c JA' → m + m' = 2 * n → IsWittStep c r JA JA' →
      ∀ (κ' : Type) [Fintype κ'] (co' : Darboux (symp c ξ JA' JB) κ')
        (om' : UG c JA' × UG c JB →* Module.End ℂ ((κ' → k) → ℂ)) (l' : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ),
        IsLinPair c ψ ξ JA' JB co' χ Cy om' → IsYForm c ψ co' Cy l' →
        ∃ q : secSpace om l →ₗ[ℂ] secSpace om' l', Function.Surjective q ∧
          ∀ (h : UG c JB) (f f₁ : secSpace om l), (∀ x, f₁.1 x = f.1 (x * h)) → ∀ x, (q f₁).1 x = (q f).1 (x * h))
end GlobalTheory.Published
end


