-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__RallisCoinvariants_77b122ff21ad2438
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__RallisCoinvariants_77b122ff21ad2438
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:21.067583+00:00
-- url     : https://prove2.me/theorems/2ed1a705-e857-4d4f-a558-06d757c832bd
-- title:
--   Rallis Coinvariants
-- statement:
--   Definitions and structural lemmas for Rallis Coinvariants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/RallisCoinvariants.lean

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
def RallisCoinvariants : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n d : ℕ) (ξ : E) (JB : Matrix (Fin d) (Fin d) E) (Cy : Matrix (Fin d) (Fin n) E), ξ ≠ 0 →
    (∀ i j, c (ξ * JB j i) = -(ξ * JB i j)) → JB.det ≠ 0 →
  ∀ (m : ℕ) (JA : Matrix (Fin m) (Fin m) E), IsHerm c JA →
  ∀ χ : Eˣ →* Circle, Continuous χ → ResEtaPow (R := k) ⊥ χ m →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp c ξ JA JB) κ) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ))
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ), IsLinPair c ψ ξ JA JB co χ Cy om → IsYForm c ψ co Cy l →
    ∀ φ ∈ SB (κ → k), secMap om l φ = 0 ↔ φ ∈ locAug om
end GlobalTheory.Published
end


