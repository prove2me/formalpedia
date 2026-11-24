-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:38:39.563922+00:00
-- url     : https://prove2.me/theorems/14375407-aa5c-4e62-b7df-68a9d9eee00e
-- title:
--   Partial Derivative Ideal
-- statement:
--   Definitions and structural lemmas for Partial Derivative Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/PartialDerivativeIdeal.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S]
def partialDerivIdeal (h : ι) (J : Ideal S) : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ g ∈ J, partialDeriv k ι S h g = x}
def partialDerivIdealIterate (h : ι) : ℕ → Ideal S → Ideal S
  | 0, J => J
  | l + 1, J => partialDerivIdeal k ι S h (partialDerivIdealIterate h l J)
def evalDerivationAddHom (g : S) : Derivation k S S →+ S where
  toFun D := D g
  map_zero' := rfl
  map_add' _ _ := rfl
def idealInfComapPartialDeriv (h : ι) (K : Ideal S) : Ideal S where
  carrier := {g : S | g ∈ K ∧ partialDeriv k ι S h g ∈ K}
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨Submodule.add_mem K ha1 hb1, ?_⟩
    rw [map_add]
    exact Submodule.add_mem K ha2 hb2
  zero_mem' := by
    refine ⟨Submodule.zero_mem K, ?_⟩
    rw [map_zero]
    exact Submodule.zero_mem K
  smul_mem' := by
    intro c x hx
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨Ideal.mul_mem_left K c hx1, ?_⟩
    have hl : partialDeriv k ι S h (c * x)
        = c * partialDeriv k ι S h x + x * partialDeriv k ι S h c := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    show partialDeriv k ι S h (c * x) ∈ K
    rw [hl]
    exact Submodule.add_mem K (Ideal.mul_mem_left K c hx2) (Ideal.mul_mem_right _ K hx1)
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution


