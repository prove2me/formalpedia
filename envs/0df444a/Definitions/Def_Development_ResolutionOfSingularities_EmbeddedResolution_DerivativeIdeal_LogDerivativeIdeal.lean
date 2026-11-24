-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:50.233614+00:00
-- url     : https://prove2.me/theorems/0542e8bd-466b-4190-9b6c-6d02cede3dd2
-- title:
--   Log Derivative Ideal
-- statement:
--   Definitions and structural lemmas for Log Derivative Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdeal.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
def tangentDerivations (P : Ideal S) : Submodule S (Derivation k S S) where
  carrier := {D : Derivation k S S | ∀ x ∈ P, D x ∈ P}
  add_mem' := by
    intro D D' hD hD' x hx
    have h := P.add_mem (hD x hx) (hD' x hx)
    simpa using h
  zero_mem' := by
    intro x _
    simp
  smul_mem' := by
    intro a D hD x hx
    have h := Ideal.mul_mem_left P a (hD x hx)
    simpa [smul_eq_mul] using h
def logDerivIdeal (P J : Ideal S) : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ D ∈ tangentDerivations k P, ∃ y ∈ J, D y = x}
def logDerivIdealIterate (P : Ideal S) : ℕ → Ideal S → Ideal S
  | 0, J => J
  | r + 1, J => logDerivIdeal k P (logDerivIdealIterate P r J)
end FunctorialResolution.EmbeddedResolution


