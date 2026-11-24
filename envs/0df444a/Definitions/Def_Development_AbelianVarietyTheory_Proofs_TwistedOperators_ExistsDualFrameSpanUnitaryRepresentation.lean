-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualFrameSpanUnitaryRepresentation
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualFrameSpanUnitaryRepresentation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:55.350081+00:00
-- url     : https://prove2.me/theorems/63fab258-a9ef-4098-87fc-821c359ba95a
-- title:
--   Exists Dual Frame Span Unitary Representation
-- statement:
--   Definitions and structural lemmas for Exists Dual Frame Span Unitary Representation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualFrameSpanUnitaryRepresentation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
namespace GlobalTheory.DualFrameSpan
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
noncomputable def pairing (W : Submodule ℂ (H →ₗ[ℂ] H)) : LinearMap.BilinForm ℂ W :=
  LinearMap.mk₂ ℂ (fun X Y : W => LinearMap.trace ℂ H ((X : H →ₗ[ℂ] H) ∘ₗ (Y : H →ₗ[ℂ] H)))
    (fun x y z => by simp [LinearMap.add_comp]) (fun c x y => by simp [LinearMap.smul_comp])
    (fun x y z => by simp [LinearMap.comp_add]) (fun c x y => by simp [LinearMap.comp_smul])
section span
variable {G : Type} [Mul G] (K : Set G) (ρ : G → (H →ₗ[ℂ] H))
end span
end GlobalTheory.DualFrameSpan


