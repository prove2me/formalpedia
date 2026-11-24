-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:42.85161+00:00
-- url     : https://prove2.me/theorems/1ab0d5de-6052-4413-bb98-de6accd09f0b
-- title:
--   Fixed Mem Of Orbit Height
-- statement:
--   Definitions and structural lemmas for Fixed Mem Of Orbit Height, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
namespace GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
def WA (V : ι → Submodule ℂ M) (A : Set ι) : Submodule ℂ M := ⨆ (j) (_ : j ∈ A), V j
end GlobalTheory.GradedFixed
namespace GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
section comp
variable (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (c : ι → M →ₗ[ℂ] M)
  (hc1 : ∀ i w, c i w ∈ V i) (hc2 : ∀ i v, v ∈ V i → c i v = v)
  (hc3 : ∀ i j v, i ≠ j → v ∈ V j → c i v = 0) (hc4 : ∀ w, ∃ F : Finset ι, w = ∑ i ∈ F, c i w)
include hc1 hc2 hc3 hc4
end comp
end GlobalTheory.GradedFixed
namespace GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
end GlobalTheory.GradedFixed
namespace GlobalTheory
end GlobalTheory


