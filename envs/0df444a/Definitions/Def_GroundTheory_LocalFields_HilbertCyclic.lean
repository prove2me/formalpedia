-- Prove2me | Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
-- name    : GroundTheory_LocalFields_HilbertCyclic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:15.380142+00:00
-- url     : https://prove2.me/theorems/e0f5b851-c4de-48cc-b337-f57601af2a90
-- title:
--   Hilbert Cyclic
-- statement:
--   Definitions and structural lemmas for Hilbert Cyclic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HilbertCyclic.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField
open Finset
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
section Partial
variable (σ : L ≃ₐ[K] L) (x : Lˣ)
noncomputable def partialNorm (m : ℕ) : Lˣ :=
  ∏ j ∈ range m, (σ ^ j) • x
variable {σ}
variable (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1)
include hσ hx
end Partial
end GroundTheory.LocalField


