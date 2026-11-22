-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Columns_MemWmPerp
-- name    : Formalism_LocalToGlobal_Columns_MemWmPerp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:25.021232+00:00
-- url     : https://prove2.me/theorems/d3f97a66-787b-4c5c-98b0-6d712268f13d
-- title:
--   Mem Wm Perp
-- statement:
--   Definitions and structural lemmas for Mem Wm Perp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/MemWmPerp.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Col
variable {K : Type} [Field K] [StarRing K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
def wmPerp (B : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule K V) : Submodule K V where
  carrier := {x | ∀ a ∈ A, B a x = 0}
  add_mem' := by
    intro x y hx hy a ha
    rw [map_add, hx a ha, hy a ha, add_zero]
  zero_mem' := by
    intro a _
    rw [map_zero]
  smul_mem' := by
    intro c x hx a ha
    rw [map_smul, hx a ha, smul_zero]
def wmZ (B : V →ₗ⋆[K] V →ₗ[K] K) (V₀ : Submodule K V) (θ : V →ₗ[K] W) : Submodule K V :=
  V₀ ⊓ wmPerp B (LinearMap.ker θ ⊓ V₀)
end Formalism.L2.Col


