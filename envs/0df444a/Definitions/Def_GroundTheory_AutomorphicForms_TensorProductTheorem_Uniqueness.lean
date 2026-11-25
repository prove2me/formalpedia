-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Uniqueness
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_Uniqueness
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:26.065847+00:00
-- url     : https://prove2.me/theorems/cf61b129-0879-4a19-976b-6b43d410e9bc
-- title:
--   Uniqueness
-- statement:
--   Definitions and structural lemmas for Uniqueness, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Uniqueness.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace RestrictedTensor
open Filter Function Module Set PiTensorProduct
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}
  {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {V' : ι → Type*} [∀ v, AddCommGroup (V' v)] [∀ v, Module ℂ (V' v)]
end RestrictedTensor
end GroundTheory.Automorphic


