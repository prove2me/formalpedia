-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:28.880888+00:00
-- url     : https://prove2.me/theorems/e7548072-16c6-4236-9355-c0a64e0dd0e5
-- title:
--   Matrix Coeff
-- statement:
--   Definitions and structural lemmas for Matrix Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean

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
namespace GroundTheory.Automorphic
open Set
namespace RestrictedTensor
variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
def orbitSpan (ρ : Representation ℂ G V) (v : V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (range fun g => ρ g v)
  apply_mem_toSubmodule g x hx := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
def orbitMap (ρ : Representation ℂ G V) (v : V) : (G →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun g => ρ g v
end RestrictedTensor
end GroundTheory.Automorphic


