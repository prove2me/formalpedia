-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_Window
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:41.090139+00:00
-- url     : https://prove2.me/theorems/a5c40bf6-c414-433d-b493-da45fdc9da63
-- title:
--   Window
-- statement:
--   Definitions and structural lemmas for Window, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
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
open Module Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
def heckeOp (g : G) : End ℂ (fixedVectors ρ K) :=
  fixedProj ρ hρ hKc hKo ∘ₗ ρ g ∘ₗ (fixedVectors ρ K).subtype
def heckeOps : Set (End ℂ (fixedVectors ρ K)) :=
  range (heckeOp hρ hKc hKo)
end RestrictedTensor
end GroundTheory.Automorphic


