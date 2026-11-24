-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProduct
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:19.490822+00:00
-- url     : https://prove2.me/theorems/14cd5513-add3-4bd0-84f5-64912da22718
-- title:
--   Mackey Inner Product
-- statement:
--   Definitions and structural lemmas for Mackey Inner Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
namespace GlobalTheory.CompanionTheory.MackeyFn
variable {Γ : Type} [Group Γ] [Fintype Γ]
open Classical in

def mS (A B : Subgroup Γ) (a b : Γ → ℂ) (x : Γ) : ℂ :=
  ∑ h, if h ∈ (A ⊓ cj x B : Subgroup Γ) then a h⁻¹ * b (x * h * x⁻¹) else 0
def dc (A B : Subgroup Γ) (g : Γ) : Set Γ := {x | ∃ β ∈ B, ∃ α ∈ A, x = β * g * α}
end GlobalTheory.CompanionTheory.MackeyFn


