-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:22.442981+00:00
-- url     : https://prove2.me/theorems/b81c679c-02b2-4d5c-99ec-29fefd0e6312
-- title:
--   Capelli Whittaker Zero
-- statement:
--   Definitions and structural lemmas for Capelli Whittaker Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {M R : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R]
def whB_c (N a : ℕ) [NeZero N] : Fin N := ⟨a % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩
def whB_seg (N s q : ℕ) [NeZero N] (i : Fin q) : Fin N := whB_c N (s + (i : ℕ))
def whB_g (k r : ℕ) (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) (a : Fin (k + 2 * r + 1)) : ℂ :=
  ∏ b, if IsSimplePair k r a b then ψ a b else 1
section Phases
variable (k r : ℕ) (E : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → Module.End ℂ M)
  (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) (l : M →ₗ[ℂ] R) (hE : IsGlRep E)
  (hl : ∀ a b, blk k r a < blk k r b → l ∘ₗ E a b = ψ a b • l)
  (hψ : ∀ a b, blk k r a < blk k r b → ¬ IsSimplePair k r a b → ψ a b = 0)
include hE hl hψ
end Phases
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli


