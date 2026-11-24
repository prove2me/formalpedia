-- Prove2me | solution 1 for AddUN.overwrite_of_notMem_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:43:06.502917+00:00
-- url     : https://prove2.me/submissions/23c5b0f9-47a5-4628-89aa-6b5a179d4986

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
variable {U : Set (ℕ → Bool)}
namespace AddUN
theorem _root_.solution {h : ℕ → ℕ} (c u : ℕ → Bool) {i : ℕ} (hi : i ∉ range h) :
    overwrite h c u i = u i := by
  unfold overwrite
  rw [if_neg fun heq ↦ hi ⟨_, heq⟩]
end AddUN
