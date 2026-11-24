-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivial
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:38.473406+00:00
-- url     : https://prove2.me/theorems/0a575606-7ae3-4e1a-884d-7bec75c9284c
-- title:
--   Char Const On Translates Trivial
-- statement:
--   Definitions and structural lemmas for Char Const On Translates Trivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CharConstOnTranslatesTrivial.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousCharUnitsComplexStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory.ArchChar
variable {ι : Type} [Fintype ι] [DecidableEq ι]
lemma add_ne {θ : ℂ} (hθ : θ.im ≠ 0) (t : ℝ) : (t : ℂ) + θ ≠ 0 := by
  intro h
  apply hθ
  have := congrArg Complex.im h
  simpa using this
lemma ofReal_ne {ρ : ℝ} (h : 0 < ρ) : (ρ : ℂ) ≠ 0 := by
  exact_mod_cast h.ne'
noncomputable def shift (θ : ι → ℂ) (hθ : ∀ i, (θ i).im ≠ 0) (a : ι → ℝ) : ι → ℂˣ :=
  fun i => Units.mk0 _ (add_ne (hθ i) (a i))
noncomputable def realUnits (r : ι → ℝ) (hr : ∀ i, 0 < r i) : ι → ℂˣ :=
  fun i => Units.mk0 _ (ofReal_ne (hr i))
end GlobalTheory.ArchChar


