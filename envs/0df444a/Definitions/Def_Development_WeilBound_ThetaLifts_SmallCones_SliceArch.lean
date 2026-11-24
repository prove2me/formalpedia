-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
-- name    : Development_WeilBound_ThetaLifts_SmallCones_SliceArch
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:35.659403+00:00
-- url     : https://prove2.me/theorems/438bd21b-bc8f-4bff-8e77-cd35566b6dd8
-- title:
--   Slice Arch
-- statement:
--   Definitions and structural lemmas for Slice Arch, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean

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
namespace PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
def Bd (m : ℕ) (f : V → ℂ) (C : ℝ) : Prop := ∀ j ≤ m, ∀ x, (1 + ‖x‖) ^ m * ‖iteratedFDeriv ℝ j f x‖ ≤ C
variable (V) in

def P (m : ℕ) : Seminorm ℂ (SchwartzMap V ℂ) := (Finset.Iic (m, m)).sup (schwartzSeminormFamily ℂ V ℂ)
def sc {Z : Type} [AddCommGroup Z] [Module ℂ Z] (C : ℝ) (p : Seminorm ℂ Z) : Seminorm ℂ Z := C.toNNReal • p
def ph (l : V →L[ℝ] ℝ) (c : ℝ) (x : V) : ℂ := cexp (I * ((l x + c : ℝ) : ℂ))
def S (w : V × (V →L[ℝ] ℝ)) : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (ph w.2 (w.2 w.1 / 2))).comp (SchwartzMap.compSubConstCLM ℂ (-w.1))
end PositivityTheory.ThKCT.Arch
end


