-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:36:54.225296+00:00
-- url     : https://prove2.me/theorems/4f42ca5b-3134-47a3-bb9a-eed5539e597f
-- title:
--   JInvariant
-- statement:
--   Definitions and structural lemmas for JInvariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/JInvariant.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_one
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_two
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_one
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_two
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_zero


set_option autoImplicit false
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology
open scoped PeriodPair Real
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
def latticeOfTau (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    refine LinearIndependent.pair_iff.2 fun s t h ↦ ?_
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp at him hre
    have hs : s = 0 := by
      rcases him with h | h
      · exact h
      · exact absurd h τ.im_pos.ne'
    subst hs
    simp at hre
    exact ⟨rfl, hre⟩
def modularJ (τ : ℍ) : ℂ := E₄ τ ^ 3 / ModularForm.discriminant τ
end Elliptic
end GroundTheory.Global


