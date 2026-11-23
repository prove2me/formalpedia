-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SgC
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_SgC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:49.167794+00:00
-- url     : https://prove2.me/theorems/50e3a278-8045-43f0-b455-ac891837d81a
-- title:
--   Sg C
-- statement:
--   Definitions and structural lemmas for Sg C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SgC.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExpUpper
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped UpperHalfPlane MatrixGroups
namespace GlobalTheory.KZ
def sgC (c : ℕ) (x : Fin 2 → ℚ) (z : ℂ) : ℂ := GlobalTheory.Sieg.sg c x (UpperHalfPlane.ofComplex z)
open Classical in

def siegel {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ) : T.K :=
  if h : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero) then h.choose else 0
end GlobalTheory.KZ


