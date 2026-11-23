-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:32.100882+00:00
-- url     : https://prove2.me/theorems/949e51d3-64f2-4a4a-b155-cdb92a678334
-- title:
--   Continuous On Cos Sq
-- statement:
--   Definitions and structural lemmas for Continuous On Cos Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOnCosSq.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
namespace GlobalTheory.LineCos
def hform (G : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ j, a i * starRingEnd ℂ (b j) * G i j
def lineVec (s : Bool) (x : ℂ) : Fin 2 → ℂ := if s then ![x, 1] else ![1, x]
def cosSq (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℝ :=
  ‖hform G (lineVec s x) (Pi.single 0 1)‖ ^ 2 / ((hform G (lineVec s x) (lineVec s x)).re * (G 0 0).re)
def base {d : ℕ} (z : V (d + 1)) : Fin d → ℂ := fun i => z (Fin.castSucc i)
def fib {d : ℕ} (z : V (d + 1)) : ℂ := z (Fin.last d)
end GlobalTheory.LineCos


