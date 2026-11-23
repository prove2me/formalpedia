-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:00.867383+00:00
-- url     : https://prove2.me/theorems/ac9f1225-2548-4c91-8e78-579f2fa8b5b2
-- title:
--   Zero Dim A
-- statement:
--   Definitions and structural lemmas for Zero Dim A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ZeroDimA.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IndCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]
def zdCnt {d n : ℕ} (t : Fin d → Fin n) : Fin n → ℕ :=
  fun k => (Finset.univ.filter fun i => t i = k).card
def zdRep {n : ℕ} (α : Fin n → ℕ) : Fin (∑ k, α k) → Fin n :=
  fun i => (finSigmaFinEquiv.symm i).1
def zdBasis (n : ℕ) : Module.Basis (Fin n) ℂ (V n) := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
end ReciprocityTheory.L2DbarEstimates.Y


