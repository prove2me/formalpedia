-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:35.46498+00:00
-- url     : https://prove2.me/theorems/a3f74638-a29a-47ff-9df3-492edff9dc4b
-- title:
--   Measure Preserving Cons
-- statement:
--   Definitions and structural lemmas for Measure Preserving Cons, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
namespace GlobalTheory.GLFirstColumn
def mulM {m : ℕ} (x y : Fin m → Fin m → ℂ) : Fin m → Fin m → ℂ :=
  fun i j => (Matrix.of x * Matrix.of y) i j
noncomputable def invM {m : ℕ} (x : Fin m → Fin m → ℂ) : Fin m → Fin m → ℂ :=
  fun i j => (Matrix.of x)⁻¹ i j
noncomputable def wt {m : ℕ} (x : Fin m → Fin m → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ m)
def blk {k : ℕ} (r : Fin k → ℂ) (m : Fin k → Fin k → ℂ) : Fin (k + 1) → Fin (k + 1) → ℂ :=
  Fin.cons (Fin.cons 1 r) fun a => Fin.cons 0 (m a)
end GlobalTheory.GLFirstColumn


