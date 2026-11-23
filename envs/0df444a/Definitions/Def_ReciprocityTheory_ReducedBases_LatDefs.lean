-- Prove2me | Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
-- name    : ReciprocityTheory_ReducedBases_LatDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:00.053974+00:00
-- url     : https://prove2.me/theorems/45dfd8d3-e1f6-4231-adf0-7380b9171bce
-- title:
--   Lat Defs
-- statement:
--   Definitions and structural lemmas for Lat Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/LatDefs.lean

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
namespace ReciprocityTheory.ReducedBases
open Matrix
def toReal {d : ℕ} (x : Fin d → ℤ) : Fin d → ℝ := fun i => (x i : ℝ)
def polar {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℤ) : ℝ :=
  toReal x ⬝ᵥ (A *ᵥ toReal y)
def Q {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℤ) : ℝ := polar A x x / 2
def SameClass {d : ℕ} (N : ℤ) (a b : Fin d → ℤ) : Prop := ∃ w : Fin d → ℤ, a = b + N • w
def IsMinInClass {d : ℕ} (F : (Fin d → ℤ) → ℝ) (N : ℤ) (a : Fin d → ℤ) : Prop :=
  ∀ w : Fin d → ℤ, F a ≤ F (a + N • w)
def IsUniqueMinInClass {d : ℕ} (F : (Fin d → ℤ) → ℝ) (N : ℤ) (a : Fin d → ℤ) : Prop :=
  ∀ w : Fin d → ℤ, w ≠ 0 → F a < F (a + N • w)
end ReciprocityTheory.ReducedBases
end


