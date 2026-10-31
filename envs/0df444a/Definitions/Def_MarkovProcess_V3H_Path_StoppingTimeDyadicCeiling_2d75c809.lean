-- Prove2me | Definitions.Def_MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
-- name    : MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:16:27.037773+00:00
-- url     : https://prove2.me/theorems/2ffd3799-02dd-40b9-b6bd-626f9233673b
-- title:
--   MarkovProcess: MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Instances.NNReal.Lemmas

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic ceiling approximation of finite stopping times

The level-`n` dyadic ceiling of a nonnegative time is the least point of the grid `2⁻ⁿ ℕ` that is
at least the time.  Composed with a finite `NNReal`-valued stopping time it produces stopping
times with countable range that decrease to the original time.  This is ordinary stopping-time
infrastructure and proves no restart identity; the restart identity obtained from this
approximation is in `Trajectory/FellerStoppingRestart.lean`.
-/

open MeasureTheory Filter Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section

/-- The level-`n` dyadic ceiling of a nonnegative real time. -/
def dyadicCeiling (n : ℕ) (t : NNReal) : NNReal :=
  ⟨(⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) / 2 ^ n, by positivity⟩

/-- The level-`n` dyadic floor of a nonnegative real time. -/
def dyadicFloor (n : ℕ) (t : NNReal) : NNReal :=
  ⟨(⌊(2 ^ n : ℝ) * (t : ℝ)⌋₊ : ℝ) / 2 ^ n, by positivity⟩





















/-- The level-`n` dyadic grid point with index `k`. -/
def dyadicGrid (n k : ℕ) : NNReal := ⟨(k : ℝ) / 2 ^ n, by positivity⟩

/-- The grid index of the level-`n` dyadic ceiling. -/
def dyadicCeilingIndex (n : ℕ) (t : NNReal) : ℕ :=
  ⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊



/-- The dyadic grid is monotone in its index. -/
theorem monotone_dyadicGrid (n : ℕ) : Monotone (dyadicGrid n) := by
  intro k l hkl
  rw [← NNReal.coe_le_coe]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hkl) (by positivity)





variable {Omega : Type*} {m : MeasurableSpace Omega}









end

end MarkovProcess


