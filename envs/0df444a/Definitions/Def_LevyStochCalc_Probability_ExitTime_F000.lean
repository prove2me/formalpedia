-- Prove2me | Definitions.Def_LevyStochCalc_Probability_ExitTime_F000
-- name    : LevyStochCalc_Probability_ExitTime_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:02:07.857933+00:00
-- url     : https://prove2.me/theorems/2c9d3a77-244e-46df-9baf-126487efaf61
-- title:
--   Source declarations: LevyStochCalc.Probability.ExitTime
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Probability.ExitTime, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Data.Rat.Denumerable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Monotone

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exit times of a process with continuous paths

`exitTime X k ω` is the first nonnegative time at which the path `X ω` has norm at least `k`, and
`⊤` when the path never reaches that norm. For continuous paths the comparison `exitTime X k ω ≤ t`
is decided by the values of the path on the rationals of `[0, t]`, so the exit time is a stopping
time for any filtration the process is adapted to. Letting `k` grow gives a localising sequence:
every time lies strictly below `exitTime X k` for all large `k`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]

/-- The nonnegative times at which the path `X ω` has norm at least `k`. -/
def exitSet (X : Ω → ℝ → E) (k : ℝ) (ω : Ω) : Set ℝ := {t : ℝ | 0 ≤ t ∧ k ≤ ‖X ω t‖}
open scoped Classical in
/-- The first nonnegative time at which the path `X ω` has norm at least `k`, and `⊤` when the
path never reaches that norm. -/
noncomputable def exitTime (X : Ω → ℝ → E) (k : ℝ) (ω : Ω) : WithTop ℝ :=
  if (exitSet X k ω).Nonempty then ((sInf (exitSet X k ω) : ℝ) : WithTop ℝ) else ⊤
/-- The `n`-th rational, clamped to `[0, t]`. -/
noncomputable def gridPt (t : ℝ) (n : ℕ) : ℝ :=
  max 0 (min t (((Denumerable.eqv ℚ).symm n : ℚ) : ℝ))
theorem bddBelow_exitSet (X : Ω → ℝ → E) (k : ℝ) (ω : Ω) : BddBelow (exitSet X k ω) :=
  ⟨0, fun _ ht => ht.1⟩
theorem isClosed_exitSet {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k : ℝ) :
    IsClosed (exitSet X k ω) := by
  have h : exitSet X k ω = Set.Ici (0 : ℝ) ∩ (fun r => ‖X ω r‖) ⁻¹' Set.Ici k := by
    ext r
    simp only [exitSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_preimage]
  rw [h]
  exact isClosed_Ici.inter (isClosed_Ici.preimage hX.norm)
theorem csInf_exitSet_mem {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {k : ℝ}
    (h : (exitSet X k ω).Nonempty) : sInf (exitSet X k ω) ∈ exitSet X k ω :=
  (isClosed_exitSet hX k).csInf_mem h (bddBelow_exitSet X k ω)
theorem coe_zero_le_exitTime (X : Ω → ℝ → E) (k : ℝ) (ω : Ω) :
    ((0 : ℝ) : WithTop ℝ) ≤ exitTime X k ω := by
  rw [exitTime]
  split_ifs with h
  · exact_mod_cast le_csInf h fun _ hr => hr.1
  · exact le_top
end LevyStochCalc.Probability


