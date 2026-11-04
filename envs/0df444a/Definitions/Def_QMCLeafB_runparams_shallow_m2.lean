-- Prove2me | Definitions.Def_QMCLeafB_runparams_shallow_m2
-- name    : QMCLeafB_runparams_shallow_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:03:45.714202+00:00
-- url     : https://prove2.me/theorems/e40f8417-f4ca-4419-b709-b01ebf04377c
-- title:
--   QMCLeafB runparams_shallow_m2
-- statement:
--   # leaf B phase 13 — brick `run-params-shallow` (swarm `smw17fqzz`, member m2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_runparams_m2
import Definitions.Def_QMCLeafB_roundcount_m2
import Definitions.Def_QMCLeafB_shallow_ceiling_m1
import Definitions.Def_QMCLeafB_roundcount_bound_m2
/-
# leaf B phase 13 — brick `run-params-shallow` (swarm `smw17fqzz`, member m2)

`FinalStroke.runParamsOf` supplies `QMCLeafB.VerdictSound.RunData`'s numeric fields from
`dq > 0`, `rmax ≥ 0`, `m ≥ 1` and the halving inequality at `rmax`.  This file *fills the halving
slot*, at the ceiling `Check_shallow_ceiling_m1` proved correct:

* `rmax = 1/(8(n·n))` (positive, as the refutation branch needs a positive cut margin),
* `m = 8(n·n)` (explicit, monomial),
* `dq = 1`, `cA = 2∑ₑ wₑ = ∑ᵢⱼ|wᵢⱼ|`, `M = 2n² + 2dq²`, `K = simRounds n Φ₀ r m`.

`hhalve` is `ShallowCeiling.halving_time_of_ceiling`, `hbudget` is
`ClosingBracket.runData_hbudget_close` at `m = 8(n·n)` — exactly the two conjuncts of
`ShallowCeiling.shallow_run_budget`.  So the endgame's numeric half is *completely* discharged at
`2 ≤ G.n`; combined with `RoundCountEnlarge.runParams_bigger_K` (or
`RoundCountBound.runParamsOfBound`) the round factor can additionally be enlarged to any monomial,
which is what the fuel slot needs.

Why `2 ≤ G.n`: `halving_time_of_ceiling` is stated at `2 ≤ n·n`; at `n = 0` one has `m = 0` and
`x^0 = 1 > 1/2`, so that endpoint needs its own argument.  `hd` is only read at `2 ≤ G.n`
(`VerdictSound.soundEpsOnBracket_of_runData`), so the indexed form is exactly what is consumed.

No `sorry`, no `axiom`; audit at the end.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.RunParamsShallow

open QuantumMaxCutEnergy

local instance instRequestCodingRunParamsShallow : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- The shallow depth ceiling `ρmax = 1/(8(n·n))`. -/
def runRmaxShallow (G : QuantumMaxCutEnergy.Input) : ℚ :=
  ((8 * (G.n * G.n : ℕ) : ℚ))⁻¹

/-- The halving time `m = 8(n·n)`. -/
noncomputable def runMcountShallow (G : QuantumMaxCutEnergy.Input) : ℕ := 8 * (G.n * G.n)

/-- The round-count factor at the shallow ceiling. -/
noncomputable def runKShallow (G : QuantumMaxCutEnergy.Input) : ℕ :=
  QMCLeafB.SimLoop.simRounds G.n (QMCLeafB.RunParamsSupply.runPhi G)
    (QMCLeafB.RunParamsSupply.runRadius G) (runMcountShallow G)

theorem runRmaxShallow_nonneg (G : QuantumMaxCutEnergy.Input) : 0 ≤ runRmaxShallow G := by
  unfold runRmaxShallow
  positivity

theorem runRmaxShallow_cast (G : QuantumMaxCutEnergy.Input) :
    ((runRmaxShallow G : ℚ) : ℝ) = (8 * ((G.n * G.n : ℕ) : ℝ))⁻¹ := by
  unfold runRmaxShallow
  push_cast
  ring

theorem runMcountShallow_ge {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) :
    1 ≤ runMcountShallow G := by
  have h : 0 < G.n * G.n := Nat.mul_pos (by omega) (by omega)
  unfold runMcountShallow
  exact Nat.succ_le_of_lt (Nat.mul_pos (by norm_num : 0 < 8) h)

theorem two_le_mul_self' {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) : 2 ≤ G.n * G.n :=
  le_trans (by norm_num) (Nat.mul_le_mul hn hn)

/-- **The numeric half of `RunData` at the shallow ceiling.** -/
noncomputable def runParamsShallow (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    QMCLeafB.FinalStroke.RunParams G where
  K := runKShallow G
  m := runMcountShallow G
  dq := QMCLeafB.RunParamsSupply.runDq
  cAq := QMCLeafB.RunParamsSupply.runCAq G
  rmax := runRmaxShallow G
  hdq := QMCLeafB.RunParamsSupply.runDq_pos
  hcAq := QMCLeafB.RunParamsSupply.runCAq_nonneg G
  hAsum := by
    rw [QMCLeafB.RunParamsSupply.runCAq_cast G]
  hrmax := runRmaxShallow_nonneg G
  hhalve := by
    have h := QMCLeafB.ShallowCeiling.halving_time_of_ceiling (N := G.n * G.n)
      (two_le_mul_self' hn) (ρmax := (8 * ((G.n * G.n : ℕ) : ℝ))⁻¹)
      (by positivity) (le_refl _)
    rwa [runRmaxShallow_cast G, runMcountShallow]
  hbudget := by
    simpa only [runKShallow, runMcountShallow, QMCLeafB.RunParamsSupply.runPhi,
      QMCLeafB.RunParamsSupply.runRadius, QMCLeafB.RunParamsSupply.runM,
      QMCLeafB.RunParamsSupply.runDq] using
      QMCLeafB.ClosingBracket.runData_hbudget_close (n := G.n)
        (M := QMCLeafB.RunParamsSupply.runM G)
        (by have h := QMCLeafB.RunParamsSupply.runM_pos G
            exact_mod_cast h)
        QMCLeafB.RunParamsSupply.runDq (QMCLeafB.RunParamsSupply.runCAq G)
        (by have h := QMCLeafB.RunParamsSupply.runDq_pos
            exact_mod_cast h)
        (by have h := QMCLeafB.RunParamsSupply.runCAq_nonneg G
            exact_mod_cast h)
        (m := runMcountShallow G) (runMcountShallow_ge hn)

/-- The ceiling is exactly `1/(8(n·n))`, as `ShallowCeiling` requires. -/
theorem runParamsShallow_rmax (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    (runParamsShallow G hn).rmax = runRmaxShallow G := rfl

/-- The halving time is exactly `8(n·n)`. -/
theorem runParamsShallow_m (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    (runParamsShallow G hn).m = 8 * (G.n * G.n) := rfl

/-- **The shallow ceiling with a monomial round factor.**  Enlarging `K` to `(1 + n·n·B)·m` (legal
by `RoundCountEnlarge.runParams_bigger_K`) gives a `RunParams` whose round count is
`(1 + n·n·B)·m²` — a monomial in `B`, i.e. a count `Fuel.fuelTake` can produce.  `B` only has to
bound `8√M(c_A+1)/dq`. -/
noncomputable def runParamsShallowBound (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (B : ℕ) (hB1 : 1 ≤ B)
    (hB : Real.sqrt (QMCLeafB.RunParamsSupply.runM G : ℝ)
        * 8 * ((QMCLeafB.RunParamsSupply.runCAq G : ℝ) + 1)
        / (QMCLeafB.RunParamsSupply.runDq : ℝ) ≤ (2 : ℝ) ^ B) :
    QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.RoundCountEnlarge.runParams_bigger_K (runParamsShallow G hn)
    ((1 + G.n * G.n * B) * runMcountShallow G)
    (by
      have h := QMCLeafB.RoundCountBound.simRounds_le_of_bound (n := G.n) hn
        (M := QMCLeafB.RunParamsSupply.runM G)
        (by have h := QMCLeafB.RunParamsSupply.runM_pos G
            exact_mod_cast h)
        (dq := QMCLeafB.RunParamsSupply.runDq)
        (cAq := QMCLeafB.RunParamsSupply.runCAq G)
        (by have h := QMCLeafB.RunParamsSupply.runDq_pos
            exact_mod_cast h)
        (by have h := QMCLeafB.RunParamsSupply.runCAq_nonneg G
            exact_mod_cast h) hB1 hB (runMcountShallow G)
      simpa only [runParamsShallow, runKShallow, QMCLeafB.RunParamsSupply.runPhi,
        QMCLeafB.RunParamsSupply.runRadius] using h)

/-- `runParamsShallowBound`'s round factor is the monomial `(1 + n·n·B)`. -/
theorem runParamsShallowBound_K (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (B : ℕ) (hB1 : 1 ≤ B)
    (hB : Real.sqrt (QMCLeafB.RunParamsSupply.runM G : ℝ)
        * 8 * ((QMCLeafB.RunParamsSupply.runCAq G : ℝ) + 1)
        / (QMCLeafB.RunParamsSupply.runDq : ℝ) ≤ (2 : ℝ) ^ B) :
    (runParamsShallowBound G hn B hB1 hB).K
      = (1 + G.n * G.n * B) * runMcountShallow G := rfl

/-- The same bundle's ceiling is still the shallow one (the cut margins stay positive). -/
theorem runParamsShallowBound_rmax (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (B : ℕ) (hB1 : 1 ≤ B)
    (hB : Real.sqrt (QMCLeafB.RunParamsSupply.runM G : ℝ)
        * 8 * ((QMCLeafB.RunParamsSupply.runCAq G : ℝ) + 1)
        / (QMCLeafB.RunParamsSupply.runDq : ℝ) ≤ (2 : ℝ) ^ B) :
    (runParamsShallowBound G hn B hB1 hB).rmax = runRmaxShallow G := rfl

/-! ## Axiom audit -/

#print axioms QMCLeafB.RunParamsShallow.runRmaxShallow_cast
#print axioms QMCLeafB.RunParamsShallow.runMcountShallow_ge
#print axioms QMCLeafB.RunParamsShallow.runParamsShallow
#print axioms QMCLeafB.RunParamsShallow.runParamsShallowBound
#print axioms QMCLeafB.RunParamsShallow.runParamsShallowBound_K

end QMCLeafB.RunParamsShallow


