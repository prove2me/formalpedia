-- Prove2me | Definitions.Def_QMCLeafB_runparams_m2
-- name    : QMCLeafB_runparams_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:52:52.433031+00:00
-- url     : https://prove2.me/theorems/8817fdcd-dc44-43b1-ba4e-20758bfedd23
-- title:
--   QMCLeafB runparams_m2
-- statement:
--   # leaf B phase 13 — brick `run-params` (swarm `smw17fqzz`, member m2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_ClosingBracket
/-
# leaf B phase 13 — brick `run-params` (swarm `smw17fqzz`, member m2)

`QMCLeafB.FinalStroke.RunParams G` is the **threshold-independent half** of
`QMCLeafB.VerdictSound.RunData`: the round-count factor `K`, the halving time `m`, the oracle
tolerance `dq`, the ledger constant `cAq`, the contraction ceiling `rmax`, and the six inequalities
`0 < dq`, `0 ≤ cAq`, `∑ᵢⱼ |Aᵢⱼ| ≤ c_A`, `0 ≤ rmax`, `hhalve`, `hbudget`.  None of it mentions the
run, the verdict or the state machine, and all of it is already on the shelf:

* `hbudget` is `ClosingBracket.runData_hbudget_close` verbatim at the campaign's radius
  `r = dq/(8(c_A+1))` — it does not even need `2 ≤ n`;
* `hhalve` is `runData_hhalve_close` verbatim at `m = 4(n·n)`, `rmax = 0` (which does need
  `2 ≤ n·n`).

This file is the concrete inhabitant `runParams G (h : 2 ≤ G.n) : RunParams G` and the integration
lemma that consumes it, `endgame_of_hn_parts`.

**Why the `2 ≤ G.n` indexing matters.**  `FinalStroke.endgame_of_parts` asks for a *total*
`P : ∀ G, RunParams G`.  `RunParams G` is presumably inhabited at `n ≤ 1` too, but the shelf theorem
for `hhalve` (`halving_time_explicit`) is stated at `2 ≤ n·n`, and at `n ≤ 1` one has to re-prove
`rho0R (n·n) ρ ≤ 0` (`rho0R 0 ρ = -1`, `rho0R 1 ρ = 0`), hence `sqrt = 0`, hence `0^m ≤ 1/2`, by
hand.  The bracket `hd` is only ever read at `2 ≤ G.n`
(`VerdictSound.soundEpsOnBracket_of_runData`), so the total family buys nothing: §4 gives the same
integration with `P` at `2 ≤ G.n` only, which is what the shelf supplies.

No `sorry`, no `axiom`; audit at the end.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.RunParamsSupply

open QuantumMaxCutEnergy

/-- The request coding of the leaf, definitionally as in `Check_brick_verdict_sound` and
`Check_brick_finish_line`: the closing forms are stated at `encodeRequest`, so the same instance
must be in scope here (it is `local` in each of those files, hence not inherited). -/
local instance instRequestCodingRunParams : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The five constants -/

/-- The oracle tolerance: `dq = 1` (any positive rational works; `M = 2n² + 2dq²` enters only
through `initShapeOf`). -/
def runDq : ℚ := 1

/-- The ledger constant `c_A`: twice the total weight `2 · ∑ₑ wₑ` (which *is*
`∑ᵢⱼ |Aᵢⱼ|`, by `wMatrix_nonneg` + `V_wMatrix`). -/
noncomputable def runCAq (G : QuantumMaxCutEnergy.Input) : ℚ :=
  2 * ∑ e : QuantumMaxCutEnergy.Edge G.n, ((G.weights e : ℚ≥0) : ℚ)

/-- The contraction ceiling: `rmax = 0`, which is what `halving_time_explicit` is stated at. -/
def runRmax : ℚ := 0

/-- The shape parameter `M` of `initShapeOf`. -/
noncomputable def runM (G : QuantumMaxCutEnergy.Input) : ℚ :=
  2 * (G.n : ℚ) ^ 2 + 2 * runDq ^ 2

/-- The halving time: `m = 4(n·n)`. -/
noncomputable def runMcount (G : QuantumMaxCutEnergy.Input) : ℕ := 4 * (G.n * G.n)

/-- The initial potential `Φ₀ = volPot (n·n) (initShapeOf (n·n) M)`. -/
noncomputable def runPhi (G : QuantumMaxCutEnergy.Input) : ℝ :=
  QMCLeafB.EngineIterates.volPot (G.n * G.n)
    (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (runM G))

/-- The contraction radius `r = dq / (8(c_A + 1))`. -/
noncomputable def runRadius (G : QuantumMaxCutEnergy.Input) : ℝ :=
  (runDq : ℝ) / (8 * ((runCAq G : ℝ) + 1))

/-- The round-count factor `K = simRounds n Φ₀ r m`. -/
noncomputable def runK (G : QuantumMaxCutEnergy.Input) : ℕ :=
  QMCLeafB.SimLoop.simRounds G.n (runPhi G) (runRadius G) (runMcount G)

/-! ## 2.  The easy fields -/

theorem runDq_pos : 0 < runDq := by norm_num [runDq]

theorem runRmax_nonneg : 0 ≤ runRmax := by norm_num [runRmax]

theorem runCAq_nonneg (G : QuantumMaxCutEnergy.Input) : 0 ≤ runCAq G := by
  unfold runCAq
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun e _ => (G.weights e).2)

/-- The ledger identity, cast into `ℝ`: `c_A` is *exactly* the total absolute entry sum, so the
ledger inequality `hAsum` is an equality. -/
theorem runCAq_cast (G : QuantumMaxCutEnergy.Input) :
    ((runCAq G : ℚ) : ℝ)
      = ∑ i : Fin G.n, ∑ j : Fin G.n, |(QMCLeafB.wMatrix G i j : ℝ)| := by
  have hcast : ((runCAq G : ℚ) : ℝ)
      = 2 * ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) := by
    unfold runCAq
    push_cast
    ring
  have habs : (∑ i : Fin G.n, ∑ j : Fin G.n, |(QMCLeafB.wMatrix G i j : ℝ)|)
      = QMCLeafB.V (QMCLeafB.wMatrix G) := by
    unfold QMCLeafB.V
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => abs_of_nonneg (QMCLeafB.wMatrix_nonneg G i j)))
  rw [hcast, habs, QMCLeafB.V_wMatrix]

theorem runM_pos (G : QuantumMaxCutEnergy.Input) : 0 < runM G := by
  have h1 : (0 : ℚ) < 2 * runDq ^ 2 := by
    unfold runDq
    norm_num
  have h2 : (0 : ℚ) ≤ (G.n : ℚ) ^ 2 := sq_nonneg _
  unfold runM
  linarith

theorem runMcount_ge {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) : 1 ≤ runMcount G := by
  have h : 0 < G.n * G.n := Nat.mul_pos (by omega) (by omega)
  unfold runMcount
  exact Nat.succ_le_of_lt (Nat.mul_pos (by norm_num : 0 < 4) h)

theorem two_le_mul_self {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) : 2 ≤ G.n * G.n :=
  le_trans (by norm_num) (Nat.mul_le_mul hn hn)

/-! ## 3.  The inhabitant -/

/-- **`RunParams G` at `2 ≤ G.n`.**  Every field is a shelf theorem at the campaign's constants:
`hbudget` is `ClosingBracket.runData_hbudget_close`, `hhalve` is `runData_hhalve_close`. -/
noncomputable def runParams (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    QMCLeafB.FinalStroke.RunParams G where
  K := runK G
  m := runMcount G
  dq := runDq
  cAq := runCAq G
  rmax := runRmax
  hdq := runDq_pos
  hcAq := runCAq_nonneg G
  hAsum := by
    rw [runCAq_cast G]
  hrmax := runRmax_nonneg
  hhalve := by
    simpa only [runMcount, runRmax, Rat.cast_zero] using
      QMCLeafB.ClosingBracket.runData_hhalve_close (G.n * G.n) (two_le_mul_self hn)
  hbudget := by
    simpa only [runK, runMcount, runPhi, runRadius, runM, runDq] using
      QMCLeafB.ClosingBracket.runData_hbudget_close (n := G.n) (M := runM G)
        (runM_pos G) runDq (runCAq G) runDq_pos (runCAq_nonneg G)
        (m := runMcount G) (runMcount_ge hn)

/-! ## 4.  Integration: `endgame_of_parts` with `P` only at `2 ≤ G.n`

`FinalStroke.endgame_of_parts` asks for `P : ∀ G, RunParams G`, i.e. also at `n ≤ 1`, where the
shelf's `hhalve` theorem does not apply.  `hd` is read only at `2 ≤ G.n`, so the indexed form below
is strictly weaker and is what `runParams` supplies. -/

/-- **`d9f601e5` from a tape-free loop and the run half at `2 ≤ G.n`.**  Same as
`FinalStroke.endgame_of_parts`, with the numeric parameters indexed by the hypothesis `2 ≤ G.n`. -/
theorem endgame_of_hn_parts {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2)
    (P : ∀ G : QuantumMaxCutEnergy.Input, 2 ≤ G.n → QMCLeafB.FinalStroke.RunParams G)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), (hn : 2 ≤ G.n) →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict T0) G t (P G hn)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_of_tape_free_loop init fuel round verdict hinit hfuel hr hv
    sizes hsize hsize0 T0 hinitTape hfuelLen
    (fun G t hn hlo hhi => (hd G t hn hlo hhi).toRunData)

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.RunParamsSupply.runDq_pos
#print axioms QMCLeafB.RunParamsSupply.runCAq_nonneg
#print axioms QMCLeafB.RunParamsSupply.runCAq_cast
#print axioms QMCLeafB.RunParamsSupply.runM_pos
#print axioms QMCLeafB.RunParamsSupply.runMcount_ge
#print axioms QMCLeafB.RunParamsSupply.runParams
#print axioms QMCLeafB.RunParamsSupply.endgame_of_hn_parts

end QMCLeafB.RunParamsSupply


