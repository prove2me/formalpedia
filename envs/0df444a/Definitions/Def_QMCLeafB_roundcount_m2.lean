-- Prove2me | Definitions.Def_QMCLeafB_roundcount_m2
-- name    : QMCLeafB_roundcount_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:58:15.138163+00:00
-- url     : https://prove2.me/theorems/0f10490e-9884-4ec4-ba86-4ef5a97d89bb
-- title:
--   QMCLeafB roundcount_m2
-- statement:
--   # leaf B phase 13 — brick `round-count-enlarge` (swarm `smw17fqzz`, member m2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_runparams_m2
import Definitions.Def_QMCLeafB_final_stroke_m7
/-
# leaf B phase 13 — brick `round-count-enlarge` (swarm `smw17fqzz`, member m2)

The round-count factor `K` of `QMCLeafB.FinalStroke.RunParams` is *not* free: `hbudget` pins it to
be at least `SimLoop.simRounds`, and `hverdict` reads the prefix `K · m` of the run.  But
`SimLoop.simRounds` is a `Nat.clog` of a real ratio (`volPot/r^(n·n)`), so it is **not** computable
by a `Poly` program, while the loop's fuel length must be (`fuel`'s length is the round count, and
`hfuel : Automatic.Poly fuel`).  The shelf says as much: `Check_fuel.lean`'s `roundBudget_le_fuel_length`
exists exactly to compare a *monomial* budget with the fuel length.

This file supplies the missing degree of freedom:

* §1 `volPot_initShape_pos` — the initial potential is positive (needed to multiply an inequality by
  it).  This is `simRounds_budget`'s `hΦ` step, extracted.
* §2 **`runParams_bigger_K`** — `RunParams` may be re-instantiated at *any larger* round count
  `K' ≥ P.K`, keeping `m dq cAq rmax` and all their proofs.  Only `hbudget` changes, and it only gets
  easier: `(1/2)^(K') ≤ (1/2)^(P.K)`.

Consequence for the endgame: the fuel length may be taken to be `K' · m` for any `Poly`-computable
`K' ≥ simRounds …`, rather than `simRounds` itself — so `T0` can be a monomial, which is what
`fuelTake` needs.  (The remaining obligation is the *estimate* `simRounds … ≤ K'`, which is not on
the shelf.)

No `sorry`, no `axiom`; audit at the end.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.RoundCountEnlarge

open QuantumMaxCutEnergy

local instance instRequestCodingRoundCount : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  Positivity of the initial potential -/

theorem shapeM_pos (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) :
    (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 := by
  have h1 : (0 : ℚ) ≤ (G.n : ℚ) ^ 2 := sq_nonneg _
  have h2 : (0 : ℚ) < dq ^ 2 := by
    have := hdq
    positivity
  nlinarith

/-- The initial potential `volPot (n·n) (initShapeOf (n·n) M)` is strictly positive. -/
theorem volPot_initShape_pos (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) :
    0 < QMCLeafB.EngineIterates.volPot (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2)) :=
  QMCLeafB.EngineIterates.volPot_pos
    (QMCLeafB.Boundary.initShapeOf_cast_posDef (shapeM_pos G hdq))

/-! ## 2.  Enlarging the round count -/

/-- **`RunParams` at any larger round count.**  Everything but `hbudget` is copied; `hbudget`
improves because `(1/2)^K` decreases in `K`.  So the choice `K := simRounds …` may be replaced by
any `Poly`-computable `K' ≥ simRounds …` — which is what the fuel slot needs. -/
noncomputable def runParams_bigger_K {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G) (K' : ℕ) (hK : P.K ≤ K') :
    QMCLeafB.FinalStroke.RunParams G where
  K := K'
  m := P.m
  dq := P.dq
  cAq := P.cAq
  rmax := P.rmax
  hdq := P.hdq
  hcAq := P.hcAq
  hAsum := P.hAsum
  hrmax := P.hrmax
  hhalve := P.hhalve
  hbudget := by
    refine lt_of_le_of_lt ?_ P.hbudget
    refine mul_le_mul_of_nonneg_left ?_
      (le_of_lt (volPot_initShape_pos G P.hdq))
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hK

/-- `runParams_bigger_K` at the same count is the original bundle (definitional check of the fields
that matter downstream). -/
theorem runParams_bigger_K_K {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G) :
    (runParams_bigger_K P P.K (le_refl _)).K = P.K ∧
    (runParams_bigger_K P P.K (le_refl _)).m = P.m ∧
    (runParams_bigger_K P P.K (le_refl _)).dq = P.dq :=
  ⟨rfl, rfl, rfl⟩

/-- The larger bundle's round count is exactly `K'`. -/
theorem runParams_bigger_K_K' {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G) (K' : ℕ) (hK : P.K ≤ K') :
    (runParams_bigger_K P K' hK).K = K' := rfl

/-! ## 3.  Axiom audit -/

#print axioms QMCLeafB.RoundCountEnlarge.shapeM_pos
#print axioms QMCLeafB.RoundCountEnlarge.volPot_initShape_pos
#print axioms QMCLeafB.RoundCountEnlarge.runParams_bigger_K
#print axioms QMCLeafB.RoundCountEnlarge.runParams_bigger_K_K'

end QMCLeafB.RoundCountEnlarge


