-- Prove2me | Definitions.Def_QMCLeafB_ledgerG_union_m3
-- name    : QMCLeafB_ledgerG_union_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:04:37.166913+00:00
-- url     : https://prove2.me/theorems/756134a3-4d5d-4af9-aedd-d48df0f272b6
-- title:
--   QMCLeafB ledgerG_union_m3
-- statement:
--   # leaf B phase 16 — brick `ledgerg`, part 2: the consumption (swarm `smw1ez4a9`, member m3, d1)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ledgerG_m3
import Definitions.Def_QMCLeafB_unionShallow
/-
# leaf B phase 16 — brick `ledgerg`, part 2: the consumption (swarm `smw1ez4a9`, member m3, d1)

Companion of `Check_ledgerG_m3.lean`, split off so that the audited size brick does not depend on
m5's moving `UnionShallow` module.  Here `ledgerG_MszG : LedgerG MszG 6` is plugged into

* `QMCLeafB.UnionShallow.solution_union_shallow_gen` at `round = roundG`, `M = MszG`,
  `C₀ = 11448595`, `c = 6`, `kr = 6` — `solution_union_shallow_roundG` (generic round factor `Kf`)
  and `solution_union_shallow_init0` (at m1's `RStInit.init0`, `htop`/`hd` read at the shelf round);
* the campaign round factor `KfB2 = UnionShallow.Kbc2 (mHalve (n·n))`, whose fuel facts and count
  side condition m5 proved unconditionally — `solution_of_three_roundG`, and
  `solution_of_three_initRound`, whose residual is exactly brick 1 (`init`, `Poly`, tape-freeness,
  normalisation), brick 3 (`htop` at `2 ≤ G.n`) and brick 4 (`hd`).

`IntegrateM6.solution_of_bricks` cannot be used: it asks `htop` on the whole bracket, including
`G.n ≤ 1`, which is false (`TopSliceRange.htop_interior_false`).

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.CapGuard

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram
open QMCLeafB.RoundSizeM6
open QMCLeafB.GuardedRound

local instance instRequestCodingLedgerUnion :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 6b.  Consumption at m5's `UnionShallow.solution_union_shallow_gen` (the correct `htop` shape)

`IntegrateM6.solution_of_bricks` (§6) asks `htop` on the whole bracket, including `G.n ≤ 1`, where it
is *false* (`TopSliceRange.htop_interior_false`).  m5's `solution_union_shallow_gen` restricts it to
`2 ≤ G.n` — that is the stroke the campaign actually uses, and its size slot is exactly
`(hMinv, hstep, hM)`, which `ledgerG_MszG` discharges.  So the theorems below are the usable ones:
the residual is `htop` (brick 3), `hd` (brick 4), `init`/`hinitTape` (brick 1) and the count
side condition `hK` (brick 1). -/

theorem solution_union_shallow_roundG
    (Kf : QuantumMaxCutEnergy.Input → ℕ) (k : ℕ)
    (hKf : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)))
    (hseed : ∀ p : QMCLeafB.FuelWire.Pkg,
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
        ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k))
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt) (hinit : Automatic.Poly init)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init roundG QMCLeafB.RoundProgram.verdict
        (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init roundG QMCLeafB.RoundProgram.verdict
          (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf Kf hK G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.UnionShallow.solution_union_shallow_gen Kf k hKf hseed hK init roundG
    QMCLeafB.RoundProgram.verdict hinit poly_roundG QMCLeafB.RoundProgram.poly_verdict
    MszG 11448595 6 6 (by norm_num) MszG_roundG_le enc_roundG_le MszG_le_pow hinitTape htop hd

/-- **The same at m1's `RStInit.init0`, with `htop`/`hd` read at the shelf round.**  `roundG` and
`round` have the same loop bit from `init0` (`GuardedRound.loopBit_G_eq`), so this is the drop-in
stroke: it is `UnionShallow.solution_union_shallow_gen` at `init0`, `roundG`, with the size slot
deleted. -/
theorem solution_union_shallow_init0
    (Kf : QuantumMaxCutEnergy.Input → ℕ) (k : ℕ)
    (hKf : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)))
    (hseed : ∀ p : QMCLeafB.FuelWire.Pkg,
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
        ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k))
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
        QMCLeafB.RoundProgram.verdict
        (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf Kf hK G)) :
    QMCLeafB.FinishLine.SolutionStatement := by
  have hloop : QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundG
        QMCLeafB.RoundProgram.verdict
        (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))
      = QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
        QMCLeafB.RoundProgram.verdict
        (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) := by
    funext G' t'
    exact loopBit_G_eq (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G' t'
  exact solution_union_shallow_roundG Kf k hKf hseed hK QMCLeafB.RStInit.init0
    QMCLeafB.RStInit.poly_init0 QMCLeafB.RStInit.init0_tape
    (fun G t hn h1 h2 => by rw [hloop]; exact htop G t hn h1 h2)
    (fun G t hn hlo hhi => by rw [hloop]; exact hd G t hn hlo hhi)

/-! ## 6c.  The minimal residual: the campaign round factor `Kbc2`, size slot gone

m5's `Kbc2` already discharges the fuel `Poly`/seed facts and the count side condition
unconditionally, so instantiating §6b at it leaves only the three items owned by the other bricks:
`init`+`hinitTape` (brick 1), `htop` (brick 3), `hd` (brick 4). -/

/-- The campaign round factor at m2's halving time. -/
noncomputable def KfB2 (G : QuantumMaxCutEnergy.Input) : ℕ :=
  QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G

/-- **`SolutionStatement` from the three remaining bricks at the guarded round** — no size slot, no
count hypothesis, no fuel arithmetic. -/
theorem solution_of_three_roundG
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt) (hinit : Automatic.Poly init)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init roundG QMCLeafB.RoundProgram.verdict
        (fun G' _ => KfB2 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init roundG QMCLeafB.RoundProgram.verdict
          (fun G' _ => KfB2 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf KfB2
          (fun G => QMCLeafB.UnionShallow.shallowKbound_Kbc2 G) G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_union_shallow_roundG KfB2 k
    (QMCLeafB.UnionShallow.poly_Kbc2_mHalve_mul)
    (QMCLeafB.UnionShallow.Kbc2_mHalve_le_seed k hk)
    (fun G => QMCLeafB.UnionShallow.shallowKbound_Kbc2 G)
    init hinit hinitTape htop hd

/-- **The three-brick stroke with `htop`/`hd` read at the shelf round, for any normalised init.** -/
theorem solution_of_three_initRound
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt) (hinit : Automatic.Poly init)
    (hnorm : ∀ p : QMCLeafB.FuelWire.Pkg,
      (stX (init p)).length = stN (init p) * stN (init p))
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init QMCLeafB.RoundProgram.round
        QMCLeafB.RoundProgram.verdict
        (fun G' _ => KfB2 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => KfB2 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsShallowKf KfB2
          (fun G => QMCLeafB.UnionShallow.shallowKbound_Kbc2 G) G)) :
    QMCLeafB.FinishLine.SolutionStatement := by
  have hloop : QMCLeafB.FinalStroke.loopBit init roundG QMCLeafB.RoundProgram.verdict
        (fun G' _ => KfB2 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))
      = QMCLeafB.FinalStroke.loopBit init QMCLeafB.RoundProgram.round
        QMCLeafB.RoundProgram.verdict
        (fun G' _ => KfB2 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) := by
    funext G' t'
    exact loopBit_G_eq_of_normalised init hnorm
      (fun G' _ => KfB2 G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G' t'
  exact solution_of_three_roundG k hk init hinit hinitTape
    (fun G t hn h1 h2 => by rw [hloop]; exact htop G t hn h1 h2)
    (fun G t hn hlo hhi => by rw [hloop]; exact hd G t hn hlo hhi)

end QMCLeafB.CapGuard

/-! ## Axiom audit -/

#print axioms QMCLeafB.CapGuard.solution_union_shallow_roundG
#print axioms QMCLeafB.CapGuard.solution_union_shallow_init0
#print axioms QMCLeafB.CapGuard.solution_of_three_roundG
#print axioms QMCLeafB.CapGuard.solution_of_three_initRound


