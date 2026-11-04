-- Prove2me | Definitions.Def_QMCLeafB_roundwrepoint
-- name    : QMCLeafB_roundwrepoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:54:56.783471+00:00
-- url     : https://prove2.me/theorems/8ebe17d4-9256-4e22-958b-1d5620301052
-- title:
--   QMCLeafB roundwrepoint
-- statement:
--   # leaf B phase 22 - brick `roundw-repoint` (swarm `smw1ntur6`, member m4, direction 4)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_htop_ledgerW_m7
import Definitions.Def_QMCLeafB_assembly_m5
import Definitions.Def_QMCLeafB_residb_m7
import Definitions.Def_QMCLeafB_endgame_m2
import Definitions.Def_QMCLeafB_verdbridge
import Definitions.Def_QMCLeafB_emptybottom
/-
# leaf B phase 22 - brick `roundw-repoint` (swarm `smw1ntur6`, member m4, direction 4)

Phase 21's verdict-bridge brick (`Check_verdbridge_m4`) showed that the residual's verdict slot
`hverdict` is **false** at the shelf round `RoundProgram.round` (the shelf's `ok` answer is the
*upper* event `stT <= fvR`, while `FlagsM5.flagOf` asks for the *lower* body) and **true** at
the reported round `OkLower.roundW` (`flag_true_of_okV`, `oracleV_ok_of_mem`,
`hverdict_at_roundW`).  This file does the consequence: it reruns the *whole closing chain* with the
programme bit

    oW  :=  loopBit InitDq.init0 OkLower.roundW RoundProgram.verdict Tbc2

in place of `loopBit InitDq.init0 RoundProgram.round RoundProgram.verdict Tbc2`, and it discharges
the obligations a repoint owes:

* **the residual and the strokes at `oW`** (section 2): `ResidFiniteB oW paramsKbc2` (m7's
  horizon-bounded shape), the supplier-friendly `ResidG oW paramsKbc2` (m2's `Check_endgame_m2`),
  `ResidH oW paramsKbc2` (the `ResidWin` of `FlagsM5`), and the verbatim `d9f601e5` sentence from any
  of them.  The ending is `LedgerW.solution_roundWG_of_init_hd_round`, the `roundW` stroke that
  phase 16 built for exactly this round (`Check_htop_ledgerW_m7`), with its `Poly`/size/`htop` slots
  all discharged - so the repoint is its application, not a re-derivation of the assembly.

* **the verdict slot at `oW`** (section 3): `hverdict` is no longer a hypothesis.
  `hverdict_at_roundW0` composes phase 21's `hverdict_at_roundW` with the campaign's init facts
  (`Tbc2 G t = K*m`, the regime test at an interior `t`, the empty `ok` record), and
  `coreDataB_at_roundW` / `residBW_of_state_data` turn per-round state read-outs plus the two drift
  slots into `ResidB_M7.CoreDataB oW ...`.  At `RoundProgram.round` the same slot is refuted.

* **the checksum** (section 4): `bit_false_at_all_bottoms` at `oW` from the residual, plus the
  *state-level* form `okV_cut_at_bottom` - at the bracket's bottom `t = -Rq G` the lower-body oracle
  reports a cut at **every** state that carries the campaign's level data, because its `ok` answer is
  a `RelaxMem` certificate there while the pinched body at the bottom is empty
  (`Sliver2M8.flagOf_false_at_bottom`).  So the programme the repoint installs meets the necessary
  condition the record route imposes on any programme (`RecordsM2.bit_false_at_all_bottoms`), and the
  bottom needs no drift data at all.

Dependencies (all phase-21-accepted, none edited): `Check_verdbridge_m4`, `Check_residb_m7`,
`Check_endgame_m2`, `Check_emptybottom_m1`, `Check_htop_ledgerW_m7`, `Check_assembly_m5`.  Feeds
direction 7 (integration) and direction 6 (ok-production).

House discipline: `set_option autoImplicit false`; a `#print`-trace after every declaration (all 24
of them are exactly `[propext, Classical.choice, Quot.sound]`); none of the disallowed
proof-escape tokens of the library discipline occurs anywhere in this file outside the `#print`
audits themselves; the strict-subset symbol is not used.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.RoundWRepoint

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram
open QMCLeafB.FinalStroke (loopBit noTape)
open QMCLeafB.OkLower (roundW okW oracleV dqOf levelOf)

local instance instCodingRoundW : OAI.MetricKMedian.Binary.Automatic.Coding
    (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The reported-round programme bit -/

/-- **The programme bit of the repointed chain.**  Same initial state, same fuel, same verdict
read-out; the round is the lower-body round `OkLower.roundW`. -/
def oW : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  loopBit QMCLeafB.InitDq.init0 roundW QMCLeafB.RoundProgram.verdict
    QMCLeafB.ClosingAssembly.Tbc2

theorem oW_apply (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    oW G t = QMCLeafB.RoundProgram.verdict
      (roundW^[QMCLeafB.ClosingAssembly.Tbc2 G t]
        (QMCLeafB.InitDq.init0 (noTape G t))) := rfl

#print axioms QMCLeafB.RoundWRepoint.oW_apply

/-- **The orbit of the reported round** from the campaign state, round by round. -/
def runW0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) : ℕ → RoundProgram.RSt :=
  fun k => roundW^[k] (QMCLeafB.InitDq.init0 (noTape G t))

theorem runW0_zero (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    runW0 G t 0 = QMCLeafB.InitDq.init0 (noTape G t) := rfl

theorem runW0_succ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    runW0 G t (k + 1) = roundW (runW0 G t k) := by
  unfold runW0
  rw [Function.iterate_succ_apply']

/-- **The fuel is the horizon**: at the campaign family, `Tbc2` is exactly `K*m`. -/
theorem hKm_Tbc2 (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.ClosingAssembly.Tbc2 G t
      = (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m := rfl

#print axioms QMCLeafB.RoundWRepoint.hKm_Tbc2

/-- **The regime test at an interior threshold fails**: below the campaign slack `roundW` is the
engine branch (`roundV`), i.e. the lower-body round. -/
theorem not_top_at_interior {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    ¬ 0 ≤ stT (QMCLeafB.InitDq.init0 (noTape G t))
        + QMCLeafB.RoundT.epsOf (QMCLeafB.InitDq.init0 (noTape G t)) :=
  QMCLeafB.RoundGUEndgame.not_top_of_init QMCLeafB.InitDq.init0
    QMCLeafB.InitDq.stT_init0 QMCLeafB.AssemblyM5.epsOf_init0_any G t hhi

#print axioms QMCLeafB.RoundWRepoint.not_top_at_interior

theorem hoks_init0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    stOks (QMCLeafB.InitDq.init0 (noTape G t)) = [] :=
  QMCLeafB.InitDq.stOks_init0 _

#print axioms QMCLeafB.RoundWRepoint.hoks_init0


/-! ## 2.  The residual and the closing strokes, at `oW` -/

/-- **The repointed residual**: m7's `ResidFiniteB` at the campaign family, at the reported-round
bit `oW`. -/
abbrev ResidBW : Type :=
  QMCLeafB.ResidB_M7.ResidFiniteB oW QMCLeafB.UnionShallow.paramsKbc2

/-- **The repointed supplier-friendly residual** (m2's `CoreDataG`) at `oW`. -/
abbrev ResidGW : Type :=
  QMCLeafB.EndgameM2.ResidG oW QMCLeafB.UnionShallow.paramsKbc2

/-- **`ResidWin` at `oW`** - `FlagsM5.ResidH`, the corrected bundle residual, at the reported
round. -/
def residWin_at_roundW (H : ResidBW) :
    QMCLeafB.FlagsM5.ResidH oW QMCLeafB.UnionShallow.paramsKbc2 :=
  QMCLeafB.ResidB_M7.residH_of_finiteB
    (fun G hn => QMCLeafB.RecordsM2.rmax_pos_paramsKbc2 G hn) H

#print axioms QMCLeafB.RoundWRepoint.residWin_at_roundW

/-- **`ResidWin` at `oW` from the supplier-friendly residual.** -/
def residWin_of_supplied (H : ResidGW) :
    QMCLeafB.FlagsM5.ResidH oW QMCLeafB.UnionShallow.paramsKbc2 :=
  QMCLeafB.EndgameM2.residH_of_supplied
    (fun G hn => QMCLeafB.RecordsM2.rmax_pos_paramsKbc2 G hn) H

#print axioms QMCLeafB.RoundWRepoint.residWin_of_supplied

/-- **The run bundle at the reported round** - `FinalStroke.RunParts` for the `hd` conduit, from the
repointed residual. -/
def hdW_at_roundW (H : ResidBW) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (loopBit QMCLeafB.InitDq.init0 roundW QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hlo hhi
  exact QMCLeafB.FlagsM5.runParts_of_bundleH oW G t
    (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.UnionShallow.paramsKbc2_rmax_pos G hn)
    (QMCLeafB.AssemblyM5.rmax_le_one G hn)
    (QMCLeafB.AssemblyM5.budget_at_interior G t hn hlo hhi)
    (residWin_at_roundW H G t hn hlo hhi)

#print axioms QMCLeafB.RoundWRepoint.hdW_at_roundW

/-- **The run bundle from the supplier-friendly residual.** -/
def hdW_of_supplied (H : ResidGW) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (loopBit QMCLeafB.InitDq.init0 roundW QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hlo hhi
  exact QMCLeafB.FlagsM5.runParts_of_bundleH oW G t
    (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.UnionShallow.paramsKbc2_rmax_pos G hn)
    (QMCLeafB.AssemblyM5.rmax_le_one G hn)
    (QMCLeafB.AssemblyM5.budget_at_interior G t hn hlo hhi)
    (residWin_of_supplied H G t hn hlo hhi)

#print axioms QMCLeafB.RoundWRepoint.hdW_of_supplied

/-- **`d9f601e5` at the reported round, in the shelf's own name for the sentence.**  The ending is
`LedgerW.solution_roundWG_of_init_hd_round`: its `Poly`, size-ledger and `htop` slots are phase 16's,
its `hd` slot is `hdW_at_roundW`. -/
theorem solution_statement_at_roundW (H : ResidBW) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.LedgerW.solution_roundWG_of_init_hd_round QMCLeafB.InitDq.init0 20
    (by norm_num : 20 ≤ 2 ^ 20) QMCLeafB.InitDq.poly_init0 QMCLeafB.InitDq.init_normalised
    QMCLeafB.InitDq.stT_init0 QMCLeafB.AssemblyM5.epsOf_init0_any QMCLeafB.InitDq.stOks_init0
    QMCLeafB.InitDq.init0_tape (hdW_at_roundW H)

#print axioms QMCLeafB.RoundWRepoint.solution_statement_at_roundW

/-- **`d9f601e5` verbatim at the reported round.**  The `exists L, Nonempty (TM2 ...) and forall G,
exists S, ...` sentence is `SolutionStatement` definitionally (the shelf's
`solutionStatement_iff_wMatrix` is `Iff.rfl`), so the ascription below *is* the statement lock. -/
theorem solution_at_roundW (H : ResidBW) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  solution_statement_at_roundW H

#print axioms QMCLeafB.RoundWRepoint.solution_at_roundW


/-! ## 3.  The verdict slot at `oW`, discharged

`hverdict` is the one field of the record that is *refuted* at the shelf round and *true* at the
reported round.  Here it stops being a hypothesis: the campaign init facts are discharged (§3.1),
and the per-round state read-outs that phase 21's `hverdict_at_roundW` asks for are read off the
orbit `runW0` (§3.2: `stN`, `stX`-length, `stA`, `stT`, `epsOf`, `dqOf` are all invariants of the
round).  What remains (§3.3) is: the symmetry of the run's states, the exact descent's `false` at
`ok` rounds, the two flag-conditioned state facts, and the two drift slots - i.e. exactly the
production directions' obligation, with no verdict equation among them. -/

/-! ### 3.1  The campaign init facts at `oW` -/

/-- `stN` is frozen by `roundV`. -/
theorem stN_roundV (s : RSt) : stN (QMCLeafB.OkLower.roundV s) = stN s := by
  unfold QMCLeafB.OkLower.roundV
  by_cases hh : (oracleV s).1
  · rw [if_pos hh]
    rfl
  · rw [if_neg hh]
    exact QMCLeafB.GuardedRound.stN_roundOk s

/-- `stN` is frozen by the reported round. -/
theorem stN_roundW (s : RSt) : stN (roundW s) = stN s := by
  unfold roundW
  by_cases h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [if_pos h]
    exact QMCLeafB.GuardedRound.stN_roundOk s
  · rw [if_neg h]
    exact stN_roundV s

theorem stN_iterateW (s : RSt) (k : ℕ) : stN (roundW^[k] s) = stN s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stN_roundW, ih]

theorem stN_runW0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    stN (runW0 G t k) = G.n := by
  unfold runW0
  rw [stN_iterateW, QMCLeafB.InitDq.stN_init0]
  rfl

#print axioms QMCLeafB.RoundWRepoint.stN_runW0

/-- **The squared-length invariant of the reported round**: from a normalised state, `roundW` keeps
`|X| = n*n`.  (`roundOk` freezes `X`; `roundV`'s cut branch is `LedgerW.roundV_normalised`.) -/
theorem stX_length_roundW (s : RSt) (hn : (stX s).length = stN s * stN s) :
    (stX (roundW s)).length = stN (roundW s) * stN (roundW s) := by
  unfold roundW
  by_cases h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [if_pos h, QMCLeafB.GuardedRound.stX_roundOk, QMCLeafB.GuardedRound.stN_roundOk]
    exact hn
  · rw [if_neg h]
    exact QMCLeafB.LedgerW.roundV_normalised s hn

theorem stX_length_iterateW (s : RSt) (hn : (stX s).length = stN s * stN s) (k : ℕ) :
    (stX (roundW^[k] s)).length
      = stN (roundW^[k] s) * stN (roundW^[k] s) := by
  induction k with
  | zero => simpa using hn
  | succ j ih => rw [Function.iterate_succ_apply']; exact stX_length_roundW _ ih

theorem stX_length_runW0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    (stX (runW0 G t k)).length = G.n * G.n := by
  unfold runW0
  rw [stX_length_iterateW _ (QMCLeafB.InitDq.init_normalised (noTape G t)) k,
    stN_iterateW, QMCLeafB.InitDq.stN_init0]
  rfl

#print axioms QMCLeafB.RoundWRepoint.stX_length_runW0

/-- **The weight code at the campaign state is `wMatrixQ G`.** -/
theorem stMat_stA_init0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.StateDiag.stMat G.n (stA (QMCLeafB.InitDq.init0 (noTape G t)))
      = QMCLeafB.Finalization.wMatrixQ G := by
  have h := (QMCLeafB.InitDq.stA_correct_noTape G t).2
  ext i j
  exact h i j

theorem stMat_stA_runW0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.StateDiag.stMat G.n (stA (runW0 G t k))
      = QMCLeafB.Finalization.wMatrixQ G := by
  unfold runW0
  rw [QMCLeafB.OkLower.stA_iterateW]
  exact stMat_stA_init0 G t

theorem stA_length_runW0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    G.n ≤ (stA (runW0 G t k)).length := by
  have h := (QMCLeafB.InitDq.stA_correct_noTape G t).1
  have h2 : (stA (runW0 G t k)).length
      = (stA (QMCLeafB.InitDq.init0 (noTape G t))).length := by
    unfold runW0
    rw [QMCLeafB.OkLower.stA_iterateW]
  rw [h2, h]
  nlinarith

#print axioms QMCLeafB.RoundWRepoint.stA_length_runW0

theorem stT_runW0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    stT (runW0 G t k) = t := by
  unfold runW0
  rw [QMCLeafB.OkLower.stT_iterateW]
  exact QMCLeafB.InitDq.stT_init0 _

theorem epsOf_runW0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundT.epsOf (runW0 G t k) = QMCLeafB.EngineRuntime.Rq G / 40000 := by
  have hA : stA (runW0 G t k) = stA (QMCLeafB.InitDq.init0 (noTape G t)) := by
    unfold runW0
    rw [QMCLeafB.OkLower.stA_iterateW]
  exact (QMCLeafB.HtopFinish.epsOf_congr hA).trans
    (QMCLeafB.AssemblyM5.epsOf_init0_any (noTape G t))

theorem massV_runW0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundT.massV (runW0 G t k) = QMCLeafB.EngineRuntime.Rq G := by
  have hA : stA (runW0 G t k) = stA (QMCLeafB.InitDq.init0 (noTape G t)) := by
    unfold runW0
    rw [QMCLeafB.OkLower.stA_iterateW]
  have h1 : QMCLeafB.RoundT.massV (runW0 G t k)
      = QMCLeafB.RoundT.massV (QMCLeafB.InitDq.init0 (noTape G t)) := by
    unfold QMCLeafB.RoundT.massV
    rw [hA]
  have h2 : QMCLeafB.RoundT.massV (QMCLeafB.InitDq.init0 (noTape G t))
      = QMCLeafB.RoundT.massV (QMCLeafB.RStInit.init0 (noTape G t)) := by
    unfold QMCLeafB.RoundT.massV
    rw [QMCLeafB.AssemblyM5.stA_init0_eq]
  rw [h1, h2]
  exact QMCLeafB.HtopFinish.massV_init0 (noTape G t)

/-- **`dqShallow` is the campaign quotient** in the positive-weight regime. -/
theorem dqShallow_eq_dqOf (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallow G
      = QMCLeafB.RundataCert.eps G / (9 * QMCLeafB.EngineRuntime.Rq G + 1) := by
  unfold QMCLeafB.RundataParams.dqShallow QMCLeafB.RundataCert.eps
  rw [if_neg (ne_of_gt hRq)]
  rfl

theorem dqOf_runW0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    dqOf (runW0 G t k) = QMCLeafB.RundataParams.dqShallow G := by
  unfold dqOf
  rw [epsOf_runW0, massV_runW0, dqShallow_eq_dqOf G hRq]
  rfl

#print axioms QMCLeafB.RoundWRepoint.dqOf_runW0

theorem paramsKbc2_dq_pos (G : QuantumMaxCutEnergy.Input) :
    0 < (QMCLeafB.UnionShallow.paramsKbc2 G).dq := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
  exact QMCLeafB.RundataParams.dqShallow_pos G

theorem paramsKbc2_dq_le_four (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.UnionShallow.paramsKbc2 G).dq ≤ 4 := by
  have he : QMCLeafB.RundataCert.eps G ≤ QMCLeafB.EngineRuntime.Rq G := by
    unfold QMCLeafB.RundataCert.eps
    rw [div_le_iff₀ (by norm_num : (0 : ℚ) < 40000)]
    linarith [QMCLeafB.RundataArith.Rq_nonneg G]
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
  unfold QMCLeafB.RundataParams.dqShallow QMCLeafB.RundataParams.dqShallowCore
  split_ifs with h
  · norm_num
  · have hpos : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1 := by
      linarith [QMCLeafB.RundataArith.Rq_nonneg G]
    rw [div_le_iff₀ hpos]
    linarith [QMCLeafB.RundataArith.Rq_nonneg G]

#print axioms QMCLeafB.RoundWRepoint.paramsKbc2_dq_le_four

/-! ### 3.2  The verdict equation at `oW` from the per-round state data -/

open QMCLeafB.FlagsM5 (flagOf) in
/-- **`hverdict` at the reported-round programme, from the state plugs.**  All the *init* facts and
all the *invariants of the round* are discharged here (`hKm_Tbc2`, `not_top_at_interior`,
`hoks_init0`, `stN_runW0`, `stX_length_runW0`, `stA_length_runW0`, `stMat_stA_runW0`,
`stT_runW0`, `epsOf_runW0`, `dqOf_runW0`, and the campaign tolerance's own two bounds); what is left
is the state's symmetry, the exact descent's `false` at `ok` rounds, and two flag-conditioned state
facts (the `hoff` plugs) — exactly the production directions' obligation.  At
`RoundProgram.round` the same equation is refuted, so this is what the repoint buys. -/
theorem hverdict_at_roundW0 {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (X : ℕ → List ℚ) (acc : ℕ → QMCLeafB.PivotProgram.Acc)
    (hX : ∀ k, X k = stX (runW0 G t k))
    (hsym : ∀ (k : ℕ) (i j : Fin G.n),
      QMCLeafB.StateDiag.stMat G.n (stX (runW0 G t k)) i j
        = QMCLeafB.StateDiag.stMat G.n (stX (runW0 G t k)) j i)
    (hpiv : ∀ k, okW (runW0 G t k) = true →
      (QMCLeafB.PivotProgram.runPiv
        (toRows (G.n, stX (runW0 G t k)), acc k)).1 = false)
    (hdv : ∀ k, flagOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
        (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k = true →
      dvR (runW0 G t k) = 0)
    (hpivf : ∀ k, flagOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
        (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k = true →
      (pivCut (runW0 G t k)).1 = false) :
    oW G t = QMCLeafB.SimLoop.anyOk
      (flagOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
        (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq))
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m) := by
  have hRq : 0 < QMCLeafB.EngineRuntime.Rq G :=
    QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi
  refine QMCLeafB.VerdictBridge.hverdict_at_roundW (init := QMCLeafB.InitDq.init0)
    (T0 := QMCLeafB.ClosingAssembly.Tbc2) (P := QMCLeafB.UnionShallow.paramsKbc2 G)
    (not_top_at_interior hhi) (hoks_init0 G t)
    (hKm_Tbc2 G t) X acc hX ?_ ?_ ?_ ?_ hsym hpiv hdv hpivf
    (paramsKbc2_dq_pos G) (paramsKbc2_dq_le_four G) ?_ ?_
  · intro k
    show stN (runW0 G t k) = G.n
    exact stN_runW0 G t k
  · intro k
    show G.n ≤ (stA (runW0 G t k)).length
    exact stA_length_runW0 G t k
  · intro k
    show G.n ≤ (stX (runW0 G t k)).length
    rw [stX_length_runW0 G t k]
    exact Nat.le_mul_self G.n
  · intro k
    show QMCLeafB.StateDiag.stMat G.n (stA (runW0 G t k))
      = QMCLeafB.Finalization.wMatrixQ G
    exact stMat_stA_runW0 G t k
  · intro k
    show stT (runW0 G t k) - QMCLeafB.RoundT.epsOf (runW0 G t k)
      = t - QMCLeafB.RundataCert.eps G
    rw [stT_runW0, epsOf_runW0]
    rw [show QMCLeafB.RundataCert.eps G = QMCLeafB.EngineRuntime.Rq G / 40000 from rfl]
  · intro k
    show dqOf (runW0 G t k) = (QMCLeafB.UnionShallow.paramsKbc2 G).dq
    rw [dqOf_runW0 G t k hRq, QMCLeafB.UnionShallow.paramsKbc2_dq]

#print axioms QMCLeafB.RoundWRepoint.hverdict_at_roundW0

/-! ### 3.3  The record at `oW`: `hverdict` supplied, the drift pair still owed -/

open QMCLeafB.FlagsM5 (flagOf) in
/-- **`CoreDataB` at the reported-round programme** from the per-round state data.  The verdict field
is `hverdict_at_roundW0`; the two drift fields are passed through untouched, because they are the
crater's content (phase 21's one open obligation) and not a verdict question. -/
def coreDataB_at_roundW {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (X : ℕ → List ℚ) (acc : ℕ → QMCLeafB.PivotProgram.Acc)
    (hX : ∀ k, X k = stX (runW0 G t k))
    (hsym : ∀ (k : ℕ) (i j : Fin G.n),
      QMCLeafB.StateDiag.stMat G.n (stX (runW0 G t k)) i j
        = QMCLeafB.StateDiag.stMat G.n (stX (runW0 G t k)) j i)
    (hpiv : ∀ k, okW (runW0 G t k) = true →
      (QMCLeafB.PivotProgram.runPiv
        (toRows (G.n, stX (runW0 G t k)), acc k)).1 = false)
    (hdv : ∀ k, flagOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
        (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k = true →
      dvR (runW0 G t k) = 0)
    (hpivf : ∀ k, flagOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
        (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k = true →
      (pivCut (runW0 G t k)).1 = false)
    (hdriftc : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m →
      flagOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
        (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k = false →
      (fun i => ((QMCLeafB.RecordsM2.nrmOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
            (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RecordsM2.cutStream G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn
                (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq)) k
            - QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat
                  (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq k)))
        ≤ ((QMCLeafB.RecordsM2.margOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
            (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m →
      flagOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
        (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k = false →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RecordsM2.cutStream G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn
                (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq)) k
            - QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat
                  (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq k)))
        ≤ 0) :
    QMCLeafB.ResidB_M7.CoreDataB oW G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn where
  X := X
  hsym := fun k => by
    ext i j
    simp only [Matrix.transpose_apply]
    rw [hX k]
    exact hsym k j i
  hdriftc := hdriftc
  hdriftd := hdriftd
  hverdict := hverdict_at_roundW0 hlo hhi X acc hX hsym hpiv hdv hpivf

#print axioms QMCLeafB.RoundWRepoint.coreDataB_at_roundW

/-! ## 4.  The checksum: the programme is `false` at every bottom

`RecordsM2.bit_false_at_all_bottoms` is the necessary condition the record route imposes on any
programme: if a horizon-bounded record exists at every interior threshold, then the programme's bit
at `t = -Rq G` is `false`.  A repoint that failed it would be dead.  It holds here in two forms: from
the residual (§4.1) and, more usefully, *state by state* (§4.2), where the reason is visible: at the
bottom the lower-body oracle's `ok` answer would be a `RelaxMem` certificate, and the pinch body at
the bottom is empty.  §4.3 is the run-level conclusion. -/

/-- **m7's record is `RecordsM2`'s `CoreDataHb`**: two names for the same five fields. -/
def coreDataHb_at_roundW {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (D : QMCLeafB.ResidB_M7.CoreDataB oW G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn) :
    QMCLeafB.RecordsM2.CoreDataHb oW G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn where
  X := D.X
  hsym := D.hsym
  hdriftc := D.hdriftc
  hdriftd := D.hdriftd
  hverdict := D.hverdict

#print axioms QMCLeafB.RoundWRepoint.coreDataHb_at_roundW

/-- **The verdict-lane checksum at `oW`**: any repointed residual forces the programme's bit at the
bracket's bottom to be `false`. -/
theorem checksum_at_roundW (H : ResidBW) {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    oW G (-QMCLeafB.EngineRuntime.Rq G) = false :=
  QMCLeafB.RecordsM2.bit_false_at_all_bottoms
    (fun G t hn hlo hhi => coreDataHb_at_roundW (H G t hn hlo hhi))
    hn hRq (QMCLeafB.UnionShallow.paramsKbc2_dq G)

#print axioms QMCLeafB.RoundWRepoint.checksum_at_roundW

open QMCLeafB.FlagsM5 (flagOf) in
/-- **The bottom has no `ok` round, state by state.**  At `t = -Rq G` the lower-body oracle reports a
*cut* at every state that carries the campaign's level data: an `ok` answer would make the state's
pinched centre a member of the lower body (`VerdictBridge.flag_true_of_okV`), while at the bottom no
matrix is a member at all (`Sliver2M8.flagOf_false_at_bottom`).  No drift data, no horizon and no
verdict equation is involved. -/
theorem okV_cut_at_bottom {G : QuantumMaxCutEnergy.Input}
    {P : QMCLeafB.FinalStroke.RunParams G} {s : RSt}
    {acc : QMCLeafB.PivotProgram.Acc}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdqP : P.dq = QMCLeafB.RundataParams.dqShallow G)
    (hN : stN s = G.n) (hlenA : G.n ≤ (stA s).length) (hlenX : G.n ≤ (stX s).length)
    (hA : QMCLeafB.StateDiag.stMat G.n (stA s) = QMCLeafB.Finalization.wMatrixQ G)
    (hsym : ∀ i j, QMCLeafB.StateDiag.stMat G.n (stX s) i j
      = QMCLeafB.StateDiag.stMat G.n (stX s) j i)
    (hT : stT s - QMCLeafB.RoundT.epsOf s
      = (-QMCLeafB.EngineRuntime.Rq G) - QMCLeafB.RundataCert.eps G)
    (hdq : dqOf s = P.dq) (hdqpos : 0 < P.dq) (hdq4 : P.dq ≤ 4)
    (hpiv : (oracleV s).1 = false →
      (QMCLeafB.PivotProgram.runPiv
        (toRows (G.n, stX s), acc)).1 = false) :
    (oracleV s).1 = true := by
  by_contra h
  have hok : (oracleV s).1 = false := by
    cases h' : (oracleV s).1 with
    | false => rfl
    | true => exact absurd h' h
  have htrue := QMCLeafB.VerdictBridge.flag_true_of_okV (G := G) (t := -QMCLeafB.EngineRuntime.Rq G)
    (P := P) (X := fun _ => stX s) (s := s) (acc := acc) (k := 0)
    hN hlenA hlenX hA hsym rfl hok (hpiv hok) hdqpos hdq4 hT hdq
  have hfalse := QMCLeafB.Sliver2M8.flagOf_false_at_bottom P hRq hdqP
    (QMCLeafB.RecordsM2.cXst G.n (fun _ => stX s) P.dq) 0
  rw [htrue] at hfalse
  exact absurd hfalse (by simp)

#print axioms QMCLeafB.RoundWRepoint.okV_cut_at_bottom

/-- **The run-level corollary**: at the bracket's bottom the programme's bit is `false`, from the
state's symmetry and the exact descent's `false` at `ok` rounds alone — the two plugs every record
producer already carries.  (Nothing else: the level data, the tolerance and the regime test are
discharged inside.) -/
theorem oW_false_at_bottom {G : QuantumMaxCutEnergy.Input}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (acc : ℕ → QMCLeafB.PivotProgram.Acc)
    (hsym : ∀ (k : ℕ) (i j : Fin G.n),
      QMCLeafB.StateDiag.stMat G.n (stX (runW0 G (-QMCLeafB.EngineRuntime.Rq G) k)) i j
        = QMCLeafB.StateDiag.stMat G.n (stX (runW0 G (-QMCLeafB.EngineRuntime.Rq G) k)) j i)
    (hpiv : ∀ k, (oracleV (runW0 G (-QMCLeafB.EngineRuntime.Rq G) k)).1 = false →
      (QMCLeafB.PivotProgram.runPiv
        (toRows (G.n, stX (runW0 G (-QMCLeafB.EngineRuntime.Rq G) k)), acc k)).1 = false) :
    oW G (-QMCLeafB.EngineRuntime.Rq G) = false := by
  rw [oW_apply G (-QMCLeafB.EngineRuntime.Rq G),
    QMCLeafB.OkLower.verdict_iterate_eq_anyOk_W _ (hoks_init0 G (-QMCLeafB.EngineRuntime.Rq G))
      (QMCLeafB.ClosingAssembly.Tbc2 G (-QMCLeafB.EngineRuntime.Rq G))]
  refine (QMCLeafB.SimLoop.anyOk_eq_false_iff _ _).mpr (fun k _ => ?_)
  have hstT : stT (runW0 G (-QMCLeafB.EngineRuntime.Rq G) k)
      = -QMCLeafB.EngineRuntime.Rq G := stT_runW0 G _ k
  have hreg : ¬ 0 ≤ stT (runW0 G (-QMCLeafB.EngineRuntime.Rq G) k)
      + QMCLeafB.RoundT.epsOf (runW0 G (-QMCLeafB.EngineRuntime.Rq G) k) := by
    rw [hstT, epsOf_runW0]
    have hpos : (0 : ℚ) < QMCLeafB.EngineRuntime.Rq G := hRq
    linarith
  have hcut : (oracleV (runW0 G (-QMCLeafB.EngineRuntime.Rq G) k)).1 = true :=
    okV_cut_at_bottom (G := G) (P := QMCLeafB.UnionShallow.paramsKbc2 G)
      (s := runW0 G (-QMCLeafB.EngineRuntime.Rq G) k) (acc := acc k)
      hRq (QMCLeafB.UnionShallow.paramsKbc2_dq G)
      (stN_runW0 G _ k)
      (stA_length_runW0 G _ k)
      (by rw [stX_length_runW0 G _ k]; exact Nat.le_mul_self G.n)
      (stMat_stA_runW0 G _ k) (hsym k)
      (by
        rw [hstT, epsOf_runW0]
        rw [show QMCLeafB.RundataCert.eps G = QMCLeafB.EngineRuntime.Rq G / 40000 from rfl])
      (dqOf_runW0 G _ k hRq) (paramsKbc2_dq_pos G) (paramsKbc2_dq_le_four G) (hpiv k)
  have h1 : okW (roundW^[k] (QMCLeafB.InitDq.init0 (noTape G (-QMCLeafB.EngineRuntime.Rq G))))
      = okW (runW0 G (-QMCLeafB.EngineRuntime.Rq G) k) := rfl
  rw [h1]
  unfold okW
  rw [if_neg hreg, hcut]
  rfl

#print axioms QMCLeafB.RoundWRepoint.oW_false_at_bottom

/-! ## 5.  Bridges between the two repointed shapes, and the supplier-friendly checksum -/

/-- **m7's record is m2's record**: the two `CoreDataB` copies have the same five fields. -/
def endgameCoreDataB_at_roundW {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (D : QMCLeafB.ResidB_M7.CoreDataB oW G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn) :
    QMCLeafB.EndgameM2.CoreDataB oW G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn where
  X := D.X
  hsym := D.hsym
  hdriftc := D.hdriftc
  hdriftd := D.hdriftd
  hverdict := D.hverdict

#print axioms QMCLeafB.RoundWRepoint.endgameCoreDataB_at_roundW

/-- **`ResidG` at `oW` from `ResidB` at `oW`** — the supplier-friendly shape is strictly weaker, so
the crater producer (direction 2) may land on either. -/
def residG_at_roundW' (H : ResidBW) : ResidGW :=
  fun G t hn hlo hhi => QMCLeafB.EndgameM2.coreDataG_of_data
    (endgameCoreDataB_at_roundW (H G t hn hlo hhi))

#print axioms QMCLeafB.RoundWRepoint.residG_at_roundW'

/-- **The checksum at `oW` for the *supplier-friendly* residual**: a `CoreDataG` at the bottom has an
all-`false` `ok` stream (`hmem` there would be a member, and the bottom body is empty), so the
programme's bit is `false`.  This is the form the crater producer's shape answers to. -/
theorem checksum_at_roundW_of_supplied (H : ResidGW) {G : QuantumMaxCutEnergy.Input}
    (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    oW G (-QMCLeafB.EngineRuntime.Rq G) = false := by
  have hb := QMCLeafB.EmptyBottomM1.bottom_mem_bracket (G := G) hRq
  have D := H G (-QMCLeafB.EngineRuntime.Rq G) hn hb.1 hb.2
  have B := QMCLeafB.EndgameM2.bundleH_of_dataG
    (QMCLeafB.RecordsM2.rmax_pos_paramsKbc2 G hn) D
  exact QMCLeafB.Sliver2M8.bundleH_forces_false_at_bottom
    (QMCLeafB.UnionShallow.paramsKbc2 G) hRq (QMCLeafB.UnionShallow.paramsKbc2_dq G) B

#print axioms QMCLeafB.RoundWRepoint.checksum_at_roundW_of_supplied

/-! ## 6.  What is left after the repoint

After this file the campaign's single hypothesis is `ResidBW`, and its fields are, per interior
`(G, t)`:

* the coded state stream `X` with its symmetry (`CoreDataB.hsym`),
* the two horizon-bounded drift slots `hdriftc`/`hdriftd` at the run's own stream — the crater,
* and nothing else: `hverdict` is `hverdict_at_roundW0`, supplied by §3 from the per-round state
  read-outs (`hsym`, the exact descent's `false` at `ok` rounds, the two `hoff` state facts) and
  the fully discharged invariants of the round.

The programme itself is checksum-clean at the bottom (§4: `false` at `t = -Rq G`, unconditionally
from the two plugs every producer carries).  The `hd` conduit, the `Poly`/size/`htop` slots and the
verbatim sentence are all applied, not re-proved (§2). -/

/-! ## 6.  The fuel is positive, and the bit is `true` at the top of the bracket -/

theorem Tbc2_pos (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    1 ≤ QMCLeafB.ClosingAssembly.Tbc2 G t := by
  rw [hKm_Tbc2 G t]
  exact QMCLeafB.UnionShallow.one_le_Kbc2_mul G

#print axioms QMCLeafB.RoundWRepoint.Tbc2_pos

/-- **`oW` is `true` on the campaign top slice** — `OkLower.htop_roundW`, with the fuel's positivity
from `Tbc2 = K*m`.  (This is the half of the programme's design that the *old* bit did not have: at
`RoundProgram.round` the top slice has no `ok` round at all.) -/
theorem oW_true_at_top {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) (hhi : t ≤ 0) :
    oW G t = true :=
  QMCLeafB.OkLower.htop_roundW QMCLeafB.InitDq.init0 QMCLeafB.InitDq.stOks_init0
    QMCLeafB.InitDq.stT_init0 QMCLeafB.AssemblyM5.epsOf_init0_any
    QMCLeafB.ClosingAssembly.Tbc2 Tbc2_pos G t hlo hhi

#print axioms QMCLeafB.RoundWRepoint.oW_true_at_top

/-- **The verdict read-out of `oW` in the engine's own stream**: the programme's bit is the `anyOk`
of `okW` along the orbit `runW0`.  This is the form a producer works with when it reasons about the
run round by round. -/
theorem oW_eq_anyOk_okW (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    oW G t = QMCLeafB.SimLoop.anyOk (fun k => okW (runW0 G t k))
      (QMCLeafB.ClosingAssembly.Tbc2 G t) := by
  rw [oW_apply,
    QMCLeafB.OkLower.verdict_iterate_eq_anyOk_W _ (hoks_init0 G t)
      (QMCLeafB.ClosingAssembly.Tbc2 G t)]
  rfl

#print axioms QMCLeafB.RoundWRepoint.oW_eq_anyOk_okW

/-- **The third entry point: `ResidWin` at `oW` gives `d9f601e5`.**  A producer that lands on the
corrected bundle residual (direction 6's shape) does not have to rebuild the `hd` bundle itself. -/
theorem solution_statement_of_residWin
    (H : QMCLeafB.FlagsM5.ResidH oW QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement := by
  refine QMCLeafB.LedgerW.solution_roundWG_of_init_hd_round QMCLeafB.InitDq.init0 20
    (by norm_num : 20 ≤ 2 ^ 20) QMCLeafB.InitDq.poly_init0 QMCLeafB.InitDq.init_normalised
    QMCLeafB.InitDq.stT_init0 QMCLeafB.AssemblyM5.epsOf_init0_any QMCLeafB.InitDq.stOks_init0
    QMCLeafB.InitDq.init0_tape ?_
  intro G t hn hlo hhi
  exact QMCLeafB.FlagsM5.runParts_of_bundleH oW G t
    (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.UnionShallow.paramsKbc2_rmax_pos G hn)
    (QMCLeafB.AssemblyM5.rmax_le_one G hn)
    (QMCLeafB.AssemblyM5.budget_at_interior G t hn hlo hhi)
    (H G t hn hlo hhi)

#print axioms QMCLeafB.RoundWRepoint.solution_statement_of_residWin

/-! ## 8.  The general refuted-point theorem: all flags `false` ⇒ the bit is `false`

This is the form the crater producer needs.  Its `ok` stream at a refuted interior point is the
all-`false` stream, so its `hverdict` slot is the equation `oW G t = anyOk (fun _ => false) (K*m)`,
i.e. `oW G t = false`.  That is a **theorem** here, from the same two plugs as everything else
(the state's symmetry, the exact descent's `false` at `ok` rounds) and the flag stream's being all
false — no emptiness, no arithmetic, no verdict work for the producer.  The empty-body case (which
is *why* the flags are all false there) is the corollary §8.2, via
`EmptyBottomM1.flagOf_false_of_emptyBody`. -/

open QMCLeafB.FlagsM5 (flagOf) in
/-- **All-`false` flags force the programme's bit `false`** at the reported round. -/
theorem oW_false_of_allFlagsFalse {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (acc : ℕ → QMCLeafB.PivotProgram.Acc)
    (hsym : ∀ (k : ℕ) (i j : Fin G.n),
      QMCLeafB.StateDiag.stMat G.n (stX (runW0 G t k)) i j
        = QMCLeafB.StateDiag.stMat G.n (stX (runW0 G t k)) j i)
    (hpiv : ∀ k, okW (runW0 G t k) = true →
      (QMCLeafB.PivotProgram.runPiv
        (toRows (G.n, stX (runW0 G t k)), acc k)).1 = false)
    (hall : ∀ k, flagOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
      (QMCLeafB.RecordsM2.cXst G.n (fun k => stX (runW0 G t k))
        (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k = false) :
    oW G t = false := by
  have hRq : 0 < QMCLeafB.EngineRuntime.Rq G :=
    QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi
  have hT : ∀ k, stT (runW0 G t k) - QMCLeafB.RoundT.epsOf (runW0 G t k)
      = t - QMCLeafB.RundataCert.eps G := by
    intro k
    rw [stT_runW0, epsOf_runW0]
    rw [show QMCLeafB.RundataCert.eps G = QMCLeafB.EngineRuntime.Rq G / 40000 from rfl]
  have hdq : ∀ k, dqOf (runW0 G t k) = (QMCLeafB.UnionShallow.paramsKbc2 G).dq := by
    intro k
    rw [dqOf_runW0 G t k hRq, QMCLeafB.UnionShallow.paramsKbc2_dq]
  have hbit : ∀ k, okW (runW0 G t k) = true →
      (oracleV (runW0 G t k)).1 = false := by
    intro k hb
    have heng := QMCLeafB.OkLower.okW_eq_engine (QMCLeafB.InitDq.init0 (noTape G t)) k
      (not_top_at_interior hhi)
    show (oracleV (runW0 G t k)).1 = false
    rw [show okW (runW0 G t k)
        = !((oracleV (runW0 G t k)).1) from heng] at hb
    cases hc : (oracleV (runW0 G t k)).1 with
    | false => rfl
    | true => rw [hc] at hb; exact absurd hb (by simp)
  rw [oW_apply,
    QMCLeafB.OkLower.verdict_iterate_eq_anyOk_W _ (hoks_init0 G t)
      (QMCLeafB.ClosingAssembly.Tbc2 G t)]
  refine (QMCLeafB.SimLoop.anyOk_eq_false_iff _ _).mpr (fun k hk => ?_)
  by_contra h
  have htrue : okW (runW0 G t k) = true := by
    cases hb : okW (runW0 G t k) with
    | false => exact absurd hb h
    | true => rfl
  have hk' : k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
      * (QMCLeafB.UnionShallow.paramsKbc2 G).m := by
    rw [← hKm_Tbc2 G t]
    exact hk
  have hflag := QMCLeafB.VerdictBridge.hon_slot
    (G := G) (t := t) (P := QMCLeafB.UnionShallow.paramsKbc2 G)
    (rb := fun k => okW (runW0 G t k))
    (X := fun k => stX (runW0 G t k)) (s := runW0 G t) (acc := acc)
    (fun k => rfl) (stN_runW0 G t)
    (stA_length_runW0 G t)
    (fun k => by rw [stX_length_runW0 G t k]; exact Nat.le_mul_self G.n)
    (stMat_stA_runW0 G t) hsym hbit hpiv
    (paramsKbc2_dq_pos G) (paramsKbc2_dq_le_four G) hT hdq k hk' htrue
  have hfl : flagOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
      (QMCLeafB.RecordsM2.cXst G.n (fun k => stX (runW0 G t k))
        (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k = false := hall k
  rw [hfl] at hflag
  exact Bool.false_ne_true hflag

#print axioms QMCLeafB.RoundWRepoint.oW_false_of_allFlagsFalse

open QMCLeafB.FlagsM5 (flagOf) in
/-- **An empty relaxed body forces the programme's bit `false`** at that interior point — the crater's
`hverdict` slot, discharged. -/
theorem oW_false_of_emptyBody {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hbody : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (acc : ℕ → QMCLeafB.PivotProgram.Acc)
    (hsym : ∀ (k : ℕ) (i j : Fin G.n),
      QMCLeafB.StateDiag.stMat G.n (stX (runW0 G t k)) i j
        = QMCLeafB.StateDiag.stMat G.n (stX (runW0 G t k)) j i)
    (hpiv : ∀ k, okW (runW0 G t k) = true →
      (QMCLeafB.PivotProgram.runPiv
        (toRows (G.n, stX (runW0 G t k)), acc k)).1 = false) :
    oW G t = false :=
  oW_false_of_allFlagsFalse (G := G) (t := t) hlo hhi acc hsym hpiv
    (fun k => QMCLeafB.EmptyBottomM1.flagOf_false_of_emptyBody hbody _ k)

#print axioms QMCLeafB.RoundWRepoint.oW_false_of_emptyBody

/-! ## 7.  The programme is not constant

Two anchors, one unconditional and one from §4.3: `oW` is `true` at `t = 0` for *every* input (the top
slice), and `false` at the bracket's bottom `t = -Rq G` given the two run plugs every record producer
carries.  So the repointed bit separates the two ends of the bracket, which is what the residual's
`hverdict` needs at both.

(What is *not* claimed here: the value of `oW` at the interior ok point `(G₀, -1/2)`.  Phase 20's
anchor there is the *constant-true* bit `fun _ _ => true`, and the repointed bit's value at that point
is a statement about the run hitting an `ok` round — the ok-production's content (direction 6), not a
verdict question.) -/

/-- **`oW` is `true` at `t = 0`**, for every input and every total weight — no hypothesis at all. -/
theorem oW_zero (G : QuantumMaxCutEnergy.Input) : oW G 0 = true :=
  oW_true_at_top (by
    have h0 := QMCLeafB.RundataArith.Rq_nonneg G
    have : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G / 40000 := by linarith
    have hR : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) := by exact_mod_cast this
    simp only [Rat.cast_zero]
    linarith) (le_refl 0)

#print axioms QMCLeafB.RoundWRepoint.oW_zero

end QMCLeafB.RoundWRepoint


