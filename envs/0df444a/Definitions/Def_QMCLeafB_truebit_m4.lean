-- Prove2me | Definitions.Def_QMCLeafB_truebit_m4
-- name    : QMCLeafB_truebit_m4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:13:26.303857+00:00
-- url     : https://prove2.me/theorems/4010dc24-ba89-4fe5-baef-c881a83c89ee
-- title:
--   QMCLeafB truebit_m4
-- statement:
--   # leaf B phase 23 — brick `truebit-completion` (swarm `smw1qbrnt`, member m4, direction d4)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_roundwrepoint
import Definitions.Def_QMCLeafB_okprod2
import Definitions.Def_QMCLeafB_audit2
import Definitions.Def_QMCLeafB_refuted_m3
import Definitions.Def_QMCLeafB_integration2
/-
# leaf B phase 23 — brick `truebit-completion` (swarm `smw1qbrnt`, member m4, direction d4)

The phase-22 split (`Check_audit2_m5` §4) confines the crater to the nonempty-body stratum; the
phase-22 production map leaves two live legs there: the **true-bit** leg (one member certificate) and
the **false-bit nonempty** leg (`(G₁,t₁)`-class).  This file discharges the first one *at the
programme*, with no analytic input, and reduces the leaf to a single named residual.

What is new here, in order:

* §1 the **read-out at the reported round is free**: `oW G t = anyOk (okW ∘ runW0 G t) (K·m)` — the
  loop's own flag stream, no flag/verdict bridge required.
* §2 the **regime**: below the campaign slack every round of the run is in the engine branch, so
  `okW` is the lower-body oracle's `ok` (`okW = !oracleV`), and `okW = true` forces the oracle's `ok`
  answer.  No hypothesis.
* §3 **the true-bit leg**: `okW`-true at one round gives `OkProd_M8.OkPoint` via
  `relaxMem_diagPinch_of_okV`, hence `CoreDataG` (through `coreDataG_of_okPoint`), hence `RunParts`
  (through `bundleH_of_dataG` + `runParts_of_bundleH`).  Cost: **two run invariants** — the symmetry
  of the run's states and the exact descent's `false` at `ok` rounds — and nothing else.  Neither
  drift budget, no margin, no normal, no stream, no flag equation.
* §4 **falsification** (the direction's falsify-first question): the true bit is **incompatible with
  "no pinched member"**.  `exists_pinched_member_of_trueBit`: a true bit exhibits a *rational member
  at pinched diagonal*.  Consequence `oW_false_of_no_pinched_member`: at any point where no pinched
  matrix is a member the programme's bit is `false` — no `CoreDataG` hypothesis (this sharpens
  `Check_okprod2_m8`'s `coreDataG_bit_false_of_no_pinched_member`, which needs an inhabitant of the
  conduit).  Instantiated at the audit's sliver: `oW_false_at_G₁`.
* §5 **the campaign data of the split stroke are free at `oW`**: `hbit` (with the run's own flag
  stream) is §1, and `hok` is §2's member implication.  So the split stroke's `rb`/`cXp`/`hbit`/`hok`
  cost nothing; only `hemptyR` (the real-empty ⇒ rational-empty bridge) survives.
* §6 the **zip**: the leaf's `RunParts` obligation over the interior bracket, hence the verbatim
  `d9f601e5` sentence at `oW` (`LedgerW.solution_roundWG_of_init_hd_round`), from

      (two run invariants) + (hemptyR) + (RunParts at the false-bit nonempty stratum)

  i.e. the whole campaign from **one named residual** — the `(G₁,t₁)`-class stratum — plus two
  run-of-program invariants and one cast bridge.  §7 shows the same zip with the third leg at the
  conduit shape `CoreDataG` (for the `solution_of_split` interface), and §8 records non-vacuity of
  the residual's *hypothesis side* (the true-bit leg fires at `(G₀, -1/2)`).

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every declaration, all `[propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.TrueBitM4

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram
open QMCLeafB.OkLower (roundW okW oracleV dqOf)
open QMCLeafB.FinalStroke (loopBit noTape)

/-! ## 0.  Notation

`oW` is the reported-round programme bit of `Check_roundwrepoint_m4` and `runW0 G t` its own orbit
from the campaign state.  `P G` is the campaign parameter family. -/

/-- The campaign parameter family, abbreviated. -/
abbrev P (G : QuantumMaxCutEnergy.Input) : QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.UnionShallow.paramsKbc2 G

/-- The reported-round orbit, abbreviated. -/
abbrev runW (G : QuantumMaxCutEnergy.Input) (t : ℚ) : ℕ → RSt :=
  QMCLeafB.RoundWRepoint.runW0 G t

/-! ## 1.  The read-out at the reported round, with no bridge -/

/-- **The programme's bit is the run's own flag read-out.**  `verdict` folds `stOks`, whose entries
below the campaign slack are `okW` (`stOks_iterateW`), so `oW` is `anyOk` of the `okW` stream.  No
flag stream, no `hon`/`hoff`, no state plug enters here. -/
theorem oW_eq_anyOk_okW (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.RoundWRepoint.oW G t
      = QMCLeafB.SimLoop.anyOk (fun k => okW (runW G t k)) ((P G).K * (P G).m) := by
  rw [QMCLeafB.RoundWRepoint.oW_apply,
    QMCLeafB.OkLower.verdict_iterate_eq_anyOk_W _ (QMCLeafB.RoundWRepoint.hoks_init0 G t),
    QMCLeafB.RoundWRepoint.hKm_Tbc2 G t]
  rfl

#print axioms QMCLeafB.TrueBitM4.oW_eq_anyOk_okW

/-! ## 2.  The regime at every round of the run -/

/-- **The regime test fails at every round of the run** on the interior bracket: `roundW`'s `okW`
flag is the engine branch's, at every `k`. -/
theorem not_regime_runW {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (k : ℕ) :
    ¬ (0 ≤ stT (runW G t k) + QMCLeafB.RoundT.epsOf (runW G t k)) := by
  rw [QMCLeafB.RoundWRepoint.stT_runW0, QMCLeafB.RoundWRepoint.epsOf_runW0]
  intro h
  have hcast : ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)
      = (QMCLeafB.EngineRuntime.Rq G : ℝ) / 40000 := by
    push_cast
    ring
  have hhi' : (t : ℝ) + (QMCLeafB.EngineRuntime.Rq G : ℝ) / 40000 < 0 := by
    rw [← hcast]
    linarith
  have h2 : ((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) < 0 := by
    push_cast
    exact hhi'
  have h3 : (t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) < 0 := by
    exact_mod_cast h2
  linarith

#print axioms QMCLeafB.TrueBitM4.not_regime_runW

/-- **`okW` is the lower-body oracle's answer along the run.** -/
theorem okW_runW_eq_engine {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (k : ℕ) :
    okW (runW G t k) = !((oracleV (runW G t k)).1) :=
  QMCLeafB.OkLower.okW_eq_engine (QMCLeafB.InitDq.init0 (noTape G t)) k
    (QMCLeafB.RoundWRepoint.not_top_at_interior hhi)

#print axioms QMCLeafB.TrueBitM4.okW_runW_eq_engine

/-- **An `ok` flag of the run is an `ok` answer of the lower-body oracle.** -/
theorem oracleV_false_of_okW {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) {k : ℕ}
    (h : okW (runW G t k) = true) :
    (oracleV (runW G t k)).1 = false := by
  have he := okW_runW_eq_engine (G := G) (t := t) hhi k
  rw [h] at he
  cases hb : (oracleV (runW G t k)).1 with
  | false => rfl
  | true => rw [hb] at he; exact Bool.noConfusion he

#print axioms QMCLeafB.TrueBitM4.oracleV_false_of_okW

/-! ## 3.  The true-bit leg: one member certificate, then `CoreDataG`, then `RunParts`

The two run invariants are taken as hypotheses throughout this section (they are the run's own
obligation, named in `Check_verdbridge_m4` §9 and `Check_roundwrepoint_m4` §3.3):

* `hRunSymm` — the run's coded states are symmetric;
* `hRunPiv`  — at an `ok` round the **exact** descent, run on the state's own rows from the
  accumulator `acc G t k`, reports `false` (i.e. it certifies PSD). -/

/-- The exact descent's `false` at the `ok` rounds of the run — the plug shape. -/
abbrev RunPiv (acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), okW (runW G t k) = true →
    (QMCLeafB.PivotProgram.runPiv
      (QMCLeafB.RoundProgram.toRows
        (G.n, stX (runW G t k)), acc G t k)).1 = false

/-- The run's coded states are symmetric — the plug shape. -/
abbrev RunSymm : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) (i j : Fin G.n),
    QMCLeafB.StateDiag.stMat G.n (stX (runW G t k)) i j
      = QMCLeafB.StateDiag.stMat G.n (stX (runW G t k)) j i

/-- **The member certificate at an `ok` round of the run**: the pinched centre there is a member of
the relaxed body.  `relaxMem_diagPinch_of_okV` with every invariant of `roundW` discharged
(`Check_roundwrepoint_m4` §3.1). -/
theorem relaxMem_pinch_of_okW {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc} {k : ℕ}
    (hsym : ∀ i j, QMCLeafB.StateDiag.stMat G.n (stX (runW G t k)) i j
      = QMCLeafB.StateDiag.stMat G.n (stX (runW G t k)) j i)
    (hpiv : (QMCLeafB.PivotProgram.runPiv
      (QMCLeafB.RoundProgram.toRows (G.n, stX (runW G t k)), acc G t k)).1 = false)
    (h : okW (runW G t k) = true) :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
      (QMCLeafB.CentreAdm.diagPinch
        (QMCLeafB.StateDiag.stMat G.n (stX (runW G t k))) (P G).dq)
      (t - QMCLeafB.RundataCert.eps G) (P G).dq := by
  have hRq : 0 < QMCLeafB.EngineRuntime.Rq G :=
    QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi
  have hlenA : G.n ≤ (stA (runW G t k)).length := QMCLeafB.RoundWRepoint.stA_length_runW0 G t k
  have hlenX : G.n ≤ (stX (runW G t k)).length := by
    rw [QMCLeafB.RoundWRepoint.stX_length_runW0 G t k]
    exact Nat.le_mul_self G.n
  refine QMCLeafB.VerdictBridge.relaxMem_diagPinch_of_okV
    (QMCLeafB.RoundWRepoint.stN_runW0 G t k) hlenA hlenX
    (QMCLeafB.RoundWRepoint.stMat_stA_runW0 G t k)
    (fun i => QMCLeafB.RecordsM2.wMatrixQ_diag G i) hsym
    (oracleV_false_of_okW hhi h) hpiv
    (QMCLeafB.RoundWRepoint.paramsKbc2_dq_pos G)
    (QMCLeafB.RoundWRepoint.paramsKbc2_dq_le_four G) ?_ ?_
  · rw [QMCLeafB.RoundWRepoint.stT_runW0, QMCLeafB.RoundWRepoint.epsOf_runW0]
    rfl
  · rw [QMCLeafB.RoundWRepoint.dqOf_runW0 G t k hRq, QMCLeafB.UnionShallow.paramsKbc2_dq]

#print axioms QMCLeafB.TrueBitM4.relaxMem_pinch_of_okW

/-- **The `OkPoint` at a true bit.**  Extract the `ok` round from the read-out (§1), freeze the
state there, and hand the member certificate to `okPoint_of_okV`. -/
def okPoint_at_trueBit {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc) (hbit : QMCLeafB.RoundWRepoint.oW G t = true) :
    QMCLeafB.OkProd_M8.OkPoint G t (P G) := by
  have hv : QMCLeafB.SimLoop.anyOk (fun k => okW (runW G t k)) ((P G).K * (P G).m) = true := by
    rw [← oW_eq_anyOk_okW G t]
    exact hbit
  have hex : ∃ k, k < (P G).K * (P G).m ∧ okW (runW G t k) = true :=
    (QMCLeafB.SimLoop.anyOk_eq_true_iff (fun k => okW (runW G t k)) _).1 hv
  let k₀ : ℕ := Classical.choose hex
  have hk₀ : k₀ < (P G).K * (P G).m := (Classical.choose_spec hex).1
  have hok : okW (runW G t k₀) = true := (Classical.choose_spec hex).2
  have hRq : 0 < QMCLeafB.EngineRuntime.Rq G :=
    QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi
  have hlenA : G.n ≤ (stA (runW G t k₀)).length := QMCLeafB.RoundWRepoint.stA_length_runW0 G t k₀
  have hlenX : G.n ≤ (stX (runW G t k₀)).length := by
    rw [QMCLeafB.RoundWRepoint.stX_length_runW0 G t k₀]
    exact Nat.le_mul_self G.n
  refine QMCLeafB.OkProd_M8.okPoint_of_okV (P := P G)
    (s := runW G t k₀) (acc := acc G t k₀) hk₀
    (QMCLeafB.RoundWRepoint.stN_runW0 G t k₀) hlenA hlenX
    (QMCLeafB.RoundWRepoint.stMat_stA_runW0 G t k₀) (hsym G t k₀)
    (oracleV_false_of_okW hhi hok) (hpiv G t k₀ hok)
    (QMCLeafB.RoundWRepoint.paramsKbc2_dq_pos G)
    (QMCLeafB.RoundWRepoint.paramsKbc2_dq_le_four G) ?_ ?_
  · rw [QMCLeafB.RoundWRepoint.stT_runW0, QMCLeafB.RoundWRepoint.epsOf_runW0]
    rfl
  · rw [QMCLeafB.RoundWRepoint.dqOf_runW0 G t k₀ hRq, QMCLeafB.UnionShallow.paramsKbc2_dq]

#print axioms QMCLeafB.TrueBitM4.okPoint_at_trueBit

/-- **`CoreDataG` at a true bit.**  `Check_okprod2_m8`'s frozen-code reduction, with the ok point
produced from the run instead of assumed. -/
def coreDataG_at_trueBit {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc) (hbit : QMCLeafB.RoundWRepoint.oW G t = true) :
    QMCLeafB.EndgameM2.CoreDataG QMCLeafB.RoundWRepoint.oW G t (P G) hn :=
  QMCLeafB.OkProd_M8.coreDataG_of_okPoint
    (okPoint_at_trueBit (acc := acc) hlo hhi hsym hpiv hbit) hbit

#print axioms QMCLeafB.TrueBitM4.coreDataG_at_trueBit

/-- **`RunParts` at a true bit** — the leaf's own interface.  The bundle assembly of
`Check_flags_m5`/`Check_endgame_m2` with the campaign's budget slots (`Check_audit2_m5` §4). -/
def runParts_at_trueBit {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc) (hbit : QMCLeafB.RoundWRepoint.oW G t = true) :
    QMCLeafB.FinalStroke.RunParts QMCLeafB.RoundWRepoint.oW G t (P G) :=
  QMCLeafB.FlagsM5.runParts_of_bundleH QMCLeafB.RoundWRepoint.oW G t (P G) hn
    (QMCLeafB.ClosingAssembly.rmaxOf_pos G hn)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one G hn)
    (QMCLeafB.ClosingAssembly.budget_dqShallow G hn
      (QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi))
    (QMCLeafB.EndgameM2.bundleH_of_dataG
      (QMCLeafB.RecordM2.rmax_pos_paramsKbc2 G hn)
      (coreDataG_at_trueBit (acc := acc) hlo hhi hsym hpiv hbit))

#print axioms QMCLeafB.TrueBitM4.runParts_at_trueBit

/-! ## 4.  Falsification: the true bit cannot coexist with "no pinched member"

The direction's falsify-first question was whether the open stratum could be *avoided* on the true
side, i.e. whether a true bit is compatible with the absence of a pinched member.  It is not: the
true bit exhibits one.  So the `(G₁,t₁)`-class stratum carries the `false` bit at the programme —
machine-checked, with no conduit inhabitant assumed. -/

/-- **A true bit exhibits a rational member at pinched diagonal.** -/
theorem exists_pinched_member_of_trueBit {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc) (hbit : QMCLeafB.RoundWRepoint.oW G t = true) :
    ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ, (∀ i, Q i i = 1 - (P G).dq / 4) ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) (P G).dq := by
  have hv : QMCLeafB.SimLoop.anyOk (fun k => okW (runW G t k)) ((P G).K * (P G).m) = true := by
    rw [← oW_eq_anyOk_okW G t]
    exact hbit
  obtain ⟨k₀, hk₀, hok⟩ :=
    (QMCLeafB.SimLoop.anyOk_eq_true_iff (fun k => okW (runW G t k)) _).1 hv
  refine ⟨QMCLeafB.RecordsM2.cXst G.n (fun k => stX (runW G t k)) (P G).dq k₀, ?_, ?_⟩
  · intro i
    exact QMCLeafB.RecordsM2.cXst_diag G.n _ (P G).dq k₀ i
  · exact relaxMem_pinch_of_okW hlo hhi (hsym G t k₀) (hpiv G t k₀ hok) hok

#print axioms QMCLeafB.TrueBitM4.exists_pinched_member_of_trueBit

/-- **At a point with no pinched member the programme's bit is `false`** — no conduit inhabitant is
assumed (contrast `Check_okprod2_m8.coreDataG_bit_false_of_no_pinched_member`, which reads the bit
off an inhabitant of `CoreDataG`). -/
theorem oW_false_of_no_pinched_member {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc)
    (hno : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ, (∀ i, Q i i = 1 - (P G).dq / 4) →
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) (P G).dq) :
    QMCLeafB.RoundWRepoint.oW G t = false := by
  cases hb : QMCLeafB.RoundWRepoint.oW G t with
  | false => rfl
  | true =>
    obtain ⟨Q, hQ, hM⟩ := exists_pinched_member_of_trueBit (acc := acc) hlo hhi hsym hpiv hb
    exact absurd hM (hno Q hQ)

#print axioms QMCLeafB.TrueBitM4.oW_false_of_no_pinched_member

/-- **The audit's sliver carries the `false` bit at the programme.**  `(G₁,t₁)`
(`Check_emptybody_m5` §5) has a *nonempty* rational body but no pinched member, so `oW` reads
`false` there: the third stratum of the thrice-split is not a choice of the assembly, it is forced by
the programme's own read-out. -/
theorem oW_false_at_G₁ (hn : 2 ≤ QMCLeafB.EmptyBodyM5.G₁.n)
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc) :
    QMCLeafB.RoundWRepoint.oW QMCLeafB.EmptyBodyM5.G₁
      (QMCLeafB.Audit2M5.t₁) = false :=
  oW_false_of_no_pinched_member (G := QMCLeafB.EmptyBodyM5.G₁) (t := QMCLeafB.Audit2M5.t₁)
    QMCLeafB.Audit2M5.anchor3_interior.1 QMCLeafB.Audit2M5.anchor3_interior.2
    hsym hpiv
    (fun Q hQ => QMCLeafB.EmptyBodyM5.no_pinched_member_G₁ Q hQ)

#print axioms QMCLeafB.TrueBitM4.oW_false_at_G₁

/-! ## 5.  The split stroke's campaign data, free at `oW`

`Check_audit2_m5`'s `runParts_of_split`/`solution_of_split` take the run's read-out `rb`, its centres
`cXp`, the bit equation `hbit` and the `ok ⇒ member` implication `hok` as *data* (direction d5's
lane).  At the reported round all four are free: `rb`/`cX` are the run's own flag stream and pinch
centres (§1), `hbit` is §1's read-out, and `hok` is §3's member theorem. -/

/-- The run's own flag stream. -/
def rbW (G : QuantumMaxCutEnergy.Input) (t : ℚ) : ℕ → Bool := fun k => okW (runW G t k)

/-- The run's queried centres: the pinch of the state at each round. -/
def cXW (G : QuantumMaxCutEnergy.Input) (t : ℚ) : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ :=
  fun k => QMCLeafB.RecordsM2.cXst G.n (fun j => stX (runW G t j)) (P G).dq k

/-- **`hbit` is free**: the programme's bit *is* the run's own read-out (`rfl` after §1). -/
theorem hbit_at_oW (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.RoundWRepoint.oW G t
      = QMCLeafB.SimLoop.anyOk (rbW G t) ((P G).K * (P G).m) :=
  oW_eq_anyOk_okW G t

#print axioms QMCLeafB.TrueBitM4.hbit_at_oW

/-- **`hok` is free**: an `ok` round of the run is a member round at its own pinched centre. -/
theorem hok_at_oW {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc) :
    ∀ k, rbW G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXW G t k)
        (t - QMCLeafB.RundataCert.eps G) (P G).dq :=
  fun k h => relaxMem_pinch_of_okW (acc := acc) hlo hhi (hsym G t k) (hpiv G t k h) h

#print axioms QMCLeafB.TrueBitM4.hok_at_oW

/-! ## 6.  The zip: one named residual at `oW`

The residual is the **third stratum only**: interior points whose relaxed body is nonempty and whose
programme bit is `false` — the `(G₁,t₁)`-class of `Check_audit2_m5` §5 (where §4 proves the bit is
forced, so this is a genuine stratum, not a case the split could avoid).  Everything else is
discharged: the empty stratum by `Check_refuted_m3`'s drift-free record (with the bit read off §1 and
§3), and the true-bit stratum by §3. -/

/-- The named residual, at the leaf's own interface. -/
abbrev FalseNonemptySupply
    (acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    (∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((P G).dq : ℚ) : ℝ) X) →
    QMCLeafB.RoundWRepoint.oW G t = false →
    QMCLeafB.FinalStroke.RunParts QMCLeafB.RoundWRepoint.oW G t (P G)

/-- The same residual at the *conduit* shape `CoreDataG` (for the `solution_of_split` interface). -/
abbrev FalseNonemptyConduit
    (acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    (∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((P G).dq : ℚ) : ℝ) X) →
    QMCLeafB.RoundWRepoint.oW G t = false →
    QMCLeafB.EndgameM2.CoreDataG QMCLeafB.RoundWRepoint.oW G t (P G) hn

/-- The real-empty ⇒ rational-empty bridge (the `hemptyR` premise of `Check_audit2_m5`'s split). -/
abbrev EmptyBridge : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
    (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((P G).dq : ℚ) : ℝ) X) →
    ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) (P G).dq

/-- **The leaf's `hd` at the reported round, from the third stratum alone.** -/
noncomputable def hdW_of_three
    (hE : EmptyBridge)
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc) (hfn : FalseNonemptySupply acc) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 roundW
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  classical
  intro G t hn hlo hhi
  by_cases hbody : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((P G).dq : ℚ) : ℝ) X
  · exact QMCLeafB.RefutedM3.runParts_of_emptyBody' G t (P G) hn
      (hbit_at_oW G t) (hok_at_oW (acc := acc) hlo hhi hsym hpiv) (hE G t hbody) hbody
  · have hne : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((P G).dq : ℚ) : ℝ) X := by
      by_contra hc
      exact hbody (fun X hX => hc ⟨X, hX⟩)
    by_cases hb : QMCLeafB.RoundWRepoint.oW G t = true
    · exact runParts_at_trueBit (acc := acc) (hn := hn) hlo hhi hsym hpiv hb
    · exact hfn G t hn hlo hhi hne (by
        cases h : QMCLeafB.RoundWRepoint.oW G t with
        | false => rfl
        | true => exact absurd h hb)

#print axioms QMCLeafB.TrueBitM4.hdW_of_three

/-- **`d9f601e5`, verbatim, from the third stratum + the two run invariants + the cast bridge.** -/
theorem solution_statement_of_three
    (hE : EmptyBridge)
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc) (hfn : FalseNonemptySupply acc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.LedgerW.solution_roundWG_of_init_hd_round QMCLeafB.InitDq.init0 20
    (by norm_num : 20 ≤ 2 ^ 20) QMCLeafB.InitDq.poly_init0 QMCLeafB.InitDq.init_normalised
    QMCLeafB.InitDq.stT_init0 QMCLeafB.AssemblyM5.epsOf_init0_any QMCLeafB.InitDq.stOks_init0
    QMCLeafB.InitDq.init0_tape (hdW_of_three hE hsym hpiv hfn)

#print axioms QMCLeafB.TrueBitM4.solution_statement_of_three

/-- **The verbatim sentence** (the ascription below is the statement lock). -/
theorem solution_of_three
    (hE : EmptyBridge)
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc) (hfn : FalseNonemptySupply acc) :
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
  solution_statement_of_three hE hsym hpiv hfn

#print axioms QMCLeafB.TrueBitM4.solution_of_three

/-! ## 7.  The conduit form of the same zip

`Check_audit2_m5`'s `solution_of_split` consumes `ResidSplit` (i.e. `CoreDataG` on the nonempty
stratum).  The true-bit half of that is §3, so the same three-way split produces `ResidSplit` at
`oW` — and hence `Check_roundwrepoint_m4`'s `ResidG`-keyed endings — from the conduit-shaped
third-stratum supply. -/

/-- **`ResidSplit` at `oW`** from the conduit-shaped third stratum. -/
noncomputable def residSplit_at_oW
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc) (hfn : FalseNonemptyConduit acc) :
    QMCLeafB.Audit2M5.ResidSplit QMCLeafB.RoundWRepoint.oW
      QMCLeafB.UnionShallow.paramsKbc2 := by
  classical
  intro G t hn hlo hhi hbody
  have hne : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((P G).dq : ℚ) : ℝ) X := by
    by_contra hc
    exact hbody (fun X hX => hc ⟨X, hX⟩)
  by_cases hb : QMCLeafB.RoundWRepoint.oW G t = true
  · exact coreDataG_at_trueBit (acc := acc) hlo hhi hsym hpiv hb
  · exact hfn G t hn hlo hhi hne (by
      cases h : QMCLeafB.RoundWRepoint.oW G t with
      | false => rfl
      | true => exact absurd h hb)

#print axioms QMCLeafB.TrueBitM4.residSplit_at_oW

/-- The false-bit residual at the conduit shape, with no body condition (this is what a
`ResidG`-shaped ending needs; the body-nonempty version above is the sharper one). -/
abbrev FalseBitConduit
    (acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    QMCLeafB.RoundWRepoint.oW G t = false →
    QMCLeafB.EndgameM2.CoreDataG QMCLeafB.RoundWRepoint.oW G t (P G) hn

/-- **`ResidG` at `oW`** (the shape `Check_roundwrepoint_m4`'s endings and `SpineC` consume), from
the false-bit conduit.  Note the discharge is *bit-keyed*: the empty and true strata never reach the
supply. -/
noncomputable def residG_at_oW
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc) (hfn : FalseBitConduit acc) :
    QMCLeafB.EndgameM2.ResidG QMCLeafB.RoundWRepoint.oW
      QMCLeafB.UnionShallow.paramsKbc2 := by
  intro G t hn hlo hhi
  by_cases hb : QMCLeafB.RoundWRepoint.oW G t = true
  · exact coreDataG_at_trueBit (acc := acc) hlo hhi hsym hpiv hb
  · exact hfn G t hn hlo hhi (by
      cases h : QMCLeafB.RoundWRepoint.oW G t with
      | false => rfl
      | true => exact absurd h hb)

#print axioms QMCLeafB.TrueBitM4.residG_at_oW



/-! ## 8.  The bridge's *shape*: `castM (wMatrixQ G) = wMatrix G`

Every stroke on the shelf states the real relaxed body at **`wMatrix G`**
(`Check_audit2_m5`'s `hemptyR`, `Check_refuted_m3.runParts_of_emptyBody`), while the transport
`RelaxMem ⟹ relaxBodyLE` (the `bridge-hemptyR` lane) lands at **`castM (wMatrixQ G)`**.  The two are
the same matrix — the pairing is pressed from the input's rational weights on both sides — so this
section supplies the identity and the adapter.  With it, §6's `EmptyBridge` premise is *the cast
bridge, verbatim*: no re-proof of the transport and no second bridge in the campaign. -/

/-- **The real weight matrix is the cast of the rational one.**  The comparison `<` decides which of
the two symmetric entries is read, so the two sides agree entry by entry (the `ℚ≥0 → ℚ → ℝ` and
`ℚ≥0 → ℝ` casts agree by `Rat.cast_nnratCast`). -/
theorem castM_wMatrixQ (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.BallFloor.castM (QMCLeafB.Finalization.wMatrixQ G) = QMCLeafB.wMatrix G := by
  ext i j
  show ((QMCLeafB.Finalization.wMatrixQ G i j : ℚ) : ℝ) = QMCLeafB.wMatrix G i j
  rcases lt_trichotomy i j with h | h | h
  · rw [QMCLeafB.Finalization.wMatrixQ_apply_of_lt h, QMCLeafB.wMatrix_apply_of_lt h]
    exact Rat.cast_nnratCast _
  · subst h
    rw [QMCLeafB.Finalization.wMatrixQ_apply_of_eq, QMCLeafB.wMatrix_apply_of_eq]
    norm_num
  · rw [QMCLeafB.Finalization.wMatrixQ_apply_of_gt h, QMCLeafB.wMatrix_apply_of_gt h]
    exact Rat.cast_nnratCast _

#print axioms QMCLeafB.TrueBitM4.castM_wMatrixQ

/-- The `EmptyBridge`'s shape, at the cast matrix: this is what a `RelaxMem ⟹ relaxBodyLE` transport
delivers, and it is all §6 needs. -/
abbrev CastEmptyBridge : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
    (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE
        (QMCLeafB.BallFloor.castM (QMCLeafB.Finalization.wMatrixQ G))
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((P G).dq : ℚ) : ℝ) X) →
    ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) (P G).dq

/-- **The cast bridge discharges `EmptyBridge`** — one rewrite of the body's weight matrix. -/
theorem emptyBridge_of_castBridge (hb : CastEmptyBridge) : EmptyBridge := by
  intro G t hempty Q hQ
  exact hb G t (fun X hX => hempty X (by rwa [castM_wMatrixQ] at hX)) Q hQ

#print axioms QMCLeafB.TrueBitM4.emptyBridge_of_castBridge

/-- **`d9f601e5` with the bridge in its cast shape.**  Same stroke as §6, one adapter deep — this is
the form a `bridge-hemptyR` deliverable plugs into with no shape work. -/
theorem solution_statement_of_three_castBridge
    (hb : CastEmptyBridge)
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc) (hfn : FalseNonemptySupply acc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_statement_of_three (emptyBridge_of_castBridge hb) hsym hpiv hfn

#print axioms QMCLeafB.TrueBitM4.solution_statement_of_three_castBridge

/-- **The verbatim sentence, bridge in cast shape.** -/
theorem solution_of_three_castBridge
    (hb : CastEmptyBridge)
    {acc : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → QMCLeafB.PivotProgram.Acc}
    (hsym : RunSymm) (hpiv : RunPiv acc) (hfn : FalseNonemptySupply acc) :
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
  solution_statement_of_three_castBridge hb hsym hpiv hfn

#print axioms QMCLeafB.TrueBitM4.solution_of_three_castBridge

end QMCLeafB.TrueBitM4


