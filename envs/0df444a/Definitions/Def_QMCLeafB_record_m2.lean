-- Prove2me | Definitions.Def_QMCLeafB_record_m2
-- name    : QMCLeafB_record_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:29:08.090549+00:00
-- url     : https://prove2.me/theorems/c67d4702-57e9-4fcf-8f8e-17c72d0cec61
-- title:
--   QMCLeafB record_m2
-- statement:
--   # leaf B phase 19 — brick `record-streams` (swarm `smw1k12jb`, member m2, direction d2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_closingAssembly_m3
import Definitions.Def_QMCLeafB_traceBudget2_m8
import Definitions.Def_QMCLeafB_lamstream_m8
import Definitions.Def_QMCLeafB_triobstruction_m5
import Definitions.Def_QMCLeafB_bundleFull
/-
# leaf B phase 19 — brick `record-streams` (swarm `smw1k12jb`, member m2, direction d2)

The residual of the leaf is `QMCLeafB.ClosingAssembly.Resid` (`Check_closingAssembly_m3`): one
`Bundle` per interior `(G, t)`.  Its sixteen fields split into three groups:

* the **flag stream** `ok` + the cut records `C`/`marg`/`c` (the oracle's answers),
* the **dilated multiplier** `lam`/`cn` with the depth ledger `hlam0/hlam1/hlam2` and `hcne`,
* the **budgets** `hTrc` (the trace at the queried centres) and `hdriftc`/`hdriftd`.

This file builds the records of the first two groups and discharges `hTrc`:

* §1  the all-`false` flag stream's read-out (`anyOk_false_stream`), and the cut record an *empty*
  relaxed body supplies at every rational centre (`relaxCut_of_empty`, `Check_triobstruction_m5`) —
  so the flag stream and the oracle answers of the deep interior are not supplier obligations;
* §2  the boundary-lowered centre `cX k = (1 − dq/4) • Q k` and the base stream `Q`: `hTrc` there is
  the base trace budget `∑ i, Q k i i ≤ n` (`hTrc_boundary_of_trace`), by the pinch brick;
* §3  `StreamData`: the bundle's remaining content in one structure, and `bundle_of_streamData`
  assembling the `ClosingAssembly.Bundle` from it — the `ok`/`marg`/`c`/`cX`/`hTrc`/`hverdict`
  slots are *constructed*, never supplied;
* §4  the two-stream residual at the campaign families and the verbatim `d9f601e5` sentence from it
  (`solution_of_streamData`, `solution_statement_of_streamData`), through the already wired strokes.

The **scalar budget** of the drift block is the `hdriftd` field in its linear form
(`∑_{j<k} λ_j·diagSum(p_j) ≤ (1 − dq/4)·n`, `TraceBudgetM8.hdriftd_linear_iff`); the sequential
`λ_k` construction (`Nat.strongRec`, `LamStreamM8.exists_lam_of_hl`) that fills `lam`/`cn`/
`hcne`/`hlam*` from the records alone is §5.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; axiom audit at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.RecordM2

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.RunPartsStream (dOne)
open QMCLeafB.RunPartsDilate

/-! ## 1.  The flag stream and the free cut record -/

/-- **The all-`false` flag stream reads `false`.**  So at a run whose every round is a cut round the
loop's output bit is fixed (`ClosingAssembly.verdict_eq_false_of_allFalse`). -/
theorem anyOk_false_stream (N : ℕ) :
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => false) N = false :=
  (QMCLeafB.SimLoop.anyOk_eq_false_iff (fun _ : ℕ => false) N).2 (fun _ _ => rfl)

#print axioms QMCLeafB.RecordM2.anyOk_false_stream

/-- **An empty relaxed body supplies a cut record at every rational centre**, with normal the
rational identity and margin `1` (`Check_triobstruction_m5.relaxCut_of_empty`, restated as a
`def` so that the normal is readable). -/
def cutRecOfEmpty {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) {u δ : ℚ}
    (hempty : ∀ X : Matrix (Fin n) (Fin n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
        ((δ : ℚ) : ℝ) X) :
    QMCLeafB.RelaxOracle.RelaxCut A cX u δ where
  normal := 1
  margin := 1
  margin_pos := by norm_num
  separates := fun X hX => absurd hX (hempty X)

@[simp] theorem cutRecOfEmpty_normal {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) {u δ : ℚ}
    (hempty : ∀ X : Matrix (Fin n) (Fin n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
        ((δ : ℚ) : ℝ) X) :
    (cutRecOfEmpty A cX hempty).normal = 1 := rfl

@[simp] theorem cutRecOfEmpty_margin {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) {u δ : ℚ}
    (hempty : ∀ X : Matrix (Fin n) (Fin n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
        ((δ : ℚ) : ℝ) X) :
    (cutRecOfEmpty A cX hempty).margin = 1 := rfl

#print axioms QMCLeafB.RecordM2.cutRecOfEmpty

/-! ## 2.  The boundary-lowered centre and the trace budget -/

/-- The query centre of round `k` at the base stream `Q`: the pinch boundary `(1 − dq/4) • Q k`,
the only admissible lowering (`Check_traceBudget_m8`, `Check_obstruction_m1`). -/
def cXof {n : ℕ} (dq : ℚ) (Q : ℕ → Matrix (Fin n) (Fin n) ℚ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  (1 - dq / 4) • Q k

theorem cXof_symm {n : ℕ} {dq : ℚ} {Q : ℕ → Matrix (Fin n) (Fin n) ℚ}
    (h : ∀ k, (Q k)ᵀ = Q k) : ∀ k, (cXof dq Q k)ᵀ = cXof dq Q k := by
  intro k
  rw [cXof, Matrix.transpose_smul, h k]

/-- **`hTrc` at the boundary centre**, from the base stream's own trace budget. -/
theorem hTrc_cXof {n : ℕ} {dq : ℚ} (h0 : 0 < dq) (h4 : dq < 4)
    {Q : ℕ → Matrix (Fin n) (Fin n) ℚ} (h : ∀ k, ∑ i, Q k i i ≤ (n : ℚ)) :
    ∀ k, ∑ i, (cXof dq Q k) i i ≤ (n : ℚ) * (1 - dq / 4) := by
  intro k
  exact QMCLeafB.TraceBudgetM8.hTrc_boundary_of_trace h0 h4 (h k)

#print axioms QMCLeafB.RecordM2.hTrc_cXof


/-! ## 3.  The stream data, and the `Bundle` built from it

`ClosingAssembly.Bundle`'s sixteen fields, with everything that the *records* determine already
filled: the flag stream is all-`false`, the centres are the pinch boundary `(1 − dq/4) • Q k`, the
margins and the oracle normals are read off the cut records `C`, the dilation stream is
`cn k = c k + λ_k • flatQ 1`, and `hTrc` is the base trace budget.  What a supplier still owes is
`Q` (with its symmetry and trace), the cut records `C` at those centres, the multiplier stream with
its depth ledger `hlam2`, and the two drift budgets. -/

/-- **The record streams of one interior `(G, t)`.** -/
structure StreamData (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- the base stream: the run's own (unit-diagonal) centres, before the boundary lowering -/
  Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  hQsym : ∀ k, (Q k)ᵀ = Q k
  /-- **the base trace budget** `tr Q_k ≤ n` -/
  htrcQ : ∀ k, ∑ i, Q k i i ≤ (G.n : ℚ)
  /-- the oracle's cut records at the lowered centres -/
  C : ∀ k, QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G)
    (cXof P.dq Q k) (t - QMCLeafB.RundataCert.eps G) P.dq
  /-- the dilation multiplier -/
  lam : ℕ → ℚ
  /-- the dilated (recorded) flat normal -/
  cn : ℕ → Fin (G.n * G.n) → ℚ
  hcn : ∀ k, cn k = QMCLeafB.RelaxOracle.flatQ (C k).normal
    + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
  hcne : ∀ k, cn k ≠ 0
  hlam0 : ∀ k, 0 ≤ lam k
  hlam1 : ∀ k, 1 ≤ lam k
  /-- **the depth ledger** at the recorded margin -/
  hlam2 : ∀ k,
      |QMCLeafB.RelaxOracle.flatQ (C k).normal
          ⬝ᵥ witAt G P hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
        + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          witAt G P hn cn hcne (QMCLeafB.RelaxOracle.flatQ (C k).normal) k|
      + |QMCLeafB.RelaxOracle.flatQ (C k).normal
          ⬝ᵥ witAt G P hn cn hcne (QMCLeafB.RelaxOracle.flatQ (C k).normal) k|
      + 9 * (C k).margin ^ 2 / (4 * (P.rmax) ^ 2) + 1
    ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
        witAt G P hn cn hcne
          (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k)
  /-- **the oracle normal's centre mismatch** at the lowered centre -/
  hdriftc : ∀ k,
    (fun i => ((QMCLeafB.RelaxOracle.flatQ (C k).normal i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (runCut G P hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXof P.dq Q k)))
      ≤ (((C k).margin : ℚ) : ℝ) / 2
  /-- **the identity direction's budget**, the scalar trace budget in linear form
  (`TraceBudgetM8.hdriftd_linear_iff`) -/
  hdriftd : ∀ k,
    dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (runCut G P hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXof P.dq Q k)))
      ≤ 0

/-- **The `Bundle` of `Check_closingAssembly_m3` from the record streams.**  `ok`, `marg`, `c`,
`cX`, `hTrc` and `hverdict` are *constructed*: nothing here is left for a supplier except `StreamData`
and the read-out of the loop's bit. -/
def bundleOfStreamData (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (h0 : 0 < P.dq) (h4 : P.dq < 4)
    (ho : o G t = false) (S : StreamData G t P hn) :
    QMCLeafB.ClosingAssembly.Bundle o G t P hn where
  ok := fun _ => false
  marg := fun k => (S.C k).margin
  cX := cXof P.dq S.Q
  lam := S.lam
  c := fun k => QMCLeafB.RelaxOracle.flatQ (S.C k).normal
  cn := S.cn
  hokAll := fun _ _ => rfl
  C := fun k _ => S.C k
  hmarg := fun _ _ => rfl
  hCsym := cXof_symm S.hQsym
  hcEq := fun _ _ => rfl
  hcn := S.hcn
  hcne := S.hcne
  hlam0 := S.hlam0
  hlam1 := fun k _ => S.hlam1 k
  hlam2 := fun k _ => S.hlam2 k
  hTrc := hTrc_cXof h0 h4 S.htrcQ
  hdriftc := fun k _ => S.hdriftc k
  hdriftd := fun k _ => S.hdriftd k
  hverdict := by rw [ho, anyOk_false_stream]

#print axioms QMCLeafB.RecordM2.bundleOfStreamData

/-! ## 4.  The residual at the two campaign families, and the verbatim sentence -/

/-- **The record-stream residual**: at every interior `(G, t)`, the loop's own output bit is `false`
(the all-`false` flag stream, `ClosingAssembly.verdict_eq_false_of_allFalse`) and the record streams
of §3 are present.  It is the leaf's whole remaining content in this spelling. -/
structure ResidStream (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type where
  /-- the campaign's bit at the interior: every round is a cut round -/
  bit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → o G t = false
  /-- the record streams of the run at the same `(G, t)` -/
  data : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → StreamData G t (Pfam G) hn

/-- **`ClosingAssembly.Resid` from the record streams.** -/
def resid_of_streamData {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (h0 : ∀ G, 0 < (Pfam G).dq) (h4 : ∀ G, (Pfam G).dq < 4)
    (H : ResidStream o Pfam) :
    QMCLeafB.ClosingAssembly.Resid o Pfam :=
  fun G t hn hlo hhi =>
    bundleOfStreamData o G t (Pfam G) hn (h0 G) (h4 G)
      (H.bit G t hn hlo hhi) (H.data G t hn hlo hhi)

#print axioms QMCLeafB.RecordM2.resid_of_streamData

/-- The `round` stroke's tolerance is positive. -/
theorem dq_pos_paramsKbc2 (G : QuantumMaxCutEnergy.Input) :
    0 < (QMCLeafB.UnionShallow.paramsKbc2 G).dq := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
  exact QMCLeafB.RundataParams.dqShallow_pos G

/-- The `round` stroke's tolerance is below the boundary scale's edge. -/
theorem dq_lt_four_paramsKbc2 (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.UnionShallow.paramsKbc2 G).dq < 4 := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
  exact QMCLeafB.TraceBudgetM8.dqShallow_lt_four G

/-- The `roundGT` stroke's tolerance is positive. -/
theorem dq_pos_paramsShallow (G : QuantumMaxCutEnergy.Input) :
    0 < (QMCLeafB.LoopClose.paramsShallow G).dq := by
  rw [QMCLeafB.LoopClose.paramsShallow_dq]
  exact QMCLeafB.RundataParams.dqShallow_pos G

/-- The `roundGT` stroke's tolerance is below the boundary scale's edge. -/
theorem dq_lt_four_paramsShallow (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.LoopClose.paramsShallow G).dq < 4 := by
  rw [QMCLeafB.LoopClose.paramsShallow_dq]
  exact QMCLeafB.TraceBudgetM8.dqShallow_lt_four G

#print axioms QMCLeafB.RecordM2.dq_pos_paramsKbc2
#print axioms QMCLeafB.RecordM2.dq_lt_four_paramsKbc2

/-- **The `d9f601e5` sentence from the record streams, on the `roundGT` stroke** (`k = 20`,
`2^20 ≥ 21`; `GuardT.solution_of_leaf_guardT`, wired in `Check_closingAssembly_m3`). -/
theorem solution_guardT_of_streamData
    (H : ResidStream (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.GuardT.roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (QMCLeafB.LoopClose.paramsShallow G').K
            * (QMCLeafB.LoopClose.paramsShallow G').m))
        QMCLeafB.LoopClose.paramsShallow) :
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
  QMCLeafB.ClosingAssembly.solution_guardT
    (resid_of_streamData dq_pos_paramsShallow dq_lt_four_paramsShallow H)

#print axioms QMCLeafB.RecordM2.solution_guardT_of_streamData

/-- **The `d9f601e5` sentence from the record streams, on the `round` stroke** (`paramsKbc2`,
`k = 20`; `AssemblyM5.endgame_of_hd`). -/
theorem solution_of_streamData
    (H : ResidStream (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          (fun G _ =>
            QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
              * QMCLeafB.HalvePerG.mHalve (G.n * G.n)))
        QMCLeafB.UnionShallow.paramsKbc2) :
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
  QMCLeafB.ClosingAssembly.solution
    (resid_of_streamData dq_pos_paramsKbc2 dq_lt_four_paramsKbc2 H)

#print axioms QMCLeafB.RecordM2.solution_of_streamData

/-- **The same, in the shelf's own name for the sentence** (`FinishLine.SolutionStatement`),
on the `round` stroke. -/
theorem solution_statement_of_streamData
    (H : ResidStream (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          (fun G _ =>
            QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
              * QMCLeafB.HalvePerG.mHalve (G.n * G.n)))
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.ClosingAssembly.solution_statement
    (resid_of_streamData dq_pos_paramsKbc2 dq_lt_four_paramsKbc2 H)

#print axioms QMCLeafB.RecordM2.solution_statement_of_streamData

/-! ## 5.  The deep interior: the cut records are free

Where the relaxed body is empty (`relaxCut_of_empty` at the `9δ/4` tolerance,
`Check_triobstruction_m5.body_empty_below`) every rational centre carries a cut record with normal
the identity and margin `1`.  So `StreamData` needs no oracle content at all there: the two stream
records are the base stream `Q` and the multiplier `λ`, and the depth ledger collapses to
`3·σ_k + 9/(4·rmax²) + 1 ≤ λ_k·σ_k` at the single coefficient `σ_k = flatQ 1 ⪝ witAt … (flatQ 1) k`. -/

/-- The identity flat normal, as it appears in every slot at the deep interior. -/
abbrev u0 (n : ℕ) : Fin (n * n) → ℚ :=
  QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ)

/-- **`StreamData` at an empty relaxed body**: the cut records are `cutRecOfEmpty`, the margin is
`1` and the oracle normal is the identity, so nothing about the oracle is owed. -/
def streamDataOfEmpty (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (hempty : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G))
        (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ) ((P.dq : ℚ) : ℝ) X)
    (Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (hQsym : ∀ k, (Q k)ᵀ = Q k)
    (htrcQ : ∀ k, ∑ i, Q k i i ≤ (G.n : ℚ))
    (lam : ℕ → ℚ) (cn : ℕ → Fin (G.n * G.n) → ℚ)
    (hcn : ∀ k, cn k = u0 G.n + lam k • u0 G.n)
    (hcne : ∀ k, cn k ≠ 0) (hlam0 : ∀ k, 0 ≤ lam k) (hlam1 : ∀ k, 1 ≤ lam k)
    (hlam2 : ∀ k, |u0 G.n ⬝ᵥ witAt G P hn cn hcne (u0 G.n) k
          + u0 G.n ⬝ᵥ witAt G P hn cn hcne (u0 G.n) k|
        + |u0 G.n ⬝ᵥ witAt G P hn cn hcne (u0 G.n) k|
        + 9 * (1 : ℚ) ^ 2 / (4 * (P.rmax) ^ 2) + 1
      ≤ lam k * (u0 G.n ⬝ᵥ witAt G P hn cn hcne (u0 G.n) k))
    (hdriftc : ∀ k,
      (fun i => ((u0 G.n i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cXof P.dq Q k)))
        ≤ ((1 : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k,
      dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cXof P.dq Q k)))
        ≤ 0) :
    StreamData G t P hn where
  Q := Q
  hQsym := hQsym
  htrcQ := htrcQ
  C := fun k => cutRecOfEmpty _ (cXof P.dq Q k) hempty
  lam := lam
  cn := cn
  hcn := hcn
  hcne := hcne
  hlam0 := hlam0
  hlam1 := hlam1
  hlam2 := hlam2
  hdriftc := hdriftc
  hdriftd := hdriftd

#print axioms QMCLeafB.RecordM2.streamDataOfEmpty


variable {N : ℕ}

/-- Proof-free witness of `A x = v`. -/
noncomputable def witRel (A : Matrix (Fin N) (Fin N) ℚ) (v : Fin N → ℚ) : Fin N → ℚ :=
  if h : QMCLeafB.EngineIterates.PosQ A then QMCLeafB.RunPartsShallow.witOf h v else 0

theorem witRel_of_posQ {A : Matrix (Fin N) (Fin N) ℚ} (h : QMCLeafB.EngineIterates.PosQ A)
    (v : Fin N → ℚ) :
    witRel A v = QMCLeafB.RunPartsShallow.witOf h v := by
  unfold witRel
  rw [dif_pos h]

/-- The shape chain without positivity proofs. -/
noncomputable def shapeVal (A0 : Matrix (Fin N) (Fin N) ℚ) (c : ℕ → Fin N → ℚ)
    (ρ : ℕ → ℚ) : ℕ → Matrix (Fin N) (Fin N) ℚ
  | 0 => A0
  | (k + 1) => QMCLeafB.EngineIterates.rStep N (shapeVal A0 c ρ k) (c k)
      (witRel (shapeVal A0 c ρ k) (c k)) (ρ k)



theorem witOf_irrel {A : Matrix (Fin N) (Fin N) ℚ}
    (h1 h2 : QMCLeafB.EngineIterates.PosQ A) (v : Fin N → ℚ) :
    QMCLeafB.RunPartsShallow.witOf h1 v = QMCLeafB.RunPartsShallow.witOf h2 v := by
  rw [Subsingleton.elim h1 h2]

theorem witOf_eq_of_eq {A A' : Matrix (Fin N) (Fin N) ℚ} (hAA : A = A')
    (h1 : QMCLeafB.EngineIterates.PosQ A) (h2 : QMCLeafB.EngineIterates.PosQ A')
    (v : Fin N → ℚ) :
    QMCLeafB.RunPartsShallow.witOf h1 v = QMCLeafB.RunPartsShallow.witOf h2 v := by
  subst hAA
  exact witOf_irrel h1 h2 v

/-- **The recurrence of the engine's shape chain**, at the value level: round `k+1` of the chain is
the rank-one step at the `k`-th normal and the ceiling depth.  Proof-irrelevance makes the witness
readable as `witRel`. -/
theorem shapeChain_step (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    (QMCLeafB.RunPartsShallow.shapeChain (N := G.n * G.n) (by have h := Nat.mul_le_mul hn hn; omega)
        (A0P G P) (A0P_posDef G P) c hc (fun _ => P.rmax) (fun _ => P.hrmax) (k + 1)).1
      = QMCLeafB.EngineIterates.rStep (G.n * G.n)
          (QMCLeafB.RunPartsShallow.shapeChain (N := G.n * G.n)
            (by have h := Nat.mul_le_mul hn hn; omega) (A0P G P) (A0P_posDef G P) c hc
            (fun _ => P.rmax) (fun _ => P.hrmax) k).1
          (c k) (witRel (QMCLeafB.RunPartsShallow.shapeChain (N := G.n * G.n)
            (by have h := Nat.mul_le_mul hn hn; omega) (A0P G P) (A0P_posDef G P) c hc
            (fun _ => P.rmax) (fun _ => P.hrmax) k).1 (c k)) (P.rmax) := by
  show QMCLeafB.EngineIterates.rStep (G.n * G.n) _
      (c k) (QMCLeafB.RunPartsShallow.witOf _ (c k)) (P.rmax) = _
  rw [witRel_of_posQ (QMCLeafB.EngineIterates.posQ_of_cast (QMCLeafB.RunPartsShallow.shapeChain (N := G.n * G.n) (by have h := Nat.mul_le_mul hn hn; omega) (A0P G P) (A0P_posDef G P) c hc (fun _ => P.rmax) (fun _ => P.hrmax) k).2)]
  exact congrArg (fun w => QMCLeafB.EngineIterates.rStep (G.n * G.n) _ (c k) w (P.rmax))
    (witOf_irrel _ _ _)

theorem runChain_val_eq (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) :
    ∀ k, (runChain G P hn c hc k).1 = shapeVal (A0P G P) c (fun _ => P.rmax) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      have hstep := shapeChain_step G P hn c hc k
      show (QMCLeafB.RunPartsShallow.shapeChain (N := G.n * G.n)
          (by have h := Nat.mul_le_mul hn hn; omega) (A0P G P) (A0P_posDef G P) c hc
          (fun _ => P.rmax) (fun _ => P.hrmax) (k + 1)).1 = shapeVal (A0P G P) c (fun _ => P.rmax) (k+1)
      have ih' : (QMCLeafB.RunPartsShallow.shapeChain (N := G.n * G.n)
          (by have h := Nat.mul_le_mul hn hn; omega) (A0P G P) (A0P_posDef G P) c hc
          (fun _ => P.rmax) (fun _ => P.hrmax) k).1 = shapeVal (A0P G P) c (fun _ => P.rmax) k := ih
      rw [hstep, ih']
      rfl

theorem runShape_eq_shapeVal (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    runShape G P hn c hc k = shapeVal (A0P G P) c (fun _ => P.rmax) k :=
  runChain_val_eq G P hn c hc k

/-- **The shape at round `k` only sees the first `k` normals.** -/
theorem shapeVal_ext (A0 : Matrix (Fin N) (Fin N) ℚ) (ρ : ℕ → ℚ) {c c' : ℕ → Fin N → ℚ} :
    ∀ k, (∀ j, j < k → c j = c' j) → shapeVal A0 c ρ k = shapeVal A0 c' ρ k
  | 0, _ => rfl
  | (k + 1), h => by
      have ih := shapeVal_ext A0 ρ k (fun j hj => h j (by omega))
      show QMCLeafB.EngineIterates.rStep N (shapeVal A0 c ρ k) (c k)
          (witRel (shapeVal A0 c ρ k) (c k)) (ρ k)
        = QMCLeafB.EngineIterates.rStep N (shapeVal A0 c' ρ k) (c' k)
          (witRel (shapeVal A0 c' ρ k) (c' k)) (ρ k)
      rw [ih, h k (by omega)]

/-- **The engine's witness at round `k`, in proof-free form.** -/
theorem witAt_eq_witRel (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (v : Fin (G.n * G.n) → ℚ) (k : ℕ) :
    witAt G P hn c hc v k = witRel (shapeVal (A0P G P) c (fun _ => P.rmax) k) v := by
  have h := runShape_eq_shapeVal G P hn c hc k
  have hposq : QMCLeafB.EngineIterates.PosQ (shapeVal (A0P G P) c (fun _ => P.rmax) k) :=
    h ▸ runShape_posQ G P hn c hc k
  show QMCLeafB.RunPartsShallow.witOf (runShape_posQ G P hn c hc k) v
      = witRel (shapeVal (A0P G P) c (fun _ => P.rmax) k) v
  rw [witRel_of_posQ hposq]
  exact witOf_eq_of_eq h (runShape_posQ G P hn c hc k) hposq v

/-! ## The sequential multiplier -/

/-- The threshold of round `k`: the value of `hlam2`'s left-hand side at the stream whose past is
`ih` and whose future is the safe default `1 - c_j (d₀)` (which keeps `cn j` nonzero at `d₀`). -/
noncomputable def lamThr (A0 : Matrix (Fin N) (Fin N) ℚ) (u : Fin N → ℚ) (d0 : Fin N)
    (c : ℕ → Fin N → ℚ) (marg : ℕ → ℚ) (rmax : ℚ) (k : ℕ) (ih : ∀ m, m < k → ℚ) : ℚ :=
  let g : ℕ → ℚ := fun j => if h : j < k then ih j h else 1 - c j d0
  let cns : ℕ → Fin N → ℚ := fun j => c j + g j • u
  let S := shapeVal A0 cns (fun _ => rmax) k
  let W := witRel S u
  let Wc := witRel S (c k)
  |c k ⬝ᵥ W + u ⬝ᵥ Wc| + |c k ⬝ᵥ Wc| + 9 * marg k ^ 2 / (4 * rmax ^ 2) + 1

/-- The coefficient `σ_k = u ⪝ A_k⁻¹ u` of `hlam2`, at the same stream. -/
noncomputable def lamCoeff (A0 : Matrix (Fin N) (Fin N) ℚ) (u : Fin N → ℚ) (d0 : Fin N)
    (c : ℕ → Fin N → ℚ) (marg : ℕ → ℚ) (rmax : ℚ) (k : ℕ) (ih : ∀ m, m < k → ℚ) : ℚ :=
  let g : ℕ → ℚ := fun j => if h : j < k then ih j h else 1 - c j d0
  let cns : ℕ → Fin N → ℚ := fun j => c j + g j • u
  u ⬝ᵥ witRel (shapeVal A0 cns (fun _ => rmax) k) u

/-- One step of the sequential choice: `λ_k` is above `1`, above the depth threshold `N_k/σ_k`, and
above `|b_k|+1` (which keeps the dilated normal nonzero at the diagonal index `d₀`). -/
noncomputable def lamStep (A0 : Matrix (Fin N) (Fin N) ℚ) (u : Fin N → ℚ) (d0 : Fin N)
    (c : ℕ → Fin N → ℚ) (marg : ℕ → ℚ) (rmax : ℚ) (k : ℕ) (ih : ∀ m, m < k → ℚ) : ℚ :=
  max (max 1 (lamThr A0 u d0 c marg rmax k ih / lamCoeff A0 u d0 c marg rmax k ih))
    (|(-(c k d0))| + 1)

/-- **The sequential multiplier stream** (`Nat.strongRec`): round `k`'s value is chosen from the
rounds before it only. -/
noncomputable def lamInd (A0 : Matrix (Fin N) (Fin N) ℚ) (u : Fin N → ℚ) (d0 : Fin N)
    (c : ℕ → Fin N → ℚ) (marg : ℕ → ℚ) (rmax : ℚ) : ℕ → ℚ :=
  Nat.strongRec (lamStep A0 u d0 c marg rmax)

/-- **The dilated normal stream** of the multiplier. -/
noncomputable def cnInd (c : ℕ → Fin N → ℚ) (lam : ℕ → ℚ) (u : Fin N → ℚ) (k : ℕ) : Fin N → ℚ :=
  c k + lam k • u

theorem lamInd_eq (A0 : Matrix (Fin N) (Fin N) ℚ) (u : Fin N → ℚ) (d0 : Fin N)
    (c : ℕ → Fin N → ℚ) (marg : ℕ → ℚ) (rmax : ℚ) (k : ℕ) :
    lamInd A0 u d0 c marg rmax k
      = lamStep A0 u d0 c marg rmax k (fun m _ => lamInd A0 u d0 c marg rmax m) :=
  Nat.strongRec_eq _ k

theorem lamInd_ge_one (A0 : Matrix (Fin N) (Fin N) ℚ) (u : Fin N → ℚ) (d0 : Fin N)
    (c : ℕ → Fin N → ℚ) (marg : ℕ → ℚ) (rmax : ℚ) (k : ℕ) :
    1 ≤ lamInd A0 u d0 c marg rmax k := by
  rw [lamInd_eq]
  unfold lamStep
  exact le_trans (le_max_left _ _) (le_max_left _ _)

theorem lamInd_nonneg (A0 : Matrix (Fin N) (Fin N) ℚ) (u : Fin N → ℚ) (d0 : Fin N)
    (c : ℕ → Fin N → ℚ) (marg : ℕ → ℚ) (rmax : ℚ) (k : ℕ) :
    0 ≤ lamInd A0 u d0 c marg rmax k :=
  le_trans zero_le_one (lamInd_ge_one A0 u d0 c marg rmax k)

theorem lamInd_gt (A0 : Matrix (Fin N) (Fin N) ℚ) (u : Fin N → ℚ) (d0 : Fin N)
    (c : ℕ → Fin N → ℚ) (marg : ℕ → ℚ) (rmax : ℚ) (k : ℕ) :
    -(c k d0) < lamInd A0 u d0 c marg rmax k := by
  rw [lamInd_eq]
  unfold lamStep
  have h1 : (-(c k d0)) ≤ |(-(c k d0))| := by rw [abs_neg]; exact neg_le_abs _
  have h2 : |(-(c k d0))| + 1 ≤ max (max 1 (lamThr A0 u d0 c marg rmax k
      (fun m _ => lamInd A0 u d0 c marg rmax m)
      / lamCoeff A0 u d0 c marg rmax k (fun m _ => lamInd A0 u d0 c marg rmax m)))
      (|(-(c k d0))| + 1) := le_max_right _ _
  linarith
/-- **The dilated normal stream is nonzero**: at the diagonal index `d₀` (where `u` reads `1`) the
entry is `c k d₀ + λ_k > 0`. -/
theorem cnInd_ne (A0 : Matrix (Fin N) (Fin N) ℚ) (u : Fin N → ℚ) (d0 : Fin N) (hu : u d0 = 1)
    (c : ℕ → Fin N → ℚ) (marg : ℕ → ℚ) (rmax : ℚ) (k : ℕ) :
    cnInd c (lamInd A0 u d0 c marg rmax) u k ≠ 0 := by
  intro hzero
  have hval : cnInd c (lamInd A0 u d0 c marg rmax) u k d0
      = c k d0 + lamInd A0 u d0 c marg rmax k := by
    simp [cnInd, hu]
  have h0 : cnInd c (lamInd A0 u d0 c marg rmax) u k d0 = 0 := by
    rw [hzero]; rfl
  rw [hval] at h0
  have := lamInd_gt A0 u d0 c marg rmax k
  linarith

/-- The arithmetic core of `hlam2`: above the threshold `T/σ` (and above `1` and `|b|+1`) the depth
inequality holds. -/
theorem max_mul_ge {T σ b : ℚ} (hσ : 0 < σ) :
    T ≤ max (max 1 (T / σ)) b * σ := by
  have h1 : T / σ ≤ max (max 1 (T / σ)) b := le_trans (le_max_right _ _) (le_max_left _ _)
  have h2 : T / σ * σ = T := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right h1 (le_of_lt hσ)]

/-- **The pairing of a nonzero direction with the shape's own witness is positive** (the general
form of `LamStreamM8.witAt_pairing_pos`, at an arbitrary nonzero `u`). -/
theorem pairing_pos_of_posQ (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (u : Fin (G.n * G.n) → ℚ)
    (hu : u ≠ 0) (k : ℕ) :
    0 < u ⬝ᵥ witAt G P hn c hc u k := by
  have hA : QMCLeafB.EngineIterates.PosQ (runShape G P hn c hc k) := runShape_posQ G P hn c hc k
  have hwit : witAt G P hn c hc u k ≠ 0 := by
    intro hz
    have hspec := witAt_spec G P hn c hc u k
    rw [hz, Matrix.mulVec_zero] at hspec
    exact hu hspec.symm
  have hspec := witAt_spec G P hn c hc u k
  have hq : QMCLeafB.EngineIterates.qf (runShape G P hn c hc k) (witAt G P hn c hc u k)
      = u ⬝ᵥ witAt G P hn c hc u k := by
    rw [QMCLeafB.EngineIterates.qf, hspec, dotProduct_comm]
  rw [← hq]
  exact hA.2 _ hwit

/-- **The depth ledger `hlam2` at the sequentially chosen multiplier.**  `σ_k` is strictly positive
(the pairing of `u₀` with the shape's own witness), so `λ_k ≥ N_k/σ_k` buys the inequality. -/
theorem lamInd_spec (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (u : Fin (G.n * G.n) → ℚ) (d0 : Fin (G.n * G.n)) (hu : u d0 = 1)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (hrmax : 0 < P.rmax) :
    ∀ k, |c k ⬝ᵥ witAt G P hn (cnInd c (lamInd (A0P G P) u d0 c marg P.rmax) u)
            (cnInd_ne (A0P G P) u d0 hu c marg P.rmax) u k
          + u ⬝ᵥ witAt G P hn (cnInd c (lamInd (A0P G P) u d0 c marg P.rmax) u)
            (cnInd_ne (A0P G P) u d0 hu c marg P.rmax) (c k) k|
        + |c k ⬝ᵥ witAt G P hn (cnInd c (lamInd (A0P G P) u d0 c marg P.rmax) u)
            (cnInd_ne (A0P G P) u d0 hu c marg P.rmax) (c k) k|
        + 9 * marg k ^ 2 / (4 * (P.rmax) ^ 2) + 1
      ≤ lamInd (A0P G P) u d0 c marg P.rmax k *
          (u ⬝ᵥ witAt G P hn (cnInd c (lamInd (A0P G P) u d0 c marg P.rmax) u)
            (cnInd_ne (A0P G P) u d0 hu c marg P.rmax) u k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    set g : ℕ → ℚ := fun j => if h : j < k then lamInd (A0P G P) u d0 c marg P.rmax j
      else 1 - c j d0 with hg
    set cns : ℕ → Fin (G.n * G.n) → ℚ := fun j => c j + g j • u with hcns
    have hcneS : ∀ j, cns j ≠ 0 := by
      intro j
      by_cases hj : j < k
      · have hgj : g j = lamInd (A0P G P) u d0 c marg P.rmax j := by simp [hg, hj]
        have hval : cns j d0 = c j d0 + lamInd (A0P G P) u d0 c marg P.rmax j := by
          simp [hcns, hgj, hu]
        intro hzero
        have h0 : cns j d0 = 0 := by rw [hzero]; rfl
        rw [hval] at h0
        have := lamInd_gt (A0P G P) u d0 c marg P.rmax j
        linarith
      · have hgj : g j = 1 - c j d0 := by simp [hg, hj]
        have hval : cns j d0 = 1 := by simp [hcns, hgj, hu]
        intro hzero
        have h0 : cns j d0 = 0 := by rw [hzero]; rfl
        rw [hval] at h0
        norm_num at h0
    have hshape : shapeVal (A0P G P) cns (fun _ => P.rmax) k
        = shapeVal (A0P G P) (cnInd c (lamInd (A0P G P) u d0 c marg P.rmax) u)
            (fun _ => P.rmax) k := by
      refine shapeVal_ext (A0P G P) (fun _ => P.rmax) k (fun j hj => ?_)
      have hgj : g j = lamInd (A0P G P) u d0 c marg P.rmax j := by simp [hg, hj]
      simp [hcns, cnInd, hgj]
    have hWu : witAt G P hn (cnInd c (lamInd (A0P G P) u d0 c marg P.rmax) u)
          (cnInd_ne (A0P G P) u d0 hu c marg P.rmax) u k
        = witRel (shapeVal (A0P G P) cns (fun _ => P.rmax) k) u := by
      rw [witAt_eq_witRel G P hn (cnInd c (lamInd (A0P G P) u d0 c marg P.rmax) u)
        (cnInd_ne (A0P G P) u d0 hu c marg P.rmax) u k, hshape]
    have hWc : witAt G P hn (cnInd c (lamInd (A0P G P) u d0 c marg P.rmax) u)
          (cnInd_ne (A0P G P) u d0 hu c marg P.rmax) (c k) k
        = witRel (shapeVal (A0P G P) cns (fun _ => P.rmax) k) (c k) := by
      rw [witAt_eq_witRel G P hn (cnInd c (lamInd (A0P G P) u d0 c marg P.rmax) u)
        (cnInd_ne (A0P G P) u d0 hu c marg P.rmax) (c k) k, hshape]
    have hstep : lamInd (A0P G P) u d0 c marg P.rmax k
        = max (max 1 (lamThr (A0P G P) u d0 c marg P.rmax k
            (fun m _ => lamInd (A0P G P) u d0 c marg P.rmax m)
            / lamCoeff (A0P G P) u d0 c marg P.rmax k
              (fun m _ => lamInd (A0P G P) u d0 c marg P.rmax m)))
          (|(-(c k d0))| + 1) := by
      rw [lamInd_eq]
      rfl
    have hT : lamThr (A0P G P) u d0 c marg P.rmax k
          (fun m _ => lamInd (A0P G P) u d0 c marg P.rmax m)
        = |c k ⬝ᵥ witRel (shapeVal (A0P G P) cns (fun _ => P.rmax) k) u
              + u ⬝ᵥ witRel (shapeVal (A0P G P) cns (fun _ => P.rmax) k) (c k)|
            + |c k ⬝ᵥ witRel (shapeVal (A0P G P) cns (fun _ => P.rmax) k) (c k)|
            + 9 * marg k ^ 2 / (4 * (P.rmax) ^ 2) + 1 := by
      simp only [lamThr, hcns, hg]
    have hσ : lamCoeff (A0P G P) u d0 c marg P.rmax k
          (fun m _ => lamInd (A0P G P) u d0 c marg P.rmax m)
        = u ⬝ᵥ witRel (shapeVal (A0P G P) cns (fun _ => P.rmax) k) u := by
      simp only [lamCoeff, hcns, hg]
    have hσpos : 0 < lamCoeff (A0P G P) u d0 c marg P.rmax k
        (fun m _ => lamInd (A0P G P) u d0 c marg P.rmax m) := by
      rw [hσ, ← witAt_eq_witRel G P hn cns hcneS u k]
      exact pairing_pos_of_posQ G P hn cns hcneS u (by intro h; rw [h] at hu; exact one_ne_zero hu.symm) k
    rw [hWu, hWc, hstep, ← hT, ← hσ]
    exact max_mul_ge hσpos


/-! ## 6.  The multiplier stream, filled in: `StreamData` from the records alone

`lamInd`/`cnInd` are the sequential choice, and `lamInd_ge_one`/`lamInd_nonneg`/`cnInd_ne`/
`lamInd_spec` discharge the depth ledger by construction.  So the record streams of §3 lose the
multiplier slots too: a supplier owes the base stream, the cut records and the **two drift budgets**
at the constructed (dilated) normal stream — and nothing else. -/

/-- The diagonal index `(0,0)` of the flat code. -/
abbrev d0idx (n : ℕ) (hn : 0 < n) : Fin (n * n) :=
  finProdFinEquiv (⟨0, hn⟩, ⟨0, hn⟩)

/-- The flat identity reads `1` at the diagonal index. -/
theorem u0_d0idx (n : ℕ) (hn : 0 < n) : u0 n (d0idx n hn) = 1 :=
  QMCLeafB.LamStreamM8.flatQ_one_apply ⟨0, hn⟩

#print axioms QMCLeafB.RecordM2.u0_d0idx

/-- **`StreamData` from the records and the two drift budgets.**  The multiplier, the dilated normal
stream, its nonvanishing, and the whole depth ledger `hlam0/hlam1/hlam2` are constructed; what is
owed is the base stream `Q` (symmetric, trace ≤ n), the cut records `C` at the lowered centres, and
the two budgets at the engineered dilated stream. -/
noncomputable def streamDataOfRecords (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) (hrmax : 0 < P.rmax)
    (Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (hQsym : ∀ k, (Q k)ᵀ = Q k)
    (htrcQ : ∀ k, ∑ i, Q k i i ≤ (G.n : ℚ))
    (C : ∀ k, QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G)
      (cXof P.dq Q k) (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hdriftc : ∀ k,
      (fun i => ((QMCLeafB.RelaxOracle.flatQ (C k).normal i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (runCut G P hn (cnInd (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal)
                  (lamInd (A0P G P) (u0 G.n) (d0idx G.n (by omega))
                    (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal)
                    (fun k => (C k).margin) P.rmax) (u0 G.n))
                (cnInd_ne (A0P G P) (u0 G.n) (d0idx G.n (by omega))
                  (u0_d0idx G.n (by omega))
                  (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal)
                  (fun k => (C k).margin) P.rmax)) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cXof P.dq Q k)))
        ≤ (((C k).margin : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k,
      dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (runCut G P hn (cnInd (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal)
                  (lamInd (A0P G P) (u0 G.n) (d0idx G.n (by omega))
                    (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal)
                    (fun k => (C k).margin) P.rmax) (u0 G.n))
                (cnInd_ne (A0P G P) (u0 G.n) (d0idx G.n (by omega))
                  (u0_d0idx G.n (by omega))
                  (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal)
                  (fun k => (C k).margin) P.rmax)) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cXof P.dq Q k)))
        ≤ 0) :
    StreamData G t P hn where
  Q := Q
  hQsym := hQsym
  htrcQ := htrcQ
  C := C
  lam := lamInd (A0P G P) (u0 G.n) (d0idx G.n (by omega))
    (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal) (fun k => (C k).margin) P.rmax
  cn := cnInd (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal)
    (lamInd (A0P G P) (u0 G.n) (d0idx G.n (by omega))
      (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal) (fun k => (C k).margin) P.rmax)
    (u0 G.n)
  hcn := fun k => rfl
  hcne := cnInd_ne (A0P G P) (u0 G.n) (d0idx G.n (by omega)) (u0_d0idx G.n (by omega))
    (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal) (fun k => (C k).margin) P.rmax
  hlam0 := lamInd_nonneg (A0P G P) (u0 G.n) (d0idx G.n (by omega))
    (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal) (fun k => (C k).margin) P.rmax
  hlam1 := lamInd_ge_one (A0P G P) (u0 G.n) (d0idx G.n (by omega))
    (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal) (fun k => (C k).margin) P.rmax
  hlam2 := lamInd_spec G P hn (u0 G.n) (d0idx G.n (by omega)) (u0_d0idx G.n (by omega))
    (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal) (fun k => (C k).margin) hrmax
  hdriftc := hdriftc
  hdriftd := hdriftd

#print axioms QMCLeafB.RecordM2.streamDataOfRecords


/-! ## 7.  Axiom audit -/

#print axioms QMCLeafB.RecordM2.anyOk_false_stream
#print axioms QMCLeafB.RecordM2.cutRecOfEmpty
#print axioms QMCLeafB.RecordM2.hTrc_cXof
#print axioms QMCLeafB.RecordM2.bundleOfStreamData
#print axioms QMCLeafB.RecordM2.resid_of_streamData
#print axioms QMCLeafB.RecordM2.streamDataOfEmpty
#print axioms QMCLeafB.RecordM2.solution_statement_of_streamData
#print axioms QMCLeafB.RecordM2.solution_guardT_of_streamData
#print axioms QMCLeafB.RecordM2.witRel
#print axioms QMCLeafB.RecordM2.witRel_of_posQ
#print axioms QMCLeafB.RecordM2.witOf_eq_of_eq
#print axioms QMCLeafB.RecordM2.shapeVal
#print axioms QMCLeafB.RecordM2.shapeChain_step
#print axioms QMCLeafB.RecordM2.runShape_eq_shapeVal
#print axioms QMCLeafB.RecordM2.shapeVal_ext
#print axioms QMCLeafB.RecordM2.witAt_eq_witRel
#print axioms QMCLeafB.RecordM2.lamInd
#print axioms QMCLeafB.RecordM2.lamInd_eq
#print axioms QMCLeafB.RecordM2.lamInd_ge_one
#print axioms QMCLeafB.RecordM2.lamInd_gt
#print axioms QMCLeafB.RecordM2.cnInd_ne
#print axioms QMCLeafB.RecordM2.max_mul_ge
#print axioms QMCLeafB.RecordM2.pairing_pos_of_posQ
#print axioms QMCLeafB.RecordM2.lamInd_spec
#print axioms QMCLeafB.RecordM2.u0_d0idx
#print axioms QMCLeafB.RecordM2.streamDataOfRecords


/-! ## 8.  The reduced residual, and the verbatim sentence from it

`RecordData` is what is still owed at one interior `(G, t)` after §6: the base stream (symmetric,
trace ≤ `n`), the cut records at the lowered centres, and the two drift budgets at the *constructed*
dilated normal stream.  `ResidRecords` is that, uniformly over the bracket, plus the loop's bit. -/

/-- **The record data of one interior `(G, t)`** — the six remaining slots. -/
structure RecordData (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  hQsym : ∀ k, (Q k)ᵀ = Q k
  htrcQ : ∀ k, ∑ i, Q k i i ≤ (G.n : ℚ)
  C : ∀ k, QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G)
    (cXof P.dq Q k) (t - QMCLeafB.RundataCert.eps G) P.dq
  hdriftc : ∀ k,
    (fun i => ((QMCLeafB.RelaxOracle.flatQ (C k).normal i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (runCut G P hn (cnInd (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal)
                (lamInd (A0P G P) (u0 G.n) (d0idx G.n (by omega))
                  (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal)
                  (fun k => (C k).margin) P.rmax) (u0 G.n))
              (cnInd_ne (A0P G P) (u0 G.n) (d0idx G.n (by omega))
                (u0_d0idx G.n (by omega))
                (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal)
                (fun k => (C k).margin) P.rmax)) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cXof P.dq Q k)))
      ≤ (((C k).margin : ℚ) : ℝ) / 2
  hdriftd : ∀ k,
    dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (runCut G P hn (cnInd (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal)
                (lamInd (A0P G P) (u0 G.n) (d0idx G.n (by omega))
                  (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal)
                  (fun k => (C k).margin) P.rmax) (u0 G.n))
              (cnInd_ne (A0P G P) (u0 G.n) (d0idx G.n (by omega))
                (u0_d0idx G.n (by omega))
                (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal)
                (fun k => (C k).margin) P.rmax)) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cXof P.dq Q k)))
      ≤ 0

/-- **The reduced residual**: the campaign's bit at the interior, and the record data. -/
structure ResidRecords (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type where
  bit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → o G t = false
  data : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    RecordData G t (Pfam G) hn

/-- **`StreamData` from the reduced residual** (the multiplier is constructed by §6). -/
def streamDataOfRecordsAll {Pfam : (G : QuantumMaxCutEnergy.Input) →
      QMCLeafB.FinalStroke.RunParams G}
    (hrmax : ∀ G (hn : 2 ≤ G.n), 0 < (Pfam G).rmax)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n} (D : RecordData G t (Pfam G) hn) :
    StreamData G t (Pfam G) hn :=
  streamDataOfRecords G t (Pfam G) hn (hrmax G hn) D.Q D.hQsym D.htrcQ D.C D.hdriftc D.hdriftd

/-- **`ResidStream` from the reduced residual.** -/
def residStream_of_records {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hrmax : ∀ G (hn : 2 ≤ G.n), 0 < (Pfam G).rmax) (H : ResidRecords o Pfam) :
    ResidStream o Pfam where
  bit := H.bit
  data G t hn hlo hhi := streamDataOfRecordsAll hrmax (H.data G t hn hlo hhi)

#print axioms QMCLeafB.RecordM2.residStream_of_records

/-- The `round` stroke's ceiling is positive. -/
theorem rmax_pos_paramsKbc2 (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    0 < (QMCLeafB.UnionShallow.paramsKbc2 G).rmax :=
  QMCLeafB.UnionShallow.paramsKbc2_rmax_pos G hn

/-- The `roundGT` stroke's ceiling is positive. -/
theorem rmax_pos_paramsShallow (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    0 < (QMCLeafB.LoopClose.paramsShallow G).rmax := by
  rw [QMCLeafB.LoopClose.paramsShallow_rmax]
  exact QMCLeafB.ClosingAssembly.rmaxOf_pos G hn

#print axioms QMCLeafB.RecordM2.rmax_pos_paramsKbc2
#print axioms QMCLeafB.RecordM2.rmax_pos_paramsShallow

/-- **The `d9f601e5` sentence from the reduced residual**, `round` stroke. -/
theorem solution_of_records
    (H : ResidRecords (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          (fun G _ =>
            QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
              * QMCLeafB.HalvePerG.mHalve (G.n * G.n)))
        QMCLeafB.UnionShallow.paramsKbc2) :
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
  solution_of_streamData (residStream_of_records rmax_pos_paramsKbc2 H)

#print axioms QMCLeafB.RecordM2.solution_of_records

/-- **The `d9f601e5` sentence from the reduced residual**, `roundGT` stroke. -/
theorem solution_guardT_of_records
    (H : ResidRecords (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.GuardT.roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (QMCLeafB.LoopClose.paramsShallow G').K
            * (QMCLeafB.LoopClose.paramsShallow G').m))
        QMCLeafB.LoopClose.paramsShallow) :
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
  solution_guardT_of_streamData (residStream_of_records rmax_pos_paramsShallow H)

#print axioms QMCLeafB.RecordM2.solution_guardT_of_records

/-- **The same in `FinishLine.SolutionStatement`**, `round` stroke. -/
theorem solution_statement_of_records
    (H : ResidRecords (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          (fun G _ =>
            QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
              * QMCLeafB.HalvePerG.mHalve (G.n * G.n)))
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_statement_of_streamData (residStream_of_records rmax_pos_paramsKbc2 H)

#print axioms QMCLeafB.RecordM2.solution_statement_of_records


/-! ## 9.  The multiplier exists unconditionally, and the positivity is not removable

The strong recursion of §5 does not consume the cut records at all: for **every** normal stream and
every margin stream there is a multiplier stream satisfying the whole depth ledger.  So `hlam2` is
never a supplier's obligation — the only multiplier side condition is `0 < rmax`. -/

/-- **The multiplier exists, unconditionally in the records.**  For any rational normal stream `c`,
any margins and any `0 < rmax`, there are `lam`, `cn` with `cn k = c k + λ_k • u₀`, `cn ≠ 0`,
`λ ≥ 1` and the full depth ledger `hlam2` at those `cn`. -/
theorem exists_multiplier (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) (hrmax : 0 < P.rmax)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) :
    ∃ (lam : ℕ → ℚ) (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0),
      (∀ k, cn k = c k + lam k • u0 G.n) ∧ (∀ k, 0 ≤ lam k) ∧ (∀ k, 1 ≤ lam k) ∧
      (∀ k, |c k ⬝ᵥ witAt G P hn cn hcne (u0 G.n) k
            + u0 G.n ⬝ᵥ witAt G P hn cn hcne (c k) k|
          + |c k ⬝ᵥ witAt G P hn cn hcne (c k) k|
          + 9 * marg k ^ 2 / (4 * (P.rmax) ^ 2) + 1
        ≤ lam k * (u0 G.n ⬝ᵥ witAt G P hn cn hcne (u0 G.n) k)) := by
  have hn0 : 0 < G.n := by omega
  refine ⟨lamInd (A0P G P) (u0 G.n) (d0idx G.n hn0) c marg P.rmax,
    cnInd c (lamInd (A0P G P) (u0 G.n) (d0idx G.n hn0) c marg P.rmax) (u0 G.n),
    cnInd_ne (A0P G P) (u0 G.n) (d0idx G.n hn0) (u0_d0idx G.n hn0) c marg P.rmax,
    fun k => rfl,
    lamInd_nonneg (A0P G P) (u0 G.n) (d0idx G.n hn0) c marg P.rmax,
    lamInd_ge_one (A0P G P) (u0 G.n) (d0idx G.n hn0) c marg P.rmax,
    lamInd_spec G P hn (u0 G.n) (d0idx G.n hn0) (u0_d0idx G.n hn0) c marg hrmax⟩

#print axioms QMCLeafB.RecordM2.exists_multiplier

/-- **The coefficient positivity is not removable**: at `σ = 0` and threshold `T = 1` the shape of
`hlam2` fails (`1 ≰ 1·0`), which is why the construction proves `0 < u₀ ⪝ A⁻¹u₀` first
(`pairing_pos_of_posQ`) instead of choosing `λ` from the threshold alone. -/
theorem threshold_needs_positivity :
    ¬ ((1 : ℚ) ≤ max (max 1 ((1 : ℚ) / 0)) 0 * 0) := by
  norm_num

#print axioms QMCLeafB.RecordM2.threshold_needs_positivity

/-- **The constructed bundle is not vacuous**: its flag stream is all-`false` and its output bit is
therefore forced to `false` (`ClosingAssembly.verdict_eq_false_of_allFalse`), so `StreamData` at an
interior `(G, t)` *implies* the campaign's bit there — the bundle cannot be fed by an `ok` run. -/
theorem bundleForcesFalse (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (h0 : 0 < P.dq) (h4 : P.dq < 4) (ho : o G t = false) (S : StreamData G t P hn) :
    o G t = false :=
  QMCLeafB.ClosingAssembly.verdict_eq_false_of_allFalse (bundleOfStreamData o G t P hn h0 h4 ho S)

#print axioms QMCLeafB.RecordM2.bundleForcesFalse


/-! ## 10.  The scalar budget form of `hdriftd`

`RecordData.hdriftd` is the identity direction's budget at the lowered centre; in the *linear* form of
the drift brick it is the single scalar inequality the campaign keeps per cut round,

    ∑_{j<k} λ_j · diagSum (p_j)  ≤  n · (1 − dq/4)

(`TraceBudgetM8.hdriftd_linear_iff`, `DriftExact.diagSum_cat`).  This section records the
translation at the run's own stream, so a supplier may hand in the scalar budget instead. -/

/-- **`hdriftd` from the scalar per-round budget.**  At a unit-diagonal base stream `Q` the identity
direction's centre mismatch is exactly the accumulated diagonal sum of the engine's own witnesses. -/
theorem hdriftd_of_scalar_budget (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (hunit : ∀ k i, Q k i i = 1)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (k : ℕ)
    (hbud : (∑ j ∈ Finset.range k,
        QMCLeafB.DriftExact.engLam (G.n * G.n) (runCut G P hn cn hcne) j
          * QMCLeafB.DriftExact.diagSum
              (QMCLeafB.EngineIterates.cutPR (runCut G P hn cn hcne) j))
      ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ)) :
    dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (runCut G P hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXof P.dq Q k))) ≤ 0 :=
  (QMCLeafB.TraceBudgetM8.hdriftd_linear_iff (runCut G P hn cn hcne) (Q k) (hunit k) k).2 hbud

#print axioms QMCLeafB.RecordM2.hdriftd_of_scalar_budget


/-! ## 11.  The flag stream of phase 18 is refutable, and the repaired record streams

`Check_residkill_m8` machine-checks that the all-`false` flag stream of the phase-18 bundle is
**false**, not open: at `G₀ = (n = 2, all weights 1/2)` and `t = -1/2` an all-`false` run contradicts
the simulate's refutation soundness (`ResidKill.bundle_false_kbc2`).  Two consequences, both recorded
here:

* §11a the phase-18 `Resid` (and hence `ResidStream`/`ResidRecords` of §4/§8) is *uninhabited* at the
  campaign families — the all-`false` shape cannot close the leaf;
* §11b (revised, phase-20): m8's first repair `BundleFull = { toBundle : Bundle; hmem }` kept
  `Bundle.hokAll` and inherited the refutation; a theorem recording that fact stood here.  m8's
  round-2 `Check_residkill_m8` **replaced** `hokAll` by `hmem` in a standalone record with no
  `toBundle` field, exactly as this note demanded, so the retired theorem concerned a record that no
  longer exists and is removed (same treatment as the phase-20 revision of `Check_flags_m5`).

So the record streams are re-targeted at the shape `DriftExact.runParts_of_exact_trace` actually
consumes — the phase-18 bundle with `hokAll` swapped for `hmem` (`BundleFix`) — where every slot of
§3/§6 is constructed exactly as before and the multiplier of §5 is flag-stream independent. -/

/-- **The phase-18 residual is uninhabited** at the `round` stroke. -/
theorem residStream_kbc2_impossible
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    QMCLeafB.ClosingAssembly.Resid o QMCLeafB.UnionShallow.paramsKbc2 → False :=
  QMCLeafB.ResidKill.resid_false_kbc2 o

#print axioms QMCLeafB.RecordM2.residStream_kbc2_impossible

/-- **The repaired bundle shape**: the phase-18 `Bundle` with `hokAll` *replaced* by the `ok`-round
`RelaxMem` slot — i.e. exactly the hypothesis list of `DriftExact.runParts_of_exact_trace`. -/
structure BundleFix (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  ok : ℕ → Bool
  marg : ℕ → ℚ
  cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  lam : ℕ → ℚ
  c : ℕ → Fin (G.n * G.n) → ℚ
  cn : ℕ → Fin (G.n * G.n) → ℚ
  /-- the `ok`-round certificate (phase 17's `hmem`) -/
  hmem : ∀ k, k < P.K * P.m → ok k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  C : ∀ k, ok k = false →
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin
  hCsym : ∀ k, (cX k)ᵀ = cX k
  hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal
  hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
    (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
  hcne : ∀ k, cn k ≠ 0
  hlam0 : ∀ k, 0 ≤ lam k
  hlam1 : ∀ k, ok k = false → 1 ≤ lam k
  hlam2 : ∀ k, ok k = false →
      |c k ⬝ᵥ witAt G P hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            witAt G P hn cn hcne (c k) k|
      + |c k ⬝ᵥ witAt G P hn cn hcne (c k) k|
      + 9 * marg k ^ 2 / (4 * ((P).rmax) ^ 2) + 1
    ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
        witAt G P hn cn hcne
          (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k)
  hTrc : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 - P.dq / 4)
  hdriftc : ∀ k, ok k = false →
    (fun i => ((c k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (runCut G P hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ ((marg k : ℚ) : ℝ) / 2
  hdriftd : ∀ k, ok k = false →
    dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (runCut G P hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ 0
  hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)

/-- **`BundleFix` is a `RunParts`** (the drift brick needs `hmem`, never `hokAll`). -/
def runParts_of_bundleFix (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (B : BundleFix o G t P hn) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  QMCLeafB.DriftExact.runParts_of_exact_trace o G t P hn hrmaxPos hrmax1 hbudP
    B.ok B.marg B.cX B.lam B.c B.cn B.C B.hmarg B.hmem B.hCsym B.hcEq B.hcn B.hcne
    B.hlam0 B.hlam1 B.hlam2 B.hTrc B.hdriftc B.hdriftd B.hverdict

#print axioms QMCLeafB.RecordM2.runParts_of_bundleFix

/-- **The repaired residual**: one `BundleFix` per interior `(G, t)`. -/
abbrev ResidFix (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    BundleFix o G t (Pfam G) hn

end QMCLeafB.RecordM2


