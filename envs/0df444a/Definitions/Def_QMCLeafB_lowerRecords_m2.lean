-- Prove2me | Definitions.Def_QMCLeafB_lowerRecords_m2
-- name    : QMCLeafB_lowerRecords_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:54:45.949313+00:00
-- url     : https://prove2.me/theorems/27795443-b9a3-448c-8524-4342203b92d2
-- title:
--   QMCLeafB lowerRecords_m2
-- statement:
--   # leaf B phase 18 — brick `lower-records` (swarm `smw1i2drp`, member m2, direction d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_pinchLower_m2
import Definitions.Def_QMCLeafB_assembly_m5
/-
# leaf B phase 18 — brick `lower-records` (swarm `smw1i2drp`, member m2, direction d3)

**The residual of item 1 as one bundle, and its one-step ending.**

`Check_pinchLower_m2` shows that the whole residual list of `DriftExact.runParts_at_interior_exact`
at the pinch-consistent centre `(1 − dq/4) • Q` follows from the *same* list at the program's own
centre `Q`.  This file packages that list as one structure and closes the leaf on top of it:

* `LoweredRecords G t` — the per-`(G,t)` bundle: the run's `ok`/`marg` streams, the queried centre
  stream `Q`, the normal/depth streams `lam`, `c`, `cn`, and
  - `hQsym`, `htraceQ` (the state's symmetry and diagonal trace),
  - `hCq` + `hpair` + `hmargq` (the `cut` verdict at the state, its nonnegative pairing, its margin),
  - `hunidiag`, `hmemq`, `huq` (the `ok` verdict at a unit-diagonal state, and the threshold shift),
  - `hcEq`, `hcn`, `hcne`, `hlam0/1/2` (the recorded normals and the depth ledger),
  - `hdriftcQ`, `hdriftdQ` (the two cumulative-drift budgets *at the state*, with the `dq/4`
    lowering charge made explicit),
  - `hverdict` (the campaign's flag read-out);
* `LoweredRecords.toRunParts` — one application of `PinchLower.runParts_lowered`;
* `HdFamily`, `hd_of_lowered` — the family form: `AssemblyM5.HdProp` from a bundle at every interior
  `(G, t)`;
* `endgame_of_lowered` — `FinishLine.SolutionStatement` (the campaign's verbatim reading of
  `d9f601e5`), and `endgame_of_lowered_verbatim` — the same sentence written out token for token, so
  that the last node of the leaf is `fun h => endgame_of_lowered h`.

What is *not* in this file (and is the whole remaining content of item 1 at the orbit): producing
`LoweredRecords G t` from the concrete iterate of the guarded round.  Everything below is the wiring
between that production and the platform sentence.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audit at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.LowerRecords

open QuantumMaxCutEnergy

/-- The campaign's produced bit — the `o` of `AssemblyM5.HdProp`. -/
noncomputable abbrev campBit : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
    QMCLeafB.RoundProgram.verdict
    (fun G' _ => QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
      * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))

/-- **The base-point record stream** at one interior `(G, t)`: the residual of item 1 after the
pinch-lowering, stated at the program's own centre `Q` (the state's `stX` reshaped). -/
structure LoweredRecords (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n) : Type where
  /-- did round `k` report `ok`? -/
  ok : ℕ → Bool
  /-- the per-round oracle margins -/
  marg : ℕ → ℚ
  /-- the queried centres: the program's own rational states -/
  Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  /-- the depth stream of the recorded normals -/
  lam : ℕ → ℚ
  /-- the recorded normal at a `cut` round -/
  c : ℕ → Fin (G.n * G.n) → ℚ
  /-- the dilated normal `c + lam • flat 1` (whose witness the ledger charges) -/
  cn : ℕ → Fin (G.n * G.n) → ℚ
  /-- the `ok` round's own threshold `stT − epsOf` -/
  u' : ℕ → ℚ
  /-- the queried state is symmetric (the entrywise snap preserves symmetry) -/
  hQsym : ∀ k, (Q k)ᵀ = Q k
  /-- the state's diagonal trace is at most `n` -/
  htraceQ : ∀ k, ∑ i, (Q k) i i ≤ (G.n : ℚ)
  /-- the `cut` verdict at the state -/
  hCq : ∀ k, ok k = false →
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (Q k)
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq
  /-- the cut's normal pairs nonnegatively with the state (the diagonal branch's `Qᵢᵢ > 0`) -/
  hpair : ∀ k (hok : ok k = false),
    0 ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat (hCq k hok).normal)
      (QMCLeafB.SepOracle.castMat (Q k))
  /-- the recorded margin *is* the oracle's -/
  hmargq : ∀ k (hok : ok k = false), marg k = (hCq k hok).margin
  /-- the `ok` verdict means the state is unit-diagonal (`dvR = 0`) -/
  hunidiag : ∀ k, ok k = true → ∀ i, Q k i i = 1
  /-- the `ok` verdict as a `RelaxMem` at the state -/
  hmemq : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
      * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (Q k) (u' k)
      (QMCLeafB.UnionShallow.paramsKbc2 G).dq
  /-- the `ok` round's threshold shift under the lowering -/
  huq : ∀ k, ok k = true →
    (1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
        * (u' k + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2)
      ≤ (t - QMCLeafB.RundataCert.eps G) + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2
  /-- the recorded normal is the oracle's -/
  hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (hCq k hok).normal
  /-- the dilated normal is `c + lam • flat 1` -/
  hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
    (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
  /-- nondegeneracy of the dilated normal -/
  hcne : ∀ k, cn k ≠ 0
  hlam0 : ∀ k, 0 ≤ lam k
  hlam1 : ∀ k, ok k = false → 1 ≤ lam k
  /-- the depth ledger (`hlam2` of `DriftExact.runParts_at_interior_exact`) -/
  hlam2 : ∀ k, ok k = false →
    |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn
          cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
        + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn
            cn hcne (c k) k|
      + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
          ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn cn hcne (c k) k|
      + 9 * marg k ^ 2
          / (4 * (((QMCLeafB.UnionShallow.paramsKbc2 G)).rmax) ^ 2) + 1
    ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
        QMCLeafB.RunPartsDilate.witAt G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn
          cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k)
  /-- the `hdriftc` budget at the state, with the `dq/4` lowering charge explicit -/
  hdriftcQ : ∀ k, ok k = false →
    (fun i => ((c k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (Q k)))
      + (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) / 4
        * ((fun i => ((c k i : ℚ) : ℝ))
            ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (Q k)))
      ≤ ((marg k : ℚ) : ℝ) / 2
  /-- the `hdriftd` budget at the state, with the `dq/4` lowering charge explicit -/
  hdriftdQ : ∀ k, ok k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (Q k)))
      + (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) / 4
        * (QMCLeafB.RunPartsStream.dOne G.n
            ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (Q k)))
      ≤ 0
  /-- the flag read-out -/
  hverdict : campBit G t = QMCLeafB.SimLoop.anyOk ok
    ((QMCLeafB.UnionShallow.paramsKbc2 G).K
      * (QMCLeafB.UnionShallow.paramsKbc2 G).m)

/-- **One bundle gives the run record.** -/
theorem LoweredRecords.toRunParts {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (R : LoweredRecords G t hn) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    Nonempty (QMCLeafB.FinalStroke.RunParts campBit G t
      (QMCLeafB.UnionShallow.paramsKbc2 G)) :=
  QMCLeafB.PinchLower.runParts_lowered campBit G t hn hRq R.ok R.marg R.Q R.lam R.c R.cn R.u'
    R.hQsym R.htraceQ R.hCq R.hpair R.hmargq R.hunidiag R.hmemq R.huq R.hcEq R.hcn R.hcne
    R.hlam0 R.hlam1 R.hlam2 R.hdriftcQ R.hdriftdQ R.hverdict

/-- The residual family: one `LoweredRecords` bundle at every interior `(G, t)`. -/
abbrev HdFamily : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    LoweredRecords G t hn

/-- **The family is the leaf's `hd`.**  The bracket forces `0 < Rq G`
(`AssemblyM5.Rq_pos_of_interior_bracket`), which is the budget's hypothesis. -/
def hd_of_lowered (h : HdFamily) : QMCLeafB.AssemblyM5.HdProp :=
  fun G t hn hlo hhi =>
    Classical.choice ((h G t hn hlo hhi).toRunParts
      (QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi))

/-- **`d9f601e5` from the base-point record family**, at the shelf's own reading of the sentence. -/
theorem endgame_of_lowered (h : HdFamily) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.AssemblyM5.endgame_of_hd_statement (hd_of_lowered h)

/-- **The same ending written out token for token** — the verbatim `d9f601e5` sentence. -/
theorem endgame_of_lowered_verbatim (h : HdFamily) :
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
  QMCLeafB.AssemblyM5.endgame_of_hd (hd_of_lowered h)

/-- The Proposition-valued form of `hd_of_lowered` (audit target). -/
theorem hd_of_lowered_spec (h : HdFamily) : Nonempty QMCLeafB.AssemblyM5.HdProp :=
  ⟨hd_of_lowered h⟩

#print axioms QMCLeafB.LowerRecords.hd_of_lowered_spec
#print axioms QMCLeafB.LowerRecords.endgame_of_lowered
#print axioms QMCLeafB.LowerRecords.endgame_of_lowered_verbatim


