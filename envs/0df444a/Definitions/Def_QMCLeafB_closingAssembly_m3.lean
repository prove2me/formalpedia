-- Prove2me | Definitions.Def_QMCLeafB_closingAssembly_m3
-- name    : QMCLeafB_closingAssembly_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:16:31.227929+00:00
-- url     : https://prove2.me/theorems/52e3764a-5d2b-421f-9784-3a4cec4c60e4
-- title:
--   QMCLeafB closingAssembly_m3
-- statement:
--   # leaf B phase 18 — brick `closing-assembly` (swarm `smw1i2drp`, member m3, direction d1)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_drift_m3
import Definitions.Def_QMCLeafB_assembly_m5
import Definitions.Def_QMCLeafB_guardT_m2
/-
# leaf B phase 18 — brick `closing-assembly` (swarm `smw1i2drp`, member m3, direction d1)

The campaign stands at exactly one residual hypothesis: one `FinalStroke.RunParts` bundle per
interior `(G, t)` (`QMCLeafB.AssemblyM5.HdProp`), from which `AssemblyM5.endgame_of_hd`
(`Check_assembly_m5`) is the last application and mints the verbatim `d9f601e5` sentence.

**This file is item 3 of the phase-18 list: the closing assembly itself.**  It does not claim the
leaf.  It does two things:

### 1.  It fixes the residual in the *narrowest shape anyone has machine-checked*

`Bundle G t P hn` is the exact hypothesis list of `DriftExact.runParts_of_exact_trace`
(`Check_drift_m3`, the phase-17 `drift-closure` brick) **with `hmem` removed** — the `ok`-round
`RelaxMem` slot, which phase 17's `Check_runstreams_m8` refuted at the shelf round and which is
*vacuous* as soon as the run's flag stream is all-`false` (`noMem_of_allFalse`).  So the residual is
not "`hd`" as an opaque blob: it is the 16-slot bundle minus the slot that provably cannot be fed,
i.e. `records {C hmarg hCsym hcEq hcn hcne hlam0 hlam1 hlam2} + hTrc + hdriftc + hdriftd +
hverdict + hokAll` at the queried centres — reproduced here verbatim from the compiled brick, so a
supplier cannot drift off the shape.

### 2.  It delivers the ending at **both** round spellings

Phase 17 recorded a coordination hazard (m8): `AssemblyM5.HdProp` is stated at
`RoundProgram.round`, while `GuardT`/`LeafAssembly` are stated at `roundGT`.  The two are not
interchangeable.  Both endings are therefore wired here, from the *same* `Bundle` shape:

* `hd_of_resid` + `solution`             — at `RoundProgram.round`, `paramsKbc2`, `k = 20`;
* `hdGT_of_resid` + `solution_guardT`    — at `GuardT.roundGT`, `LoopClose.paramsShallow`.

Whichever spelling's flag stream lands, the leaf closes by one application; the choice of stroke is
therefore *not* on the critical path.

### What is still open (and is not claimed here)

The leaf is **not** proved.  `Resid` is unproved: the flag stream (all-`false` on the interior
bracket, phase-18 d3) and the trace budget `hTrc`/`hdriftd` (phase-18 d2) are the two live slots.
§5 records the sense in which the bundle is *not* vacuous.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audit at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.ClosingAssembly

open QuantumMaxCutEnergy

/-! ## 1.  The residual bundle: `runParts_of_exact_trace`'s hypotheses minus `hmem`

The hypothesis types below are copied verbatim from `QMCLeafB.DriftExact.runParts_of_exact_trace`
(`Solutions/Check_drift_m3.lean`, §5).  The only *removed* slot is `hmem`
(`∀ k, k < P.K * P.m → ok k = true → RelaxMem …`), replaced by the flag stream
`hokAll : ∀ k, k < P.K * P.m → ok k = false`, from which `hmem` is vacuous. -/

structure Bundle (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- did round `k` report `ok`? -/
  ok : ℕ → Bool
  /-- the per-round oracle margins -/
  marg : ℕ → ℚ
  /-- the per-round queried centres -/
  cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  /-- the dilation parameters -/
  lam : ℕ → ℚ
  /-- the oracle's flat cut normals -/
  c : ℕ → Fin (G.n * G.n) → ℚ
  /-- the dilated (recorded) flat normals -/
  cn : ℕ → Fin (G.n * G.n) → ℚ
  /-- **the flag stream**: every round of the loop is a cut round -/
  hokAll : ∀ k, k < P.K * P.m → ok k = false
  /-- **the cut records** -/
  C : ∀ k, ok k = false →
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin
  /-- **the queried centre is symmetric** -/
  hCsym : ∀ k, (cX k)ᵀ = cX k
  /-- the recorded normal is the oracle's -/
  hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal
  /-- the recorded normal is the dilated one -/
  hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
    (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
  hcne : ∀ k, cn k ≠ 0
  hlam0 : ∀ k, 0 ≤ lam k
  hlam1 : ∀ k, ok k = false → 1 ≤ lam k
  hlam2 : ∀ k, ok k = false →
    |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G (P) hn
          cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
        + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (P) hn
            cn hcne (c k) k|
      + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
          (P) hn cn hcne (c k) k|
      + 9 * marg k ^ 2
          / (4 * ((P).rmax) ^ 2) + 1
    ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
        QMCLeafB.RunPartsDilate.witAt G (P) hn
          cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k)
  /-- **the trace budget at the queried centres** (`hdiagc`, in the trace form) -/
  hTrc : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 - P.dq / 4)
  /-- the oracle normal's centre mismatch -/
  hdriftc : ∀ k, ok k = false →
    (fun i => ((c k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ ((marg k : ℚ) : ℝ) / 2
  /-- the identity direction's cumulative trace budget -/
  hdriftd : ∀ k, ok k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ 0
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)

/-! ## 2.  `hmem` is vacuous at an all-`false` flag stream

This is the phase-18 form of phase-17's headline (`Check_runstreams_m8.not_relaxMem_of_ok`): that
`RelaxMem` *cannot* be fed at the shelf round's `ok` rounds means the slot is not something a
supplier can owe — it is something to be **eliminated**, which the flag stream does. -/

/-- **A run with no `ok` round owes no `RelaxMem`.** -/
theorem noMem_of_allFalse {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    {t dq eps : ℚ} {ok : ℕ → Bool} {cX : ℕ → Matrix (Fin n) (Fin n) ℚ} (N : ℕ)
    (h : ∀ k, k < N → ok k = false) :
    ∀ k, k < N → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem A (cX k) (t - eps) dq := by
  intro k hk htrue
  exact absurd htrue (by rw [h k hk]; simp)

#print axioms QMCLeafB.ClosingAssembly.noMem_of_allFalse

/-- **The bundle is a genuine `RunParts`** — the whole content of the phase-17 drift brick, with the
`hmem` slot eliminated by the flag stream.  All three scalar inputs (`hrmaxPos`, `hrmax1`,
`hbudP`) are kept explicit here; §3 discharges them at both campaign families. -/
def runParts_of_bundle (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (B : Bundle o G t P hn) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  QMCLeafB.DriftExact.runParts_of_exact_trace o G t P hn hrmaxPos hrmax1 hbudP
    B.ok B.marg B.cX B.lam B.c B.cn B.C B.hmarg
    (noMem_of_allFalse (P.K * P.m) B.hokAll)
    B.hCsym B.hcEq B.hcn B.hcne B.hlam0 B.hlam1 B.hlam2 B.hTrc
    B.hdriftc B.hdriftd B.hverdict

#print axioms QMCLeafB.ClosingAssembly.runParts_of_bundle

/-! ## 3.  The three scalars, at the campaign tolerance `dqShallow G`

Both campaign families (`UnionShallow.paramsKbc2` for the `round` stroke,
`LoopClose.paramsShallow` for the `roundGT` stroke) have

  `dq = dqShallow G`, `rmax = rmaxOf (n·n)`, `m = mHalve (n·n)`   (`rfl`)

and differ only in `K`.  So the three scalar slots are family-independent. -/

/-- The campaign ceiling is positive. -/
theorem rmaxOf_pos (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    0 < QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) := by
  unfold QMCLeafB.RundataHalving.rmaxOf
  have hN : (0 : ℚ) < ((G.n * G.n : ℕ) : ℚ) := by
    have : 0 < G.n * G.n := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  positivity

/-- The campaign ceiling is at most `1`. -/
theorem rmaxOf_le_one (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) ≤ 1 := by
  have hN : 1 ≤ G.n * G.n := by nlinarith
  unfold QMCLeafB.RundataHalving.rmaxOf
  rw [div_le_one (by positivity)]
  have hq : (1 : ℚ) ≤ ((G.n * G.n : ℕ) : ℚ) := by exact_mod_cast hN
  linarith

/-- **The ok-branch rounding budget**, at the campaign tolerance and in the positive regime. -/
theorem budget_dqShallow (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * QMCLeafB.RundataParams.dqShallow G / 4)
      + QMCLeafB.RundataParams.dqShallow G / 2 - QMCLeafB.RundataCert.eps G
      ≤ QMCLeafB.RundataCert.eps G := by
  have h := QMCLeafB.RunPartsShallow.runParamsShallow_budget G hn hRq
  rwa [QMCLeafB.RunPartsShallow.runParamsShallow_dq] at h

#print axioms QMCLeafB.ClosingAssembly.rmaxOf_pos
#print axioms QMCLeafB.ClosingAssembly.rmaxOf_le_one
#print axioms QMCLeafB.ClosingAssembly.budget_dqShallow

/-! ## 4.  The residual, stated once, and the two endings

`Resid o Pfam` is the leaf's entire remaining content: for every `(G, t)` in the interior bracket, one
`Bundle` at the family `Pfam` held by the loop of output bit `o`.  It is a `Type`, not a `Prop`
(`RunParts` carries data), which is why it is an `abbrev` of a `Π`-type. -/

/-- **The one remaining residual of the leaf**, at an arbitrary output bit and parameter family. -/
abbrev Resid (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    Bundle o G t (Pfam G) hn

/-! ### 4a.  The `round` stroke (`paramsKbc2`, `k = 20`) -/

/-- The tape-free round count of the `round` ending. -/
noncomputable def Tbc2 (G : QuantumMaxCutEnergy.Input) (_t : ℚ) : ℕ :=
  QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
    * QMCLeafB.HalvePerG.mHalve (G.n * G.n)

/-- **`hd` at `RoundProgram.round`** from the residual bundle.  `Rq G > 0` comes from the bracket
itself (`AssemblyM5.Rq_pos_of_interior_bracket`), which is what makes the budget's positive regime
available. -/
def hd_of_resid
    (h : Resid (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp := by
  intro G t hn hlo hhi
  exact runParts_of_bundle _ G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (rmaxOf_pos G hn) (rmaxOf_le_one G hn)
    (budget_dqShallow G hn
      (QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi))
    (h G t hn hlo hhi)

#print axioms QMCLeafB.ClosingAssembly.hd_of_resid

/-- **`d9f601e5` from the residual, in the shelf's own name for the sentence.** -/
theorem solution_statement
    (h : Resid (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.AssemblyM5.endgame_of_hd_statement (hd_of_resid h)

#print axioms QMCLeafB.ClosingAssembly.solution_statement

/-- **`theorem solution` : the verbatim `d9f601e5` sentence, from the residual bundle alone.** -/
theorem solution (h : Resid (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
      QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict Tbc2)
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
  QMCLeafB.AssemblyM5.endgame_of_hd (hd_of_resid h)

#print axioms QMCLeafB.ClosingAssembly.solution

/-! ### 4b.  The `roundGT` stroke (`LoopClose.paramsShallow`, `k = 20`)

Phase 17's coordination hazard: `AssemblyM5.HdProp` is at `RoundProgram.round`, the guarded stroke
`GuardT` at `roundGT`.  The same bundle shape therefore feeds the second ending too — so whichever
spelling's flag stream a supplier lands, the leaf closes without re-wiring. -/

/-- **`hd` at `GuardT.roundGT`** from the residual bundle at the `roundGT` family. -/
def hdGT_of_resid
    (h : Resid (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.GuardT.roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (QMCLeafB.LoopClose.paramsShallow G').K
            * (QMCLeafB.LoopClose.paramsShallow G').m))
        QMCLeafB.LoopClose.paramsShallow) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.GuardT.roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (QMCLeafB.LoopClose.paramsShallow G').K
            * (QMCLeafB.LoopClose.paramsShallow G').m)) G t
        (QMCLeafB.LoopClose.paramsShallow G) := by
  intro G t hn hlo hhi
  exact runParts_of_bundle _ G t (QMCLeafB.LoopClose.paramsShallow G) hn
    (rmaxOf_pos G hn) (rmaxOf_le_one G hn)
    (budget_dqShallow G hn
      (QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi))
    (h G t hn hlo hhi)

#print axioms QMCLeafB.ClosingAssembly.hdGT_of_resid

/-- **`theorem solution` again, on the guarded stroke**: `k = 20`, `2^20 ≥ 21`. -/
theorem solution_guardT
    (h : Resid (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.GuardT.roundGT
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
  QMCLeafB.GuardT.solution_of_leaf_guardT 20 (by norm_num) (hdGT_of_resid h)

#print axioms QMCLeafB.ClosingAssembly.solution_guardT

/-! ## 5.  The two readings the supplier of the bundle must satisfy

The bundle is a `Type` with data, so the honest question is *what does a supplier have to produce*.
Two of the slots are forced by the others, and are recorded here so that nobody hunts them: -/

/-- **An all-`false` flag stream forces the interior verdict to be `false`.**  So `hverdict` is not a
free choice: the loop's output bit at every interior `(G, t)` is `false`, and a supplier of the bundle
must produce exactly that read-out. -/
theorem verdict_eq_false_of_allFalse {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool} (B : Bundle o G t P hn) :
    o G t = false := by
  have hany : QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m) = false := by
    have h1 : ¬ ∃ k, k < P.K * P.m ∧ B.ok k = true := by
      rintro ⟨k, hk, htrue⟩
      exact absurd htrue (by rw [B.hokAll k hk]; simp)
    cases hany0 : QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m) with
    | false => rfl
    | true => exact absurd ((QMCLeafB.SimLoop.anyOk_eq_true_iff B.ok (P.K * P.m)).mp hany0) h1
  rw [B.hverdict, hany]

#print axioms QMCLeafB.ClosingAssembly.verdict_eq_false_of_allFalse

/-- **The bundle is not vacuous at a positive-weight input.**  The interior bracket is inhabited
exactly when `Rq G > 0`, and the bundle is demanded there at *every* `t` of the half-open interval —
so `Resid` is a substantive obligation at every input with a positive weight, not an empty
quantification.  (This is the phase-17 non-vacuity audit, restated at the bundle.) -/
theorem resid_range_nonempty_iff (G : QuantumMaxCutEnergy.Input) :
    (∃ t : ℚ, -QMCLeafB.EngineRuntime.Rq G ≤ t
        ∧ (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
      ↔ 0 < QMCLeafB.EngineRuntime.Rq G := by
  constructor
  · rintro ⟨t, hlo, hhi⟩
    exact QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi
  · intro hRq
    refine ⟨-QMCLeafB.EngineRuntime.Rq G, le_refl _, ?_⟩
    have h : ((-QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ)
        < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
      have h1 : (-QMCLeafB.EngineRuntime.Rq G : ℚ) < -(QMCLeafB.EngineRuntime.Rq G / 40000) := by
        have h2 : (0 : ℚ) < QMCLeafB.EngineRuntime.Rq G / 40000 := by
          have : (0 : ℚ) < QMCLeafB.EngineRuntime.Rq G := hRq
          positivity
        linarith
      exact_mod_cast h1
    exact h

#print axioms QMCLeafB.ClosingAssembly.resid_range_nonempty_iff

end QMCLeafB.ClosingAssembly

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.ClosingAssembly.noMem_of_allFalse
#print axioms QMCLeafB.ClosingAssembly.runParts_of_bundle
#print axioms QMCLeafB.ClosingAssembly.rmaxOf_pos
#print axioms QMCLeafB.ClosingAssembly.rmaxOf_le_one
#print axioms QMCLeafB.ClosingAssembly.budget_dqShallow
#print axioms QMCLeafB.ClosingAssembly.hd_of_resid
#print axioms QMCLeafB.ClosingAssembly.solution_statement
#print axioms QMCLeafB.ClosingAssembly.solution
#print axioms QMCLeafB.ClosingAssembly.hdGT_of_resid
#print axioms QMCLeafB.ClosingAssembly.solution_guardT
#print axioms QMCLeafB.ClosingAssembly.verdict_eq_false_of_allFalse
#print axioms QMCLeafB.ClosingAssembly.resid_range_nonempty_iff


