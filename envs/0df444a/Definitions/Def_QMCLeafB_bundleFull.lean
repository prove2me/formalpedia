-- Prove2me | Definitions.Def_QMCLeafB_bundleFull
-- name    : QMCLeafB_bundleFull
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:58:43.090674+00:00
-- url     : https://prove2.me/theorems/0009f27e-ead1-4d50-b357-c4f3eb10d87a
-- title:
--   QMCLeafB bundleFull
-- statement:
--   # leaf B phase 19 — brick `resid-kill` (swarm `smw1k12jb`, member m8, direction d9)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_closingAssembly_m3
import Definitions.Def_QMCLeafB_residRefute
/-
# leaf B phase 19 — brick `resid-kill` (swarm `smw1k12jb`, member m8, direction d9)

Phase 18's closing assembly (`QMCLeafB.ClosingAssembly`, `Check_closingAssembly_m3`) reduced the leaf
to one `Bundle` per interior `(G, t)`, whose flag stream is required to be **all-`false`**

    hokAll : ∀ k, k < P.K * P.m → ok k = false

with `hmem` (the `ok`-round `RelaxMem` slot) eliminated as vacuous.  This file shows that slot is not
eliminable: the residual is **unsatisfiable**, at a concrete two-vertex input.

The point: at `G₀` (two vertices, the single edge of weight `1/2`, so `Rq G₀ = 1`) and `t = -1/2` —
inside the interior bracket `-Rq ≤ t < -Rq/40000` — an all-`false` flag stream makes the shelf's
refuted-branch soundness (`SimLoop.simulate_refuted_sound`) conclude

    ∀ Z, IsUnitDiagPSD Z → (t:ℝ) - Rq/40000 ≤ (wMatrix G₀ * Z).trace,

which is false at `Z₀ = !![1, -1; -1, 1]` (`(wMatrix G₀ * Z₀).trace = -1`).  That refutation is
`QMCLeafB.ResidRefute.no_runParts_allFalse` (compiled, standard axioms); §1 lifts it from the shelf's
`RunParts` to phase 18's `Bundle` by the closing assembly's own `runParts_of_bundle` at the campaign
families (whose three scalar slots are the assembly's own theorems), and §2 concludes

    ¬ Resid o paramsKbc2        (and the same at LoopClose.paramsShallow).

Consequently `ClosingAssembly.solution` / `solution_guardT` — both of which *take* `Resid` — can
never be applied: the `hmem`-eliminated shape is not a proof obligation but a false one.  The repair
is §4: `BundleFull` is `Bundle` with `hmem` restored, `ResidFull` is the same bracket
quantification at it, and `ResidFull → SolutionStatement` is the re-aimed closing stroke — so the
price of the repair is exactly the `ok`-round `RelaxMem` slot, which §3 shows is *forced* (every
`RunParts` at the refuted point has an `ok` round).

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.ResidKill

open QuantumMaxCutEnergy

/-! ## 1.  The residual `Bundle` is unsatisfiable at `(G₀, -1/2)` -/

/-- **`(G₀, -1/2)` is inside the interior bracket.** -/
theorem G₀_bracket :
    -QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ ≤ -(1 / 2) ∧
      ((-(1 / 2) : ℚ) : ℝ)
        < -(((QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ / 40000 : ℚ)) : ℝ) := by
  rw [QMCLeafB.ResidRefute.Rq_G₀]
  constructor <;> norm_num

/-- `2 ≤ G₀.n` (definitionally). -/
theorem hnG₀ : 2 ≤ QMCLeafB.ResidRefute.G₀.n := by decide

/-- **No phase-18 `Bundle` at `(G₀, -1/2)`**, at the `paramsKbc2` family. -/
theorem bundle_false_kbc2 (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    QMCLeafB.ClosingAssembly.Bundle o QMCLeafB.ResidRefute.G₀ (-(1 / 2))
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) hnG₀ → False := by
  intro B
  have hRq : 0 < QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ := by
    rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num
  have R := QMCLeafB.ClosingAssembly.runParts_of_bundle o QMCLeafB.ResidRefute.G₀ (-(1 / 2))
    (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) hnG₀
    (QMCLeafB.ClosingAssembly.rmaxOf_pos QMCLeafB.ResidRefute.G₀ hnG₀)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one QMCLeafB.ResidRefute.G₀ hnG₀)
    (QMCLeafB.ClosingAssembly.budget_dqShallow QMCLeafB.ResidRefute.G₀ hnG₀ hRq) B
  have hany : QMCLeafB.SimLoop.anyOk R.ok
      ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
        * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m) = false := by
    rw [← R.hverdict]
    exact QMCLeafB.ClosingAssembly.verdict_eq_false_of_allFalse B
  exact QMCLeafB.ResidRefute.no_runParts_allFalse o
    (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) R
    ((QMCLeafB.SimLoop.anyOk_eq_false_iff R.ok _).mp hany)

/-- **No phase-18 `Bundle` at `(G₀, -1/2)`**, at the `paramsShallow` family of the `roundGT` stroke. -/
theorem bundle_false_shallow (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    QMCLeafB.ClosingAssembly.Bundle o QMCLeafB.ResidRefute.G₀ (-(1 / 2))
        (QMCLeafB.LoopClose.paramsShallow QMCLeafB.ResidRefute.G₀) hnG₀ → False := by
  intro B
  have hRq : 0 < QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ := by
    rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num
  have R := QMCLeafB.ClosingAssembly.runParts_of_bundle o QMCLeafB.ResidRefute.G₀ (-(1 / 2))
    (QMCLeafB.LoopClose.paramsShallow QMCLeafB.ResidRefute.G₀) hnG₀
    (QMCLeafB.ClosingAssembly.rmaxOf_pos QMCLeafB.ResidRefute.G₀ hnG₀)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one QMCLeafB.ResidRefute.G₀ hnG₀)
    (QMCLeafB.ClosingAssembly.budget_dqShallow QMCLeafB.ResidRefute.G₀ hnG₀ hRq) B
  have hany : QMCLeafB.SimLoop.anyOk R.ok
      ((QMCLeafB.LoopClose.paramsShallow QMCLeafB.ResidRefute.G₀).K
        * (QMCLeafB.LoopClose.paramsShallow QMCLeafB.ResidRefute.G₀).m) = false := by
    rw [← R.hverdict]
    exact QMCLeafB.ClosingAssembly.verdict_eq_false_of_allFalse B
  exact QMCLeafB.ResidRefute.no_runParts_allFalse o
    (QMCLeafB.LoopClose.paramsShallow QMCLeafB.ResidRefute.G₀) R
    ((QMCLeafB.SimLoop.anyOk_eq_false_iff R.ok _).mp hany)

/-! ## 2.  Hence the residual itself is refuted — at both strokes' families -/

/-- **The `round` stroke's residual is unsatisfiable.** -/
theorem resid_false_kbc2 (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    QMCLeafB.ClosingAssembly.Resid o QMCLeafB.UnionShallow.paramsKbc2 → False := by
  intro h
  exact bundle_false_kbc2 o (h _ _ hnG₀ G₀_bracket.1 G₀_bracket.2)

/-- **The `roundGT` stroke's residual is unsatisfiable.** -/
theorem resid_false_shallow (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    QMCLeafB.ClosingAssembly.Resid o QMCLeafB.LoopClose.paramsShallow → False := by
  intro h
  exact bundle_false_shallow o (h _ _ hnG₀ G₀_bracket.1 G₀_bracket.2)

/-- **The two closing strokes of phase 18 have unsatisfiable hypotheses**: there is no output bit
`o` at which `ClosingAssembly.solution` (or `solution_guardT`) can be applied. -/
theorem no_closure_via_resid :
    (∀ o : QuantumMaxCutEnergy.Input → ℚ → Bool,
        QMCLeafB.ClosingAssembly.Resid o QMCLeafB.UnionShallow.paramsKbc2 → False)
      ∧ (∀ o : QuantumMaxCutEnergy.Input → ℚ → Bool,
        QMCLeafB.ClosingAssembly.Resid o QMCLeafB.LoopClose.paramsShallow → False) :=
  ⟨resid_false_kbc2, resid_false_shallow⟩

/-! ## 3.  The repair is *forced*: at the refuted point an `ok` round must exist

So restoring `hmem` is not one option among two — the all-`cut` run is impossible there. -/

/-- **Every `RunParts` at `(G₀, -1/2)` has an `ok` round.** -/
theorem exists_ok_round (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : QMCLeafB.FinalStroke.RunParams QMCLeafB.ResidRefute.G₀)
    (R : QMCLeafB.FinalStroke.RunParts o QMCLeafB.ResidRefute.G₀ (-(1 / 2)) P) :
    ∃ k, k < P.K * P.m ∧ R.ok k = true := by
  by_contra hcon
  refine QMCLeafB.ResidRefute.no_runParts_allFalse o P R (fun k hk => ?_)
  cases hb : R.ok k with
  | false => rfl
  | true => exact absurd ⟨k, hk, hb⟩ hcon

/-- **A `Bundle` at the campaign family is refuted, in the form the supplier meets it**: there is no
all-`cut` bundle at `(G₀, -1/2)`, hence the `ok` round (and its `hmem` slot) is unavoidable. -/
theorem exists_ok_round_of_bundle (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (B : QMCLeafB.ClosingAssembly.Bundle o QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) hnG₀) :
    ∃ k, k < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
        * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m
      ∧ B.ok k = true :=
  exists_ok_round o _ (QMCLeafB.ClosingAssembly.runParts_of_bundle o QMCLeafB.ResidRefute.G₀
    (-(1 / 2)) (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) hnG₀
    (QMCLeafB.ClosingAssembly.rmaxOf_pos QMCLeafB.ResidRefute.G₀ hnG₀)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one QMCLeafB.ResidRefute.G₀ hnG₀)
    (QMCLeafB.ClosingAssembly.budget_dqShallow QMCLeafB.ResidRefute.G₀ hnG₀
      (by rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num)) B)

/-! ## 4.  The repaired residual: `hokAll` **deleted**, `hmem` restored

The repaired bundle must **not** extend phase 18's `Bundle`: that structure carries `hokAll`, so a
structure extending it inherits §1's refutation and is equally unsatisfiable.  The fields below are
phase 18's list with the `hokAll` slot **removed** and the `ok`-round `RelaxMem` slot **added** — i.e.
exactly the hypothesis list of `DriftExact.runParts_of_exact_trace` (phase 17's drift brick).  The
flag stream is free, so §3's forced `ok` round costs nothing structurally and the assembly needs no
`noMem_of_allFalse`. -/

structure BundleFull (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
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
  /-- **the cut records** -/
  C : ∀ k, ok k = false →
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin
  /-- **the `ok`-round `RelaxMem` slot** (phase 17's `hmem`) — the slot the all-`false` stream tried
  to eliminate, and which `exists_ok_round` shows is forced -/
  hmem : ∀ k, k < P.K * P.m → ok k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
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

/-- **The repaired bundle is a `RunParts`** — the drift brick verbatim, with a free flag stream. -/
def runParts_of_bundleFull (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (B : BundleFull o G t P hn) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  QMCLeafB.DriftExact.runParts_of_exact_trace o G t P hn hrmaxPos hrmax1 hbudP
    B.ok B.marg B.cX B.lam B.c B.cn B.C B.hmarg B.hmem B.hCsym B.hcEq B.hcn B.hcne
    B.hlam0 B.hlam1 B.hlam2 B.hTrc B.hdriftc B.hdriftd B.hverdict

/-- **The repaired bundle is not refuted by the all-`false` argument**: at `(G₀, -1/2)` its flag
stream cannot be all-`false` — the `ok` round, and with it `hmem`, is forced. -/
theorem bundleFull_not_allFalse (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : QMCLeafB.FinalStroke.RunParams QMCLeafB.ResidRefute.G₀)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost
        (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀
        ≤ QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀)
    (B : BundleFull o QMCLeafB.ResidRefute.G₀ (-(1 / 2)) P hnG₀) :
    ¬ ∀ k, k < P.K * P.m → B.ok k = false := by
  intro h
  exact QMCLeafB.ResidRefute.no_runParts_allFalse o P
    (runParts_of_bundleFull o QMCLeafB.ResidRefute.G₀ (-(1 / 2)) P hnG₀ hrmaxPos hrmax1 hbudP B) h

/-- **The repaired residual**: one `BundleFull` per interior `(G, t)`. -/
abbrev ResidFull (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    BundleFull o G t (Pfam G) hn

/-- **`hd` at the `round` stroke from the repaired residual.** -/
def hd_of_residFull
    (h : ResidFull (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp := by
  intro G t hn hlo hhi
  exact runParts_of_bundleFull _ G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.ClosingAssembly.rmaxOf_pos G hn)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one G hn)
    (QMCLeafB.ClosingAssembly.budget_dqShallow G hn
      (QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi))
    (h G t hn hlo hhi)

/-- **`d9f601e5` from the repaired residual, in the shelf's own name for the sentence.** -/
theorem solution_statement_of_residFull
    (h : ResidFull (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.AssemblyM5.endgame_of_hd_statement (hd_of_residFull h)

/-- **The verbatim `d9f601e5` sentence from the repaired residual.** -/
theorem solution_of_residFull
    (h : ResidFull (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
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
  QMCLeafB.AssemblyM5.endgame_of_hd (hd_of_residFull h)

end QMCLeafB.ResidKill

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.ResidKill.G₀_bracket
#print axioms QMCLeafB.ResidKill.hnG₀
#print axioms QMCLeafB.ResidKill.bundle_false_kbc2
#print axioms QMCLeafB.ResidKill.bundle_false_shallow
#print axioms QMCLeafB.ResidKill.resid_false_kbc2
#print axioms QMCLeafB.ResidKill.resid_false_shallow
#print axioms QMCLeafB.ResidKill.no_closure_via_resid
#print axioms QMCLeafB.ResidKill.exists_ok_round
#print axioms QMCLeafB.ResidKill.exists_ok_round_of_bundle
#print axioms QMCLeafB.ResidKill.runParts_of_bundleFull
#print axioms QMCLeafB.ResidKill.bundleFull_not_allFalse
#print axioms QMCLeafB.ResidKill.hd_of_residFull
#print axioms QMCLeafB.ResidKill.solution_statement_of_residFull
#print axioms QMCLeafB.ResidKill.solution_of_residFull


