-- Prove2me | Definitions.Def_QMCLeafB_windowC
-- name    : QMCLeafB_windowC
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:49:50.056172+00:00
-- url     : https://prove2.me/theorems/b8190263-a256-496b-ba29-d0e00ba205fa
-- title:
--   QMCLeafB windowC
-- statement:
--   # leaf B phase 22 — the ceiling-free window residual `BundleC` and its closing stroke
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ceiling_free
import Definitions.Def_QMCLeafB_residbundle_m7
import Definitions.Def_QMCLeafB_endgame_m2
import Definitions.Def_QMCLeafB_assembly_m5
/-
# leaf B phase 22 — the ceiling-free window residual `BundleC` and its closing stroke
(swarm `smw1ntur6`, member m3, direction `ceiling-analysis`)

Phase 21's producer target is `ResidBundle_M7.ResidWin` (a `BundleHWin` per interior `(G, t)`) and
`BundleHWin.hTrc` is an **unconditional** field: `tr (cX k) ≤ n(1 − dq/4)` at every `k`.  Together
with `hdriftd` it forces `diagSum (Cat k) ≤ n(1 − dq/4)` (`window_forces_engine_trace`), which m8's
`Check_cutbudget_m8` refutes below the horizon at every base `Q` and every positive multiplier
stream.  `Check_ceiling_m3` shows where that field is actually consumed:

* its only consumer in the cone is the `hbody` slot of `runParts_of_dilated`;
* `hbody` in the identity direction is *equivalent* to the ceiling where the body is non-empty
  (`CeilingM3.ceiling_exact`) — so the number cannot be widened there;
* `hbody` is **vacuous at an empty body** (`CeilingM3.hbody_of_empty`) — so the ceiling carries no
  content at a refuted point with an empty relaxed body.

This file is the shape-level consequence: `BundleC` is `BundleHWin` with the `hTrc` field replaced by
`hbody`, and the whole closing chain is rebuilt on it.

```
BundleHWin ──► BundleC ──► BundleCAll (ok clipped) ──► RunParts ──► HdProp ──► d9f601e5
   (CeilingM3.ceiling_gives_hbody)        (CeilingFree.runParts_of_exact_hbody)
```

Nothing is lost: `bundleC_of_window : BundleHWin → BundleC` (since `hTrc ⟹ hbody`), so every phase-21
producer still lands; and at a refuted point with an empty body `bundleC_of_empty` shows the `hbody`
slot is filled by the emptiness.  The downstream consumer is untouched: the assembly is literally
`RunPartsDilate.runParts_of_dilated` through `CeilingFree.runParts_of_exact_hbody`, and the closing
stroke is the shelf's own `AssemblyM5.endgame_of_hd`.

House discipline: `set_option autoImplicit false`; `#print axioms` after every declaration; no
`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`; no `⊊`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.WindowC

open QuantumMaxCutEnergy
open QMCLeafB.ResidB_M7 (okClip okClip_apply_lt okClip_apply_ge okClip_eq_false_iff anyOk_okClip)

/-! ## 1.  The ceiling-free window record

Field for field `ResidBundle_M7.BundleHWin` except that `hTrc` is replaced by `hbody` — the slot the
assembly consumes — and `hbody` is stated at the run's window, exactly where the drift pair lives. -/

structure BundleC (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- did round `k` report `ok`? (free, on the run's own rounds) -/
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
  /-- the cut records — supplied, on the window -/
  C : ∀ k, k < P.K * P.m → ok k = false →
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  hmarg : ∀ k (hk : k < P.K * P.m) (hok : ok k = false), marg k = (C k hk hok).margin
  /-- the `ok`-round member certificate, on the window -/
  hmem : ∀ k, k < P.K * P.m → ok k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  hCsym : ∀ k, (cX k)ᵀ = cX k
  hcEq : ∀ k (hk : k < P.K * P.m) (hok : ok k = false),
    c k = QMCLeafB.RelaxOracle.flatQ (C k hk hok).normal
  hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
    (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
  hcne : ∀ k, cn k ≠ 0
  hlam0 : ∀ k, 0 ≤ lam k
  hlam1 : ∀ k, k < P.K * P.m → ok k = false → 1 ≤ lam k
  hlam2 : ∀ k, k < P.K * P.m → ok k = false →
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
  /-- **the body lies above the queried centre in the identity direction** — the slot the assembly
  consumes, in place of the unconditional trace ceiling -/
  hbody : ∀ k, k < P.K * P.m → ok k = false → ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
    QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
        (QMCLeafB.Finalization.wMatrixQ G))
      (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ) ((P.dq : ℚ) : ℝ) X →
    -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
      (X - QMCLeafB.SepOracle.castMat (cX k))
  /-- the oracle normal's centre mismatch, on the window -/
  hdriftc : ∀ k, k < P.K * P.m → ok k = false →
    (fun i => ((c k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ ((marg k : ℚ) : ℝ) / 2
  /-- the identity direction's cumulative trace budget, on the window -/
  hdriftd : ∀ k, k < P.K * P.m → ok k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ 0
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)

/-- **Nothing is lost**: every phase-21 window record is a `BundleC`.  `hTrc` implies `hbody`
(`CeilingM3.ceiling_gives_hbody`), so no producer is lost by the restate. -/
def bundleC_of_window {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (W : QMCLeafB.ResidBundle_M7.BundleHWin o G t P hn) : BundleC o G t P hn where
  ok := W.ok
  marg := W.marg
  cX := W.cX
  lam := W.lam
  c := W.c
  cn := W.cn
  C := W.C
  hmarg := W.hmarg
  hmem := W.hmem
  hCsym := W.hCsym
  hcEq := W.hcEq
  hcn := W.hcn
  hcne := W.hcne
  hlam0 := W.hlam0
  hlam1 := W.hlam1
  hlam2 := W.hlam2
  hbody := by
    intro k _hk _hok X hX
    have htr : (∑ i, ((W.cX k i i : ℚ) : ℝ)) ≤ (G.n : ℝ) * (1 - ((P.dq : ℚ) : ℝ) / 4) := by
      have h := W.hTrc k
      have h2 : (((G.n : ℚ) * (1 - P.dq / 4) : ℚ) : ℝ)
          = (G.n : ℝ) * (1 - ((P.dq : ℚ) : ℝ) / 4) := by push_cast; ring
      have h3 : (∑ i, ((W.cX k i i : ℚ) : ℝ)) = ((∑ i, W.cX k i i : ℚ) : ℝ) := by
        push_cast; ring
      rw [h3, ← h2]
      exact_mod_cast h
    exact QMCLeafB.CeilingM3.ceiling_gives_hbody htr X hX
  hdriftc := W.hdriftc
  hdriftd := W.hdriftd
  hverdict := W.hverdict

#print axioms QMCLeafB.WindowC.bundleC_of_window

/-- **A refuted point with an empty relaxed body fills the `hbody` slot by emptiness** — so `BundleC`
at such a point is precisely the records plus the two budget inequalities, with no ceiling. -/
def bundleC_of_empty {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, k < P.K * P.m → ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hmarg : ∀ k (hk : k < P.K * P.m) (hok : ok k = false), marg k = (C k hk hok).margin)
    (hmem : ∀ k, k < P.K * P.m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hk : k < P.K * P.m) (hok : ok k = false),
      c k = QMCLeafB.RelaxOracle.flatQ (C k hk hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, k < P.K * P.m → ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, k < P.K * P.m → ok k = false →
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
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hempty : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G))
        (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ) ((P.dq : ℚ) : ℝ) X)
    (hdriftc : ∀ k, k < P.K * P.m → ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, k < P.K * P.m → ok k = false →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)) :
    BundleC o G t P hn where
  ok := ok
  marg := marg
  cX := cX
  lam := lam
  c := c
  cn := cn
  C := C
  hmarg := hmarg
  hmem := hmem
  hCsym := hCsym
  hcEq := hcEq
  hcn := hcn
  hcne := hcne
  hlam0 := hlam0
  hlam1 := hlam1
  hlam2 := hlam2
  hbody := fun k _hk _hok X hX => absurd hX (hempty X)
  hdriftc := hdriftc
  hdriftd := hdriftd
  hverdict := hverdict

#print axioms QMCLeafB.WindowC.bundleC_of_empty

/-! ## 2.  `BundleC` is a `RunParts` — the consumer, unchanged

Clip the `ok` stream at the horizon (beyond it every flag-conditioned slot is vacuous) and hand the
result to `CeilingFree.runParts_of_exact_hbody`, which is `RunPartsDilate.runParts_of_dilated` with
the ceiling removed from the hypothesis list. -/

/-- **The ceiling-free window record is a `RunParts`.** -/
noncomputable def runParts_of_bundleC
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (B : BundleC o G t P hn) :
    QMCLeafB.FinalStroke.RunParts o G t P := by
  refine QMCLeafB.CeilingFree.runParts_of_exact_hbody o G t P hn hrmaxPos hrmax1 hbudP
    (okClip (P.K * P.m) B.ok) B.marg B.cX B.lam B.c B.cn ?_ ?_ ?_ B.hCsym ?_ B.hcn B.hcne
    B.hlam0 ?_ ?_ ?_ ?_ ?_ ?_
  · -- cut records on the clipped stream
    intro k hok
    exact B.C k (okClip_eq_false_iff.1 hok).1 (okClip_eq_false_iff.1 hok).2
  · -- their margins
    intro k hok
    exact B.hmarg k (okClip_eq_false_iff.1 hok).1 (okClip_eq_false_iff.1 hok).2
  · -- member certificates below the horizon
    intro k hk htrue
    exact B.hmem k hk (by rwa [okClip_apply_lt hk] at htrue)
  · -- the recorded normal is the oracle's
    intro k hok
    exact B.hcEq k (okClip_eq_false_iff.1 hok).1 (okClip_eq_false_iff.1 hok).2
  · -- the dilation parameter is at least one
    intro k hok
    exact B.hlam1 k (okClip_eq_false_iff.1 hok).1 (okClip_eq_false_iff.1 hok).2
  · -- the depth ledger
    intro k hok
    exact B.hlam2 k (okClip_eq_false_iff.1 hok).1 (okClip_eq_false_iff.1 hok).2
  · -- `hbody`, the slot that replaces the ceiling
    intro k hok
    exact B.hbody k (okClip_eq_false_iff.1 hok).1 (okClip_eq_false_iff.1 hok).2
  · -- the cut direction's mismatch
    intro k hok
    exact B.hdriftc k (okClip_eq_false_iff.1 hok).1 (okClip_eq_false_iff.1 hok).2
  · -- the trace direction's mismatch
    intro k hok
    exact B.hdriftd k (okClip_eq_false_iff.1 hok).1 (okClip_eq_false_iff.1 hok).2
  · -- the verdict bit is the run's
    rw [B.hverdict, anyOk_okClip]

#print axioms QMCLeafB.WindowC.runParts_of_bundleC

/-! ## 3.  The residual and the closing stroke

`ResidC` is `ResidWin` with `BundleC` in place of `BundleHWin`.  Its closing stroke goes through
`AssemblyM5.endgame_of_hd`, so the sentence delivered is the verbatim `d9f601e5` one. -/

/-- **The ceiling-free residual**: one `BundleC` per interior `(G, t)`. -/
abbrev ResidC (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    BundleC o G t (Pfam G) hn

#print axioms QMCLeafB.WindowC.ResidC

/-- The campaign's halving side conditions at `paramsKbc2`, discharged from the shelf. -/
theorem paramsKbc2_sides (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    0 < (QMCLeafB.UnionShallow.paramsKbc2 G).rmax
      ∧ (QMCLeafB.UnionShallow.paramsKbc2 G).rmax ≤ 1
      ∧ (QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
            (3 * (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
          + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2 - QMCLeafB.RundataCert.eps G
          ≤ QMCLeafB.RundataCert.eps G) := by
  refine ⟨QMCLeafB.UnionShallow.paramsKbc2_rmax_pos G hn, ?_,
    QMCLeafB.UnionShallow.paramsKbc2_budget G hn hRq⟩
  have h1 : 1 ≤ G.n * G.n := by nlinarith
  exact QMCLeafB.RunPartsStream.rmaxOf_le_one h1

#print axioms QMCLeafB.WindowC.paramsKbc2_sides

/-- **The `hd` slot from the ceiling-free residual** — the campaign's program bit and parameter
family, so the shelf's `endgame_of_hd` applies directly. -/
noncomputable def hdProp_of_residC
    (H : ResidC (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)))
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp := by
  intro G t hn hlo hhi
  obtain ⟨hrp, hr1, hbud⟩ :=
    paramsKbc2_sides G hn (QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi)
  exact runParts_of_bundleC _ G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn hrp hr1 hbud
    (H G t hn hlo hhi)

#print axioms QMCLeafB.WindowC.hdProp_of_residC

/-- **`SolutionStatement` from the ceiling-free residual.** -/
theorem statement_of_residC
    (H : ResidC (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)))
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.AssemblyM5.endgame_of_hd_statement (hdProp_of_residC H)

#print axioms QMCLeafB.WindowC.statement_of_residC

/-- **The verbatim `d9f601e5` sentence from the ceiling-free residual.** -/
theorem solution_of_residC
    (H : ResidC (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)))
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
  QMCLeafB.AssemblyM5.endgame_of_hd (hdProp_of_residC H)

#print axioms QMCLeafB.WindowC.solution_of_residC

/-! ## 4.  Nothing lost, non-vacuity, and the statement lock -/

/-- **Every phase-21 window residual is a ceiling-free residual** — so the restate loses no producer. -/
def residC_of_residWin {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.ResidBundle_M7.ResidWin o Pfam) : ResidC o Pfam :=
  fun G t hn hlo hhi => bundleC_of_window (H G t hn hlo hhi)

#print axioms QMCLeafB.WindowC.residC_of_residWin

/-- **Non-vacuity at the ok anchor** `(G₀, −1/2)`: the ceiling-free record is inhabited there (it is
the phase-21 window record, transported). -/
theorem bundleC_G₀_inhabited :
    Nonempty (BundleC (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) := by
  obtain ⟨W⟩ := QMCLeafB.ResidBundle_M7.window_G₀_inhabited
  exact ⟨bundleC_of_window W⟩

#print axioms QMCLeafB.WindowC.bundleC_G₀_inhabited

/-- **Every `CoreDataG` is a `BundleC`**: the whole shelf producer layer (`EndgameM2.CoreDataG`,
`FlagsM5.BundleH`, `ResidBundle_M7.BundleHB`, `BundleHWin`) lands in the ceiling-free record, so no
producer — and no phase-21 residue — is lost by the restate. -/
def bundleC_of_dataG {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (hrmax : 0 < P.rmax) (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) :
    BundleC o G t P hn :=
  bundleC_of_window (QMCLeafB.ResidBundle_M7.window_of_bundleHB
    (QMCLeafB.ResidBundle_M7.bundleHB_of_bundleH
      (QMCLeafB.EndgameM2.bundleH_of_dataG hrmax D)))

#print axioms QMCLeafB.WindowC.bundleC_of_dataG

/-- **The statement lock**: `solution_of_residC`'s conclusion is definitionally the shelf's
`FinishLine.SolutionStatement`, so the two spellings of `d9f601e5` agree. -/
theorem verbatim_is_statement
    (h : ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000) :
    QMCLeafB.FinishLine.SolutionStatement :=
  h

#print axioms QMCLeafB.WindowC.verbatim_is_statement

/-- The same in the shelf's own name (the leaf's exact target): the ceiling-free residual delivers
`SolutionStatement` itself, not a look-alike. -/
theorem solution_lock
    (H : ResidC (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)))
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.AssemblyM5.endgame_of_hd (hdProp_of_residC H)

#print axioms QMCLeafB.WindowC.solution_lock

end QMCLeafB.WindowC


