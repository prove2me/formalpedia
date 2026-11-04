-- Prove2me | Definitions.Def_QMCLeafB_ceiling_free
-- name    : QMCLeafB_ceiling_free
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:47:33.209373+00:00
-- url     : https://prove2.me/theorems/7ec74a3a-fc46-4126-8cd7-96d4874abca1
-- title:
--   QMCLeafB ceiling_free
-- statement:
--   # leaf B phase 22 — the ceiling-free drift slot: `hbody` in place of `n(1 − dq/4)`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ceiling
/-
# leaf B phase 22 — the ceiling-free drift slot: `hbody` in place of `n(1 − dq/4)`
(swarm `smw1ntur6`, member m3, direction `ceiling-analysis`)

`Check_ceiling_m3` establishes the ledger: in the compiled cone the trace ceiling `n(1 − dq/4)`
has exactly one consumer — the `hbody` slot of `RunPartsDilate.runParts_of_dilated` (through
`DriftExact.hbody_of_trace`, inside `runParts_of_exact_trace`).  `hdriftd`'s own right-hand side is
`0` against the *query centre*, so the ceiling is a statement about the query centre, not about the
drift lemma; and `CeilingM3.hbody_of_empty` shows it is vacuous whenever the relaxed body is empty.

This file therefore does the repair at exactly that joint, with **no downstream re-proof**:

* §1 `runParts_of_exact_hbody`: verbatim `DriftExact.runParts_of_exact_trace` with the single
  hypothesis `hTrc` replaced by `hbody` (the slot `runParts_of_dilated` actually consumes).  Since
  `hTrc ⟹ hbody` (`CeilingM3.ceiling_gives_hbody`), every existing producer still lands, and the
  consumer `runParts_of_dilated` is the same theorem — nothing below moves.
* §2 `runParts_of_exact_hbody_of_empty`: at an **empty relaxed body** the `hbody` slot is *free*, so
  the drift slot needs no trace condition at all.  This is the refuted-point case: the whole residual
  is `{records, hlam0/1/2, hdriftc, hdriftd, hverdict}`.
* §3 `runParts_of_exact_dM`: the same with an **arbitrary nonzero dilation direction** `dM`
  (`hcn`/`hdriftd`/`hbody` at `dM`), and `runParts_of_exact_dM_of_empty`: at an empty body *every*
  direction is admissible, so a producer at a refuted point may choose the direction that makes the
  two budget inequalities easiest.  The campaign direction `dM = 1` is §1.

Both readings of m8's falsification are covered: the killed inequality is `hTrc ∧ hdriftd`, and this
module removes `hTrc` exactly where it carries no content, keeping it (as `hbody`) where it is the
body's own floor (`CeilingM3.ceiling_exact`/`ceiling_not_widenable`).

House discipline: `set_option autoImplicit false`; `#print axioms` after every declaration; no
`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`; no `⊊`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.CeilingFree

open QuantumMaxCutEnergy

/-! ## 1.  The drift slot with `hbody` instead of `hTrc`

Identical to `QMCLeafB.DriftExact.runParts_of_exact_trace` except that the single trace hypothesis is
replaced by the condition `runParts_of_dilated` consumes.  `hTrc` (any constant) is *not* read. -/

noncomputable def runParts_of_exact_hbody
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (P.dq))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < (P).K
        * (P).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (P.dq))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, ok k = false →
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
    (hbody : ∀ k, ok k = false → ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE
        (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G))
        (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ) ((P.dq : ℚ) : ℝ) X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob
        (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
        (X - QMCLeafB.SepOracle.castMat (cX k)))
    (hdriftc : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, ok k = false →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((P).K
        * (P).m)) :
    QMCLeafB.FinalStroke.RunParts o G t
      (P) := by
  refine QMCLeafB.RunPartsDilate.runParts_of_dilated o G t P hn hrmaxPos hbudP ok marg cX
    (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ?_ lam c cn C hmarg hmem hCsym hcEq
    (fun k _ => hcn k) hcne hlam0 ?_ hdriftc hdriftd hlam1 hlam2 hverdict
  · -- the identity dilation direction is nonzero
    intro hzero
    have hidx : 0 < G.n := by omega
    have h1 := congrFun (congrFun hzero ⟨0, hidx⟩) ⟨0, hidx⟩
    simp at h1
  · -- `hbody` is taken as a hypothesis
    exact hbody

#print axioms QMCLeafB.CeilingFree.runParts_of_exact_hbody

/-- **Nothing is lost**: a `hTrc` supplied stream is an `hbody` one.  So every producer of the
phase-21 residual, and `FlagsM5.runParts_of_bundleH` in particular, is an instance of §1. -/
noncomputable def runParts_of_exact_hbody_of_trace
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (P.dq))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < (P).K
        * (P).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (P.dq))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, ok k = false →
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
    (hTrc : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 - P.dq / 4))
    (hdriftc : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, ok k = false →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((P).K
        * (P).m)) :
    QMCLeafB.FinalStroke.RunParts o G t
      (P) := by
  refine runParts_of_exact_hbody o G t P hn hrmaxPos hrmax1 hbudP ok marg cX lam c cn C
    hmarg hmem hCsym hcEq hcn hcne hlam0 hlam1 hlam2 ?_ hdriftc hdriftd hverdict
  intro k _hok X hX
  simpa using QMCLeafB.DriftExact.hbody_of_trace (hTrc k) X hX

#print axioms QMCLeafB.CeilingFree.runParts_of_exact_hbody_of_trace

/-! ## 2.  Refuted points: an empty body releases the trace hypothesis

At a refuted interior point whose relaxed body is empty, §1's `hbody` slot is free — the whole
analytic content of the drift block is then the two budget inequalities. -/

/-- **The drift slot needs no trace condition at an empty body.** -/
noncomputable def runParts_of_exact_hbody_of_empty
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (P.dq))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < (P).K
        * (P).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (P.dq))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, ok k = false →
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
      ¬ QMCLeafB.BallFloor.relaxBodyLE
        (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G))
        (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ) ((P.dq : ℚ) : ℝ) X)
    (hdriftc : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, ok k = false →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((P).K
        * (P).m)) :
    QMCLeafB.FinalStroke.RunParts o G t
      (P) := by
  refine runParts_of_exact_hbody o G t P hn hrmaxPos hrmax1 hbudP ok marg cX lam c cn C
    hmarg hmem hCsym hcEq hcn hcne hlam0 hlam1 hlam2 ?_ hdriftc hdriftd hverdict
  intro k _hok X hX
  exact absurd hX (hempty X)

#print axioms QMCLeafB.CeilingFree.runParts_of_exact_hbody_of_empty

end QMCLeafB.CeilingFree


