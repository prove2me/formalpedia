-- Prove2me | Definitions.Def_QMCLeafB_assembly_stream_m5
-- name    : QMCLeafB_assembly_stream_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:04:20.25853+00:00
-- url     : https://prove2.me/theorems/d52635bf-434d-41d9-9e0c-1cccecf48924
-- title:
--   QMCLeafB assembly_stream_m5
-- statement:
--   # leaf B phase 17 — the stream-level residual, composed (swarm `smw1gfajf`, m5, d4)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_assembly_m5
import Definitions.Def_QMCLeafB_runparts_stream_m4
/-
# leaf B phase 17 — the stream-level residual, composed (swarm `smw1gfajf`, m5, d4)

`Check_assembly_m5` reduces the leaf to `AssemblyM5.HdProp`: one `FinalStroke.RunParts` per interior
`(G, t)`, at `InitDq.init0` / `RoundProgram.round` / the campaign family `paramsKbc2`.  This file
reduces `HdProp` *further*, to the hypothesis list of the shelf's own stream conduit
`QMCLeafB.RunPartsStream.runParts_of_stream_data`, at the campaign constants:

* the family is fixed (`P := paramsKbc2 G`), so the producer never mentions `RunParams`;
* its three scalar inputs are discharged here —
  `rmax_pos_at_interior` (`0 < rmax`), `rmax_le_one` (`rmax ≤ 1`),
  `budget_at_interior` (`hbudP`, from `paramsKbc2_budget` and the bracket's `Rq > 0`);
* the verdict bit is fixed to the campaign loop, so `hverdict` is a statement about the producer's
  own `ok` stream and the campaign count `Kbc2 (mHalve (n·n)) G · mHalve (n·n)`.

So after this file the leaf's entire content is `runParts_at_interior`'s twenty stream hypotheses —
`hdiagc` + `hstatec` + `hstated` (analytic, d1), `C`/`hmarg`/`hmem`/`hcEq`/`hCsym`/`hverdict` (the
oracle's records, d3).  Nothing here is new mathematics: it is the composition, checked.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`.  Axiom audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open QuantumMaxCutEnergy
open Matrix

namespace QMCLeafB.AssemblyStreamM5

/-- **`RunParts` at the campaign family from the shelf's stream data** — the shelf's
`RunPartsStream.runParts_of_stream_data` at `P := UnionShallow.paramsKbc2 G`, with its `hrmaxPos`,
`hrmax1` and `hbudP` discharged, its `o` fixed to the campaign loop, and `hverdict` at the campaign
count.  Everything a producer must still supply is one of the stream hypotheses. -/
noncomputable def runParts_at_interior
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (mu delta : ℕ → ℝ) (dvec : Fin (G.n * G.n) → ℝ)
    (hdvec : dvec = fun i =>
      ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) i : ℚ) : ℝ))
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.UnionShallow.paramsKbc2 G).dq))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.UnionShallow.paramsKbc2 G).dq))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, ok k = false →
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
              cn hcne (c k) k|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
            (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne (c k) k|
        + 9 * marg k ^ 2
            / (4 * ((QMCLeafB.UnionShallow.paramsKbc2 G).rmax) ^ 2) + 1
      ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hdiagc : ∀ k, ∀ i, (cX k) i i ≤ 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (qSurr : ℕ → Fin (G.n * G.n) → ℝ)
    (hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k, mu j •
          QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G)
              hn cn hcne) j)
    (hmu_up : ∀ j, QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne)
      j ≤ mu j)
    (hmu_lo : ∀ j, mu j - delta j ≤ QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne)
      j)
    (hlam3 : ∀ j,
      |(fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne (c j) j i : ℚ) : ℝ))|
        ≤ ((lam j : ℚ) : ℝ) * ((fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ))))
    (hstatec : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        + ∑ j ∈ Finset.range k, delta j * max 0
            (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
              (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) j))
          ≤ ((marg k : ℚ) : ℝ) / 2)
    (hstated : ∀ k, ok k = false →
      dvec ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) ≤ 0)
    (hverdict : QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
      QMCLeafB.RoundProgram.verdict
      (fun G' _ => QMCLeafB.UnionShallow.Kbc2
        (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
        * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t
      = QMCLeafB.SimLoop.anyOk ok ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    : QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
      (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  QMCLeafB.RunPartsStream.runParts_of_stream_data
    (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
      QMCLeafB.RoundProgram.verdict
      (fun G' _ => QMCLeafB.UnionShallow.Kbc2
        (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
        * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)))
    G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.AssemblyM5.rmax_pos_at_interior G hn)
    (QMCLeafB.AssemblyM5.rmax_le_one G hn)
    (QMCLeafB.AssemblyM5.budget_at_interior G t hn hlo hhi)
    ok marg cX lam c cn mu delta dvec hdvec C hmarg hmem hCsym hcEq hcn hcne hlam0 hlam1 hlam2
    hdiagc qSurr hqSurr hmu_up hmu_lo hlam3 hstatec hstated hverdict

/-- **The residual is exactly the stream data**: `AssemblyM5.HdProp` from a pointwise
`runParts_at_interior`. -/
def HdProp_of_stream
    (h : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n)
      (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
      (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)),
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.AssemblyM5.HdProp :=
  h

/-- The leaf from the stream-level supply, in the verbatim `d9f601e5` sentence. -/
theorem endgame_of_stream
    (h : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n)
      (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
      (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)),
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
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
  QMCLeafB.AssemblyM5.endgame_of_hd (HdProp_of_stream h)

end QMCLeafB.AssemblyStreamM5

/-! ## Axiom audit -/

#print axioms QMCLeafB.AssemblyStreamM5.runParts_at_interior
#print axioms QMCLeafB.AssemblyStreamM5.HdProp_of_stream
#print axioms QMCLeafB.AssemblyStreamM5.endgame_of_stream


