-- Prove2me | Definitions.Def_QMCLeafB_cutrec
-- name    : QMCLeafB_cutrec
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T06:11:33.091453+00:00
-- url     : https://prove2.me/theorems/d0a75097-eee6-4eed-88e3-9f35a36984e2
-- title:
--   QMCLeafB cutrec
-- statement:
--   # leaf B phase 21 — the cut-branch record at the CHOICE-FREE oracle (m5, direction d1 follow-on)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_okprod_m6
import Definitions.Def_QMCLeafB_endgame_m2
/-
# leaf B phase 21 — the cut-branch record at the CHOICE-FREE oracle (m5, direction d1 follow-on)

`Check_okprod_m6` (d4/m6) shows that `FlagsM5.cutOf` carries no separation content: `RelaxCut.separates`
is one-sided, so `defaultCut` (normal `0`, margin `1`) is a valid `RelaxCut` at **every** centre, the
cut disjunct of `relaxMem_or_cut` is unconditional, and `cutOf` at a non-member is a
`Classical.choice` over an always-inhabited `Nonempty`.  Consequently `nrmOf`/`margOf` — hence
`cnOf`, `cutStream`, `Cat` and the two drift slots of `RecordsM2.CoreData`/`CoreDataF`, and of the
horizon-bounded `EndgameM2.CoreDataB`/`ResidB_M7.CoreDataB` — are statements about an *opaque* term,
which no producer can discharge.  The cut branch therefore has to be recorded at the **choice-free**
oracle (`OkProdM6.cutOfC`, which is `RelaxOracle.relaxOracle` on the cut side).

This file supplies that record, with the smallest possible delta:

* §1 `nrmC`/`margC`/`lamC`/`cnC`/`cutStreamC`: the whole `RecordsM2` centre family and multiplier
  construction re-rooted at `cutOfC`.  Everything is an instantiation — `RecordM2.lamInd` is
  parametric in the normal/margin streams, so `lamC_spec` (the depth ledger) is
  `RecordM2.lamInd_spec` at the new inputs, and `cnC_ne` is `RecordM2.cnInd_ne`.
* §2 `CoreDataC`: `EndgameM2.CoreDataB` with the two drift slots at the choice-free stream (same five
  fields, same horizon `k < K·m`; the flag-shaped content is untouched because `flagOf` never reads a
  cut record).
* §3 `bundleH_of_dataC`: the assembly, field-for-field the same proof as `EndgameM2.bundleH_of_data`
  with `cutOf → cutOfC`.  `BundleH`'s `C` field is free data, so the closing chain
  (`FlagsM5.runParts_of_bundleH` → `AssemblyM5.endgame_of_hd`) is reused untouched.
* §4 `ResidC`, `residH_of_dataC`, `solution_of_dataC`, `solution_statement_of_dataC`: the verbatim
  `d9f601e5` sentence and `FinishLine.SolutionStatement`.

So after this file the leaf needs exactly ONE thing from the producers: the two drift budgets at the
**concrete** normals `−A` / `v vᵀ` / `±eᵢeᵢᵀ` that `cutOfC` names (`OkProdM6.cutOfC_trace` etc.).

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.CutRecM5

open QuantumMaxCutEnergy
open QMCLeafB.FlagsM5 (flagOf cutOf BundleH ResidH)
open QMCLeafB.RecordsM2

/-! ## 1.  The record stream at the choice-free oracle -/

/-- **The queried centre of round `k`** (unchanged: the pinched state, `RecordsM2.cXst`). -/
abbrev cXt (G : QuantumMaxCutEnergy.Input) (X : ℕ → List ℚ) (dq : ℚ) (k : ℕ) :
    Matrix (Fin G.n) (Fin G.n) ℚ :=
  QMCLeafB.RecordsM2.cXst G.n X dq k

/-- **The choice-free canonical cut** at the run's own centre family, with the symmetry of the
coded state available (the guard `cutOfC` needs). -/
noncomputable def cutC (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (X : ℕ → List ℚ)
    (hs : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k))
    (k : ℕ) :
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cXt G X P.dq k)
      (t - QMCLeafB.RundataCert.eps G) P.dq :=
  QMCLeafB.OkProdM6.cutOfC (QMCLeafB.Finalization.wMatrixQ G) (cXt G X P.dq k)
    (t - QMCLeafB.RundataCert.eps G) P.dq P.hdq (QMCLeafB.RecordsM2.cXst_symm G.n X P.dq hs k)

/-- **The concrete cut at a round whose objective exceeds the level.**  `relaxOracle` tests the
trace slot *first*, so whenever `t - eps + dq/2 < ⟪A, cX_k⟫` the recorded cut is the trace one with
normal exactly `-A` and margin exactly the excess — no `Classical.choice` remains.  (§1's floor
`EmptyBodyM5.frob_ge_of_relaxMem` uses only `psd_margin` and `diag_near`, so at the refuting points of
`Check_emptybody_m5` this case holds at EVERY round and every centre: the whole record there is
concrete, and the two drift slots become statements about the engine chain alone.) -/
theorem cutC_trace (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (X : ℕ → List ℚ)
    (hs : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k))
    (k : ℕ) (h : t - QMCLeafB.RundataCert.eps G + P.dq / 2
      < QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G) (cXt G X P.dq k)) :
    (cutC G t P X hs k).normal = -QMCLeafB.Finalization.wMatrixQ G
      ∧ (cutC G t P X hs k).margin
          = QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G) (cXt G X P.dq k)
            - (t - QMCLeafB.RundataCert.eps G + P.dq / 2) :=
  QMCLeafB.OkProdM6.cutOfC_trace P.hdq
    (QMCLeafB.RecordsM2.cXst_symm G.n X P.dq hs k) h

#print axioms QMCLeafB.CutRecM5.cutC_trace

/-- The choice-free normal of round `k`. -/
abbrev nrmC (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (X : ℕ → List ℚ)
    (hs : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k))
    (k : ℕ) : Fin (G.n * G.n) → ℚ :=
  QMCLeafB.RelaxOracle.flatQ (cutC G t P X hs k).normal

/-- The choice-free margin of round `k`. -/
abbrev margC (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (X : ℕ → List ℚ)
    (hs : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k))
    (k : ℕ) : ℚ :=
  (cutC G t P X hs k).margin

/-- The constructed multiplier at the choice-free normals. -/
abbrev lamC (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) (X : ℕ → List ℚ)
    (hs : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)) :
    ℕ → ℚ :=
  QMCLeafB.RecordM2.lamInd (QMCLeafB.RunPartsDilate.A0P G P) (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega)) (nrmC G t P X hs) (margC G t P X hs) P.rmax

/-- The constructed dilated normal at the choice-free normals. -/
abbrev cnC (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) (X : ℕ → List ℚ)
    (hs : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)) :
    ℕ → Fin (G.n * G.n) → ℚ :=
  QMCLeafB.RecordM2.cnInd (nrmC G t P X hs) (lamC G t P hn X hs) (QMCLeafB.RecordM2.u0 G.n)

theorem cnC_ne (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) (X : ℕ → List ℚ)
    (hs : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)) :
    ∀ k, cnC G t P hn X hs k ≠ 0 :=
  QMCLeafB.RecordM2.cnInd_ne (QMCLeafB.RunPartsDilate.A0P G P) (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega)) (QMCLeafB.RecordM2.u0_d0idx G.n (by omega))
    (nrmC G t P X hs) (margC G t P X hs) P.rmax

#print axioms QMCLeafB.CutRecM5.cnC_ne

/-- The engine's recorded stream at the choice-free dilated normals. -/
abbrev cutStreamC (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) (X : ℕ → List ℚ)
    (hs : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)) :
    ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
  QMCLeafB.RunPartsDilate.runCut G P hn (cnC G t P hn X hs) (cnC_ne G t P hn X hs)

/-- **The depth ledger at the choice-free normals** (`hlam2`), flag-independently. -/
theorem lamC_spec (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) (X : ℕ → List ℚ)
    (hs : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k))
    (hrmax : 0 < P.rmax) :
    ∀ k,
      |nrmC G t P X hs k
            ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn (cnC G t P hn X hs) (cnC_ne G t P hn X hs)
              (QMCLeafB.RecordM2.u0 G.n) k
          + QMCLeafB.RecordM2.u0 G.n
            ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn (cnC G t P hn X hs) (cnC_ne G t P hn X hs)
              (nrmC G t P X hs k) k|
        + |nrmC G t P X hs k
            ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn (cnC G t P hn X hs) (cnC_ne G t P hn X hs)
              (nrmC G t P X hs k) k|
        + 9 * (margC G t P X hs k) ^ 2 / (4 * (P.rmax) ^ 2) + 1
      ≤ lamC G t P hn X hs k *
          (QMCLeafB.RecordM2.u0 G.n
            ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn (cnC G t P hn X hs) (cnC_ne G t P hn X hs)
              (QMCLeafB.RecordM2.u0 G.n) k) :=
  QMCLeafB.RecordM2.lamInd_spec G P hn (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega)) (QMCLeafB.RecordM2.u0_d0idx G.n (by omega))
    (nrmC G t P X hs) (margC G t P X hs) hrmax

#print axioms QMCLeafB.CutRecM5.lamC_spec

/-! ## 2.  The bounded residual at the choice-free stream -/

/-- **The horizon-bounded residual, cut records at the choice-free oracle.**  Same shape as
`EndgameM2.CoreDataB`/`ResidB_M7.CoreDataB` (five fields, drifts at `k < K·m`); only the normal and
margin streams are the concrete ones. -/
structure CoreDataC (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  X : ℕ → List ℚ
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  hdriftc : ∀ k, k < P.K * P.m → flagOf G t P (cXt G X P.dq) k = false →
    (fun i => ((nrmC G t P X hsym k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (cutStreamC G t P hn X hsym) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cXt G X P.dq k)))
      ≤ ((margC G t P X hsym k : ℚ) : ℝ) / 2
  hdriftd : ∀ k, k < P.K * P.m → flagOf G t P (cXt G X P.dq) k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (cutStreamC G t P hn X hsym) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cXt G X P.dq k)))
      ≤ 0
  hverdict : o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P (cXt G X P.dq)) (P.K * P.m)

/-! ## 3.  The assembly (`bundleH_of_data` with `cutOf → cutOfC`) -/

/-- **A `BundleH` at `(G, t)` from the choice-free record.** -/
def bundleH_of_dataC {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (hrmax : 0 < P.rmax) (D : CoreDataC o G t P hn) : BundleH o G t P hn where
  ok := QMCLeafB.EndgameM2.okHor G t P (cXt G D.X P.dq)
  marg := fun k => margC G t P D.X D.hsym k
  cX := cXt G D.X P.dq
  lam := lamC G t P hn D.X D.hsym
  c := fun k => nrmC G t P D.X D.hsym k
  cn := cnC G t P hn D.X D.hsym
  C := fun k _ => cutC G t P D.X D.hsym k
  hmarg := fun k _ => rfl
  hmem := fun k hk htrue => by
    have hf : flagOf G t P (cXt G D.X P.dq) k = true := by
      rw [QMCLeafB.EndgameM2.okHor_of_lt hk] at htrue
      exact htrue
    exact QMCLeafB.FlagsM5.relaxMem_of_flagOf_true G t P (cXt G D.X P.dq) k hf
  hCsym := QMCLeafB.RecordsM2.cXst_symm G.n D.X P.dq D.hsym
  hcEq := fun k _ => rfl
  hcn := fun k => rfl
  hcne := cnC_ne G t P hn D.X D.hsym
  hlam0 := QMCLeafB.RecordM2.lamInd_nonneg (QMCLeafB.RunPartsDilate.A0P G P)
    (QMCLeafB.RecordM2.u0 G.n) (QMCLeafB.RecordM2.d0idx G.n (by omega))
    (nrmC G t P D.X D.hsym) (margC G t P D.X D.hsym) P.rmax
  hlam1 := fun k _ => QMCLeafB.RecordM2.lamInd_ge_one (QMCLeafB.RunPartsDilate.A0P G P)
    (QMCLeafB.RecordM2.u0 G.n) (QMCLeafB.RecordM2.d0idx G.n (by omega))
    (nrmC G t P D.X D.hsym) (margC G t P D.X D.hsym) P.rmax k
  hlam2 := fun k _ => lamC_spec G t P hn D.X D.hsym hrmax k
  hTrc := QMCLeafB.RecordsM2.hTrc_cXst G.n D.X P.dq
  hdriftc := fun k hok => D.hdriftc k (QMCLeafB.EndgameM2.okHor_lt hok)
    (QMCLeafB.EndgameM2.okHor_flag hok)
  hdriftd := fun k hok => D.hdriftd k (QMCLeafB.EndgameM2.okHor_lt hok)
    (QMCLeafB.EndgameM2.okHor_flag hok)
  hverdict := by
    rw [D.hverdict, QMCLeafB.EndgameM2.anyOk_okHor (P := P)]

#print axioms QMCLeafB.CutRecM5.bundleH_of_dataC

/-! ## 4.  The closing stroke -/

/-- **The residual**: one choice-free record per interior `(G, t)`. -/
abbrev ResidC (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    CoreDataC o G t (Pfam G) hn

/-- `ResidH` from the choice-free residual. -/
def residH_of_dataC {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hrmax : ∀ (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n), 0 < (Pfam G).rmax)
    (H : ResidC o Pfam) : ResidH o Pfam :=
  fun G t hn hlo hhi => bundleH_of_dataC (hrmax G hn) (H G t hn hlo hhi)

#print axioms QMCLeafB.CutRecM5.residH_of_dataC

/-- **The verbatim `d9f601e5` sentence from the choice-free residual.** -/
theorem solution_of_dataC
    (H : ResidC (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  QMCLeafB.FlagsM5.solution_of_residH
    (residH_of_dataC (fun G hn => QMCLeafB.RecordsM2.rmax_pos_paramsKbc2 G hn) H)

#print axioms QMCLeafB.CutRecM5.solution_of_dataC

/-- **The same, in `FinishLine.SolutionStatement`.** -/
theorem solution_statement_of_dataC
    (H : ResidC (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FlagsM5.solution_statement_of_residH
    (residH_of_dataC (fun G hn => QMCLeafB.RecordsM2.rmax_pos_paramsKbc2 G hn) H)

#print axioms QMCLeafB.CutRecM5.solution_statement_of_dataC

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.CutRecM5.cutC_trace
#print axioms QMCLeafB.CutRecM5.cnC_ne
#print axioms QMCLeafB.CutRecM5.lamC_spec
#print axioms QMCLeafB.CutRecM5.bundleH_of_dataC
#print axioms QMCLeafB.CutRecM5.residH_of_dataC
#print axioms QMCLeafB.CutRecM5.solution_of_dataC
#print axioms QMCLeafB.CutRecM5.solution_statement_of_dataC

end QMCLeafB.CutRecM5


