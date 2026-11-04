-- Prove2me | Definitions.Def_QMCLeafB_records_m2
-- name    : QMCLeafB_records_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:34:05.8262+00:00
-- url     : https://prove2.me/theorems/09c3b249-ec3f-4cbe-afcb-b3d64fc790cb
-- title:
--   QMCLeafB records_m2
-- statement:
--   # leaf B phase 20 — brick `records-zip` (swarm `smw1kspvn`, member m2, direction d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_flags_m5
import Definitions.Def_QMCLeafB_record_m2
import Definitions.Def_QMCLeafB_stateDiag
import Definitions.Def_QMCLeafB_pinchbudget
import Definitions.Def_QMCLeafB_centre_adm_m1
/-
# leaf B phase 20 — brick `records-zip` (swarm `smw1kspvn`, member m2, direction d3)

The phase-19 residual of the leaf is `QMCLeafB.FlagsM5.StreamCore` (equivalently `BundleH`, which is
`ClosingAssembly.Bundle` with the refuted `hokAll` **replaced** by the `ok`-round `RelaxMem` slot).
This file produces that record at every interior `(G, t)` from a strictly smaller data set, and
records exactly what is still owed.

* §1 **the centre family of the guarded run**: `cXst n X dq k := diagPinch (stMat n (X k)) dq`, the
  diagonal overwrite of the run's own coded state.  Its trace slot `hTrc` holds **unconditionally
  and with equality** (`sum_diagPinch`: `∑ i, cXst … i i = n(1 − dq/4)`), and its symmetry is
  inherited from the state (`diagPinch_symm`); so two of `StreamCore`'s slots cost nothing at all.
* §2 **the drift collapse at the pinched centre, without a unit-diagonal hypothesis**: the trace
  direction's pairing with the flattened pinch is exactly `(1 − dq/4)·n` (`dOne_flat_diagPinch`), so
  `TraceBudgetM8.drift_linear_iff` turns `hdriftd` into the *one* scalar inequality
  `∑_{j<k} λ_j·diagSum(p_j) ≤ (1 − dq/4)·n` at the run's own centres — the banked form
  (`TraceBudgetM8.hdriftd_linear_iff`) needs `Q` unit-diagonal, and at a *cut* round the state is
  not, so the hypothesis is dropped here rather than assumed.  Similarly `hdriftc` is transcribed
  into its linear form (`hdriftc_diagPinch_iff`).
* §3 **the zip**: `streamCore_of_drifts` builds the whole `StreamCore` record from
  `{cX, hCsym, hTrc, hdriftc, hdriftd, hverdict}`.  The multiplier `lam`, the dilated normal `cn`,
  its nonvanishing `hcne` and the entire depth ledger `hlam0/hlam1/hlam2` are *constructed*
  (`RecordM2.lamInd`/`cnInd`, flag-independent), and the flag stream, the margins and the cut
  records are the canonical ones of `FlagsM5.flagOf`/`cutOf` — never supplied.
* §4 **the reduced residual** `CoreData` = the run's coded states (with their symmetry), the two
  drift budgets at the constructed stream, and the verdict bit; `residCore_of_data` turns it into
  `FlagsM5.ResidCore`, and `solution_of_coreData` is the verbatim `d9f601e5` sentence.
* §5 **the residual is inhabited where the phase-19 shape is refuted**: an explicit `StreamCore` at
  `(G₀, −1/2)` whose flags are all `ok` — so the corrected shape is not vacuous and not refutable
  in the way `hokAll` was (`FlagsM5.bundleFull_false_kbc2`).
* §6 **the honest limit**: §2's scalar is *not* implied by anything else on the shelf — at a unit
  diagonal base the trace slot `hTrc` itself fails (`CentreAdm.unit_diag_breaks_trace`), which is
  why the run's centres must be pinched; and the scalar is what remains of the trace-budget
  residual after this brick.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.RecordsM2

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.RunPartsStream (dOne)
open QMCLeafB.RunPartsDilate

/-! ## 1.  The centre family of the guarded run -/

/-- **The queried centre of round `k`**: the run's own coded state, with its diagonal overwritten by
the pinch value `1 − dq/4` (`CentreAdm.diagPinch`).  This is the family the endgame's notes prescribe:
`diagPinch` of the state at *every* round, which agrees with the scaled centre `(1 − dq/4) • Q`
exactly where the state is unit-diagonal. -/
def cXst (n : ℕ) (X : ℕ → List ℚ) (dq : ℚ) (k : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  QMCLeafB.CentreAdm.diagPinch (QMCLeafB.StateDiag.stMat n (X k)) dq

/-- The pinched centre's diagonal is the pinch value, entry by entry. -/
@[simp] theorem cXst_diag (n : ℕ) (X : ℕ → List ℚ) (dq : ℚ) (k : ℕ) (i : Fin n) :
    cXst n X dq k i i = 1 - dq / 4 :=
  QMCLeafB.CentreAdm.diagPinch_diag _ _ _

/-- **`hTrc` at the run's own centres, with equality and no hypothesis at all.** -/
theorem cXst_trace (n : ℕ) (X : ℕ → List ℚ) (dq : ℚ) (k : ℕ) :
    ∑ i, cXst n X dq k i i = (n : ℚ) * (1 - dq / 4) :=
  QMCLeafB.CentreAdm.sum_diagPinch _ _

/-- **The trace slot of `StreamCore` at the run's centres** — unconditional. -/
theorem hTrc_cXst (n : ℕ) (X : ℕ → List ℚ) (dq : ℚ) :
    ∀ k, ∑ i, cXst n X dq k i i ≤ (n : ℚ) * (1 - dq / 4) :=
  fun k => le_of_eq (cXst_trace n X dq k)

/-- **The symmetry slot of `StreamCore` at the run's centres**, inherited from the state's own
symmetry (`CentreAdm.diagPinch_symm`: the overwrite is invisible off the diagonal). -/
theorem cXst_symm (n : ℕ) (X : ℕ → List ℚ) (dq : ℚ)
    (hsym : ∀ k, (QMCLeafB.StateDiag.stMat n (X k))ᵀ = QMCLeafB.StateDiag.stMat n (X k)) :
    ∀ k, (cXst n X dq k)ᵀ = cXst n X dq k := by
  intro k
  have hbase : ∀ i j, QMCLeafB.StateDiag.stMat n (X k) i j
      = QMCLeafB.StateDiag.stMat n (X k) j i := by
    intro i j
    have h := congrFun (congrFun (hsym k) i) j
    simpa [Matrix.transpose_apply] using h.symm
  have hpin := QMCLeafB.CentreAdm.diagPinch_symm hbase dq
  ext i j
  rw [Matrix.transpose_apply]
  exact (hpin i j).symm

#print axioms QMCLeafB.RecordsM2.cXst_trace
#print axioms QMCLeafB.RecordsM2.hTrc_cXst
#print axioms QMCLeafB.RecordsM2.cXst_symm

/-- **The objective at the pinched centre is the objective at the state**: the overwrite touches only
the diagonal, where the weight matrix is zero (`CentreAdm.frob_diagPinch`). -/
theorem frob_cXst {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ} (hA : ∀ i, A i i = 0) :
    QMCLeafB.SepOracle.frob A (QMCLeafB.CentreAdm.diagPinch Q dq)
      = QMCLeafB.SepOracle.frob A Q :=
  QMCLeafB.CentreAdm.frob_diagPinch hA

#print axioms QMCLeafB.RecordsM2.frob_cXst

/-! ## 2.  The drift collapse at the pinched centre, with no unit-diagonal hypothesis

`TraceBudgetM8.hdriftd_linear_iff` identifies `hdriftd` at the *scaled* centre `(1 − dq/4) • Q` with
the single scalar budget, but only when `Q` is unit-diagonal.  At a cut round the run's state is not
unit-diagonal, so the scaled centre is the wrong object (`CentreAdm.full_scale_forces_unit_base`):
the prescribed centre is the *overwrite* `diagPinch Q dq`.  The trace direction does not see
off-diagonal entries, and the overwrite fixes the diagonal exactly, so the same collapse holds with
**no** hypothesis on `Q`. -/

/-- **The trace direction pairs with the pinched centre as `(1 − dq/4)·n`** — for *every* base `Q`. -/
theorem dOne_flat_diagPinch {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (dq : ℚ) :
    dOne n ⬝ᵥ QMCLeafB.AnswerProducer.flat
        (QMCLeafB.SepOracle.castMat (QMCLeafB.CentreAdm.diagPinch Q dq))
      = ((1 - dq / 4 : ℚ) : ℝ) * ((n : ℚ) : ℝ) := by
  rw [QMCLeafB.DriftExact.dOne_dot_flat_castMat]
  have h : ∑ i : Fin n, (QMCLeafB.CentreAdm.diagPinch Q dq i i : ℝ)
      = (((n : ℚ) * (1 - dq / 4) : ℚ) : ℝ) := by
    rw [← Rat.cast_sum, QMCLeafB.CentreAdm.sum_diagPinch]
  rw [h]
  push_cast
  ring

#print axioms QMCLeafB.RecordsM2.dOne_flat_diagPinch

/-- **`hdriftd` at the run's own centres *is* the one scalar budget** — with no unit-diagonal
hypothesis (`∑_{j<k} λ_j·diagSum(p_j) ≤ (1 − dq/4)·n`). -/
theorem hdriftd_diagPinch_iff {n : ℕ} {dq : ℚ}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n))
    (Q : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) :
    dOne n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (QMCLeafB.CentreAdm.diagPinch Q dq))) ≤ 0
      ↔ (∑ j ∈ Finset.range k,
          QMCLeafB.DriftExact.engLam (n * n) cd j
            * QMCLeafB.DriftExact.diagSum (QMCLeafB.EngineIterates.cutPR cd j))
        ≤ ((1 - dq / 4 : ℚ) : ℝ) * ((n : ℚ) : ℝ) := by
  have hsum : (∑ j ∈ Finset.range k,
        QMCLeafB.DriftExact.engLam (n * n) cd j
          * QMCLeafB.DriftExact.diagSum (QMCLeafB.EngineIterates.cutPR cd j))
      = (∑ j ∈ Finset.range k,
          QMCLeafB.CentreTrack.lam (n * n) cd j
            * (dOne n ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j)) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [QMCLeafB.DriftExact.dOne_dot]
    rfl
  rw [QMCLeafB.TraceBudgetM8.drift_linear_iff, hsum, dOne_flat_diagPinch]
  constructor <;> intro h <;> linarith

#print axioms QMCLeafB.RecordsM2.hdriftd_diagPinch_iff

/-- **`hdriftc` in its linear form** at the pinched centre: the oracle normal's pairing with the
rounded centre is a per-round sum against the engine's own witnesses plus the pinched centre's own
read-out. -/
theorem hdriftc_diagPinch_iff {n : ℕ} {dq : ℚ} {marg : ℚ}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n))
    (Q : Matrix (Fin n) (Fin n) ℚ) (c : Fin (n * n) → ℝ) (k : ℕ) :
    c ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
        - QMCLeafB.AnswerProducer.flat
            (QMCLeafB.SepOracle.castMat (QMCLeafB.CentreAdm.diagPinch Q dq)))
        ≤ ((marg : ℚ) : ℝ) / 2
      ↔ (∑ j ∈ Finset.range k,
          QMCLeafB.CentreTrack.lam (n * n) cd j
            * (c ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j))
        ≤ c ⬝ᵥ QMCLeafB.AnswerProducer.flat
            (QMCLeafB.SepOracle.castMat (QMCLeafB.CentreAdm.diagPinch Q dq))
          + ((marg : ℚ) : ℝ) / 2 :=
  QMCLeafB.TraceBudgetM8.drift_linear_iff cd c _ _ k

#print axioms QMCLeafB.RecordsM2.hdriftc_diagPinch_iff

/-- **The two drifts from the collapse**: the single scalar budget gives the trace direction, and the
normal budget gives the cut normal's direction — both at the run's own pinched centres. -/
theorem drift_pair_of_collapse {n : ℕ} {dq : ℚ}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n))
    (Q : Matrix (Fin n) (Fin n) ℚ) (c : ℕ → Fin (n * n) → ℝ) (marg : ℕ → ℚ)
    (hbud : ∀ k, (∑ j ∈ Finset.range k,
        QMCLeafB.DriftExact.engLam (n * n) cd j
          * QMCLeafB.DriftExact.diagSum (QMCLeafB.EngineIterates.cutPR cd j))
      ≤ ((1 - dq / 4 : ℚ) : ℝ) * ((n : ℚ) : ℝ))
    (hnorm : ∀ k, (∑ j ∈ Finset.range k,
        QMCLeafB.CentreTrack.lam (n * n) cd j
          * (c k ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j))
      ≤ c k ⬝ᵥ QMCLeafB.AnswerProducer.flat
            (QMCLeafB.SepOracle.castMat (QMCLeafB.CentreAdm.diagPinch Q dq))
          + ((marg k : ℚ) : ℝ) / 2) :
    (∀ k, dOne n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (QMCLeafB.CentreAdm.diagPinch Q dq))) ≤ 0)
    ∧ (∀ k, c k ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (QMCLeafB.CentreAdm.diagPinch Q dq)))
        ≤ ((marg k : ℚ) : ℝ) / 2) :=
  ⟨fun k => (hdriftd_diagPinch_iff cd Q k).2 (hbud k),
    fun k => (hdriftc_diagPinch_iff cd Q (c k) k).2 (hnorm k)⟩

#print axioms QMCLeafB.RecordsM2.drift_pair_of_collapse

/-! ## 3.  The zip: `StreamCore` from the centre family and the two drift budgets

`StreamCore` has twelve fields.  Three are the *canonical* stream (`flagOf`, `margOf`, `nrmOf` are
decided from the centres by `RelaxOracle.relaxMem_or_cut`, so the flag, the margins and the cut
records are never supplied); four are the multiplier block (`lam`, `cn`, `hcne`, `hlam0/hlam1/hlam2`)
which `RecordM2.lamInd`/`cnInd` construct from the records alone, flag-independently.  What is left,
and what the theorem below asks for, is the centre family with its two structural slots, the two
drift budgets at the constructed stream, and the verdict bit. -/

open QMCLeafB.FlagsM5 (StreamCore flagOf cutOf)

/-- **The canonical oracle normal of round `k`**: the flat normal of the chosen cut record. -/
abbrev nrmOf (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) : Fin (G.n * G.n) → ℚ :=
  QMCLeafB.RelaxOracle.flatQ (cutOf G t P cX k).normal

/-- **The canonical margin of round `k`.** -/
abbrev margOf (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) : ℚ :=
  (cutOf G t P cX k).margin

/-- **The constructed multiplier stream** (the sequential choice of `RecordM2.lamInd`). -/
abbrev lamOf (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) : ℕ → ℚ :=
  QMCLeafB.RecordM2.lamInd (A0P G P) (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega)) (nrmOf G t P cX) (margOf G t P cX) P.rmax

/-- **The constructed dilated normal stream**: the oracle's normal dilated in the trace direction. -/
abbrev cnOf (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) : ℕ → Fin (G.n * G.n) → ℚ :=
  QMCLeafB.RecordM2.cnInd (nrmOf G t P cX) (lamOf G t P hn cX) (QMCLeafB.RecordM2.u0 G.n)

/-- The constructed dilated normal is nowhere zero (at the diagonal index the entry is
`c_k(d₀) + λ_k > 0`). -/
theorem cnOf_ne (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) : ∀ k, cnOf G t P hn cX k ≠ 0 :=
  QMCLeafB.RecordM2.cnInd_ne (A0P G P) (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega)) (QMCLeafB.RecordM2.u0_d0idx G.n (by omega))
    (nrmOf G t P cX) (margOf G t P cX) P.rmax

#print axioms QMCLeafB.RecordsM2.cnOf_ne

/-- **The engine's recorded stream** at the constructed dilated normals. -/
abbrev cutStream (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) :
    ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
  runCut G P hn (cnOf G t P hn cX) (cnOf_ne G t P hn cX)

/-- **The depth ledger at the constructed multiplier** — `hlam2`, flag-independently. -/
theorem lamOf_spec (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (hrmax : 0 < P.rmax) :
    ∀ k,
      |nrmOf G t P cX k
            ⬝ᵥ witAt G P hn (cnOf G t P hn cX) (cnOf_ne G t P hn cX)
              (QMCLeafB.RecordM2.u0 G.n) k
          + QMCLeafB.RecordM2.u0 G.n
            ⬝ᵥ witAt G P hn (cnOf G t P hn cX) (cnOf_ne G t P hn cX) (nrmOf G t P cX k) k|
        + |nrmOf G t P cX k
            ⬝ᵥ witAt G P hn (cnOf G t P hn cX) (cnOf_ne G t P hn cX) (nrmOf G t P cX k) k|
        + 9 * (margOf G t P cX k) ^ 2 / (4 * (P.rmax) ^ 2) + 1
      ≤ lamOf G t P hn cX k *
          (QMCLeafB.RecordM2.u0 G.n
            ⬝ᵥ witAt G P hn (cnOf G t P hn cX) (cnOf_ne G t P hn cX)
              (QMCLeafB.RecordM2.u0 G.n) k) :=
  QMCLeafB.RecordM2.lamInd_spec G P hn (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega)) (QMCLeafB.RecordM2.u0_d0idx G.n (by omega))
    (nrmOf G t P cX) (margOf G t P cX) hrmax

#print axioms QMCLeafB.RecordsM2.lamOf_spec

/-- **The zip.**  A `StreamCore` at `(G, t)` from the centre family, its two structural slots, the
two drift budgets at the constructed stream, and the verdict bit.  Every other field is built:
`hcn` is `rfl`, `hcne`/`hlam0`/`hlam1`/`hlam2` are the multiplier brick's, `hTrc` is passed in (and is
unconditional at the run's own centres, §1), and the flag stream, the margins and the cut records are
the canonical ones. -/
def streamCore_of_drifts (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hrmax : 0 < P.rmax)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hTrc : ∀ k, ∑ i, cX k i i ≤ (G.n : ℚ) * (1 - P.dq / 4))
    (hdriftc : ∀ k, flagOf G t P cX k = false →
      (fun i => ((nrmOf G t P cX k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (cutStream G t P hn cX) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((margOf G t P cX k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, flagOf G t P cX k = false →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (cutStream G t P hn cX) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P cX) (P.K * P.m)) :
    StreamCore o G t P hn where
  cX := cX
  lam := lamOf G t P hn cX
  cn := cnOf G t P hn cX
  hCsym := hCsym
  hcn := fun _ => rfl
  hcne := cnOf_ne G t P hn cX
  hlam0 := QMCLeafB.RecordM2.lamInd_nonneg (A0P G P) (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega)) (nrmOf G t P cX) (margOf G t P cX) P.rmax
  hlam1 := fun k _ => QMCLeafB.RecordM2.lamInd_ge_one (A0P G P) (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega)) (nrmOf G t P cX) (margOf G t P cX) P.rmax k
  hlam2 := fun k _ => lamOf_spec G t P hn cX hrmax k
  hTrc := hTrc
  hdriftc := hdriftc
  hdriftd := hdriftd
  hverdict := hverdict

#print axioms QMCLeafB.RecordsM2.streamCore_of_drifts

/-! ## 4.  The reduced residual, and the verbatim sentence

`CoreData` is what §3 leaves owed at one interior `(G, t)`: the run's coded states with their
symmetry (a structural slot of the programme, not of the analysis), the two drift budgets at the
*constructed* stream, and the read-out of the loop's bit.  `ResidData` is that uniformly over the
interior bracket; `solution_of_coreData` is `d9f601e5`. -/

/-- **The remaining data at one interior `(G, t)`** — the run's coded state stream, and the three
analysis slots. -/
structure CoreData (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- the run's coded states (row-major), round by round -/
  X : ℕ → List ℚ
  /-- the coded state's matrix is symmetric at every round -/
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  /-- the cut normal's centre mismatch at the pinched centre -/
  hdriftc : ∀ k, flagOf G t P (cXst G.n X P.dq) k = false →
    (fun i => ((nrmOf G t P (cXst G.n X P.dq) k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (cutStream G t P hn (cXst G.n X P.dq)) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ ((margOf G t P (cXst G.n X P.dq) k : ℚ) : ℝ) / 2
  /-- the identity direction's cumulative trace budget -/
  hdriftd : ∀ k, flagOf G t P (cXst G.n X P.dq) k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (cutStream G t P hn (cXst G.n X P.dq)) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ 0
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P (cXst G.n X P.dq)) (P.K * P.m)

/-- **`StreamCore` from the reduced data** — the centre family is `cXst` of the state, whose `hTrc`
and symmetry slots are §1's (the trace one unconditionally). -/
def streamCore_of_core {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n} (hrmax : 0 < P.rmax)
    (D : CoreData o G t P hn) : StreamCore o G t P hn :=
  streamCore_of_drifts o G t P hn hrmax (cXst G.n D.X P.dq)
    (cXst_symm G.n D.X P.dq D.hsym) (hTrc_cXst G.n D.X P.dq)
    D.hdriftc D.hdriftd D.hverdict

#print axioms QMCLeafB.RecordsM2.streamCore_of_core

/-- **The reduced residual**: one `CoreData` per interior `(G, t)`. -/
abbrev ResidData (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    CoreData o G t (Pfam G) hn

/-- **`ResidCore` from the reduced residual.** -/
def residCore_of_data {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hrmax : ∀ (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n), 0 < (Pfam G).rmax)
    (H : ResidData o Pfam) : QMCLeafB.FlagsM5.ResidCore o Pfam :=
  fun G t hn hlo hhi => streamCore_of_core (hrmax G hn) (H G t hn hlo hhi)

#print axioms QMCLeafB.RecordsM2.residCore_of_data

/-- The `round` stroke's ceiling is positive. -/
theorem rmax_pos_paramsKbc2 (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    0 < (QMCLeafB.UnionShallow.paramsKbc2 G).rmax :=
  QMCLeafB.UnionShallow.paramsKbc2_rmax_pos G hn

#print axioms QMCLeafB.RecordsM2.rmax_pos_paramsKbc2

/-- **The verbatim `d9f601e5` sentence from the reduced residual** — the `round` stroke, through
`FlagsM5.solution_of_residCore`. -/
theorem solution_of_coreData
    (H : ResidData (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  QMCLeafB.FlagsM5.solution_of_residCore
    (residCore_of_data (fun G hn => rmax_pos_paramsKbc2 G hn) H)

#print axioms QMCLeafB.RecordsM2.solution_of_coreData

/-- **The same in the shelf's own name for the sentence.** -/
theorem solution_statement_of_coreData
    (H : ResidData (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FlagsM5.solution_statement_of_residH
    (QMCLeafB.FlagsM5.residH_of_core
      (residCore_of_data (fun G hn => rmax_pos_paramsKbc2 G hn) H))

#print axioms QMCLeafB.RecordsM2.solution_statement_of_coreData

/-- **The reduced residual in the collapsed bookkeeping.**  `CoreData`'s two drift fields are
`Cat`-inequalities; via §2 they are *equivalent* to per-round sums over the engine's own witnesses, so
a supplier may hand in the arithmetic instead of the geometry:

* `hbud` — the ONE scalar trace budget `∑_{j<k} λ_j·diagSum(p_j) ≤ (1 − dq/4)·n`;
* `hnorm` — the cut normal's budget, per round, in the same increment form;
* `hverdict` — the verdict bit.

Both are statements about the run's own constructed stream (`cutStream` at the pinched centres), i.e.
about explicit rationals once the state stream is fixed. -/
structure CoreDataScalar (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- the run's coded states (row-major), round by round -/
  X : ℕ → List ℚ
  /-- the coded state's matrix is symmetric at every round -/
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  /-- **the one scalar**: the accumulated trace budget, at the cut rounds -/
  hbud : ∀ k, flagOf G t P (cXst G.n X P.dq) k = false →
      (∑ j ∈ Finset.range k,
        QMCLeafB.DriftExact.engLam (G.n * G.n) (cutStream G t P hn (cXst G.n X P.dq)) j
          * QMCLeafB.DriftExact.diagSum
              (QMCLeafB.EngineIterates.cutPR (cutStream G t P hn (cXst G.n X P.dq)) j))
      ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ)
  /-- the cut normal's per-round budget, in the same increment form -/
  hnorm : ∀ k, flagOf G t P (cXst G.n X P.dq) k = false →
    (∑ j ∈ Finset.range k,
        QMCLeafB.CentreTrack.lam (G.n * G.n) (cutStream G t P hn (cXst G.n X P.dq)) j
          * ((fun i => ((nrmOf G t P (cXst G.n X P.dq) k i : ℚ) : ℝ))
              ⬝ᵥ QMCLeafB.EngineIterates.cutPR (cutStream G t P hn (cXst G.n X P.dq)) j))
      ≤ (fun i => ((nrmOf G t P (cXst G.n X P.dq) k i : ℚ) : ℝ))
            ⬝ᵥ QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k))
          + ((margOf G t P (cXst G.n X P.dq) k : ℚ) : ℝ) / 2
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P (cXst G.n X P.dq)) (P.K * P.m)

/-- **`CoreData` from the collapsed data** — §2's two equivalences, at the run's own stream. -/
def coreData_of_scalar {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : CoreDataScalar o G t P hn) : CoreData o G t P hn where
  X := D.X
  hsym := D.hsym
  hdriftd := fun k hk =>
    (hdriftd_diagPinch_iff (cutStream G t P hn (cXst G.n D.X P.dq))
      (QMCLeafB.StateDiag.stMat G.n (D.X k)) k).2 (D.hbud k hk)
  hdriftc := fun k hk =>
    (hdriftc_diagPinch_iff (cutStream G t P hn (cXst G.n D.X P.dq))
      (QMCLeafB.StateDiag.stMat G.n (D.X k))
      (fun i => ((nrmOf G t P (cXst G.n D.X P.dq) k i : ℚ) : ℝ)) k).2 (D.hnorm k hk)
  hverdict := D.hverdict

#print axioms QMCLeafB.RecordsM2.coreData_of_scalar

/-- **The collapsed residual**: one `CoreDataScalar` per interior `(G, t)`. -/
abbrev ResidScalar (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    CoreDataScalar o G t (Pfam G) hn

/-- **`ResidData` from the collapsed residual.** -/
def residData_of_scalar {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : ResidScalar o Pfam) : ResidData o Pfam :=
  fun G t hn hlo hhi => coreData_of_scalar (H G t hn hlo hhi)

#print axioms QMCLeafB.RecordsM2.residData_of_scalar

/-- **The verbatim `d9f601e5` sentence from the one scalar plus the normal budget.** -/
theorem solution_of_scalar
    (H : ResidScalar (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  solution_of_coreData (residData_of_scalar H)

#print axioms QMCLeafB.RecordsM2.solution_of_scalar

/-- **The same, in `FinishLine.SolutionStatement`.** -/
theorem solution_statement_of_scalar
    (H : ResidScalar (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_statement_of_coreData (residData_of_scalar H)

#print axioms QMCLeafB.RecordsM2.solution_statement_of_scalar

/-! ## 5.  The corrected shape is inhabited: an explicit `StreamCore` at `(G₀, −1/2)`

`FlagsM5.bundleFull_false_kbc2` refutes the phase-19 flag stream at the two-vertex input `G₀` and
`t = −1/2`; `FlagsM5.bundleH_G₀_inhabited` shows the *corrected* bundle is not vacuous there.  Here
the same is done for the stronger `StreamCore` shape — the stream is not a hypothesis any more, so
the instance has to exhibit the canonical `flagOf`/`cutOf` at a member centre and the trace slot. -/

/-- **A member centre raises the canonical flag**: the `true` side of the dichotomy. -/
theorem flagOf_eq_true_of_mem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    flagOf G t P cX k = true := by
  unfold QMCLeafB.FlagsM5.flagOf
  exact dif_pos h

#print axioms QMCLeafB.RecordsM2.flagOf_eq_true_of_mem

/-- **A member centre's canonical cut record is the trivial one**, so its flat normal vanishes. -/
theorem flatQ_normal_cutOf_of_mem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    QMCLeafB.RelaxOracle.flatQ (cutOf G t P cX k).normal = 0 := by
  unfold QMCLeafB.FlagsM5.cutOf
  rw [dif_pos h]
  simp only [QMCLeafB.FlagsM5.defaultCut]
  rfl

#print axioms QMCLeafB.RecordsM2.flatQ_normal_cutOf_of_mem

/-- The pinch centre of §5: the boundary point `(1 − dq/4) • Q₀` of `FlagsM5`. -/
abbrev pinchG₀ : Matrix (Fin QMCLeafB.ResidRefute.G₀.n) (Fin QMCLeafB.ResidRefute.G₀.n) ℚ :=
  (1 - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq / 4)
    • QMCLeafB.FlagsM5.Q₀

/-- **The flag is `ok` at the pinch centre** — `RelaxMem` holds there (`FlagsM5.relaxMem_G₀`), and
`flagOf` decides membership. -/
theorem flag_pinchG₀ (k : ℕ) :
    flagOf QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) (fun _ => pinchG₀) k = true :=
  flagOf_eq_true_of_mem QMCLeafB.FlagsM5.relaxMem_G₀

#print axioms QMCLeafB.RecordsM2.flag_pinchG₀

/-- **The canonical cut record at the pinch centre is the trivial one** (the member side of the
dichotomy), so its flat normal is zero. -/
theorem flatQ_normal_cutOf_pinchG₀ (k : ℕ) :
    QMCLeafB.RelaxOracle.flatQ
        (cutOf QMCLeafB.ResidRefute.G₀ (-(1 / 2))
          (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) (fun _ => pinchG₀) k).normal
      = 0 :=
  flatQ_normal_cutOf_of_mem QMCLeafB.FlagsM5.relaxMem_G₀

#print axioms QMCLeafB.RecordsM2.flatQ_normal_cutOf_pinchG₀

/-- **`StreamCore` is inhabited at `(G₀, −1/2)`**: all-`ok` flags (so the cut side of every slot is
vacuous), the multiplier `λ ≡ 1` on the trace direction, the trace slot from the base's unit
diagonal, and the verdict bit `true` read out of the all-`ok` stream. -/
theorem streamCore_G₀_inhabited :
    Nonempty (StreamCore (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) := by
  have hKm : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
      * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m :=
    lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul _)
  have hany : QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true)
      ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
        * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m) = true := by
    conv_lhs => rw [show (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
        * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m
          = ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
              * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m - 1) + 1 from by omega]
    exact QMCLeafB.InhabitM5.anyOk_true_succ _
  have hflag : (flagOf QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) (fun _ => pinchG₀))
      = (fun _ : ℕ => true) := funext flag_pinchG₀
  refine ⟨{ cX := fun _ => pinchG₀
            lam := fun _ => 1
            cn := fun _ => QMCLeafB.RecordM2.u0 QMCLeafB.ResidRefute.G₀.n
            hCsym := fun _ => ?_
            hcn := fun k => ?_
            hcne := fun _ => QMCLeafB.FlagsM5.flatQ_one_ne_zero' (by norm_num)
            hlam0 := fun _ => by norm_num
            hlam1 := fun _ => by norm_num
            hlam2 := fun k hk => by rw [flag_pinchG₀ k] at hk; exact absurd hk (by simp)
            hTrc := fun _ => ?_
            hdriftc := fun k hk => by rw [flag_pinchG₀ k] at hk; exact absurd hk (by simp)
            hdriftd := fun k hk => by rw [flag_pinchG₀ k] at hk; exact absurd hk (by simp)
            hverdict := by rw [hflag]; exact hany.symm }⟩
  · -- the pinch centre is symmetric
    rw [Matrix.transpose_smul, QMCLeafB.FlagsM5.Q₀_transpose]
  · -- the canonical cut record is the trivial one at a member centre
    rw [flatQ_normal_cutOf_pinchG₀ k]
    simp [QMCLeafB.RecordM2.u0]
  · -- the trace slot at the pinch centre
    have htr : ∑ i, pinchG₀ i i
        = 2 * (1 - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq / 4) := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.smul_apply, smul_eq_mul, QMCLeafB.FlagsM5.Q₀_diag, mul_one]
      ring
    have hn2 : ((QMCLeafB.ResidRefute.G₀.n : ℕ) : ℚ) = 2 := by
      norm_num [QMCLeafB.ResidRefute.G₀]
    show ∑ i, pinchG₀ i i ≤ (QMCLeafB.ResidRefute.G₀.n : ℚ)
      * (1 - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq / 4)
    rw [htr, hn2]

#print axioms QMCLeafB.RecordsM2.streamCore_G₀_inhabited

/-! ## 6.  The honest limit

What §3 has *not* bought: the trace slot `hTrc` cannot be met by the run's raw (unit-diagonal) state
at all, so the centres must be pinched (`CentreAdm.unit_diag_breaks_trace`); and §2's single scalar
is not implied by the trace slot — it is a genuine statement about the engine's accumulated witnesses
`∑_{j<k} λ_j·diagSum(p_j)`, which is where the remaining trace-budget work sits. -/

/-- **The raw state is not an admissible centre family**: at a unit-diagonal state the trace slot
fails, so §1's pinch is forced rather than cosmetic. -/
theorem hTrc_state_fails {n : ℕ} (hn : 0 < n) {X : List ℚ} {dq : ℚ} (hdq : 0 < dq)
    (hunit : ∀ i, QMCLeafB.StateDiag.stMat n X i i = 1) :
    ¬ (∑ i, QMCLeafB.StateDiag.stMat n X i i ≤ (n : ℚ) * (1 - dq / 4)) :=
  QMCLeafB.CentreAdm.unit_diag_breaks_trace hn hdq hunit

#print axioms QMCLeafB.RecordsM2.hTrc_state_fails

/-- **The one scalar is not vacuous**: at `dq = 4` the budget's right-hand side is `0`, and any
nonnegative accumulated witness sum violates it — so the scalar inequality of §2 is a real
constraint on the engine's stream, not a restatement of the trace slot. -/
theorem scalar_budget_not_free (S : ℝ) (hS : 0 < S) :
    ¬ (S ≤ ((1 - (4 : ℚ) / 4 : ℚ) : ℝ) * ((1 : ℚ) : ℝ)) := by
  intro h
  norm_num at h
  linarith

#print axioms QMCLeafB.RecordsM2.scalar_budget_not_free

/-! ## 7.  The verdict bit: the interface between this brick and the ok-branch bricks

`CoreData.hverdict` is the one field that ties the canonically built flag stream to the *programme's*
output bit.  It splits in two, and the two halves have different owners:

* **`ok` ⇒ flag**: at a round the programme's own test accepts, the pinched state is a member, so the
  canonical flag is `true`.  This is *proved here* (`flag_cXst_of_ok`), from the banked ok-branch
  brick `CentreAdm.relaxMem_diagPinch` (unit diagonal + exact PSD + the programme's `ok` test at the
  level) — no PSD margin and no tolerance accounting.
* **not `ok` ⇒ not flag**: at a round the test rejects, the pinched state is *outside* the relaxation
  by a positive margin.  This is where the OK branch's PSD-margin certificate belongs (brick
  `interval-ldlt-psdmargin`): the snapped test is refuted (`pivAns_not_sound`), so the rejection
  side has to be bought by a genuine eps-entrywise certificate
  (`SepOracle.psdMargin_of_shifted_cert`).

Given the two halves, `hverdict` is a pure formality: `hverdict_of_agreement` composes them with the
loop's own read-out `o G t = anyOk (programme's bit) (K·m)`. -/

/-- **The weight matrix has zero diagonal** — the reason the diagonal overwrite is invisible to the
objective. -/
theorem wMatrixQ_diag (G : QuantumMaxCutEnergy.Input) (i : Fin G.n) :
    QMCLeafB.Finalization.wMatrixQ G i i = 0 := by
  rw [QMCLeafB.Finalization.wMatrixQ_apply]
  simp

#print axioms QMCLeafB.RecordsM2.wMatrixQ_diag

/-- **The `ok` half of the verdict read-out**: if the programme's own test accepts the state at round
`k` (unit diagonal, exactly PSD, objective within `dq/2` of the level `t − ε`), then the canonical
flag at the run's pinched centre is `true`. -/
theorem flag_cXst_of_ok {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {X : ℕ → List ℚ} (k : ℕ)
    (hdq : 0 < P.dq) (hdq4 : P.dq ≤ 4)
    (hunit : ∀ i, QMCLeafB.StateDiag.stMat G.n (X k) i i = 1)
    (hpsd : ∀ x : Fin G.n → ℚ,
      0 ≤ QMCLeafB.SepOracle.qf (QMCLeafB.StateDiag.stMat G.n (X k)) x)
    (htrace : QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G)
        (QMCLeafB.StateDiag.stMat G.n (X k))
      ≤ (t - QMCLeafB.RundataCert.eps G) + P.dq / 2) :
    flagOf G t P (cXst G.n X P.dq) k = true :=
  flagOf_eq_true_of_mem
    (QMCLeafB.CentreAdm.relaxMem_diagPinch hdq hdq4 (wMatrixQ_diag G) hunit hpsd htrace)

#print axioms QMCLeafB.RecordsM2.flag_cXst_of_ok

/-- **`anyOk` depends only on the first `N` bits.** -/
theorem anyOk_congr {f g : ℕ → Bool} {N : ℕ} (h : ∀ k, k < N → f k = g k) :
    QMCLeafB.SimLoop.anyOk f N = QMCLeafB.SimLoop.anyOk g N := by
  induction N with
  | zero => rfl
  | succ k ih =>
      rw [QMCLeafB.SimLoop.anyOk_succ, QMCLeafB.SimLoop.anyOk_succ, h k (by omega),
        ih (fun j hj => h j (by omega))]

#print axioms QMCLeafB.RecordsM2.anyOk_congr

/-- **The verdict bit from the round-by-round agreement** with the programme's own bit stream. -/
theorem hverdict_of_agreement {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {rb : ℕ → Bool}
    (hbit : o G t = QMCLeafB.SimLoop.anyOk rb (P.K * P.m))
    (hagree : ∀ k, k < P.K * P.m → (flagOf G t P cX k = false ↔ rb k = false)) :
    o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P cX) (P.K * P.m) := by
  rw [hbit]
  refine anyOk_congr (fun k hk => ?_)
  have h := hagree k hk
  cases hf : flagOf G t P cX k <;> cases hr : rb k <;> simp_all

#print axioms QMCLeafB.RecordsM2.hverdict_of_agreement

/-! ## 8.  The verdict equation, split into the half that is proved and the half that is a
certificate, plus the *finite-cut* form of the drift slots

`hverdict` is an equation between the programme's verdict bit and `anyOk` of the membership flags.
Its two directions have different owners:

* **sound half, PROVED here** (`hverdict_sound_half`): if the programme's bit at round `k` is "ok"
  then the canonical flag at round `k` is `true`.  That premise is `flag_cXst_of_ok` (§7), so
  `o G t = true` forces `anyOk (flagOf …) (K·m) = true` with **no** certificate.
* **cut half** (`hverdict_cut_half`): `o G t = false` forces `anyOk (flagOf …) = false`, i.e. the
  programme never reports "ok" at a round *and* no queried centre is a member.  The per-round form of
  the premise is `flag true → programme ok`, i.e. *no false cut* — this is exactly where the
  PSD-margin certificate of brick 1 enters (§9), because membership allows a `dq/2` PSD margin while
  the pivot test rejects at a much coarser scale (`pivAns_not_sound`).

§10 then states the two drift slots in the **finite-cut** form (all cut rounds below the run's
horizon `K·m`), which is the satisfiable reading: the engine's centre accumulates one witness per
round, so the trace budget cannot be demanded past the last cut round.  `coreData_of_finite` converts
it back into the `∀ k` shape, so `FlagsM5`'s shapes are untouched. -/

/-- **`anyOk` is monotone in the bit stream** (roundwise, on the first `N` rounds). -/
theorem anyOk_true_of_imp {f g : ℕ → Bool} {N : ℕ}
    (h : ∀ k, k < N → f k = true → g k = true)
    (hf : QMCLeafB.SimLoop.anyOk f N = true) : QMCLeafB.SimLoop.anyOk g N = true := by
  obtain ⟨k, hk, hfk⟩ := (QMCLeafB.SimLoop.anyOk_eq_true_iff f N).1 hf
  exact (QMCLeafB.SimLoop.anyOk_eq_true_iff g N).2 ⟨k, hk, h k hk hfk⟩

#print axioms QMCLeafB.RecordsM2.anyOk_true_of_imp

/-- **The sound half of the verdict equation, proved.**  If every programme-`ok` round is a member
round (which is `flag_cXst_of_ok` at the pinched centres), then a `true` verdict forces the membership
stream to read `true`. -/
theorem hverdict_sound_half {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {rb : ℕ → Bool}
    (hbit : o G t = QMCLeafB.SimLoop.anyOk rb (P.K * P.m))
    (himp : ∀ k, k < P.K * P.m → rb k = true → flagOf G t P cX k = true)
    (ho : o G t = true) :
    QMCLeafB.SimLoop.anyOk (flagOf G t P cX) (P.K * P.m) = true := by
  rw [hbit] at ho
  exact anyOk_true_of_imp himp ho

#print axioms QMCLeafB.RecordsM2.hverdict_sound_half

/-- **The cut half of the verdict equation**: a `false` verdict forces the membership stream to read
`false`, *provided* no member round is reported as a cut.  That premise is the PSD-margin
certificate's job (§9), not the soundness of the descent. -/
theorem hverdict_cut_half {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {rb : ℕ → Bool}
    (hbit : o G t = QMCLeafB.SimLoop.anyOk rb (P.K * P.m))
    (himp : ∀ k, k < P.K * P.m → flagOf G t P cX k = true → rb k = true)
    (ho : o G t = false) :
    QMCLeafB.SimLoop.anyOk (flagOf G t P cX) (P.K * P.m) = false := by
  rw [hbit] at ho
  rw [QMCLeafB.SimLoop.anyOk_eq_false_iff] at ho ⊢
  intro k hk
  by_cases hb : flagOf G t P cX k = true
  · exact absurd (himp k hk hb) (by rw [ho k hk]; simp)
  · cases hbb : flagOf G t P cX k
    · rfl
    · exact absurd hbb hb

#print axioms QMCLeafB.RecordsM2.hverdict_cut_half

/-- **The verdict equation is exactly its two halves.**  `hverdict` follows from the loop's own
read-out `o G t = anyOk rb (K·m)` plus

* `hon` — a programme-`ok` round is a member round (proved at the pinched centres by
  `flag_cXst_of_ok`, hence free once the ok-branch brick is quoted);
* `hoff` — a member round is not reported as a cut (the no-false-cut premise, which is the PSD-margin
  certificate's job, §9).

Nothing else is hidden in it. -/
theorem hverdict_of_halves {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {rb : ℕ → Bool}
    (hbit : o G t = QMCLeafB.SimLoop.anyOk rb (P.K * P.m))
    (hon : ∀ k, k < P.K * P.m → rb k = true → flagOf G t P cX k = true)
    (hoff : ∀ k, k < P.K * P.m → flagOf G t P cX k = true → rb k = true) :
    o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P cX) (P.K * P.m) := by
  by_cases ho : o G t = true
  · rw [ho, hverdict_sound_half hbit hon ho]
  · have hof : o G t = false := by
      cases h : o G t
      · rfl
      · exact absurd h ho
    rw [hof, hverdict_cut_half hbit hoff hof]

#print axioms QMCLeafB.RecordsM2.hverdict_of_halves

/-! ## 9.  The three ways a centre can be *outside* the relaxation

`RelaxMem` has three numeric slots — `psd_margin` (`dq/2`), `diag_near` (`dq/4`), `trace_le`
(`u + dq/2`).  A violated one is a proof of non-membership, hence (by the dichotomy) a `false` flag.
These are the targets brick 1 (the eps-entrywise PSD certificate) and the programme's own diagonal /
trace tests have to hit; they are one line each, and they are what `hverdict_cut_half` consumes. -/

/-- A violated PSD margin puts the centre outside the relaxation. -/
theorem notMem_of_psdMargin {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (h : ∃ x : Fin n → ℚ, QMCLeafB.SepOracle.qf Q x < -(dq / 2) * ∑ i, x i ^ 2) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem A Q u dq := by
  intro hM
  obtain ⟨x, hx⟩ := h
  have := hM.psd_margin x
  linarith

#print axioms QMCLeafB.RecordsM2.notMem_of_psdMargin

/-- A diagonal entry outside the `dq/4` band puts the centre outside the relaxation. -/
theorem notMem_of_diag {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ} (i : Fin n)
    (h : dq / 4 < |Q i i - 1|) : ¬ QMCLeafB.RelaxOracle.RelaxMem A Q u dq := by
  intro hM
  have := hM.diag_near i
  linarith

#print axioms QMCLeafB.RecordsM2.notMem_of_diag

/-- An objective above the level `u + dq/2` puts the centre outside the relaxation. -/
theorem notMem_of_trace {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (h : u + dq / 2 < QMCLeafB.SepOracle.frob A Q) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem A Q u dq := by
  intro hM
  have := hM.trace_le
  linarith

#print axioms QMCLeafB.RecordsM2.notMem_of_trace

/-- **A violated PSD margin raises the canonical `false` flag** — the shape brick 1 plugs into. -/
theorem flag_false_of_psdMargin {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : ∃ x : Fin G.n → ℚ,
      QMCLeafB.SepOracle.qf (cX k) x < -(P.dq / 2) * ∑ i, x i ^ 2) :
    flagOf G t P cX k = false :=
  QMCLeafB.FlagsM5.flagOf_false_of_not_mem G t P cX k (notMem_of_psdMargin h)

#print axioms QMCLeafB.RecordsM2.flag_false_of_psdMargin

/-! ## 10.  The finite-cut form of the residual

`StreamCore` states the two drift slots at **every** `k : ℕ`.  The engine's centre accumulates one
witness per round and the recorded normal is `lam_k • u₀` on the member side, so the accumulated trace
cannot be bounded past the last cut round; the honest obligation is finite.  `CoreDataF` states it
that way — the cut rounds are below the run's horizon `K·m` — and `coreData_of_finite` converts it back
into `CoreData`, so no `FlagsM5` shape changes. -/

/-- **The residual in finite-cut form**: the run's coded states, the statement that every cut round is
below the horizon, the two budgets on those rounds only, and the verdict bit. -/
structure CoreDataF (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  X : ℕ → List ℚ
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  /-- **finitely many cut rounds**: every non-member round is inside the run's horizon -/
  hcutfin : ∀ k, flagOf G t P (cXst G.n X P.dq) k = false → k < P.K * P.m
  hdriftc : ∀ k, k < P.K * P.m → flagOf G t P (cXst G.n X P.dq) k = false →
    (fun i => ((nrmOf G t P (cXst G.n X P.dq) k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (cutStream G t P hn (cXst G.n X P.dq)) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ ((margOf G t P (cXst G.n X P.dq) k : ℚ) : ℝ) / 2
  hdriftd : ∀ k, k < P.K * P.m → flagOf G t P (cXst G.n X P.dq) k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (cutStream G t P hn (cXst G.n X P.dq)) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ 0
  hverdict : o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P (cXst G.n X P.dq)) (P.K * P.m)

/-- **`CoreData` from the finite-cut data**: the `∀ k` slots follow because there are no cut rounds
beyond the horizon. -/
def coreData_of_finite {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : CoreDataF o G t P hn) : CoreData o G t P hn where
  X := D.X
  hsym := D.hsym
  hdriftc := fun k hk => D.hdriftc k (D.hcutfin k hk) hk
  hdriftd := fun k hk => D.hdriftd k (D.hcutfin k hk) hk
  hverdict := D.hverdict

#print axioms QMCLeafB.RecordsM2.coreData_of_finite

/-- **The finite-cut residual.** -/
abbrev ResidFinite (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    CoreDataF o G t (Pfam G) hn

/-- **`ResidData` from the finite-cut residual.** -/
def residData_of_finite {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : ResidFinite o Pfam) : ResidData o Pfam :=
  fun G t hn hlo hhi => coreData_of_finite (H G t hn hlo hhi)

#print axioms QMCLeafB.RecordsM2.residData_of_finite

/-- **The verbatim `d9f601e5` sentence from the finite-cut residual.** -/
theorem solution_of_finite
    (H : ResidFinite (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  solution_of_coreData (residData_of_finite H)

#print axioms QMCLeafB.RecordsM2.solution_of_finite

/-- **The same, in `FinishLine.SolutionStatement`.** -/
theorem solution_statement_of_finite
    (H : ResidFinite (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_statement_of_coreData (residData_of_finite H)

#print axioms QMCLeafB.RecordsM2.solution_statement_of_finite

/-! ## 11.  The finite-cut residual is inhabited at `(G₀, −1/2)`

The point where the phase-19 flag stream is refuted (`FlagsM5.bundleFull_false_kbc2`).  The instance
is the run state whose matrix is `FlagsM5.Q₀ = !![1, −3/4; −3/4, 1]` at every round; its pinched
centre is a member by the ok-branch brick (unit diagonal, exactly PSD, objective `−3/4` well below
`−1/2 − ε + dq/2`), so every canonical flag is `true`, every cut-side slot is vacuous, and the
verdict bit of an all-`ok` stream is `true`. -/

/-- The row-major code of `FlagsM5.Q₀`. -/
abbrev Q₀code : List ℚ := [1, -(3 / 4), -(3 / 4), 1]

/-- The coded matrix is `Q₀`. -/
theorem stMat_Q₀code :
    QMCLeafB.StateDiag.stMat QMCLeafB.ResidRefute.G₀.n Q₀code = QMCLeafB.FlagsM5.Q₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QMCLeafB.StateDiag.stMat_apply, Q₀code, QMCLeafB.FlagsM5.Q₀]

#print axioms QMCLeafB.RecordsM2.stMat_Q₀code

/-- **The pinched `Q₀` is a member at `(G₀, −1/2)`**: the ok-branch brick at a unit-diagonal, exactly
PSD base whose objective is far below the level. -/
theorem relaxMem_pinch_Q₀ :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀)
      (QMCLeafB.CentreAdm.diagPinch QMCLeafB.FlagsM5.Q₀
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq)
      (-(1 / 2) - QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq := by
  have hdq : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq :=
    QMCLeafB.RecordM2.dq_pos_paramsKbc2 _
  have hdq4 : (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq ≤ 4 :=
    le_of_lt (QMCLeafB.RecordM2.dq_lt_four_paramsKbc2 QMCLeafB.ResidRefute.G₀)
  refine QMCLeafB.CentreAdm.relaxMem_diagPinch hdq hdq4 (wMatrixQ_diag _)
    QMCLeafB.FlagsM5.Q₀_diag QMCLeafB.FlagsM5.Q₀_qf ?_
  rw [QMCLeafB.FlagsM5.frob_Q₀, QMCLeafB.FlagsM5.eps_G₀]
  nlinarith [hdq]

#print axioms QMCLeafB.RecordsM2.relaxMem_pinch_Q₀

/-- **Every canonical flag of the pinched `Q₀` stream is `ok`.** -/
theorem flag_cXst_Q₀ (k : ℕ) :
    flagOf QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      (cXst QMCLeafB.ResidRefute.G₀.n (fun _ => Q₀code)
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq) k = true := by
  refine flagOf_eq_true_of_mem ?_
  show QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀)
    (QMCLeafB.CentreAdm.diagPinch
      (QMCLeafB.StateDiag.stMat QMCLeafB.ResidRefute.G₀.n Q₀code)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq)
    (-(1 / 2) - QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀)
    (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq
  rw [stMat_Q₀code]
  exact relaxMem_pinch_Q₀

#print axioms QMCLeafB.RecordsM2.flag_cXst_Q₀

/-- **The finite-cut residual is inhabited at `(G₀, −1/2)`** — the corrected shape, unlike the
phase-19 one, is not vacuous at the point where the latter is refuted. -/
theorem coreDataF_G₀_inhabited :
    Nonempty (CoreDataF (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) := by
  have hKm : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
      * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m :=
    lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul _)
  have hany : QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true)
      ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
        * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m) = true := by
    conv_lhs => rw [show (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
        * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m
          = ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
              * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m - 1) + 1 from by omega]
    exact QMCLeafB.InhabitM5.anyOk_true_succ _
  have hflag : (flagOf QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      (cXst QMCLeafB.ResidRefute.G₀.n (fun _ => Q₀code)
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq))
      = (fun _ : ℕ => true) := funext flag_cXst_Q₀
  refine ⟨{ X := fun _ => Q₀code
            hsym := fun _ => ?_
            hcutfin := fun k hk => by rw [hflag] at hk; exact absurd hk (by simp)
            hdriftc := fun k _ hk => by rw [hflag] at hk; exact absurd hk (by simp)
            hdriftd := fun k _ hk => by rw [hflag] at hk; exact absurd hk (by simp)
            hverdict := by rw [hflag]; exact hany.symm }⟩
  rw [stMat_Q₀code]
  exact QMCLeafB.FlagsM5.Q₀_transpose

#print axioms QMCLeafB.RecordsM2.coreDataF_G₀_inhabited

end QMCLeafB.RecordsM2


