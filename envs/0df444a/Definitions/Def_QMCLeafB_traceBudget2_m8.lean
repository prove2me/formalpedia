-- Prove2me | Definitions.Def_QMCLeafB_traceBudget2_m8
-- name    : QMCLeafB_traceBudget2_m8
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:25:04.259416+00:00
-- url     : https://prove2.me/theorems/3961c15d-9f38-489f-9e8c-5d0810d91247
-- title:
--   QMCLeafB traceBudget2_m8
-- statement:
--   # leaf B phase 18, second attempt — brick `trace-budget` (swarm `smw1i2drp`, member m8, d2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_traceBudget_m8
import Definitions.Def_QMCLeafB_runparts_dilate_m5
/-
# leaf B phase 18, second attempt — brick `trace-budget` (swarm `smw1i2drp`, member m8, d2)

Follows `Check_traceBudget_m8.lean` (which reduces the slot at the pinch-lowered centre and refutes the
naive `diag_near ⇒ hTrc` route).  Two things are added here, on the judge's request:

## A.  The linear accounting (`diagSum_cat` and the `c_k ⪝`-indexed sums)

`Cat k = ∑_{j<k} λ_j • p_j` (`CentreTrack.Cat_eq_sum`), so for **every** direction `u` and bound `β`
the drift condition is *exactly* the accumulated per-round pairing:

    u ⪝ (Cat k − q) ≤ β   ⟺   ∑_{j<k} λ_j · (u ⪝ p_j) ≤ u ⪝ q + β.        (`drift_linear_iff`)

Instantiating at the pinch-lowered centre `q = (1 − dq/4) • flat Q_k`:

* `hdriftd` ⟺ `∑_{j<k} λ_j · diagSum (p_j) ≤ (1 − dq/4) · n`     (`hdriftd_linear_iff`,
  via `DriftExact.diagSum_cat` — the trace budget read as a *sum of increments*, and `tr Q_k = n`
  by the pinch of the earlier brick);
* `hdriftc` ⟺ `∑_{j<k} λ_j · (c_k ⪝ p_j) ≤ (1 − dq/4) · (c_k ⪝ flat Q_k) + marg_k/2`
  (`hdriftc_linear_iff`).

Both are the **same** functional form `∑_{j<k} λ_j (u ⪝ p_j) ≤ u ⪝ q + β` — one linear budget, two
instances.  §B removes the duplication at the interface: the two drift hypotheses of
`RunPartsDilate.runParts_of_dilated` are replaced by the *single* centre-approximation condition on
the dilated normal, which is what the two of them are only ever used for.

## B.  The single-budget conduit

`runParts_of_dilated_appr` : `RunParts o G t P` with **one** drift hypothesis

    happr : ∀ k hok, cn_k ⪝ (Cat k − flat (cX k)) ≤ marg_k / 2

in place of `hdriftc` and `hdriftd`.  At `dM = 1` and `cn_k = c_k + λ_k • dOne` this is the combined
budget; the pair implies it (`happr_of_drifts`) but not conversely, so the residual strictly shrinks.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.TraceBudgetM8

open QuantumMaxCutEnergy
open QMCLeafB.DriftExact (diagSum)
open QMCLeafB.RunPartsStream (dOne)
open QMCLeafB.RunPartsDilate

/-! ## A.  The linear accounting -/

/-- The diagonal read-out of a unit-diagonal rational matrix, cast to `ℝ`. -/
theorem sum_diag_cast_of_unitDiag {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ)
    (h : ∀ i, Q i i = 1) : (∑ i, ((Q i i : ℚ) : ℝ)) = ((n : ℚ) : ℝ) := by
  rw [← Rat.cast_sum, diag_sum_one_diag Q h]

/-- **The master linear-accounting identity of the drift slot.**  For *every* direction `u`, query
point `q` and bound `β`: the drift condition is exactly the accumulated per-round pairing of `u`
against the engine's own witnesses `p_j`, with coefficients `λ_j`. -/
theorem drift_linear_iff {N : ℕ} (cd : ℕ → QMCLeafB.EngineIterates.CutData N)
    (u q : Fin N → ℝ) (β : ℝ) (k : ℕ) :
    u ⬝ᵥ (QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k - q) ≤ β
      ↔ (∑ j ∈ Finset.range k,
          QMCLeafB.CentreTrack.lam N cd j
            * (u ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j)) ≤ u ⬝ᵥ q + β := by
  rw [QMCLeafB.CentreTrack.Cat_eq_sum, dotProduct_sub, QMCLeafB.CentreTrack.dot_sum_smul]
  constructor <;> intro h <;> linarith [h]

/-- **`hdriftd` as a sum of increments** (`diagSum_cat` at the pinch-lowered centre).  The engine
centre's diagonal read-out is `∑_{j<k} λ_j · diagSum (p_j)`, and the pinch makes the query centre's
trace exactly `(1 − dq/4) · n`. -/
theorem hdriftd_linear_iff {n : ℕ} {dq : ℚ}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n))
    (Q : Matrix (Fin n) (Fin n) ℚ) (hunit : ∀ i, Q i i = 1) (k : ℕ) :
    dOne n ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
        - QMCLeafB.AnswerProducer.flat
            (QMCLeafB.SepOracle.castMat ((1 - dq / 4) • Q))) ≤ 0
      ↔ (∑ j ∈ Finset.range k,
          QMCLeafB.DriftExact.engLam (n * n) cd j
            * diagSum (QMCLeafB.EngineIterates.cutPR cd j))
        ≤ ((1 - dq / 4 : ℚ) : ℝ) * ((n : ℚ) : ℝ) := by
  rw [hdriftd_boundary_iff, QMCLeafB.DriftExact.diagSum_cat, sum_diag_cast_of_unitDiag Q hunit]

/-- **`hdriftc` as a sum of increments**: the same budget, evaluated at the cut normal. -/
theorem hdriftc_linear_iff {n : ℕ} {dq : ℚ} {marg : ℚ}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n))
    (Q : Matrix (Fin n) (Fin n) ℚ) (c : Fin (n * n) → ℝ) (k : ℕ) :
    c ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
        - QMCLeafB.AnswerProducer.flat
            (QMCLeafB.SepOracle.castMat ((1 - dq / 4) • Q))) ≤ ((marg : ℚ) : ℝ) / 2
      ↔ (∑ j ∈ Finset.range k,
          QMCLeafB.CentreTrack.lam (n * n) cd j
            * (c ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j))
        ≤ ((1 - dq / 4 : ℚ) : ℝ) * (c ⬝ᵥ QMCLeafB.AnswerProducer.flat
            (QMCLeafB.SepOracle.castMat Q)) + ((marg : ℚ) : ℝ) / 2 := by
  rw [drift_linear_iff,
    QMCLeafB.CentreClosure.flat_castMat_smul (1 - dq / 4) Q, dotProduct_smul, smul_eq_mul]

/-- **The two halves make the single budget**: the drift pair at `dM = 1` implies the centre
approximation on the dilated normal `c_k + λ_k • dOne`. -/
theorem happr_of_drifts {n : ℕ} (v c : Fin (n * n) → ℝ) (m : ℚ) (lam : ℝ) (hl : 0 ≤ lam)
    (hc : c ⬝ᵥ v ≤ ((m : ℚ) : ℝ) / 2) (hd : dOne n ⬝ᵥ v ≤ 0) :
    (c + lam • dOne n) ⬝ᵥ v ≤ ((m : ℚ) : ℝ) / 2 := by
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
  have h2 : lam * (dOne n ⬝ᵥ v) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl hd
  linarith [hc, h2]

/-- The single budget in the same linear form (one instance of `drift_linear_iff`). -/
theorem happr_linear_iff {N : ℕ} (cd : ℕ → QMCLeafB.EngineIterates.CutData N)
    (c : Fin N → ℝ) (q : Fin N → ℝ) (m : ℚ) (k : ℕ) :
    c ⬝ᵥ (QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k - q) ≤ ((m : ℚ) : ℝ) / 2
      ↔ (∑ j ∈ Finset.range k,
          QMCLeafB.CentreTrack.lam N cd j
            * (c ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j))
        ≤ c ⬝ᵥ q + ((m : ℚ) : ℝ) / 2 :=
  drift_linear_iff cd c q (((m : ℚ) : ℝ) / 2) k


/-! ## B.  The single-budget conduit: two drift hypotheses become one

`RunPartsDilate.runParts_of_dilated` takes both `hdriftc` (the cut normal's centre mismatch) and
`hdriftd` (the dilation direction's).  They are used for exactly one thing — the centre
approximation `happr` of `RunPartsShallow.runParts_of_relaxRun` at the dilated normal
`c_k + λ_k • dM`.  This conduit takes that single inequality as the hypothesis instead:

    happr : ∀ k hok, cn_k ⬝ᵥ (Cat k − flat (cX k)) ≤ marg_k / 2.

The pair implies it (`happr_of_drifts`), so nothing is lost on the producing side, and the residual
of the drift slot is one condition per round rather than two.  Everything else (the depth ledger
`hlam2`/`hdepth`, `hbody`, the ok branch) is verbatim `runParts_of_dilated`.
-/

noncomputable def runParts_of_dilated_appr
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hrmax : 0 < P.rmax)
    (hbud : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (dM : Matrix (Fin G.n) (Fin G.n) ℚ) (hdM : dM ≠ 0)
    (lam : ℕ → ℚ) (c : ℕ → Fin (G.n * G.n) → ℚ) (cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < P.K * P.m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k (hok : ok k = false),
      cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ dM)
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hbody : ∀ k (hok : ok k = false), ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G)) (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ)
        ((P.dq : ℚ) : ℝ) X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
        (X - QMCLeafB.SepOracle.castMat (cX k)))
    (happr : ∀ k (hok : ok k = false),
      (fun i => ((cn k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hlam1 : ∀ k (hok : ok k = false), 1 ≤ lam k)
    (hlam2 : ∀ k (hok : ok k = false),
      |(c k ⬝ᵥ witAt G P hn cn hcne (QMCLeafB.RelaxOracle.flatQ dM) k)
          + (QMCLeafB.RelaxOracle.flatQ dM ⬝ᵥ witAt G P hn cn hcne (c k) k)|
        + |c k ⬝ᵥ witAt G P hn cn hcne (c k) k|
        + 9 * (marg k) ^ 2 / (4 * (P.rmax) ^ 2) + 1
        ≤ lam k * (QMCLeafB.RelaxOracle.flatQ dM
            ⬝ᵥ witAt G P hn cn hcne (QMCLeafB.RelaxOracle.flatQ dM) k))
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)) :
    QMCLeafB.FinalStroke.RunParts o G t P := by
  classical
  have hN : 2 ≤ G.n * G.n := by
    have h := Nat.mul_le_mul hn hn
    omega
  -- the dilated cut stream
  have hbody' := hbody
  -- the recorded stream is `runCut` at `cn`
  refine QMCLeafB.RunPartsShallow.runParts_of_relaxRun o G t P hn hbud ok
    (runCut G P hn cn hcne) marg cX
    (dilCut G t P.dq ok cX dM C lam hlam0 hbody') ?_ hmem hCsym ?_ ?_ ?_ ?_ ?_ ?_ ?_ hverdict
  · -- `hmarg`
    intro k hok
    rw [dilCut_margin G t P.dq ok cX dM C lam hlam0 hbody' k hok]
    exact hmarg k hok
  · -- `hnorm`
    intro k hok
    rw [runCut_c G P hn cn hcne k, hcn k hok, hcEq k hok,
      dilCut_normal G t P.dq ok cX dM C lam hlam0 hbody' k hok]
  · -- `happr`: supplied as the single drift hypothesis
    intro k hok
    have hcr : QMCLeafB.EngineIterates.cutCR (runCut G P hn cn hcne) k
        = fun i => ((cn k i : ℚ) : ℝ) := by
      funext i
      simp [QMCLeafB.EngineIterates.cutCR, runCut_c]
    have hmg : (((dilCut G t P.dq ok cX dM C lam hlam0 hbody' k hok).margin : ℚ) : ℝ)
        = ((marg k : ℚ) : ℝ) := by
      rw [dilCut_margin G t P.dq ok cX dM C lam hlam0 hbody' k hok, hmarg k hok]
    rw [hcr, hmg]
    exact happr k hok
  · -- `hdepth`: the ledger, from the dilation
    intro k hok
    have hT0 : (0 : ℚ) ≤ 9 * (marg k) ^ 2 / (4 * (P.rmax) ^ 2) := by positivity
    have hstep := depth_of_dilation (runShape_posQ G P hn cn hcne k)
      (witAt_spec G P hn cn hcne (c k) k)
      (witAt_spec G P hn cn hcne (QMCLeafB.RelaxOracle.flatQ dM) k)
      (fun hzero => hdM (QMCLeafB.RunPartsDilate.flatQ_eq_zero hzero))
      hT0 (hlam1 k hok) (hlam2 k hok)
    -- identify the recorded σ with the dilated one
    have hinj : witAt G P hn cn hcne (cn k) k
        = witAt G P hn cn hcne (c k) k
          + lam k • witAt G P hn cn hcne (QMCLeafB.RelaxOracle.flatQ dM) k := by
      refine QMCLeafB.RunPartsDilate.mulVec_inj_of_posQ (runShape_posQ G P hn cn hcne k) ?_
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, witAt_spec, witAt_spec, witAt_spec, hcn k hok]
    have hσ : QMCLeafB.EngineIterates.sigmaQ (runCut G P hn cn hcne k).c
        (runCut G P hn cn hcne k).p
        = (c k + lam k • QMCLeafB.RelaxOracle.flatQ dM)
          ⬝ᵥ (witAt G P hn cn hcne (c k) k
            + lam k • witAt G P hn cn hcne (QMCLeafB.RelaxOracle.flatQ dM) k) := by
      rw [runCut_c, runCut_eq_witAt]
      simp only [QMCLeafB.EngineIterates.sigmaQ]
      rw [hinj, hcn k hok]
    rw [hσ, runCut_rho]
    have hquad : (P.rmax) ^ 2 * (9 * (marg k) ^ 2 / (4 * (P.rmax) ^ 2))
        = (3 * marg k / 2) ^ 2 := by
      field_simp
      ring
    have hpos : (0 : ℚ) ≤ (P.rmax) ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hstep hpos
    rw [hquad] at hmul
    exact hmul
  · -- `hwit`
    exact runCut_wit G P hn cn hcne
  · -- `hρ0`
    intro k
    exact P.hrmax
  · -- `hρmax`
    intro k
    exact le_refl _
  · -- `hcne`
    exact hcne

/-! ## C.  The drop-in at the campaign family, with one drift hypothesis

`runParts_at_interior_appr`: `RunParts o G t (paramsKbc2 G)` at the pinch-lowered centre
`cX k = (1 − dq/4) • Q k`, with `hmem`, `hCsym`, `hTrc` and `hbody` all discharged from base-stream
data, and the drift block reduced to the **single** centre-approximation inequality `happr`.  This is
the drop-in replacement for `DriftExact.runParts_at_interior_exact`: its residual is

    hQ1  : ∀ k i, 1 ≤ Q k i i                     (base point above the band, for the lowering)
    hQsym, htrcQ, hraw, hu                        (base-stream trace budget + ok-branch certificate)
    C, hmarg, hcEq, hcn, hcne, hlam0, hlam1, hlam2 (the oracle's records, verbatim)
    happr : ∀ k hok, cn_k ⪝ (Cat k − flat cX_k) ≤ marg_k/2      (ONE inequality, not two)
    hverdict

instead of `hTrc` + `hdriftc` + `hdriftd`. -/

noncomputable def runParts_at_interior_appr
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ) (u' : ℚ)
    (hQ1 : ∀ k i, 1 ≤ Q k i i)
    (hQsym : ∀ k, (Q k)ᵀ = Q k)
    (htrcQ : ∀ k, ∑ i, Q k i i ≤ (G.n : ℚ))
    (hraw : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (Q k) u'
        (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hu : (1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
        * (u' + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2)
        ≤ (t - QMCLeafB.RundataCert.eps G) + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G)
        ((1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) • Q k)
        (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.UnionShallow.paramsKbc2 G).dq))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hcEq : ∀ k (hok : ok k = false),
      c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k (hok : ok k = false),
      cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
        (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k (hok : ok k = false), 1 ≤ lam k)
    (hlam2 : ∀ k (hok : ok k = false),
      |c k ⬝ᵥ witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne (c k) k|
        + |c k ⬝ᵥ witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne (c k) k|
        + 9 * marg k ^ 2 / (4 * ((QMCLeafB.UnionShallow.paramsKbc2 G).rmax) ^ 2) + 1
      ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (happr : ∀ k (hok : ok k = false),
      (fun i => ((cn k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat
                ((1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) • Q k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m)) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  have hdq0 : 0 < (QMCLeafB.UnionShallow.paramsKbc2 G).dq := by
    rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
    exact QMCLeafB.RundataParams.dqShallow_pos G
  have hdq4 : (QMCLeafB.UnionShallow.paramsKbc2 G).dq < 4 := by
    rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
    exact dqShallow_lt_four G
  have hdM : (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ≠ 0 := by
    intro hz
    have h0 : 0 < G.n := by omega
    have h1 := congrFun (congrFun hz ⟨0, h0⟩) ⟨0, h0⟩
    simp at h1
  refine runParts_of_dilated_appr o G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.UnionShallow.paramsKbc2_rmax_pos G hn)
    (QMCLeafB.UnionShallow.paramsKbc2_budget G hn hRq)
    ok marg (fun k => (1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) • Q k)
    (1 : Matrix (Fin G.n) (Fin G.n) ℚ) hdM lam c cn C hmarg ?_ ?_ hcEq ?_ hcne hlam0 ?_ happr
    hlam1 hlam2 hverdict
  · -- `hmem`: the ok-branch certificate at the boundary centre
    intro k hk hok
    exact QMCLeafB.AuditM1.relaxMem_boundary_smul (hraw k hk hok) hdq0 (le_of_lt hdq4)
      (hQ1 k) hu
  · -- `hCsym`
    intro k
    rw [Matrix.transpose_smul, hQsym k]
  · -- `hcn`
    intro k hok
    rw [hcn k hok]
  · -- `hbody`: the relaxed body lies above the lowerered centre in direction `1`
    intro k _hok X hX
    simpa using QMCLeafB.DriftExact.hbody_of_trace
      (hTrc := hTrc_boundary_of_trace hdq0 hdq4 (htrcQ k)) X hX


/-! ## D.  The collapse: the drift block is bought by the trace budget

At the pinch-lowered centre `v_k = Cat k − flat cX_k` has `dOne ⪝ v_k = diagSum (Cat k) − n(1 − dq/4)`,
i.e. the *trace budget residual*.  The point of this section is that once that budget is **strict**,
the whole drift block is no longer a residual at all: the multiplier `λ_k` is free above `hlam2`'s
lower bound and the centre approximation `cn_k ⪝ v_k ≤ marg_k/2` holds for every `λ_k` large enough,
because `dOne ⪝ v_k < 0`.  So the two drift inequalities collapse onto the single trace budget — the
one quantity the program already keeps. -/

/-- **Strict trace budget ⇒ every multiplier above a lower bound works.** -/
theorem exists_lam_of_trace_lt {n : ℕ} (v c : Fin (n * n) → ℝ) (m L : ℚ)
    (hstrict : dOne n ⬝ᵥ v < 0) :
    ∃ lam : ℚ, L ≤ lam ∧ c ⬝ᵥ v + ((lam : ℚ) : ℝ) * (dOne n ⬝ᵥ v) ≤ ((m : ℚ) : ℝ) / 2 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((((m : ℚ) : ℝ) / 2 - c ⬝ᵥ v) / (dOne n ⬝ᵥ v))
  have hkey : ((N : ℝ)) * (dOne n ⬝ᵥ v) ≤ (((m : ℚ) : ℝ) / 2 - c ⬝ᵥ v) := by
    have h := mul_le_mul_of_nonpos_right hN (le_of_lt hstrict)
    rwa [div_mul_cancel₀ _ (ne_of_lt hstrict)] at h
  refine ⟨max L (N : ℚ), le_max_left _ _, ?_⟩
  have hNr : ((N : ℚ) : ℝ) ≤ ((max L (N : ℚ) : ℚ) : ℝ) := by
    have h : (N : ℚ) ≤ max L (N : ℚ) := le_max_right _ _
    exact_mod_cast h
  have hmul : ((max L (N : ℚ) : ℚ) : ℝ) * (dOne n ⬝ᵥ v)
      ≤ ((N : ℚ) : ℝ) * (dOne n ⬝ᵥ v) :=
    mul_le_mul_of_nonpos_right hNr (le_of_lt hstrict)
  have hkey' : ((N : ℚ) : ℝ) * (dOne n ⬝ᵥ v) ≤ (((m : ℚ) : ℝ) / 2 - c ⬝ᵥ v) := by
    have hc : ((N : ℚ) : ℝ) = (N : ℝ) := by push_cast; ring
    rw [hc]
    exact hkey
  linarith [hmul, hkey']

/-- The same, in the shape of the single drift hypothesis: the dilated centre approximation at
`cn = c + λ • dOne` is bought by the strict trace budget. -/
theorem exists_lam_happr {n : ℕ} (v c : Fin (n * n) → ℝ) (m L : ℚ)
    (hstrict : dOne n ⬝ᵥ v < 0) :
    ∃ lam : ℚ, L ≤ lam
      ∧ (c + ((lam : ℚ) : ℝ) • dOne n) ⬝ᵥ v ≤ ((m : ℚ) : ℝ) / 2 := by
  obtain ⟨lam, hL, hle⟩ := exists_lam_of_trace_lt v c m L hstrict
  refine ⟨lam, hL, ?_⟩
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
  exact hle

/-- **The strict trace budget at the pinch-lowered centre**, i.e. the one inequality the drift block
collapses onto. -/
theorem hstrict_iff_trace {n : ℕ} {dq : ℚ} (Cat : Fin (n * n) → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℚ) :
    dOne n ⬝ᵥ (Cat - QMCLeafB.AnswerProducer.flat
        (QMCLeafB.SepOracle.castMat ((1 - dq / 4) • Q))) < 0
      ↔ diagSum Cat < ((1 - dq / 4 : ℚ) : ℝ) * (∑ i, ((Q i i : ℚ) : ℝ)) := by
  have hcast' : ((1 - dq / 4 : ℚ) : ℝ) = 1 - (dq : ℝ) / 4 := by
    push_cast
    ring
  rw [driftd_boundary_shift (1 - dq / 4) Q Cat, dOne_dot_sub_flat, hcast_dq, hcast']
  constructor <;> intro h <;> linarith

/-- At a unit-diagonal base stream the collapse reads `diagSum (Cat k) < n·(1 − dq/4)`. -/
theorem hstrict_iff_trace_unitDiag {n : ℕ} {dq : ℚ}
    (Cat : Fin (n * n) → ℝ) (Q : Matrix (Fin n) (Fin n) ℚ) (hunit : ∀ i, Q i i = 1) :
    dOne n ⬝ᵥ (Cat - QMCLeafB.AnswerProducer.flat
        (QMCLeafB.SepOracle.castMat ((1 - dq / 4) • Q))) < 0
      ↔ diagSum Cat < ((1 - dq / 4 : ℚ) : ℝ) * ((n : ℚ) : ℝ) := by
  rw [hstrict_iff_trace, sum_diag_cast_of_unitDiag Q hunit]

end QMCLeafB.TraceBudgetM8

/-! ## Axiom audit -/

#print axioms QMCLeafB.TraceBudgetM8.sum_diag_cast_of_unitDiag
#print axioms QMCLeafB.TraceBudgetM8.drift_linear_iff
#print axioms QMCLeafB.TraceBudgetM8.hdriftd_linear_iff
#print axioms QMCLeafB.TraceBudgetM8.hdriftc_linear_iff
#print axioms QMCLeafB.TraceBudgetM8.happr_of_drifts
#print axioms QMCLeafB.TraceBudgetM8.happr_linear_iff
#print axioms QMCLeafB.TraceBudgetM8.runParts_of_dilated_appr
#print axioms QMCLeafB.TraceBudgetM8.runParts_at_interior_appr
#print axioms QMCLeafB.TraceBudgetM8.exists_lam_of_trace_lt
#print axioms QMCLeafB.TraceBudgetM8.exists_lam_happr
#print axioms QMCLeafB.TraceBudgetM8.hstrict_iff_trace
#print axioms QMCLeafB.TraceBudgetM8.hstrict_iff_trace_unitDiag


