-- Prove2me | Definitions.Def_QMCLeafB_emptyC
-- name    : QMCLeafB_emptyC
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:52:23.622267+00:00
-- url     : https://prove2.me/theorems/001377ef-e773-4a50-900a-e71894567fb3
-- title:
--   QMCLeafB emptyC
-- statement:
--   # leaf B phase 22 — an empty body admits a ceiling-free window record (satisfiability, m3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_windowC
/-
# leaf B phase 22 — an empty body admits a ceiling-free window record (satisfiability, m3)

Direction 1 of the phase asks whether **any** legal stream at a refuted point (empty relaxed body)
satisfies the two drift budgets.  With the trace ceiling in place (`BundleHWin.hTrc`) the answer is
NO: m8's `Check_cutbudget_m8` refutes `diagSum (Cat k) ≤ n(1 − dq/4)`, and the campaign's centre
family sits exactly on the ceiling (`CeilingM3.ceiling_attained_cXst`).  With the ceiling replaced by
`hbody` (`WindowC.BundleC`), the answer is YES, and this file constructs it:

    cX k  :=  M k • 1        (M k rational, chosen per round)
    ok    :=  false
    C k   :=  the cut record with the prescribed normal and margin (legal: the body is empty)

**No knowledge of the engine's iterate is needed.**  The two budgets become linear in `M k`:

    hdriftd  ⟺  diagSum (Cat k) − n·M k ≤ 0
    hdriftc  ⟺  c k ⪝ Cat k − ↑(marg k)/2 ≤ M k · (dOne ⪝ c k)

and `M k` is chosen above both thresholds (`exists_rat_gt`), which is possible exactly because the
normal has **strictly positive trace** (`dOne ⪝ c k > 0`).  Nothing bounds `diagSum (Cat k)`: the
stream may accumulate as m8's drill does, and the centre simply follows it upward.

What is left over is the depth ledger (`hlam2`) and the `λ`-bounds — the campaign's own
`RecordM2.lamInd` obligation, not a trace condition.

House discipline: `set_option autoImplicit false`; `#print axioms` after every declaration; no
`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`; no `⊊`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.EmptyC

open QuantumMaxCutEnergy
open QMCLeafB.RunPartsStream (dOne)

/-! ## 1.  Three pieces of flattening algebra -/

/-- `flat` commutes with scalar multiples. -/
theorem flat_smul {n : ℕ} (c : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.AnswerProducer.flat (c • X) = c • QMCLeafB.AnswerProducer.flat X := by
  funext k
  simp [QMCLeafB.AnswerProducer.flat, Matrix.smul_apply]

#print axioms QMCLeafB.EmptyC.flat_smul

/-- A rational multiple of the identity casts to the real multiple of the identity. -/
theorem castMat_smul_one {n : ℕ} (M : ℚ) :
    QMCLeafB.SepOracle.castMat (M • (1 : Matrix (Fin n) (Fin n) ℚ))
      = (M : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  rw [QMCLeafB.SepOracle.castMat_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

#print axioms QMCLeafB.EmptyC.castMat_smul_one

/-- The flattened identity is the diagonal read-out vector. -/
theorem flat_one_eq_dOne (n : ℕ) :
    QMCLeafB.AnswerProducer.flat (1 : Matrix (Fin n) (Fin n) ℝ) = dOne n := by
  funext k
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨i, j⟩ := p
  rw [QMCLeafB.AnswerProducer.flat, Equiv.symm_apply_apply, Matrix.one_apply,
    QMCLeafB.DriftExact.dOne_apply]

#print axioms QMCLeafB.EmptyC.flat_one_eq_dOne

/-! ## 2.  The flattened normal of a cut record -/

/-- The matrix whose row-major flattening is `v`. -/
def nrmOf {n : ℕ} (v : Fin (n * n) → ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => v (finProdFinEquiv (i, j))

/-- The flattening of `nrmOf v` is `v`. -/
theorem flatQ_nrmOf {n : ℕ} (v : Fin (n * n) → ℚ) :
    QMCLeafB.RelaxOracle.flatQ (nrmOf v) = v := by
  funext k
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨i, j⟩ := p
  simp [QMCLeafB.RelaxOracle.flatQ, nrmOf]

#print axioms QMCLeafB.EmptyC.flatQ_nrmOf

/-! ## 3.  The construction

At an empty body, with the multiplier stream and the depth ledger supplied, a rational centre stream
above the engine's own iterate makes both budgets hold. -/

/-- **An empty body admits a ceiling-free window record.**  Hypotheses: the body is empty (so no cut
record carries content), the margins are positive, the normals have strictly positive trace, and the
`λ`-stream satisfies its bounds and the depth ledger.  No trace ceiling anywhere. -/
noncomputable def bundleC_of_emptyBody
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (lam : ℕ → ℚ)
    (cn : ℕ → Fin (G.n * G.n) → ℚ)
    (hcne : ∀ k, cn k ≠ 0)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (htrpos : ∀ k, 0 < dOne G.n ⬝ᵥ (fun i => ((c k i : ℚ) : ℝ)))
    (hmargpos : ∀ k, 0 < marg k)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, k < P.K * P.m → 1 ≤ lam k)
    (hlam2 : ∀ k, k < P.K * P.m →
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
    (hverdict : o G t = false) :
    QMCLeafB.WindowC.BundleC o G t P hn := by
  classical
  -- the engine's iterate at the recorded stream
  set CD := QMCLeafB.RunPartsDilate.runCut G P hn cn hcne with hCD
  -- the normal's trace along the identity direction
  set del : ℕ → ℝ := fun k => dOne G.n ⬝ᵥ (fun i => ((c k i : ℚ) : ℝ)) with hdel
  have hdelpos : ∀ k, 0 < del k := htrpos
  -- per-round rational heights above both budget thresholds
  have hex : ∀ k : ℕ, ∃ M : ℚ,
      QMCLeafB.DriftExact.diagSum
          (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) CD k)
          ≤ (G.n : ℝ) * (M : ℝ)
        ∧ (fun i => ((c k i : ℚ) : ℝ))
            ⬝ᵥ QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) CD k
            - ((marg k : ℚ) : ℝ) / 2
          ≤ (M : ℝ) * del k := by
    intro k
    have hnpos : (0 : ℝ) < (G.n : ℝ) := by
      have h2 : 0 < G.n := by omega
      exact_mod_cast h2
    set A : ℝ := QMCLeafB.DriftExact.diagSum
      (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) CD k) with hA
    set B : ℝ := (fun i => ((c k i : ℚ) : ℝ))
        ⬝ᵥ QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) CD k
        - ((marg k : ℚ) : ℝ) / 2 with hB
    obtain ⟨M, hM⟩ := exists_rat_gt (max (A / (G.n : ℝ)) (B / del k))
    refine ⟨M, ?_, ?_⟩
    · have h1 : A / (G.n : ℝ) < ((M : ℚ) : ℝ) := lt_of_le_of_lt (le_max_left _ _) hM
      have h2 : (A / (G.n : ℝ)) * (G.n : ℝ) < ((M : ℚ) : ℝ) * (G.n : ℝ) :=
        mul_lt_mul_of_pos_right h1 hnpos
      rw [div_mul_cancel₀ A (ne_of_gt hnpos)] at h2
      linarith
    · have h1 : B / del k < ((M : ℚ) : ℝ) := lt_of_le_of_lt (le_max_right _ _) hM
      have h2 : (B / del k) * del k < ((M : ℚ) : ℝ) * del k :=
        mul_lt_mul_of_pos_right h1 (hdelpos k)
      rw [div_mul_cancel₀ B (ne_of_gt (hdelpos k))] at h2
      linarith
  -- the chosen heights
  set HH : ℕ → ℚ := fun k => Classical.choose (hex k) with hHH
  have hHH_trace : ∀ k, QMCLeafB.DriftExact.diagSum
      (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) CD k)
      ≤ (G.n : ℝ) * ((HH k : ℚ) : ℝ) := fun k => (Classical.choose_spec (hex k)).1
  have hHH_drift : ∀ k, (fun i => ((c k i : ℚ) : ℝ))
      ⬝ᵥ QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) CD k
      - ((marg k : ℚ) : ℝ) / 2 ≤ ((HH k : ℚ) : ℝ) * del k :=
    fun k => (Classical.choose_spec (hex k)).2
  -- the flattening of the rational centre
  have hflat : ∀ k, QMCLeafB.AnswerProducer.flat
      (QMCLeafB.SepOracle.castMat (HH k • (1 : Matrix (Fin G.n) (Fin G.n) ℚ)))
      = ((HH k : ℚ) : ℝ) • dOne G.n := by
    intro k
    rw [castMat_smul_one, flat_smul, flat_one_eq_dOne]
  refine
    { ok := fun _ => false
      marg := marg
      cX := fun k => HH k • (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
      lam := lam
      c := c
      cn := cn
      C := ?_
      hmarg := ?_
      hmem := ?_
      hCsym := ?_
      hcEq := ?_
      hcn := hcn
      hcne := hcne
      hlam0 := hlam0
      hlam1 := ?_
      hlam2 := ?_
      hbody := ?_
      hdriftc := ?_
      hdriftd := ?_
      hverdict := ?_ }
  · -- the cut records: legal at an empty body
    intro k _hk _hok
    exact ⟨nrmOf (c k), marg k, hmargpos k, fun X hX => absurd hX (hempty X)⟩
  · -- their margins
    intro k _hk _hok
    rfl
  · -- no member rounds
    intro k _hk htrue
    exact absurd htrue (by simp)
  · -- the centre is symmetric
    intro k
    rw [Matrix.transpose_smul, Matrix.transpose_one]
  · -- the recorded normal is the oracle's
    intro k _hk _hok
    exact (flatQ_nrmOf (c k)).symm
  · -- the dilation parameter
    intro k hk _hok
    exact hlam1 k hk
  · -- the depth ledger
    intro k hk _hok
    exact hlam2 k hk
  · -- `hbody` is vacuous
    intro k _hk _hok X hX
    exact absurd hX (hempty X)
  · -- the cut direction's budget: the centre sits above it
    intro k _hk _hok
    have hkey : (fun i => ((c k i : ℚ) : ℝ))
        ⬝ᵥ QMCLeafB.AnswerProducer.flat
          (QMCLeafB.SepOracle.castMat (HH k • (1 : Matrix (Fin G.n) (Fin G.n) ℚ)))
        = ((HH k : ℚ) : ℝ) * del k := by
      rw [hflat, dotProduct_smul,
        dotProduct_comm (fun i => ((c k i : ℚ) : ℝ)) (dOne G.n), smul_eq_mul]
    rw [dotProduct_sub, hkey]
    have := hHH_drift k
    linarith
  · -- the trace direction's budget: the centre's trace dominates the engine's
    intro k _hk _hok
    have hsm : QMCLeafB.RunPartsStream.dOne G.n ⬝ᵥ QMCLeafB.AnswerProducer.flat
        (QMCLeafB.SepOracle.castMat (HH k • (1 : Matrix (Fin G.n) (Fin G.n) ℚ)))
        = (G.n : ℝ) * ((HH k : ℚ) : ℝ) := by
      rw [QMCLeafB.DriftExact.dOne_dot_flat_castMat]
      have hterm : ∀ i : Fin G.n,
          (((HH k • (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i i : ℚ) : ℝ) = ((HH k : ℚ) : ℝ) := by
        intro i
        simp [Matrix.smul_apply]
      rw [Finset.sum_congr rfl (fun i _ => hterm i)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [dotProduct_sub, hsm, QMCLeafB.DriftExact.dOne_dot]
    have := hHH_trace k
    linarith
  · -- the verdict bit
    rw [hverdict, QMCLeafB.ResidB_M7.anyOk_false_fun]

#print axioms QMCLeafB.EmptyC.bundleC_of_emptyBody

/-! ## 4.  The consequence for the residual: `RunParts` at an empty body without any trace condition -/

/-- **`RunParts` at a refuted point with an empty relaxed body**, from the depth ledger and positivity
alone.  This is the exact content direction 1 asked for: the ceiling is gone, and what remains is the
campaign's own `λ`-ledger. -/
noncomputable def runParts_of_emptyBody
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (lam : ℕ → ℚ)
    (cn : ℕ → Fin (G.n * G.n) → ℚ)
    (hcne : ∀ k, cn k ≠ 0)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (htrpos : ∀ k, 0 < dOne G.n ⬝ᵥ (fun i => ((c k i : ℚ) : ℝ)))
    (hmargpos : ∀ k, 0 < marg k)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, k < P.K * P.m → 1 ≤ lam k)
    (hlam2 : ∀ k, k < P.K * P.m →
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
    (hverdict : o G t = false) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  QMCLeafB.WindowC.runParts_of_bundleC o G t P hn hrmaxPos hrmax1 hbudP
    (bundleC_of_emptyBody o G t P hn c marg lam cn hcne hcn htrpos hmargpos hlam0 hlam1 hlam2
      hempty hverdict)

#print axioms QMCLeafB.EmptyC.runParts_of_emptyBody

/-! ## 5.  Discharging the multiplier ledger: the empty-body case is unconditional

`RecordM2.lamInd`/`RecordM2.cnInd` construct the multiplier stream and the dilated normals at any
supplied normal/margin pair, with `hlam0`/`hlam1`/`hlam2` proved (`lamInd_nonneg`, `lamInd_ge_one`,
`lamInd_spec`).  With the identity normal `u0 = flatQ 1` (margin `1`) both positivity hypotheses of §4
hold outright, so **at an empty relaxed body `RunParts` needs nothing but the empty body and the
verdict bit**. -/

/-- The identity normal has strictly positive trace. -/
theorem dOne_dot_u0_pos (G : QuantumMaxCutEnergy.Input) (hn : 0 < G.n) :
    0 < dOne G.n ⬝ᵥ (fun i => ((QMCLeafB.RecordM2.u0 G.n i : ℚ) : ℝ)) := by
  have hcast : (fun i => ((QMCLeafB.RecordM2.u0 G.n i : ℚ) : ℝ))
      = QMCLeafB.AnswerProducer.flat
          (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) := by
    funext e
    rfl
  rw [hcast, QMCLeafB.DriftExact.dOne_dot_flat_castMat]
  have hterm : ∀ i : Fin G.n,
      (((1 : Matrix (Fin G.n) (Fin G.n) ℚ) i i : ℚ) : ℝ) = 1 := by
    intro i
    simp
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (G.n : ℝ) := by exact_mod_cast hn
  nlinarith

#print axioms QMCLeafB.EmptyC.dOne_dot_u0_pos

/-- **The empty-body residual, unconditional**: at a refuted interior point whose relaxed body is
empty, `RunParts` at the given parameters needs nothing but the empty body and the verdict bit.  The
normal stream is the identity normal `u0`, the margins are `1`, and the multiplier is the shelf's
`RecordM2.lamInd`, whose depth ledger is `lamInd_spec`. -/
noncomputable def runParts_of_emptyBody_uncond
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (hempty : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G))
        (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ) ((P.dq : ℚ) : ℝ) X)
    (hverdict : o G t = false) :
    QMCLeafB.FinalStroke.RunParts o G t P := by
  refine runParts_of_emptyBody o G t P hn hrmaxPos hrmax1 hbudP
    (fun _ => QMCLeafB.RecordM2.u0 G.n) (fun _ => 1)
    (QMCLeafB.EndgameM2.gLam G P hn (fun _ => QMCLeafB.RecordM2.u0 G.n) (fun _ => 1))
    (QMCLeafB.EndgameM2.gCn G P hn (fun _ => QMCLeafB.RecordM2.u0 G.n) (fun _ => 1))
    (QMCLeafB.EndgameM2.gCn_ne G P hn (fun _ => QMCLeafB.RecordM2.u0 G.n) (fun _ => 1))
    (fun _ => rfl)
    (fun _ => dOne_dot_u0_pos G (by omega))
    (fun _ => one_pos)
    (fun k => QMCLeafB.RecordM2.lamInd_nonneg (QMCLeafB.RunPartsDilate.A0P G P)
      (QMCLeafB.RecordM2.u0 G.n) (QMCLeafB.RecordM2.d0idx G.n (by omega))
      (fun _ => QMCLeafB.RecordM2.u0 G.n) (fun _ => 1) P.rmax k)
    (fun k _ => QMCLeafB.RecordM2.lamInd_ge_one (QMCLeafB.RunPartsDilate.A0P G P)
      (QMCLeafB.RecordM2.u0 G.n) (QMCLeafB.RecordM2.d0idx G.n (by omega))
      (fun _ => QMCLeafB.RecordM2.u0 G.n) (fun _ => 1) P.rmax k)
    (fun k _ => QMCLeafB.RecordM2.lamInd_spec G P hn (QMCLeafB.RecordM2.u0 G.n)
      (QMCLeafB.RecordM2.d0idx G.n (by omega)) (QMCLeafB.RecordM2.u0_d0idx G.n (by omega))
      (fun _ => QMCLeafB.RecordM2.u0 G.n) (fun _ => 1) hrmaxPos k)
    hempty hverdict

#print axioms QMCLeafB.EmptyC.runParts_of_emptyBody_uncond

/-- **The campaign's `hd` slot at an empty-body interior point** — the program bit and the parameter
family of `AssemblyM5.HdProp`, with the halving side conditions discharged from the shelf. -/
noncomputable def hd_at_emptyBody
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hempty : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G))
        (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ)
        (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X)
    (hverdict : o G t = false) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  obtain ⟨hrp, hr1, hbud⟩ :=
    QMCLeafB.WindowC.paramsKbc2_sides G hn
      (QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi)
  exact runParts_of_emptyBody_uncond o G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn hrp hr1 hbud
    hempty hverdict

#print axioms QMCLeafB.EmptyC.hd_at_emptyBody

end QMCLeafB.EmptyC


