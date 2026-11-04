-- Prove2me | Definitions.Def_QMCLeafB_centreCore
-- name    : QMCLeafB_centreCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:22:41.857055+00:00
-- url     : https://prove2.me/theorems/79df80f1-d0c9-4977-8d9a-5f3d8bea9307
-- title:
--   QMCLeafB centreCore
-- statement:
--   # centre core — the WORKING sections of `Check_centre_closure_m4` (which fails to compile in its tail;
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_runparts_stream_m4
/-
# centre core — the WORKING sections of `Check_centre_closure_m4` (which fails to compile in its tail;
  extracted 2026-11-04 verbatim up to §7 so downstream modules have a compilable home for the
  centre-shift algebra: `flat_castMat_smul`, `centre_shift`, `centre_shift_dot_le`,
  `dOne_dot_flat_eq_trace`, `relaxMem_scaled_false` and the trace/surrogate producers.
  The tail's three failing precision declarations are re-proved soundly in `Check_direct_m7`
  §6 (`exists_dyadic_small`, `exists_uniform_precision`, `exists_grid_budget`).
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.CentreClosure

open QuantumMaxCutEnergy

/-! ## 1.  `hbody` at the identity direction is a *trace* condition -/

/-- **The rational trace inequality transports to `ℝ`.** -/
theorem trace_cast_le {n : ℕ} {δ : ℚ} {Q : Matrix (Fin n) (Fin n) ℚ}
    (h : ∑ i, Q i i ≤ (n : ℚ) * (1 - δ / 4)) :
    ∑ i, ((Q i i : ℚ) : ℝ) ≤ (n : ℝ) * (1 - (δ : ℝ) / 4) := by
  have h' : ((∑ i, Q i i : ℚ) : ℝ) ≤ (((n : ℚ) * (1 - δ / 4) : ℚ) : ℝ) := by exact_mod_cast h
  have h1 : ((∑ i, Q i i : ℚ) : ℝ) = ∑ i, ((Q i i : ℚ) : ℝ) := by push_cast; rfl
  rw [h1] at h'
  push_cast at h'
  linarith [h']

/-- **`hbody` at the identity direction, from the centre's *trace*.**  The relaxed body's diagonal
clause `|Xᵢᵢ − 1| ≤ δ/4` forces `tr X ≥ n(1 − δ/4)`; so a centre whose trace is at most that is
below every body point in the identity direction.  This is strictly weaker than the entrywise
condition `∀ i, Qᵢᵢ ≤ 1 − δ/4` that `hbody_of_diag` asks for, and is the exact form `hbody` takes
at `dM = 1`. -/
theorem hbody_of_trace {n : ℕ} {δ : ℝ} {Q : Matrix (Fin n) (Fin n) ℚ}
    (htr : ∑ i, ((Q i i : ℚ) : ℝ) ≤ (n : ℝ) * (1 - δ / 4))
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : ∀ i, |X i i - 1| ≤ δ / 4) :
    -(0 : ℝ) ≤ QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ))
      (X - QMCLeafB.SepOracle.castMat Q) := by
  have h1 : ∀ i, (1 : ℝ) - δ / 4 ≤ X i i := fun i => by
    linarith [(abs_le.mp (hX i)).1]
  have hXtr : (n : ℝ) * (1 - δ / 4) ≤ ∑ i, X i i := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i)
    rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hQtr : (∑ i, ((Q i i : ℚ) : ℝ)) = ∑ i, (QMCLeafB.SepOracle.castMat Q) i i := rfl
  rw [show -(0 : ℝ) = 0 by ring, QMCLeafB.RunPartsStream.castMat_one,
    QMCLeafB.SepOracle.frob_sub, QMCLeafB.RunPartsStream.frob_one_eq_trace,
    QMCLeafB.RunPartsStream.frob_one_eq_trace]
  linarith [hQtr ▸ htr, hXtr]

/-- The same on the campaign's relaxed-body predicate. -/
theorem hbody_of_trace_body {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ}
    {Q : Matrix (Fin n) (Fin n) ℚ}
    (htr : ∑ i, ((Q i i : ℚ) : ℝ) ≤ (n : ℝ) * (1 - δ / 4))
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : QMCLeafB.BallFloor.relaxBodyLE A u δ X) :
    -(0 : ℝ) ≤ QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ))
      (X - QMCLeafB.SepOracle.castMat Q) :=
  hbody_of_trace htr hX.2.1

/-- **The entrywise condition implies the trace condition** — so `hTrc` really is the weaker
hypothesis: nothing that satisfied `hdiagc` is lost. -/
theorem trace_le_of_diag {n : ℕ} {δ : ℚ} {Q : Matrix (Fin n) (Fin n) ℚ}
    (hdiag : ∀ i, Q i i ≤ 1 - δ / 4) :
    ∑ i, Q i i ≤ (n : ℚ) * (1 - δ / 4) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hdiag i)
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h

#print axioms QMCLeafB.CentreClosure.trace_cast_le
#print axioms QMCLeafB.CentreClosure.hbody_of_trace
#print axioms QMCLeafB.CentreClosure.hbody_of_trace_body
#print axioms QMCLeafB.CentreClosure.trace_le_of_diag

/-! ## 2.  The alternative repair (f64): query at `(1 − dq/2)·X`, and its exact cost -/

/-- Row-major flattening commutes with rational scaling. -/
theorem flatQ_smul {n : ℕ} (a : ℚ) (X : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.RelaxOracle.flatQ (a • X) = a • QMCLeafB.RelaxOracle.flatQ X := by
  funext k
  simp [QMCLeafB.RelaxOracle.flatQ, Matrix.smul_apply, smul_eq_mul]

/-- The rational-to-real cast commutes with scaling. -/
theorem castMat_smul {n : ℕ} (a : ℚ) (X : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.castMat (a • X)
      = (a : ℝ) • QMCLeafB.SepOracle.castMat X := by
  ext i j
  simp [QMCLeafB.SepOracle.castMat, Matrix.smul_apply, smul_eq_mul]

/-- The real flattening commutes with scaling. -/
theorem flat_smul {n : ℕ} (a : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.AnswerProducer.flat (a • X) = a • QMCLeafB.AnswerProducer.flat X := by
  funext k
  simp [QMCLeafB.AnswerProducer.flat, Matrix.smul_apply, smul_eq_mul]

/-- **The scaled centre's flat code is the scaled flat code.** -/
theorem flat_castMat_smul {n : ℕ} (a : ℚ) (X : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (a • X))
      = (a : ℝ) • QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat X) := by
  rw [castMat_smul, flat_smul]

/-- **The centre switch is an exact shift at the flat level.** -/
theorem centre_shift {n : ℕ} (a : ℚ) (X : Matrix (Fin n) (Fin n) ℚ)
    (q : Fin (n * n) → ℝ) :
    q - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (a • X))
      = (q - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat X))
        + (1 - (a : ℝ)) • QMCLeafB.AnswerProducer.flat
            (QMCLeafB.SepOracle.castMat X) := by
  rw [flat_castMat_smul]
  module

/-- **`hstatec`/`hstated` at the scaled centre, with its exact cost.**  Pairing the shift with any
direction `u` charges `|1 − a|·|u ⪝ flat (castMat X)|`; at `a = 1 − dq/2` that is
`(dq/2)·|u ⪝ flat (castMat X)|`, the f64 cost. -/
theorem centre_shift_dot_le {n : ℕ} (a : ℚ) (X : Matrix (Fin n) (Fin n) ℚ)
    (q u : Fin (n * n) → ℝ) (δ : ℝ) (ha : |1 - (a : ℝ)| ≤ δ) :
    u ⬝ᵥ (q - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (a • X)))
      ≤ u ⬝ᵥ (q - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat X))
        + δ * |u ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat X)| := by
  rw [centre_shift, dotProduct_add]
  have hsm : u ⬝ᵥ ((1 - (a : ℝ)) • QMCLeafB.AnswerProducer.flat
      (QMCLeafB.SepOracle.castMat X))
      = (1 - (a : ℝ)) * (u ⬝ᵥ QMCLeafB.AnswerProducer.flat
          (QMCLeafB.SepOracle.castMat X)) := by
    rw [dotProduct_smul, smul_eq_mul]
  rw [hsm]
  have h2 : (1 - (a : ℝ)) * (u ⬝ᵥ QMCLeafB.AnswerProducer.flat
      (QMCLeafB.SepOracle.castMat X))
      ≤ δ * |u ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat X)| := by
    have hle : (1 - (a : ℝ)) * (u ⬝ᵥ QMCLeafB.AnswerProducer.flat
          (QMCLeafB.SepOracle.castMat X))
        ≤ |1 - (a : ℝ)| * |u ⬝ᵥ QMCLeafB.AnswerProducer.flat
            (QMCLeafB.SepOracle.castMat X)| := by
      rw [← abs_mul]
      exact le_abs_self _
    exact le_trans hle (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
  linarith [h2]

/-- **The scaled centre's diagonal is below the body, from an upper band on the raw state.**  If
`Xᵢᵢ ≤ 1 + dq/4` (the upper half of the body's diagonal clause) and `0 ≤ dq ≤ 2`, then the scaled
centre `(1 − dq/2)·X` has `(1 − dq/2)Xᵢᵢ ≤ 1 − dq/4` — the `hdiagc` slot, with no run invariant
needed beyond the band's *upper* side (which holds at `init0`, where `hdiagc` itself does not). -/
theorem diag_scaled_le {n : ℕ} {δ : ℚ} (h0 : 0 ≤ δ) (h2 : δ ≤ 2)
    {X : Matrix (Fin n) (Fin n) ℚ} (i : Fin n) (hi : X i i ≤ 1 + δ / 4) :
    ((1 - δ / 2) • X) i i ≤ 1 - δ / 4 := by
  have ha : (0 : ℚ) ≤ 1 - δ / 2 := by linarith
  have hX : (1 - δ / 2) * X i i ≤ (1 - δ / 2) * (1 + δ / 4) :=
    mul_le_mul_of_nonneg_left hi ha
  have hexp : (1 - δ / 2) * (1 + δ / 4) ≤ 1 - δ / 4 := by nlinarith [sq_nonneg δ]
  rw [Matrix.smul_apply, smul_eq_mul]
  linarith [hX, hexp]

/-- The identity direction is the flat code of the real identity matrix. -/
theorem dOne_eq_flat_one (n : ℕ) :
    QMCLeafB.RunPartsStream.dOne n
      = QMCLeafB.AnswerProducer.flat (1 : Matrix (Fin n) (Fin n) ℝ) := by
  funext k
  have h1 : (((1 : Matrix (Fin n) (Fin n) ℚ) (finProdFinEquiv.symm k).1
        (finProdFinEquiv.symm k).2 : ℚ) : ℝ)
      = (1 : Matrix (Fin n) (Fin n) ℝ) (finProdFinEquiv.symm k).1
        (finProdFinEquiv.symm k).2 := by
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases h : k.divNat = k.modNat <;> simp [h]
  simpa [QMCLeafB.RunPartsStream.dOne, QMCLeafB.RelaxOracle.flatQ,
    QMCLeafB.AnswerProducer.flat] using h1

/-- **The identity direction's pairing against a state is its trace.**  This puts the f64 cost of
the centre switch into the program's own arithmetic: at `a = 1 − dq/2` the `hstated` charge is
`(dq/2)·|tr X_k|`. -/
theorem dOne_dot_flat_eq_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.RunPartsStream.dOne n
        ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat X)
      = ∑ i, ((X i i : ℚ) : ℝ) := by
  rw [dOne_eq_flat_one, dotProduct, ← QMCLeafB.RelaxOracle.frob_eq_flat_dot,
    QMCLeafB.RunPartsStream.frob_one_eq_trace]
  rfl

#print axioms QMCLeafB.CentreClosure.flatQ_smul
#print axioms QMCLeafB.CentreClosure.castMat_smul
#print axioms QMCLeafB.CentreClosure.flat_smul
#print axioms QMCLeafB.CentreClosure.flat_castMat_smul
#print axioms QMCLeafB.CentreClosure.centre_shift
#print axioms QMCLeafB.CentreClosure.centre_shift_dot_le
#print axioms QMCLeafB.CentreClosure.diag_scaled_le
#print axioms QMCLeafB.CentreClosure.dOne_eq_flat_one
#print axioms QMCLeafB.CentreClosure.dOne_dot_flat_eq_trace

/-! ## 3.  The stream assembly with the trace condition (`hdiagc` → `hTrc`) -/

/-- **`RunParts` at `runParamsShallow` from the program's stream data, with `hbody` bought by a
trace.**  Identical to `QMCLeafB.RunPartsStream.runParts_of_stream_data` except that the entrywise
centre condition `hdiagc` is replaced by the strictly weaker single rational inequality

    hTrc : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ)·(1 − P.dq/4).

Every other hypothesis is verbatim. -/
noncomputable def runParts_of_stream_data_trace
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (mu delta : ℕ → ℝ) (dvec : Fin (G.n * G.n) → ℝ)
    (hdvec : dvec = fun i =>
      ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) i : ℚ) : ℝ))
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
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
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
    (qSurr : ℕ → Fin (G.n * G.n) → ℝ)
    (hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k, mu j •
          QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G (P)
              hn cn hcne) j)
    (hmu_up : ∀ j, QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne)
      j ≤ mu j)
    (hmu_lo : ∀ j, mu j - delta j ≤ QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne)
      j)
    (hlam3 : ∀ j,
      |(fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (P) hn cn hcne (c j) j i : ℚ) : ℝ))|
        ≤ ((lam j : ℚ) : ℝ) * ((fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (P) hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ))))
    (hstatec : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        + ∑ j ∈ Finset.range k, delta j * max 0
            (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j))
          ≤ ((marg k : ℚ) : ℝ) / 2)
    (hstated : ∀ k, ok k = false →
      dvec ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((P).K
        * (P).m)) :
    QMCLeafB.FinalStroke.RunParts o G t
      (P) := by
  have hpos : ∀ j, 0 ≤ dvec ⬝ᵥ QMCLeafB.EngineIterates.cutPR
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j := by
    intro j
    have h := QMCLeafB.RunPartsStream.dir_pairing_nonneg G (P) hn cn hcne j
      (c j) (lam j) (hlam0 j) (hlam3 j)
    have heq : QMCLeafB.EngineIterates.cutPR
        (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j
        = (fun i => ((QMCLeafB.RunPartsDilate.witAt G
            (P) hn cn hcne
            (c j + lam j • QMCLeafB.RelaxOracle.flatQ
              (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ)) := by
      funext i
      show ((QMCLeafB.RunPartsShallow.witOf
          (QMCLeafB.RunPartsDilate.runShape_posQ G
            (P) hn cn hcne j) (cn j)) i : ℝ) = _
      rw [hcn j]
      rfl
    rw [hdvec, heq]
    exact h
  refine QMCLeafB.RunPartsDilate.runParts_of_dilated o G t P hn hrmaxPos hbudP ok marg cX
    (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ?_ lam c cn C hmarg hmem hCsym hcEq (fun k _ => hcn k)
    hcne hlam0 ?_ ?_ ?_ hlam1 hlam2 hverdict
  · -- the identity matrix is not zero at `1 ≤ n`
    intro hzero
    have hidx : 0 < G.n := by omega
    have h1 := congrFun (congrFun hzero ⟨0, hidx⟩) ⟨0, hidx⟩
    simp at h1
  · -- `hbody` from the centre's **trace** (this is the only change against `runParts_of_stream_data`)
    intro k hok X hX
    simpa using hbody_of_trace_body (trace_cast_le (hTrc k)) X hX
  · -- `hdriftc`: the surrogate's budget plus the state's mismatch
    intro k hok
    have hsplit : QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
        = (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k - qSurr k)
          + (qSurr k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) := by
      abel
    rw [hsplit, dotProduct_add]
    have hb := QMCLeafB.RunPartsStream.drift_bound_upper (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne)
      (fun i => ((c k i : ℚ) : ℝ)) k mu delta (fun j _ => hmu_lo j)
      (fun j _ => hmu_up j)
    rw [← hqSurr k] at hb
    linarith [hb, hstatec k hok]
  · -- `hdriftd`: the direction's sign, plus the state's mismatch
    intro k hok
    rw [← hdvec]
    have hsplit : QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
        = (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k - qSurr k)
          + (qSurr k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) := by
      abel
    rw [hsplit, dotProduct_add]
    have hb := QMCLeafB.RunPartsStream.drift_nonpos_of_upper (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne)
      dvec k (qSurr k) mu (hqSurr k) (fun j _ => hmu_up j) (fun j _ => hpos j)
    linarith [hb, hstated k hok]

#print axioms QMCLeafB.CentreClosure.runParts_of_stream_data_trace

/-! ## 4.  The dyadic endpoint: a drop-in for `runParts_shallow_dyadic` -/

/-- **`RunParts` at `runParamsShallow` from the concrete dyadic stream data, with `hbody` bought by
the centre's trace.**  This is `QMCLeafB.RunPartsStream.runParts_shallow_dyadic` with

    hdiagc : ∀ k i, (cX k) i i ≤ 1 − P.dq/4        (n entrywise rational inequalities per round)

replaced by

    hTrc   : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ)·(1 − P.dq/4)     (one, strictly weaker),

and every other hypothesis verbatim (`trace_le_of_diag` shows nothing is lost).  The surrogate and
the width are the program's own dyadic data (`muUp`, `deltaUp`), the direction is the flat identity
`dOne`, and the bracket hypotheses of §3 are discharged from `CentreTrack.lam_bracket`. -/
noncomputable def runParts_shallow_trace
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
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
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
    (grid : ℕ → ℕ)
    (hgrid1 : ∀ j, 1 ≤ QMCLeafB.EngineIterates.sigmaQ
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne j).c
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne j).p
      * 4 ^ (grid j))
    (hTrc : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 - P.dq / 4))
    (qSurr : ℕ → Fin (G.n * G.n) → ℝ)
    (hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k,
          QMCLeafB.RunPartsStream.muUp (G.n * G.n)
            (QMCLeafB.RunPartsDilate.runCut G (P)
              hn cn hcne) grid j •
          QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G (P)
              hn cn hcne) j)
    (hlam3 : ∀ j,
      |(fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (P) hn cn hcne (c j) j i : ℚ) : ℝ))|
        ≤ ((lam j : ℚ) : ℝ) * ((fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (P) hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ))))
    (hstatec : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        + ∑ j ∈ Finset.range k,
            QMCLeafB.RunPartsStream.deltaUp (G.n * G.n)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) grid j
            * max 0
              (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
                (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j))
          ≤ ((marg k : ℚ) : ℝ) / 2)
    (hstated : ∀ k, ok k = false →
      QMCLeafB.RunPartsStream.dOne G.n ⬝ᵥ
        (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((P).K
        * (P).m)) :
    QMCLeafB.FinalStroke.RunParts o G t
      (P) := by
  have hN2 : 2 ≤ G.n * G.n := by
    have h := Nat.mul_le_mul hn hn
    omega
  have hρ1 : ∀ j, (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne j).rho ≤ 1 := by
    intro j
    rw [QMCLeafB.RunPartsDilate.runCut_rho]
    exact hrmax1
  have hρ0 : ∀ j, (0 : ℚ) ≤ (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne j).rho := by
    intro j
    rw [QMCLeafB.RunPartsDilate.runCut_rho]
    exact P.hrmax
  have hσ : ∀ j, 0 < QMCLeafB.EngineIterates.sigmaQ
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne j).c
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne j).p :=
    QMCLeafB.RunPartsShallow.sigmaQ_pos_of_wit hN2
      (QMCLeafB.RunPartsDilate.A0P_posDef G (P))
      (QMCLeafB.RunPartsDilate.runCut_wit G
        (P) hn cn hcne)
      hρ0 hcne
  refine runParts_of_stream_data_trace o G t P hn hrmaxPos hrmax1 hbudP ok marg cX lam c cn
    (QMCLeafB.RunPartsStream.muUp (G.n * G.n) _ grid)
    (QMCLeafB.RunPartsStream.deltaUp (G.n * G.n) _ grid)
    (QMCLeafB.RunPartsStream.dOne G.n) rfl
    C hmarg hmem hCsym hcEq hcn hcne hlam0 hlam1 hlam2 hTrc qSurr hqSurr ?_ ?_ hlam3 hstatec
    hstated hverdict
  · intro j
    exact QMCLeafB.RunPartsStream.upper_bracket (G.n * G.n) _ j (grid j) (hρ1 j) (hσ j) (hgrid1 j)
  · intro j
    exact QMCLeafB.RunPartsStream.upper_bracket_lo (G.n * G.n) _ j (grid j) (hρ1 j) (hσ j)
      (hgrid1 j)

#print axioms QMCLeafB.CentreClosure.runParts_shallow_trace

/-! ## 5.  `hstated` in the program's own arithmetic, and the obstruction to switching the centre

`hstated` is the last centre condition of the residual list.  With the identity direction it is not
an abstract real inequality: `dOne ⪝ flat (castMat X) = tr X`, and the surrogate side is
`∑_{j<k} μ_j·(dOne ⪝ p_j)`, so `hstated` says exactly *the state's trace dominates the surrogate's
identity pairing*.  That is one real inequality between computable quantities — which is what the
run's resulting-state ledger has to deliver.

Then the f64 repair itself.  §2 gives the algebra, but the repair has a structural cost that the
current `RunParts` interface cannot express: an `ok` round must exhibit
`RelaxMem A (cX k) u dq` at the **same** centre the cut branch queried, and `RelaxMem.diag_near`
requires `|cXᵢᵢ − 1| ≤ dq/4`.  A scaled centre `(1 − dq/2)·X` with `Xᵢᵢ ≤ 1 + dq/4` misses that
band *strictly* by `dq²/8`, so `RelaxMem` fails at it for every state in the campaign's slab. -/

/-- **`hstated` in the program's arithmetic.**  With the identity direction, the surrogate state
condition is the single inequality `∑_{j<k} μ_j·(d ⪝ p_j) ≤ tr X_k`: the state's trace must
dominate the surrogate's identity pairing.  Both sides are quantities the program computes. -/
theorem hstated_iff_trace (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (k : ℕ) (mu : ℕ → ℝ)
    (qSurr : Fin (G.n * G.n) → ℝ)
    (hqSurr : qSurr = ∑ j ∈ Finset.range k, mu j •
      QMCLeafB.EngineIterates.cutPR
        (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) j)
    (X : Matrix (Fin G.n) (Fin G.n) ℚ) :
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (qSurr - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat X)) ≤ 0
      ↔ (∑ j ∈ Finset.range k, mu j *
          (QMCLeafB.RunPartsStream.dOne G.n ⬝ᵥ QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) j))
        ≤ ∑ i, ((X i i : ℚ) : ℝ) := by
  rw [hqSurr, dotProduct_sub, QMCLeafB.CentreTrack.dot_sum_smul,
    dOne_dot_flat_eq_trace]
  constructor <;> intro h <;> linarith

/-- **`RelaxMem` is false at the scaled centre.**  If `dq > 0` and some diagonal entry of the raw
state satisfies `Xᵢᵢ ≤ 1 + dq/4` (the *upper* half of the relaxation's own band — true at
`InitDq.init0`, where `Xᵢᵢ = (2n² + 2dq²)⁻¹`), then the scaled centre `(1 − dq/2)·X` violates
`RelaxMem`'s diagonal clause: `(1 − dq/2)·Xᵢᵢ ≤ 1 − dq/4 − dq²/8 < 1 − dq/4`.

So the f64 repair cannot be read as "query at the scaled centre": it makes `hdiagc`/`hbody`
*provable*, but it destroys the `ok` branch at that centre.  Consuming it inside the present
`RunParts` interface needs the cut centre and the membership centre to be **two different
streams** — the interface has one (`cX k` feeds both `C`/`hmarg`/`hcEq` and `hmem`). -/
theorem relaxMem_scaled_false {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 2) {X : Matrix (Fin n) (Fin n) ℚ} (i : Fin n)
    (hi : X i i ≤ 1 + δ / 4) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem A ((1 - δ / 2) • X) u δ := by
  intro h
  have hn := h.diag_near i
  rw [Matrix.smul_apply, smul_eq_mul] at hn
  have hsq : (0 : ℚ) < δ ^ 2 := by positivity
  have ha : (0 : ℚ) ≤ 1 - δ / 2 := by linarith
  have h2 : (1 - δ / 2) * X i i ≤ (1 - δ / 2) * (1 + δ / 4) :=
    mul_le_mul_of_nonneg_left hi ha
  have h3 : (1 - δ / 2) * (1 + δ / 4) < 1 - δ / 4 := by nlinarith [hsq]
  have h5 : (1 - δ / 2) * X i i - 1 < -δ / 4 := by linarith
  have h6 : |(1 - δ / 2) * X i i - 1| = -((1 - δ / 2) * X i i - 1) :=
    abs_of_neg (by linarith)
  rw [h6] at hn
  linarith

/-- The same obstruction on the real relaxed body (`relaxBodyLE`'s diagonal clause). -/
theorem relaxBodyLE_scaled_false {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 2) {X : Matrix (Fin n) (Fin n) ℚ} (i : Fin n)
    (hi : X i i ≤ 1 + δ / 4) :
    ¬ QMCLeafB.BallFloor.relaxBodyLE A u δ
      ((1 - (δ : ℝ) / 2) • QMCLeafB.SepOracle.castMat X) := by
  intro h
  have hn := h.2.1 i
  have h1 : QMCLeafB.SepOracle.castMat X i i = ((X i i : ℚ) : ℝ) := rfl
  rw [Matrix.smul_apply, smul_eq_mul, h1] at hn
  have hXr : ((X i i : ℚ) : ℝ) ≤ 1 + δ / 4 := hi
  have hsq : (0 : ℝ) < δ ^ 2 := by positivity
  have ha : (0 : ℝ) ≤ 1 - δ / 2 := by linarith
  have h2 : (1 - δ / 2) * ((X i i : ℚ) : ℝ) ≤ (1 - δ / 2) * (1 + δ / 4) :=
    mul_le_mul_of_nonneg_left hXr ha
  have h3 : (1 - δ / 2) * (1 + δ / 4) < 1 - δ / 4 := by nlinarith [hsq]
  have h5 : (1 - δ / 2) * ((X i i : ℚ) : ℝ) - 1 < -δ / 4 := by linarith
  have h6 : |(1 - δ / 2) * ((X i i : ℚ) : ℝ) - 1|
      = -((1 - δ / 2) * ((X i i : ℚ) : ℝ) - 1) := abs_of_neg (by linarith)
  rw [h6] at hn
  linarith

#print axioms QMCLeafB.CentreClosure.hstated_iff_trace
#print axioms QMCLeafB.CentreClosure.relaxMem_scaled_false
#print axioms QMCLeafB.CentreClosure.relaxBodyLE_scaled_false

/-! ## 6.  The query centre that kills the state-mismatch terms

Phase 16 kept the query centre at the program's *state* `stX` and therefore paid two mismatch terms
(`hstatec`'s first summand, `hstated`) against the rational surrogate `q_k = ∑_{j<k} μ_j p_j`.  But
`cX` is a **free rational stream**: nothing in `RunParts` forces it to be the state.  Querying the
oracle at the surrogate itself — `cX k := qMat k`, the rational matrix whose row-major code is
`qVec k = ∑_{j<k} μQ_j·p_j` — makes both mismatch terms *identical zero*, and the residual reduces
to

* `hTrc` on the surrogate: `tr (qMat k) ≤ n·(1 − dq/4)` — a bound on a sum of small positive terms;
* `hCsym` on the surrogate;
* the pure bracket budget `hbud : ∑_{j<k} δ_j·max 0 (−(c_k ⪝ p_j)) ≤ marg_k/2`.

This is the point `hcut_of_approx` was designed for (`q_k` within the drift budget of the ellipsoid
centre `Cat k = ∑ λ_j p_j`), and `q_k` is computable from the program's own records.  The price is
that the oracle is queried at `q_k` rather than at `stX`. -/

/-- Row-major **un**flattening (the inverse of `QMCLeafB.RelaxOracle.flatQ`). -/
def unflatQ {n : ℕ} (v : Fin (n * n) → ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => v (finProdFinEquiv (i, j))

/-- `unflatQ` is a right inverse of the row-major flattening. -/
theorem flatQ_unflatQ {n : ℕ} (v : Fin (n * n) → ℚ) :
    QMCLeafB.RelaxOracle.flatQ (unflatQ v) = v := by
  funext k
  have h : ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2) = finProdFinEquiv.symm k :=
    rfl
  simp only [QMCLeafB.RelaxOracle.flatQ, unflatQ, h, Equiv.apply_symm_apply]

/-- The real flattening of a rational matrix is the cast of its row-major code. -/
theorem flat_castMat_eq_flatQ {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat X)
      = fun i => ((QMCLeafB.RelaxOracle.flatQ X i : ℚ) : ℝ) := rfl

/-- The dyadic upper surrogate coefficient, over `ℚ` (the program's own rational). -/
noncomputable def muQUp (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (grid : ℕ → ℕ)
    (j : ℕ) : ℚ :=
  QMCLeafB.CentreTrack.gamQ N cd j
    * DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j)

/-- `muUp` is the cast of `muQUp`. -/
theorem muUp_eq_muQUp (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (grid : ℕ → ℕ)
    (j : ℕ) : QMCLeafB.RunPartsStream.muUp N cd grid j = ((muQUp N cd grid j : ℚ) : ℝ) := rfl

/-- **The rational surrogate vector** `q_k = ∑_{j<k} μQ_j·p_j` of the engine's centre at round `k`. -/
noncomputable def qVec (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (grid : ℕ → ℕ) (k : ℕ) :
    Fin (G.n * G.n) → ℚ :=
  fun i => ∑ j ∈ Finset.range k,
    muQUp (G.n * G.n) (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) grid j
      * QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (cn j) j i

/-- **The surrogate as a rational matrix** — the query centre of §6. -/
noncomputable def qMat (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (grid : ℕ → ℕ) (k : ℕ) :
    Matrix (Fin G.n) (Fin G.n) ℚ :=
  unflatQ (qVec G P hn cn hcne grid k)

/-- **The surrogate stream in the engine's coordinates.** -/
theorem qVec_cast (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (grid : ℕ → ℕ) (k : ℕ) :
    (fun i => ((qVec G P hn cn hcne grid k i : ℚ) : ℝ))
      = ∑ j ∈ Finset.range k,
          QMCLeafB.RunPartsStream.muUp (G.n * G.n)
            (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) grid j •
          QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) j := by
  funext i
  have h1 : ((qVec G P hn cn hcne grid k i : ℚ) : ℝ)
      = ∑ j ∈ Finset.range k,
          ((muQUp (G.n * G.n)
            (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) grid j : ℚ) : ℝ)
          * ((QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (cn j) j i : ℚ) : ℝ) := by
    simp only [qVec, Rat.cast_sum, Rat.cast_mul]
  have h2 : (∑ j ∈ Finset.range k,
        QMCLeafB.RunPartsStream.muUp (G.n * G.n)
          (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) grid j •
        QMCLeafB.EngineIterates.cutPR
          (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) j) i
      = ∑ j ∈ Finset.range k,
          ((muQUp (G.n * G.n)
            (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) grid j : ℚ) : ℝ)
          * ((QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (cn j) j i : ℚ) : ℝ) := by
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, muUp_eq_muQUp]
    rw [QMCLeafB.EngineIterates.cutPR, QMCLeafB.RunPartsDilate.runCut_eq_witAt]
  rw [h1, h2]

/-- **The surrogate's flat code is the surrogate stream itself.** -/
theorem flat_qMat (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (grid : ℕ → ℕ) (k : ℕ) :
    QMCLeafB.AnswerProducer.flat
        (QMCLeafB.SepOracle.castMat (qMat G P hn cn hcne grid k))
      = ∑ j ∈ Finset.range k,
          QMCLeafB.RunPartsStream.muUp (G.n * G.n)
            (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) grid j •
          QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) j := by
  rw [← qVec_cast G P hn cn hcne grid k, flat_castMat_eq_flatQ]
  show (fun i => ((QMCLeafB.RelaxOracle.flatQ (unflatQ (qVec G P hn cn hcne grid k)) i : ℚ) : ℝ))
      = fun i => ((qVec G P hn cn hcne grid k i : ℚ) : ℝ)
  rw [flatQ_unflatQ]

/-- **`hstated` is identically satisfied at the surrogate centre.** -/
theorem hstated_at_surrogate (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (grid : ℕ → ℕ) (k : ℕ) :
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ ((∑ j ∈ Finset.range k,
              QMCLeafB.RunPartsStream.muUp (G.n * G.n)
                (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) grid j •
              QMCLeafB.EngineIterates.cutPR
                (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) j)
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (qMat G P hn cn hcne grid k))) ≤ 0 := by
  rw [← flat_qMat G P hn cn hcne grid k, sub_self, dotProduct_zero]

/-- **`hstatec` at the surrogate centre is the pure bracket budget** — the state-mismatch summand
is gone. -/
theorem hstatec_at_surrogate (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (grid : ℕ → ℕ)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (k : ℕ)
    (hbud : (∑ j ∈ Finset.range k,
        QMCLeafB.RunPartsStream.deltaUp (G.n * G.n)
          (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) grid j
        * max 0 (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) j)))
      ≤ ((marg k : ℚ) : ℝ) / 2) :
    (fun i => ((c k i : ℚ) : ℝ))
        ⬝ᵥ ((∑ j ∈ Finset.range k,
              QMCLeafB.RunPartsStream.muUp (G.n * G.n)
                (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) grid j •
              QMCLeafB.EngineIterates.cutPR
                (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) j)
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (qMat G P hn cn hcne grid k)))
      + ∑ j ∈ Finset.range k,
          QMCLeafB.RunPartsStream.deltaUp (G.n * G.n)
            (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) grid j
          * max 0 (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
              (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) j))
        ≤ ((marg k : ℚ) : ℝ) / 2 := by
  rw [← flat_qMat G P hn cn hcne grid k, sub_self, dotProduct_zero, zero_add]
  exact hbud

#print axioms QMCLeafB.CentreClosure.flatQ_unflatQ
#print axioms QMCLeafB.CentreClosure.qVec_cast
#print axioms QMCLeafB.CentreClosure.flat_qMat
#print axioms QMCLeafB.CentreClosure.hstated_at_surrogate
/-- **`RunParts` at `runParamsShallow` with the oracle queried at the rational surrogate.**

Against `QMCLeafB.RunPartsStream.runParts_shallow_dyadic` / `runParts_shallow_trace`, the residual
list loses `hstatec`'s state-mismatch summand, loses `hstated` altogether, and loses `hqSurr`
(definitional).  What is left is the pure bracket budget `hbud` plus the surrogate's own trace and
symmetry.  The centre stream is `qMat G P hn cn hcne grid`, i.e. `q_k = ∑_{j<k} μ_j p_j` — the
program's own rational surrogate of the engine's centre `Cat k`. -/
noncomputable def runParts_shallow_surrogate
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (grid : ℕ → ℕ)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (lam : ℕ → ℚ) (c : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G)
        (qMat G P hn cn hcne grid k)
        (t - QMCLeafB.RundataCert.eps G) (P.dq))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < (P).K * (P).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
        (qMat G P hn cn hcne grid k)
        (t - QMCLeafB.RundataCert.eps G) (P.dq))
    (hCsym : ∀ k, (qMat G P hn cn hcne grid k)ᵀ = qMat G P hn cn hcne grid k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
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
    (hgrid1 : ∀ j, 1 ≤ QMCLeafB.EngineIterates.sigmaQ
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne j).c
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne j).p
      * 4 ^ (grid j))
    (hTrc : ∀ k, ∑ i, (qMat G P hn cn hcne grid k) i i ≤ (G.n : ℚ) * (1 - P.dq / 4))
    (hbud : ∀ k, ok k = false →
      (∑ j ∈ Finset.range k,
          QMCLeafB.RunPartsStream.deltaUp (G.n * G.n)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) grid j
          * max 0 (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hlam3 : ∀ j,
      |(fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (P) hn cn hcne (c j) j i : ℚ) : ℝ))|
        ≤ ((lam j : ℚ) : ℝ) * ((fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (P) hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ))))
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok ((P).K * (P).m)) :
    QMCLeafB.FinalStroke.RunParts o G t (P) :=
  runParts_shallow_trace o G t P hn hrmaxPos hrmax1 hbudP ok marg
    (fun k => qMat G P hn cn hcne grid k) lam c cn C hmarg hmem hCsym hcEq hcn hcne
    hlam0 hlam1 hlam2 grid hgrid1 hTrc
    (fun k => ∑ j ∈ Finset.range k,
      QMCLeafB.RunPartsStream.muUp (G.n * G.n)
        (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) grid j •
      QMCLeafB.EngineIterates.cutPR
        (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) j)
    (fun k => rfl) hlam3
    (fun k hok => hstatec_at_surrogate G P hn cn hcne grid c marg k (hbud k hok))
    (fun k _ => hstated_at_surrogate G P hn cn hcne grid k) hverdict


