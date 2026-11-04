-- Prove2me | Definitions.Def_QMCLeafB_drift_m3
-- name    : QMCLeafB_drift_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:35:13.082613+00:00
-- url     : https://prove2.me/theorems/c18f0655-0cf1-4d16-ae7b-9f3c413752d7
-- title:
--   QMCLeafB drift_m3
-- statement:
--   # leaf B phase 17 — brick `drift-closure` (swarm `smw1gfajf`, member m3, direction d5)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_runparts_stream_m4
import Definitions.Def_QMCLeafB_unionShallow
/-
# leaf B phase 17 — brick `drift-closure` (swarm `smw1gfajf`, member m3, direction d5)

`RunPartsDilate.runParts_of_dilated` consumes the centre mismatch **at the engine's own centre**
`Cat N 0 cd k`:

    hdriftc : c_k ⬝ᵥ (Cat k − flat (cX k)) ≤ margin_k / 2
    hdriftd : d     ⬝ᵥ (Cat k − flat (cX k)) ≤ 0.

The phase-14/15/16 route (`RunPartsStream.runParts_of_stream_data`, m4) re-expressed these through a
*rational surrogate* `q_k = ∑_{j<k} μ_j p_j` inside a bracket `μ_j − δ_j ≤ λ_j ≤ μ_j`, costing six
surrogate hypotheses, a dyadic grid (`grid`/`hgrid1`), the `δ`-charge in `hstatec`, and — because a
bracket makes the sign of `λ_j − μ_j` matter — the direction-sign condition `hpos`, itself bought
from a *large dilation parameter* (`hlam3`).

**This file removes the surrogate.**  `μ_j`, `δ_j` are proof-side reals; nothing forces the
surrogate to be rational, so `μ_j := λ_j`, `δ_j := 0` is admissible.  Then
`Cat k − q_k = ∑_{j<k} (λ_j − μ_j) p_j = 0` identically, and

* `hmu_up`/`hmu_lo` are `le_refl`; `hqSurr` *is* `CentreTrack.Cat_eq_sum` (§1);
* the drift is **zero for both signs**, so `hpos`/`hlam3` are unused by the drift slot — the
  m4-f57 lower-bracket obstruction and the "λ large enough" cost disappear with the bracket;
* `hstatec`'s `δ`-sum vanishes (`∑ 0 · max 0 (…) = 0`), and `grid`/`hgrid1` are not needed.

§2 identifies the surviving conditions: `dvec` is the flattened identity, so its pairing is the
trace.  Hence

    hdriftd  ⟺  diagSum (Cat k) ≤ ∑ i, (cX k) i i        (engine centre's diagonal read-out below
                                                           the query centre's trace)
    diagSum (Cat k) = ∑_{j<k} (γ_j/√σ_j) · diagSum (p_j)   (telescoped over the rounds),

so the surviving content of the drift slot is a *cumulative trace budget*, not a square-root
estimate: it is exactly the quantity the program keeps in its own state.

## What is delivered (all compiled, `#print axioms` = [propext, Classical.choice, Quot.sound])

* §1 `exact_surr`, `exact_mismatch`, `exact_bracket` — the exact surrogate and its empty bracket.
* §2 `dOne_apply`, `dOne_dot`, `dOne_dot_flat_castMat`, `stated_iff_trace`, `diagSum_cat`,
  `trace_budget_of_drift` — the diagonal read-out and the telescope.
* §3 `runParts_of_exact_stream` — `RunParts o G t P` from the exact state conditions:
  `hbody` from the centre's diagonal (`hdiagc`), and the two drift inequalities verbatim.
* §4 `exact_state_of_dyadic` — **no loss**: the phase-16 residual pair (surrogate + bracket +
  `hpos`) *implies* the exact pair, so every instantiation of `runParts_of_stream_data` is an
  instantiation of §3.
* §5 `hbody_of_trace` + `runParts_of_exact_trace` — the same assembly with `hdiagc` replaced by the
  single rational trace inequality `hTrc : ∑ i, (cX k) i i ≤ (G.n:ℚ)·(1 − P.dq/4)` (the
  `centre-closure` reduction; re-derived here so the file imports only the frozen shelf).
* §6 `runParts_shallow_trace` — the brick-4 slot at the campaign family
  `RundataParams.runParamsShallow`, with `hrmaxPos`/`hrmax1`/`hbudP` discharged from the shelf.

## Residual list of §5/§6 (the whole drift slot)

    records { C, hmarg, hmem, hCsym, hcEq, hcn, hcne } + hlam0/hlam1/hlam2 + hverdict
    hTrc     : ∀ k, ∑ i, (cX k) i i ≤ (G.n:ℚ)*(1 − P.dq/4)
    hdriftc  : ∀ k, ok k = false → c_k ⪝ (Cat k − flat (cX k)) ≤ marg_k/2
    hdriftd  : ∀ k, ok k = false → d ⬝ᵥ (Cat k − flat (cX k)) ≤ 0

i.e. no `mu`, `delta`, `qSurr`, `hqSurr`, `hmu_up`, `hmu_lo`, `grid`, `hgrid1`, `hlam3`, no `δ`-sum.
Note the two drift conditions are *equivalent* to stating them at the query centre when the query
centre is chosen to be the surrogate (m4's `hstated_at_surrogate`), so §4 makes the two routes
interchangeable; §5/§6 minimise the *number* of hypotheses (16 versus 20 + grid).

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.DriftExact

open QuantumMaxCutEnergy
open QMCLeafB.RunPartsStream (dOne)

/-! ## 1.  The exact surrogate is the engine's own centre -/

/-- The engine's increment coefficient at `j` (the real `γ_j/√σ_j`). -/
noncomputable def engLam (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (j : ℕ) : ℝ :=
  QMCLeafB.CentreTrack.lam N cd j

/-- **The exact surrogate is the engine's centre.**  With `μ_j := λ_j` the surrogate *is* `Cat k`,
so the surrogate identification hypothesis of `runParts_of_stream_data` is the closed form. -/
theorem exact_surr (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (k : ℕ) :
    (∑ j ∈ Finset.range k, engLam N cd j • QMCLeafB.EngineIterates.cutPR cd j)
      = QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k :=
  (QMCLeafB.CentreTrack.Cat_eq_sum N cd k).symm

/-- **The mismatch vanishes identically** (both signs): with the exact surrogate the engine centre's
displacement from the surrogate is the zero vector. -/
theorem exact_mismatch (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (k : ℕ) :
    QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k
      - (∑ j ∈ Finset.range k, engLam N cd j • QMCLeafB.EngineIterates.cutPR cd j) = 0 := by
  rw [exact_surr, sub_self]

/-- The zero width is an admissible bracket: `μ_j − 0 ≤ λ_j ≤ μ_j` at `μ_j := λ_j`. -/
theorem exact_bracket (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (j : ℕ) :
    engLam N cd j - 0 ≤ QMCLeafB.CentreTrack.lam N cd j
      ∧ QMCLeafB.CentreTrack.lam N cd j ≤ engLam N cd j := by
  constructor <;> simp [engLam]

#print axioms QMCLeafB.DriftExact.exact_surr
#print axioms QMCLeafB.DriftExact.exact_mismatch
#print axioms QMCLeafB.DriftExact.exact_bracket

/-! ## 2.  The diagonal read-out: both surviving conditions are *trace* statements

`dvec` is the flattened identity (`RunPartsStream.dOne`), so its pairing is the diagonal read-out —
i.e. the matrix trace.  Hence `hdriftd` is *one scalar inequality per round*, and the engine centre's
side of it telescopes over the rounds. -/

/-- **The `(i,j)`-entry of the flattened identity.** -/
theorem dOne_apply (n : ℕ) (i j : Fin n) :
    dOne n (finProdFinEquiv (i, j)) = if i = j then 1 else 0 := by
  have hs : finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) :=
    Equiv.symm_apply_apply _ _
  have h1 : QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) (finProdFinEquiv (i, j))
      = (1 : Matrix (Fin n) (Fin n) ℚ) i j := by
    rw [show QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) (finProdFinEquiv (i, j))
        = (1 : Matrix (Fin n) (Fin n) ℚ) (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
            (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 from rfl, hs]
  change ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ)
    (finProdFinEquiv (i, j)) : ℚ) : ℝ) = if i = j then 1 else 0
  rw [h1, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h]
    norm_num

/-- **`flat` reads a matrix at the row-major index.** -/
theorem flat_finProdFinEquiv {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    QMCLeafB.AnswerProducer.flat X (finProdFinEquiv (i, j)) = X i j := by
  have hs : finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) :=
    Equiv.symm_apply_apply _ _
  simp only [QMCLeafB.AnswerProducer.flat, hs]

/-- The diagonal read-out of a flat vector: the trace seen through the row-major code. -/
noncomputable def diagSum {n : ℕ} (z : Fin (n * n) → ℝ) : ℝ :=
  ∑ i : Fin n, z (finProdFinEquiv (i, i))

theorem diagSum_add {n : ℕ} (a b : Fin (n * n) → ℝ) :
    diagSum (a + b) = diagSum a + diagSum b := by
  simp only [diagSum, Pi.add_apply, Finset.sum_add_distrib]

theorem diagSum_smul {n : ℕ} (c : ℝ) (a : Fin (n * n) → ℝ) :
    diagSum (c • a) = c * diagSum a := by
  simp only [diagSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- **The identity direction's pairing is the diagonal read-out.** -/
theorem dOne_dot {n : ℕ} (z : Fin (n * n) → ℝ) :
    dOne n ⬝ᵥ z = diagSum z := by
  have hsplit : dOne n ⬝ᵥ z
      = ∑ p : Fin n × Fin n, dOne n (finProdFinEquiv p) * z (finProdFinEquiv p) := by
    rw [dotProduct, ← Equiv.sum_comp finProdFinEquiv
      (fun k : Fin (n * n) => dOne n k * z k)]
  rw [hsplit, Fintype.sum_prod_type, diagSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [dOne_apply, if_pos rfl, one_mul]
  · intro j _ hji
    rw [dOne_apply, if_neg (Ne.symm hji), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **The identity direction against a cast matrix is its trace.** -/
theorem dOne_dot_flat_castMat {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℚ) :
    dOne n ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Y)
      = ∑ i : Fin n, (Y i i : ℝ) := by
  rw [dOne_dot, diagSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [flat_finProdFinEquiv, QMCLeafB.SepOracle.castMat_apply]

/-- **`hdriftd` is the scalar trace inequality.** -/
theorem stated_iff_trace {n : ℕ} (z : Fin (n * n) → ℝ) (Y : Matrix (Fin n) (Fin n) ℚ) :
    dOne n ⬝ᵥ (z - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Y)) ≤ 0
      ↔ diagSum z ≤ ∑ i : Fin n, (Y i i : ℝ) := by
  rw [dotProduct_sub, dOne_dot, dOne_dot_flat_castMat, sub_nonpos]

/-- **The engine centre's diagonal read-out telescopes over the rounds.** -/
theorem diagSum_cat (n : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n)) (k : ℕ) :
    diagSum (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k)
      = ∑ j ∈ Finset.range k,
          engLam (n * n) cd j * diagSum (QMCLeafB.EngineIterates.cutPR cd j) := by
  rw [← exact_surr (n * n) cd k]
  induction k with
  | zero => simp [diagSum]
  | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, diagSum_add, diagSum_smul, ← ih]

/-- **The accumulated engine trace must fit under the program centre's trace.**  With the identity
direction the drift condition `hdriftd` is exactly: the engine centre's diagonal read-out (a sum of
the round increments, telescoped) is dominated by the query centre's diagonal. -/
theorem trace_budget_of_drift {n : ℕ} (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n))
    (Y : Matrix (Fin n) (Fin n) ℚ) (k : ℕ)
    (h : dOne n ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
      - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Y)) ≤ 0) :
    ∑ j ∈ Finset.range k,
        engLam (n * n) cd j * diagSum (QMCLeafB.EngineIterates.cutPR cd j)
      ≤ ∑ i : Fin n, (Y i i : ℝ) := by
  have h' : diagSum (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k)
      ≤ ∑ i : Fin n, (Y i i : ℝ) := (stated_iff_trace _ Y).1 h
  rw [diagSum_cat] at h'
  exact h'

#print axioms QMCLeafB.DriftExact.dOne_apply
#print axioms QMCLeafB.DriftExact.flat_finProdFinEquiv
#print axioms QMCLeafB.DriftExact.diagSum_add
#print axioms QMCLeafB.DriftExact.diagSum_smul
#print axioms QMCLeafB.DriftExact.dOne_dot
#print axioms QMCLeafB.DriftExact.dOne_dot_flat_castMat
#print axioms QMCLeafB.DriftExact.stated_iff_trace
#print axioms QMCLeafB.DriftExact.diagSum_cat
#print axioms QMCLeafB.DriftExact.trace_budget_of_drift

/-! ## 3.  The assembly with the *exact* centre: no surrogate, no bracket, no direction sign

`RunPartsDilate.runParts_of_dilated` already speaks about the engine's own centre `Cat N 0 cd k`.
The phase-14/16 route routed that through a rational surrogate (§`RunPartsStream`), which cost the
six surrogate hypotheses and the direction-sign condition `hlam3`/`hpos`.  Here the surrogate is
pinned to the engine's own coefficient stream (`§1 exact_surr`) and the assembly is written directly
at the exact state conditions. -/

/-- **`RunParts o G t P` from the exact centre conditions.**  The residual list is
`RunPartsStream.runParts_of_stream_data`'s with the whole surrogate block removed:
`mu`, `delta`, `qSurr`, `hqSurr`, `hmu_up`, `hmu_lo`, `grid`, `hgrid1`, `hlam3` and the `δ`-sum of
`hstatec` are all gone; `hstatec`/`hstated` are the two exact inequalities
`c_k ⪝ (Cat k − flat (cX k)) ≤ marg_k/2` and `d ⬝ᵥ (Cat k − flat (cX k)) ≤ 0`. -/
noncomputable def runParts_of_exact_stream
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
    (hdiagc : ∀ k, ∀ i, (cX k) i i ≤ 1 - P.dq / 4)
    (hdriftc : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, ok k = false →
      dOne G.n
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
  · -- `hbody` from the centre's diagonal
    intro k _hok X hX
    have hd' : ∀ i, ((cX k i i : ℚ) : ℝ) ≤ 1 - ((P.dq : ℚ) : ℝ) / 4 := by
      intro i
      have h := hdiagc k i
      have h2 : ((1 - P.dq / 4 : ℚ) : ℝ) = 1 - ((P.dq : ℚ) : ℝ) / 4 := by
        push_cast
        ring
      calc ((cX k i i : ℚ) : ℝ)
          ≤ ((1 - P.dq / 4 : ℚ) : ℝ) := by exact_mod_cast h
        _ = 1 - ((P.dq : ℚ) : ℝ) / 4 := h2
    simpa using QMCLeafB.RunPartsStream.hbody_of_diag_body hd' X hX

#print axioms QMCLeafB.DriftExact.runParts_of_exact_stream

/-! ## 4.  The reduction loses nothing: the phase-16 dyadic residuals imply the exact ones

Any instantiation of `RunPartsStream.runParts_of_stream_data` gives an instantiation of §3, because
the dyadic residual pair (a rational surrogate inside a bracket, plus the direction's sign `hpos`)
*implies* the exact pair.  So the campaign's existing route is a special case, and switching to the
exact centre only removes hypotheses. -/

/-- **The exact pair from the phase-16 residual pair.**  Replacing the surrogate by the engine's own
centre (`§1`) and noting that the direction's sign is *not needed* once the surrogate is exact, the
two exact state conditions follow from the phase-16 ones. -/
theorem exact_state_of_dyadic
    (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (ok : ℕ → Bool) (marg : ℕ → ℚ) (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (c cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0)
    (mu delta : ℕ → ℝ) (qSurr : ℕ → Fin (G.n * G.n) → ℝ)
    (hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k, mu j • QMCLeafB.EngineIterates.cutPR
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j)
    (hmu_up : ∀ j, QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j ≤ mu j)
    (hmu_lo : ∀ j, mu j - delta j ≤ QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j)
    (hpos : ∀ j, 0 ≤ dOne G.n ⬝ᵥ QMCLeafB.EngineIterates.cutPR
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j)
    (hstatec : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        + ∑ j ∈ Finset.range k, delta j * max 0
            (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j))
          ≤ ((marg k : ℚ) : ℝ) / 2)
    (hstated : ∀ k, ok k = false →
      dOne G.n ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0) :
    (∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    ∧ (∀ k, ok k = false →
      dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0) := by
  constructor
  · -- the cut direction: bracket width + state mismatch
    intro k hok
    have hb := QMCLeafB.RunPartsStream.drift_bound_upper (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne)
      (fun i => ((c k i : ℚ) : ℝ)) k mu delta
      (fun j _ => hmu_lo j) (fun j _ => hmu_up j)
    rw [← hqSurr k] at hb
    have hsplit : (∑ j ∈ Finset.range k, mu j • QMCLeafB.EngineIterates.cutPR
          (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j)
        - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
        = qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)) := by
      rw [hqSurr k]
    have hcat : QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
        - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
        = (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - ∑ j ∈ Finset.range k, mu j • QMCLeafB.EngineIterates.cutPR
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j)
          + ((∑ j ∈ Finset.range k, mu j • QMCLeafB.EngineIterates.cutPR
                (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j)
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) := by
      abel
    rw [hcat, dotProduct_add, hsplit, ← hqSurr k]
    linarith [hb, hstatec k hok]
  · -- the identity direction: the bracket's upper end + the state mismatch
    intro k hok
    have hb := QMCLeafB.RunPartsStream.drift_nonpos_of_upper (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) (dOne G.n) k (qSurr k) mu
      (hqSurr k) (fun j _ => hmu_up j) (fun j _ => hpos j)
    have hcat : QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
        - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
        = (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k - qSurr k)
          + (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) := by
      abel
    rw [hcat, dotProduct_add]
    linarith [hb, hstated k hok]

#print axioms QMCLeafB.DriftExact.exact_state_of_dyadic


/-! ## 5.  Composability with the centre-closure reduction (`hdiagc` → `hTrc`)

The entrywise centre condition `hdiagc` can be replaced by the single rational trace inequality
`hTrc` of the `centre-closure` brick (`Check_centre_closure_m4.lean`, `CentreClosure.hbody_of_trace`
— the same reduction, re-derived here so that this file imports only the frozen shelf).  Together
with §3 the residual of the drift slot becomes:

    records + hTrc + hdriftc + hdriftd + hverdict,

with `hdriftd` the trace budget `diagSum (Cat k) ≤ ∑ i (cX k) i i` of §2. -/

/-- **`hbody` at the identity direction from the centre's *trace*.**  The body's diagonal clause
only gives `tr X ≥ n·(1 − δ/4)` (the strict diagonal form would need `n` entrywise inequalities), so
the trace bound on the centre is the weakest condition that works. -/
theorem hbody_of_trace {n : ℕ} {δ : ℚ} {Q : Matrix (Fin n) (Fin n) ℚ}
    (hTrc : ∑ i, Q i i ≤ (n : ℚ) * (1 - δ / 4))
    {A : Matrix (Fin n) (Fin n) ℝ} {u : ℝ}
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : QMCLeafB.BallFloor.relaxBodyLE A u ((δ : ℚ) : ℝ) X) :
    -(0 : ℝ) ≤ QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ))
      (X - QMCLeafB.SepOracle.castMat Q) := by
  have h1 : ∀ i, (1 : ℝ) - ((δ : ℚ) : ℝ) / 4 ≤ X i i := by
    intro i
    have h := (abs_le.mp (hX.2.1 i)).1
    linarith
  have hXtr : (n : ℝ) * (1 - ((δ : ℚ) : ℝ) / 4) ≤ ∑ i, X i i := by
    have hsum : (∑ _i : Fin n, ((1 : ℝ) - ((δ : ℚ) : ℝ) / 4))
        = (n : ℝ) * (1 - ((δ : ℚ) : ℝ) / 4) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hsum]
    exact Finset.sum_le_sum fun i _ => h1 i
  have hQtr : (∑ i, ((Q i i : ℚ) : ℝ)) ≤ (n : ℝ) * (1 - ((δ : ℚ) : ℝ) / 4) := by
    have hcast : ((∑ i, Q i i : ℚ) : ℝ) ≤ (((n : ℚ) * (1 - δ / 4) : ℚ) : ℝ) := by
      exact_mod_cast hTrc
    push_cast at hcast
    exact hcast
  have hQsum : (∑ i, QMCLeafB.SepOracle.castMat Q i i) = ∑ i, ((Q i i : ℚ) : ℝ) := rfl
  rw [show -(0 : ℝ) = 0 by ring, QMCLeafB.RunPartsStream.castMat_one, QMCLeafB.SepOracle.frob_sub,
    QMCLeafB.RunPartsStream.frob_one_eq_trace, QMCLeafB.RunPartsStream.frob_one_eq_trace, hQsum]
  linarith [hXtr, hQtr]

#print axioms QMCLeafB.DriftExact.hbody_of_trace

noncomputable def runParts_of_exact_trace
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
      dOne G.n
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
  · -- `hbody` from the centre's trace
    intro k _hok X hX
    simpa using hbody_of_trace (hTrc k) X hX

#print axioms QMCLeafB.DriftExact.runParts_of_exact_trace

/-! ## 6.  The brick-4 slot at the campaign family, with the reduced residual list

`RunParts o G t (runParamsShallow G hn)` — the per-bracketed-`(G,t)` slot the endgame consumes — from

    records {C, hmarg, hmem, hCsym, hcEq, hcn, hcne} + hlam0/hlam1/hlam2 + hTrc
      + hdriftc (c_k ⪝ (Cat k − flat cX) ≤ marg_k/2) + hdriftd (d ⬝ (Cat k − flat cX) ≤ 0)
      + hverdict,

i.e. no surrogate, no bracket, no direction sign, and `hdiagc` weakened to the single trace
inequality.  This is the drop-in replacement for `RunPartsStream.runParts_shallow_concrete` and
`CentreClosure.runParts_shallow_trace` with the drift block removed. -/

noncomputable def runParts_shallow_trace
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.RundataParams.runParamsShallow G hn).dq))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < ((QMCLeafB.RundataParams.runParamsShallow G hn)).K
        * ((QMCLeafB.RundataParams.runParamsShallow G hn)).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.RundataParams.runParamsShallow G hn).dq))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, ok k = false →
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G ((QMCLeafB.RundataParams.runParamsShallow G hn)) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G ((QMCLeafB.RundataParams.runParamsShallow G hn)) hn
              cn hcne (c k) k|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
            ((QMCLeafB.RundataParams.runParamsShallow G hn)) hn cn hcne (c k) k|
        + 9 * marg k ^ 2
            / (4 * (((QMCLeafB.RundataParams.runParamsShallow G hn)).rmax) ^ 2) + 1
      ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G ((QMCLeafB.RundataParams.runParamsShallow G hn)) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hTrc : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 - (QMCLeafB.RundataParams.runParamsShallow G hn).dq / 4))
    (hdriftc : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G ((QMCLeafB.RundataParams.runParamsShallow G hn)) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, ok k = false →
      dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G ((QMCLeafB.RundataParams.runParamsShallow G hn)) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((QMCLeafB.RundataParams.runParamsShallow G hn).K
        * (QMCLeafB.RundataParams.runParamsShallow G hn).m)) :
    QMCLeafB.FinalStroke.RunParts o G t
      (QMCLeafB.RundataParams.runParamsShallow G hn) := by
  have hrmax1 : (QMCLeafB.RundataParams.runParamsShallow G hn).rmax ≤ 1 := by
    show QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) ≤ 1
    unfold QMCLeafB.RundataHalving.rmaxOf
    rw [div_le_one (by positivity)]
    have h : (1 : ℚ) ≤ ((G.n * G.n : ℕ) : ℚ) := by
      have h1 : 1 ≤ G.n * G.n := by nlinarith
      exact_mod_cast h1
    linarith
  exact runParts_of_exact_trace o G t (QMCLeafB.RundataParams.runParamsShallow G hn) hn
    (QMCLeafB.RunPartsDilate.runParamsShallow_rmax_pos G hn) hrmax1
    (QMCLeafB.RunPartsShallow.runParamsShallow_budget G hn hRq)
    ok marg cX lam c cn C hmarg hmem hCsym hcEq hcn hcne hlam0 hlam1 hlam2 hTrc hdriftc hdriftd
    hverdict

#print axioms QMCLeafB.DriftExact.runParts_shallow_trace


/-! ## 7.  The assembly's own family: brick 4's slot at `UnionShallow.paramsKbc2`

`AssemblyStreamM5.runParts_at_interior` produces exactly this slot from the twenty stream
hypotheses of `runParts_of_stream_data`.  This is the same slot with the drift block replaced by the
exact conditions, so the coordinator can drop §3's residual list into the wired assembly
(`HdProp`/`HDProp_of_stream`) without touching anything else. -/

noncomputable def runParts_at_interior_exact
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.UnionShallow.paramsKbc2 G).dq))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < ((QMCLeafB.UnionShallow.paramsKbc2 G)).K
        * ((QMCLeafB.UnionShallow.paramsKbc2 G)).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.UnionShallow.paramsKbc2 G).dq))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, ok k = false →
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn
              cn hcne (c k) k|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
            ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn cn hcne (c k) k|
        + 9 * marg k ^ 2
            / (4 * (((QMCLeafB.UnionShallow.paramsKbc2 G)).rmax) ^ 2) + 1
      ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hTrc : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4))
    (hdriftc : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, ok k = false →
      dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m)) :
    QMCLeafB.FinalStroke.RunParts o G t
      (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  have hrmax1 : (QMCLeafB.UnionShallow.paramsKbc2 G).rmax ≤ 1 := by
    have h1 : 1 ≤ G.n * G.n := by nlinarith
    exact QMCLeafB.RunPartsStream.rmaxOf_le_one h1
  exact runParts_of_exact_trace o G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.UnionShallow.paramsKbc2_rmax_pos G hn) hrmax1
    (QMCLeafB.UnionShallow.paramsKbc2_budget G hn hRq)
    ok marg cX lam c cn C hmarg hmem hCsym hcEq hcn hcne hlam0 hlam1 hlam2 hTrc hdriftc hdriftd
    hverdict

#print axioms QMCLeafB.DriftExact.runParts_at_interior_exact


