-- Prove2me | Definitions.Def_QMCLeafB_ceiling
-- name    : QMCLeafB_ceiling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:44:55.699636+00:00
-- url     : https://prove2.me/theorems/afa99fc5-509c-41f4-90b1-3a5a4f978af0
-- title:
--   QMCLeafB ceiling
-- statement:
--   # leaf B phase 22 — the trace ceiling `n(1 − dq/4)`: every consumption site, machine-checked
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_drift_m3
import Definitions.Def_QMCLeafB_records_m2
import Definitions.Def_QMCLeafB_residbundle_m7
/-
# leaf B phase 22 — the trace ceiling `n(1 − dq/4)`: every consumption site, machine-checked
(swarm `smw1ntur6`, member m3, direction `ceiling-analysis`)

Phase 21 left one analytic crater: at a refuted interior point the drift pair `hdriftc`/`hdriftd`
is demanded below the horizon, and m8's `Check_cutbudget_m8` killed the identity-direction stream
(increments `γ·√(2M)·(13/16)^j` accumulate past `n(1 − dq/4)` at round 4 and every `k ≥ 4`, at every
base `Q` and every positive multiplier stream).  The two routes on the table are

  (a) exhibit a legal stream at an empty body with both budgets (`crater-satisfiability`), or
  (b) widen the ceiling in `BundleH`/`DriftExact` and re-check every consumer.

This file does the analysis route (b) needs, and nothing else.  Its content:

* §1  `frob_id_sub`: in the identity dilation direction the pairing `dM ⪝ (X − Q)` **is** the trace
  difference `tr X − tr Q`.  So `hbody` at `dM = 1` is the statement `tr Q ≤ tr X` on the body.
* §2  `body_trace_ge`: every point of the relaxed body `relaxBodyLE A u δ` has trace at least
  `n(1 − δ/4)` (the body's diagonal band `|Xᵢᵢ − 1| ≤ δ/4`, summed).  Hence the ceiling suffices:
  `ceiling_gives_hbody`.
* §3  `pinchPt_mem`: the *pinched* point `(1 − δ/4)•1` is in the body as soon as its objective
  passes (`(1 − δ/4)·tr A ≤ u + δ/2`, and `δ ≥ 0`).  Its trace is exactly `n(1 − δ/4)`.
* §4  **`ceiling_exact`**: with the pinched point in the body, `hbody` at `dM = 1` is *equivalent*
  to `tr Q ≤ n(1 − δ/4)`.  Consequently `ceiling_not_widenable`: **no constant above `n(1 − δ/4)`
  can replace the ceiling** while keeping `dM = 1` and the campaign body — the ceiling is the body's
  own trace floor, not a slack estimate.  (Route (b) can therefore not be a widening of the number.)
* §5  `hbody_of_empty`: at an **empty** body `hbody` holds in *every* direction `dM` for *every*
  centre `Q` — the ceiling's only role (`hbody`) evaporates there.  `hdriftd_free_of_empty` records
  that the trace cap is then not needed at all.
* §6  `member_diag_eq_of_ceiling`: the ceiling plus a member certificate (`RelaxMem`) force the
  centre's diagonal onto the boundary `1 − δ/4` entry by entry (m1's pinch, re-derived here at the
  trace form the conduit actually supplies).
* §7  producer side: `ceiling_attained_cXst` / `ceiling_attained_diagPinch` — the campaign's own
  centre family `cXst = diagPinch (stMat …) dq` sits **exactly on** the ceiling at **every** round,
  with no hypothesis.  So `hTrc` is not a slack constraint in the campaign: any change of the number
  is a change of the centre family.  `driftd_at_cXst_iff`: at those centres `hdriftd` **is**
  `diagSum (Cat k) ≤ n(1 − dq/4)` — m8's killed inequality.
* §8  `engine_trace_of_ceiling`: the composition actually consumed, `hTrc + hdriftd ⟹
  diagSum (Cat k) ≤ n(1 − dq/4)` (`trace_budget_of_drift` at a cast trace bound).

Nothing is assumed about the other lanes' shapes; this module imports the frozen shelf only.
House discipline: `set_option autoImplicit false`; a `#print axioms` audit after every declaration;
no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`; no `⊊`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.CeilingM3

open QuantumMaxCutEnergy

/-! ## 1.  The identity direction's pairing is the trace difference -/

/-- **`dM = 1`: the pairing is the trace difference.**  `frob 1 (X − Q) = tr X − tr Q`. -/
theorem frob_id_sub (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ))
        (X - QMCLeafB.SepOracle.castMat Q)
      = (∑ i, X i i) - ∑ i, ((Q i i : ℚ) : ℝ) := by
  have h1 : QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ)) X = ∑ i, X i i := by
    rw [QMCLeafB.RunPartsStream.castMat_one]
    exact QMCLeafB.RunPartsStream.frob_one_eq_trace X
  have h2 : QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ))
      (QMCLeafB.SepOracle.castMat Q) = ∑ i, ((Q i i : ℚ) : ℝ) := by
    rw [QMCLeafB.RunPartsStream.castMat_one, QMCLeafB.RunPartsStream.frob_one_eq_trace]
    rfl
  rw [QMCLeafB.SepOracle.frob_sub, h1, h2]

#print axioms QMCLeafB.CeilingM3.frob_id_sub

/-- **`hbody` in the identity direction, unwound**: the body lies above the centre `Q` iff every
body point has at least the centre's trace. -/
theorem hbody_iff_trace (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (u δ : ℝ)
    (Q : Matrix (Fin n) (Fin n) ℚ) :
    (∀ X : Matrix (Fin n) (Fin n) ℝ, QMCLeafB.BallFloor.relaxBodyLE A u δ X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob
        (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ))
        (X - QMCLeafB.SepOracle.castMat Q))
      ↔ (∀ X : Matrix (Fin n) (Fin n) ℝ, QMCLeafB.BallFloor.relaxBodyLE A u δ X →
          (∑ i, ((Q i i : ℚ) : ℝ)) ≤ ∑ i, X i i) := by
  constructor
  · intro h X hX
    have h1 := h X hX
    rw [frob_id_sub] at h1
    have h0 : (-(((0 : ℚ)) : ℝ)) = 0 := by norm_num
    rw [h0] at h1
    linarith
  · intro h X hX
    have h1 := h X hX
    rw [frob_id_sub]
    have h0 : (-(((0 : ℚ)) : ℝ)) = 0 := by norm_num
    rw [h0]
    linarith

#print axioms QMCLeafB.CeilingM3.hbody_iff_trace

/-- **The general direction's form**: in *any* dilation direction `dM`, the `hbody` slot is the
statement that the centre's pairing is below the body's support floor in that direction.  So the
"ceiling" is never a number intrinsic to the drift lemma: it is the body's support floor read in the
chosen direction, which for `dM = 1` is `n(1 − δ/4)` (§2) and for other directions is different. -/
theorem hbody_iff_support_le (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (u δ : ℝ)
    (dM : Matrix (Fin n) (Fin n) ℚ) (Q : Matrix (Fin n) (Fin n) ℚ) :
    (∀ X : Matrix (Fin n) (Fin n) ℝ, QMCLeafB.BallFloor.relaxBodyLE A u δ X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
        (X - QMCLeafB.SepOracle.castMat Q))
      ↔ (∀ X : Matrix (Fin n) (Fin n) ℝ, QMCLeafB.BallFloor.relaxBodyLE A u δ X →
          QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
              (QMCLeafB.SepOracle.castMat Q)
            ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM) X) := by
  have hsub : ∀ X : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
          (X - QMCLeafB.SepOracle.castMat Q)
        = QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM) X
          - QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
            (QMCLeafB.SepOracle.castMat Q) :=
    fun X => QMCLeafB.SepOracle.frob_sub _ _ _
  constructor
  · intro h X hX
    have h1 := h X hX
    rw [hsub X] at h1
    have h0 : (-(((0 : ℚ)) : ℝ)) = 0 := by norm_num
    rw [h0] at h1
    linarith
  · intro h X hX
    have h1 := h X hX
    rw [hsub X]
    have h0 : (-(((0 : ℚ)) : ℝ)) = 0 := by norm_num
    rw [h0]
    linarith

#print axioms QMCLeafB.CeilingM3.hbody_iff_support_le

/-! ## 2.  The body's trace floor, and the ceiling as a sufficient condition -/

/-- **The body's trace floor**: every point of the relaxed body has trace `≥ n(1 − δ/4)`. -/
theorem body_trace_ge {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : QMCLeafB.BallFloor.relaxBodyLE A u δ X) :
    (n : ℝ) * (1 - δ / 4) ≤ ∑ i, X i i := by
  have h : ∀ i : Fin n, 1 - δ / 4 ≤ X i i := fun i => by
    have h1 := (abs_le.mp (hX.2.1 i)).1
    linarith
  calc (n : ℝ) * (1 - δ / 4) = ∑ _i : Fin n, (1 - δ / 4) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ i, X i i := Finset.sum_le_sum fun i _ => h i

#print axioms QMCLeafB.CeilingM3.body_trace_ge


/-- **The ceiling suffices for `hbody`** in the identity direction (the site every consumer of
`hTrc` goes through; the same statement as `DriftExact.hbody_of_trace`, restated in trace-floor
form so that §3/§4 can compare it with the floor).  Statement at `ℝ` traces (`δ : ℝ`). -/
theorem ceiling_gives_hbody {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ}
    {Q : Matrix (Fin n) (Fin n) ℚ}
    (hTrc : (∑ i, ((Q i i : ℚ) : ℝ)) ≤ (n : ℝ) * (1 - δ / 4)) :
    ∀ X : Matrix (Fin n) (Fin n) ℝ, QMCLeafB.BallFloor.relaxBodyLE A u δ X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob
        (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ))
        (X - QMCLeafB.SepOracle.castMat Q) := by
  refine (hbody_iff_trace n A u δ Q).2 (fun X hX => ?_)
  have hfloor := body_trace_ge hX
  linarith

#print axioms QMCLeafB.CeilingM3.ceiling_gives_hbody

/-! ## 3.  The pinched point

The campaign's ceiling is attained by the diagonal-overwritten point `(1 − δ/4)•1`.  That point is
the exact witness for §4: whenever it is feasible, the ceiling cannot be moved. -/

/-- The pinched point `(1 − δ/4) • 1`. -/
def pinchPt (n : ℕ) (δ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 - δ / 4) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- The pinched point's trace is exactly the ceiling value. -/
theorem pinchPt_trace (n : ℕ) (δ : ℝ) :
    ∑ i, pinchPt n δ i i = (n : ℝ) * (1 - δ / 4) := by
  have hdiag : ∀ i : Fin n, pinchPt n δ i i = 1 - δ / 4 := by
    intro i
    simp [pinchPt]
  calc ∑ i, pinchPt n δ i i = ∑ _i : Fin n, (1 - δ / 4) := Finset.sum_congr rfl fun i _ => hdiag i
    _ = (n : ℝ) * (1 - δ / 4) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

#print axioms QMCLeafB.CeilingM3.pinchPt_trace

/-- The pairing of a scalar multiple of the identity against `A` is that scalar times `tr A`. -/
theorem frob_smul_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    QMCLeafB.SepOracle.frob A (c • (1 : Matrix (Fin n) (Fin n) ℝ)) = c * ∑ i, A i i := by
  rw [QMCLeafB.SepOracle.frob]
  have hinner : ∀ i : Fin n, ∑ j, A i j * (c • (1 : Matrix (Fin n) (Fin n) ℝ)) i j
      = c * A i i := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp [Matrix.smul_apply, mul_comm]
    · intro j _ hj
      simp [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hj)]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  calc ∑ i, ∑ j, A i j * (c • (1 : Matrix (Fin n) (Fin n) ℝ)) i j
      = ∑ i, c * A i i := Finset.sum_congr rfl fun i _ => hinner i
    _ = c * ∑ i, A i i := by rw [Finset.mul_sum]

#print axioms QMCLeafB.CeilingM3.frob_smul_one

/-- **The pinched point is in the body** whenever its objective passes: this is the cheapest
inhabitant of the relaxed body, and it sits exactly on the ceiling's trace. -/
theorem pinchPt_mem {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ}
    (hδ : 0 ≤ δ) (hobj : (1 - δ / 4) * ∑ i, A i i ≤ u + δ / 2) :
    QMCLeafB.BallFloor.relaxBodyLE A u δ (pinchPt n δ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hnn : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hqf : QMCLeafB.BallFloor.qfR (pinchPt n δ) x = (1 - δ / 4) * ∑ i, x i ^ 2 := by
      rw [QMCLeafB.BallFloor.qfR, pinchPt, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      congr 1
      rw [Matrix.one_mulVec]
      simp [dotProduct, pow_two]
    rw [hqf]
    nlinarith
  · intro i
    have hdiag : pinchPt n δ i i = 1 - δ / 4 := by simp [pinchPt]
    rw [hdiag, show (1 - δ / 4) - 1 = -(δ / 4) by ring, abs_neg,
      abs_of_nonneg (by linarith)]
  · show QMCLeafB.SepOracle.frob A ((1 - δ / 4) • (1 : Matrix (Fin n) (Fin n) ℝ)) ≤ u + δ / 2
    rw [frob_smul_one]
    exact hobj

#print axioms QMCLeafB.CeilingM3.pinchPt_mem

/-! ## 4.  The ceiling is the body's floor: no widening at `dM = 1`

This is the machine-checked half of the ledger: with the pinched point feasible, `hbody` at the
identity direction **is** `tr Q ≤ n(1 − δ/4)`.  So the constant cannot be raised: a raised constant
makes `hbody` false at a legal centre, and `hbody` is exactly what the drift assembly consumes. -/

/-- **The ceiling is exact** (given the pinched point is in the body). -/
theorem ceiling_exact {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ} {Q : Matrix (Fin n) (Fin n) ℚ}
    (hδ : 0 ≤ δ) (hobj : (1 - δ / 4) * ∑ i, A i i ≤ u + δ / 2) :
    (∀ X : Matrix (Fin n) (Fin n) ℝ, QMCLeafB.BallFloor.relaxBodyLE A u δ X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob
        (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ))
        (X - QMCLeafB.SepOracle.castMat Q))
      ↔ ((∑ i, ((Q i i : ℚ) : ℝ)) ≤ (n : ℝ) * (1 - δ / 4)) := by
  constructor
  · intro h
    have h1 := ((hbody_iff_trace n A u δ Q).1 h) (pinchPt n δ) (pinchPt_mem hδ hobj)
    rw [pinchPt_trace] at h1
    exact h1
  · intro hTrc
    exact ceiling_gives_hbody (A := A) (u := u) (δ := δ) hTrc

#print axioms QMCLeafB.CeilingM3.ceiling_exact

/-- **The ceiling cannot be widened** at `dM = 1` with the campaign body: any centre whose trace
exceeds `n(1 − δ/4)` (in particular one at a widened ceiling) violates `hbody`, hence the drift
assembly's `hbody` slot. -/
theorem ceiling_not_widenable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ}
    {Q : Matrix (Fin n) (Fin n) ℚ} (hδ : 0 ≤ δ)
    (hobj : (1 - δ / 4) * ∑ i, A i i ≤ u + δ / 2) (σ : ℝ) (hσ : 0 < σ)
    (hQ : (n : ℝ) * (1 - δ / 4) + σ ≤ ∑ i, ((Q i i : ℚ) : ℝ)) :
    ¬ (∀ X : Matrix (Fin n) (Fin n) ℝ, QMCLeafB.BallFloor.relaxBodyLE A u δ X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob
        (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ))
        (X - QMCLeafB.SepOracle.castMat Q)) := by
  intro h
  have h1 := (ceiling_exact hδ hobj).1 h
  linarith

#print axioms QMCLeafB.CeilingM3.ceiling_not_widenable

/-! ## 5.  An empty body releases the ceiling entirely

The ceiling's only role in the assembly is `hbody` (§8 of the ledger: it is the *sole* consumer).
At a refuted point whose relaxed body is empty, `hbody` is vacuous in every direction — so the
ceiling carries no analytic content there, and a producer may put the queried centre anywhere. -/

/-- **`hbody` is free at an empty body** — in every dilation direction, at every centre. -/
theorem hbody_of_empty {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ}
    (hempty : ∀ X : Matrix (Fin n) (Fin n) ℝ, ¬ QMCLeafB.BallFloor.relaxBodyLE A u δ X)
    (dM : Matrix (Fin n) (Fin n) ℚ) (Q : Matrix (Fin n) (Fin n) ℚ) :
    ∀ X : Matrix (Fin n) (Fin n) ℝ, QMCLeafB.BallFloor.relaxBodyLE A u δ X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob
        (QMCLeafB.SepOracle.castMat dM) (X - QMCLeafB.SepOracle.castMat Q) :=
  fun X hX => absurd hX (hempty X)

#print axioms QMCLeafB.CeilingM3.hbody_of_empty

/-- **The same at the campaign's body** (the shape the drift slot uses): if no real point of the
relaxed body exists, the `hbody` slot of `RunPartsDilate.runParts_of_dilated` holds at every round
with no trace condition on the centre stream. -/
theorem hbody_campaign_of_empty (G : QuantumMaxCutEnergy.Input) (t : ℚ) (dq : ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hempty : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G))
        (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ) ((dq : ℚ) : ℝ) X)
    (dM : Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) (hok : (fun _ => false : ℕ → Bool) k = false) :
    ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G))
        (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ) ((dq : ℚ) : ℝ) X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
        (X - QMCLeafB.SepOracle.castMat (cX k)) :=
  hbody_of_empty hempty dM (cX k)

#print axioms QMCLeafB.CeilingM3.hbody_campaign_of_empty

/-- **The ceiling is strictly stronger than what the assembly consumes at an empty body.**  There
`hbody` holds in the identity direction for every centre, including centres whose trace is far above
`n(1 − δ/4)`: so replacing the `hTrc` slot by `hbody` is a genuine relaxation, not a re-spelling, and
it removes exactly the inequality m8's drill refutes. -/
theorem hbody_not_ceiling_of_empty {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ}
    (hempty : ∀ X : Matrix (Fin n) (Fin n) ℝ, ¬ QMCLeafB.BallFloor.relaxBodyLE A u δ X)
    (Q : Matrix (Fin n) (Fin n) ℚ)
    (hbig : (n : ℝ) * (1 - δ / 4) < ∑ i, ((Q i i : ℚ) : ℝ)) :
    (∀ X : Matrix (Fin n) (Fin n) ℝ, QMCLeafB.BallFloor.relaxBodyLE A u δ X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob
        (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ))
        (X - QMCLeafB.SepOracle.castMat Q))
      ∧ ¬ ((∑ i, ((Q i i : ℚ) : ℝ)) ≤ (n : ℝ) * (1 - δ / 4)) := by
  exact ⟨hbody_of_empty hempty _ Q, fun hle => absurd hle (not_le.mpr hbig)⟩

#print axioms QMCLeafB.CeilingM3.hbody_not_ceiling_of_empty

/-! ## 6.  The second tight site: a member on the ceiling is *on the boundary*

`hTrc` plus a member certificate force the centre's diagonal to `1 − δ/4` entry by entry (m1's
pinch).  This is why the ceiling cannot simply be deleted where the body is non-empty: it is what
turns membership into the boundary form the ok-branch certificates are stated at. -/

/-- **`hTrc` + `RelaxMem` ⟹ the diagonal is the boundary value.** -/
theorem member_diag_eq_of_ceiling {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hm : QMCLeafB.RelaxOracle.RelaxMem A Q u δ)
    (htr : (∑ i, Q i i) ≤ (n : ℚ) * (1 - δ / 4)) :
    ∀ i, Q i i = 1 - δ / 4 := by
  have hge : ∀ i : Fin n, 1 - δ / 4 ≤ Q i i := fun i => by
    have h1 := (abs_le.mp (hm.diag_near i)).1
    linarith
  have hconst : (∑ _i : Fin n, (1 - δ / 4)) = (n : ℚ) * (1 - δ / 4) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum_ge : (n : ℚ) * (1 - δ / 4) ≤ ∑ i, Q i i := by
    rw [← hconst]
    exact Finset.sum_le_sum fun i _ => hge i
  have heq : (∑ _i : Fin n, (1 - δ / 4)) = ∑ i, Q i i := by
    rw [hconst]
    linarith
  intro i
  exact ((Finset.sum_eq_sum_iff_of_le (fun j _ => hge j)).1 heq i (Finset.mem_univ i)).symm

#print axioms QMCLeafB.CeilingM3.member_diag_eq_of_ceiling

/-! ## 7.  Producer side: the campaign's own centres sit exactly on the ceiling

`cXst n X dq k = diagPinch (stMat n (X k)) dq`: the diagonal of the coded state is *overwritten*
with the pinch value, so `hTrc` holds with **equality** at every round and with no hypothesis at all.
That is the ceiling's true source in this campaign — not an estimate but a definition, which is why
"widening the ceiling" is a change of the centre family, and why m8's kill bites the shape. -/

/-- The campaign's centre family attains the ceiling with equality (from `RecordsM2`). -/
theorem ceiling_attained_cXst (n : ℕ) (X : ℕ → List ℚ) (dq : ℚ) (k : ℕ) :
    (∑ i, QMCLeafB.RecordsM2.cXst n X dq k i i) = (n : ℚ) * (1 - dq / 4) :=
  QMCLeafB.RecordsM2.cXst_trace n X dq k

#print axioms QMCLeafB.CeilingM3.ceiling_attained_cXst

/-- The pinch overwrite itself attains the ceiling with equality, for every base state. -/
theorem ceiling_attained_diagPinch {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (dq : ℚ) :
    (∑ i, QMCLeafB.CentreAdm.diagPinch Q dq i i) = (n : ℚ) * (1 - dq / 4) :=
  QMCLeafB.CentreAdm.sum_diagPinch Q dq

#print axioms QMCLeafB.CeilingM3.ceiling_attained_diagPinch

/-- **No slack at any round**: the campaign's centre family does not sit *under* the ceiling, it sits
on it. -/
theorem ceiling_no_slack_cXst (n : ℕ) (X : ℕ → List ℚ) (dq : ℚ) (k : ℕ) :
    ¬ ((∑ i, QMCLeafB.RecordsM2.cXst n X dq k i i) < (n : ℚ) * (1 - dq / 4)) := by
  rw [ceiling_attained_cXst n X dq k]
  exact lt_irrefl _

#print axioms QMCLeafB.CeilingM3.ceiling_no_slack_cXst

/-- **`hdriftd` at the campaign's centres is exactly m8's killed inequality.**  With the centre on
the ceiling, the identity-direction drift budget says `diagSum (Cat k) ≤ n(1 − dq/4)` — no room is
left by the shape, whatever the stream. -/
theorem driftd_at_cXst_iff (n : ℕ) (dq : ℚ)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n)) (X : ℕ → List ℚ) (k : ℕ) :
    (QMCLeafB.RunPartsStream.dOne n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (QMCLeafB.RecordsM2.cXst n X dq k))) ≤ 0)
      ↔ QMCLeafB.DriftExact.diagSum
          (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k)
        ≤ (n : ℝ) * (1 - ((dq : ℚ) : ℝ) / 4) := by
  rw [QMCLeafB.DriftExact.stated_iff_trace]
  have hcast : (∑ i, ((QMCLeafB.RecordsM2.cXst n X dq k i i : ℚ) : ℝ))
      = (n : ℝ) * (1 - ((dq : ℚ) : ℝ) / 4) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (ceiling_attained_cXst n X dq k)
    push_cast at h
    simpa using h
  rw [hcast]

#print axioms QMCLeafB.CeilingM3.driftd_at_cXst_iff

/-! ## 8.  The composition the cone consumes

`hTrc` + `hdriftd` give the engine's own trace budget — the single number every window record
forces (`ResidBundle_M7.window_forces_engine_trace`), and the one m8 refutes with the drill.  Kept
here in the general `ℚ`-matrix form so that the ledger is self-contained. -/

/-- **The engine centre's trace under the ceiling.** -/
theorem engine_trace_of_ceiling (n : ℕ) (dq : ℚ)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n))
    (Y : Matrix (Fin n) (Fin n) ℚ) (k : ℕ)
    (h : QMCLeafB.RunPartsStream.dOne n
      ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
        - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Y)) ≤ 0)
    (htr : (∑ i, Y i i) ≤ (n : ℚ) * (1 - dq / 4)) :
    QMCLeafB.DriftExact.diagSum
        (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k)
      ≤ (n : ℝ) * (1 - ((dq : ℚ) : ℝ) / 4) := by
  have h1 := QMCLeafB.DriftExact.trace_budget_of_drift (n := n) cd Y k h
  rw [QMCLeafB.DriftExact.diagSum_cat]
  have hcast : (∑ i, ((Y i i : ℚ) : ℝ)) ≤ (n : ℝ) * (1 - ((dq : ℚ) : ℝ) / 4) := by
    have := htr
    have h2 : (((n : ℚ) * (1 - dq / 4) : ℚ) : ℝ) = (n : ℝ) * (1 - ((dq : ℚ) : ℝ) / 4) := by
      push_cast; ring
    have h3 : (∑ i, ((Y i i : ℚ) : ℝ)) = ((∑ i, Y i i : ℚ) : ℝ) := by push_cast; ring
    rw [h3]
    calc ((∑ i, Y i i : ℚ) : ℝ) ≤ (((n : ℚ) * (1 - dq / 4) : ℚ) : ℝ) := by exact_mod_cast htr
      _ = (n : ℝ) * (1 - ((dq : ℚ) : ℝ) / 4) := h2
  linarith

#print axioms QMCLeafB.CeilingM3.engine_trace_of_ceiling

end QMCLeafB.CeilingM3


