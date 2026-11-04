-- Prove2me | Definitions.Def_QMCLeafB_triobstruction_m5
-- name    : QMCLeafB_triobstruction_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:13:20.594207+00:00
-- url     : https://prove2.me/theorems/59a48e16-75d8-4f6a-8fd7-ee6f0fd1951d
-- title:
--   QMCLeafB triobstruction_m5
-- statement:
--   # leaf B phase 18 — brick `triobstruction` (swarm `smw1i2drp`, member m5, direction d5)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_drift_m3
import Definitions.Def_QMCLeafB_unionShallow
/-
# leaf B phase 18 — brick `triobstruction` (swarm `smw1i2drp`, member m5, direction d5)

`Check_inhabit_m5.lean` shows the last two residuals are *inhabited*: at the two-vertex
one-edge instance the whole `RunParts` bundle is realised by an all-`ok` run (centres at the
pinch boundary `(1 - dq/4) • Q₀`).  This file proves that the all-`ok` route is **not** a general
route — so the `RelaxCut` half of the residual (item 1) is genuinely load-bearing.

The mechanics.  `RunParts.hcert` asks, at every `ok` round and threshold `t`, for a unit-diagonal
PSD matrix `X` with

    trace(wMatrix G · X) ≤ t + eps G.

For the triangle graph `Gtri` (n = 3, every edge of weight 1) the left side has a hard floor:

    trace(wMatrix Gtri · X) ≥ -3 = -Rq Gtri / 2      (for every unit-diagonal PSD X),

because `wMatrix Gtri = J - 1` and, for a PSD `X` with unit diagonal,
`0 ≤ 1 ⬝ᵥ (X *ᵥ 1) = ∑ᵢ ∑ⱼ Xᵢⱼ` gives `∑ᵢ≠ⱼ Xᵢⱼ = ∑ᵢⱼ Xᵢⱼ - 3 ≥ -3`; the bound is attained at
`X = (3·1 - J)/2`, so it is sharp.  Hence for every `t < -Rq/2 - eps` (the whole lower half of the
interior bracket `[-Rq, -eps)`) **no `ok` round can certify**, and since `anyOk` is a disjunction
of the flags, `hverdict` forces the verdict bit to be `false`:

* §1 `Rq_Gtri = 6`, `wMatrix Gtri = J - 1`, `trace_ge` — the arithmetic and the floor.
* §2 `no_ok_cert_below` — no unit-diag PSD certificate under `-3`.
* §3 `anyOk_true_iff` — `anyOk ok N = true ↔ ∃ k < N, ok k = true`.
* §4 `no_true_verdict_below` / `no_true_verdict_half` — **every** `RunParts` at the triangle with
  `t < -Rq/2 - eps` has `o Gtri t = false`.
* §5 the complement: in the same range the relaxed body at the triangle is **empty**
  (`body_empty_below`, with the `9δ/4` tolerance bookkeeping), and an empty body gives the whole
  `RelaxCut` record for free (`relaxCut_of_empty`, `relaxCut_Gtri_below`: any normal, margin `1`).

Consequence for the swarm: at `n = 2` the relaxation's optimum is `-Rq`, which is what makes the
interior `ok` certificate available (`Check_inhabit_m5`); at the triangle the lower interior bracket
is certificate-free, so the run *must* cut there and the `RelaxCut` lane (item 1's cut half) is the
only way through.  The same computation gives the floor `-n·w = -Rq/(n-1)` on the uniform complete
graph `K_n`, so the effect is not an artefact of `n = 3`; what is special to the two-vertex
instance is that its floor equals `-Rq` exactly.  At graphs where the floor sits above `-Rq/2` the
crux of the residual is therefore `hlam2` (the dilated-cut cost) together with the drift pair, not
`hcert`.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; axiom audits at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.TriObstructionM5

open QuantumMaxCutEnergy

/-! ## 1.  The triangle graph: scale, weight matrix, and the trace floor -/

/-- The triangle: three vertices, every edge of weight `1`. -/
def Gtri : QuantumMaxCutEnergy.Input := ⟨3, fun _ => 1⟩

instance : NeZero Gtri.n := ⟨by decide⟩

/-- The all-ones matrix. -/
def Jm : Matrix (Fin Gtri.n) (Fin Gtri.n) ℝ := Matrix.of (fun _ _ => 1)

/-- The campaign's energy scale at the triangle: `Rq = 2·3 = 6`. -/
theorem Rq_Gtri : QMCLeafB.EngineRuntime.Rq Gtri = 6 := by
  have hcard : Fintype.card (QuantumMaxCutEnergy.Edge 3) = 3 := by decide
  have h1 : ∀ e : QuantumMaxCutEnergy.Edge 3, ((Gtri.weights e : ℚ≥0) : ℚ) = 1 := fun _ => rfl
  have h : (∑ e : QuantumMaxCutEnergy.Edge 3, ((Gtri.weights e : ℚ≥0) : ℚ)) = 3 := by
    simp only [h1]
    rw [Finset.sum_const, Finset.card_univ, hcard]
    norm_num
  show 2 * (∑ e : QuantumMaxCutEnergy.Edge 3, ((Gtri.weights e : ℚ≥0) : ℚ)) = 6
  rw [h]
  norm_num

/-- The entries of the triangle's weight matrix: `0` on the diagonal, `1` off it. -/
theorem wMatrix_Gtri_apply (i j : Fin Gtri.n) :
    QMCLeafB.wMatrix Gtri i j = (if i = j then (0 : ℝ) else 1) := by
  rw [QMCLeafB.wMatrix, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp [Gtri]

/-- **The weight matrix of the triangle is `J - 1`.** -/
theorem wMatrix_Gtri : QMCLeafB.wMatrix Gtri = Jm - 1 := by
  ext i j
  rw [wMatrix_Gtri_apply]
  simp only [Jm, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

/-- The quadratic form of a PSD matrix at the all-ones vector is nonnegative. -/
theorem sum_nonneg_of_psd (X : Matrix (Fin Gtri.n) (Fin Gtri.n) ℝ) (hX : X.PosSemidef) :
    0 ≤ ∑ i, ∑ j, X i j := by
  have h := hX.dotProduct_mulVec_nonneg (fun _ : Fin Gtri.n => (1 : ℝ))
  simpa [dotProduct, Matrix.mulVec, Matrix.cons_val', RCLike.star_def] using h

/-- **The trace floor at the triangle**: every unit-diagonal PSD point pairs to at least
`-3 = -Rq Gtri / 2`. -/
theorem trace_ge (X : Matrix (Fin Gtri.n) (Fin Gtri.n) ℝ)
    (hX : X.PosSemidef) (hdiag : ∀ i, X i i = 1) :
    -3 ≤ (QMCLeafB.wMatrix Gtri * X).trace := by
  have hsum := sum_nonneg_of_psd X hX
  have hcard : Fintype.card (Fin Gtri.n) = 3 := by
    show Fintype.card (Fin 3) = 3
    simp
  have htrX : X.trace = 3 := by
    simp only [Matrix.trace, Matrix.diag_apply, hdiag]
    rw [Finset.sum_const, Finset.card_univ, hcard]
    norm_num
  have htr : (Jm * X).trace = ∑ i, ∑ j, X i j := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Jm, Matrix.of_apply, one_mul]
    rw [Finset.sum_comm]
  rw [wMatrix_Gtri, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, htrX, htr]
  linarith

/-! ## 2.  No `ok` certificate in the lower interior bracket -/

/-- **No unit-diagonal PSD certificate below `-3`.**  This is the obstruction that blocks the
`ok` branch at the triangle: `hcert` at threshold `t` demands a point under `t + eps`. -/
theorem no_ok_cert_below (t : ℚ)
    (ht : (t : ℝ) + ((QMCLeafB.RundataCert.eps Gtri : ℚ) : ℝ) < -3)
    (X : Matrix (Fin Gtri.n) (Fin Gtri.n) ℝ)
    (hX : QMCLeafB.AnswerProducer.IsUnitDiagPSD X)
    (hle : (QMCLeafB.wMatrix Gtri * X).trace
      ≤ (t : ℝ) + ((QMCLeafB.RundataCert.eps Gtri : ℚ) : ℝ)) : False := by
  have h1 := trace_ge X hX.1 hX.2
  linarith

/-! ## 3.  `anyOk` is a disjunction of the flags -/

theorem anyOk_true_iff (ok : ℕ → Bool) : ∀ N : ℕ,
    QMCLeafB.SimLoop.anyOk ok N = true ↔ ∃ k, k < N ∧ ok k = true
  | 0 => by
      constructor
      · intro h
        simp [QMCLeafB.SimLoop.anyOk] at h
      · rintro ⟨k, hk, _⟩
        omega
  | (n + 1) => by
      rw [QMCLeafB.SimLoop.anyOk_succ, Bool.or_eq_true]
      constructor
      · rintro (h | h)
        · exact ⟨n, Nat.lt_succ_self n, h⟩
        · obtain ⟨k, hk, hok⟩ := (anyOk_true_iff ok n).1 h
          exact ⟨k, Nat.lt_succ_of_lt hk, hok⟩
      · rintro ⟨k, hk, hok⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h' | h'
        · exact Or.inr ((anyOk_true_iff ok n).2 ⟨k, h', hok⟩)
        · exact Or.inl (h' ▸ hok)

/-! ## 4.  The verdict at the triangle is forced to `false` -/

/-- **The `ok` route is dead at the triangle.**  Every `RunParts` whose threshold is below
`-3 - eps = -Rq/2 - eps` has verdict bit `false`: a `true` verdict would exhibit one `ok` round,
and that round's `hcert` would contradict the trace floor. -/
theorem no_true_verdict_below (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (t : ℚ)
    (ht : (t : ℝ) + ((QMCLeafB.RundataCert.eps Gtri : ℚ) : ℝ) < -3)
    (B : QMCLeafB.FinalStroke.RunParts o Gtri t (QMCLeafB.UnionShallow.paramsKbc2 Gtri)) :
    o Gtri t = false := by
  rcases Bool.eq_false_or_eq_true (o Gtri t) with h | h
  · exfalso
    rw [B.hverdict] at h
    obtain ⟨k, hk, hok⟩ := (anyOk_true_iff B.ok _).1 h
    obtain ⟨X, hX, hle⟩ := B.hcert k hk hok
    exact no_ok_cert_below t ht X hX hle
  · exact h

/-- The same statement in the bracket's own units: every `RunParts` at the triangle with
`t < -Rq Gtri / 2 - eps` has verdict bit `false`. -/
theorem no_true_verdict_half (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (t : ℚ)
    (ht : t < -(QMCLeafB.EngineRuntime.Rq Gtri) / 2 - QMCLeafB.RundataCert.eps Gtri)
    (B : QMCLeafB.FinalStroke.RunParts o Gtri t (QMCLeafB.UnionShallow.paramsKbc2 Gtri)) :
    o Gtri t = false := by
  refine no_true_verdict_below o t ?_ B
  have h1 : (t : ℝ) < ((-(QMCLeafB.EngineRuntime.Rq Gtri) / 2
      - QMCLeafB.RundataCert.eps Gtri : ℚ) : ℝ) := by exact_mod_cast ht
  have h2 : ((-(QMCLeafB.EngineRuntime.Rq Gtri) / 2
      - QMCLeafB.RundataCert.eps Gtri : ℚ) : ℝ)
      = -(6 : ℝ) / 2 - ((QMCLeafB.RundataCert.eps Gtri : ℚ) : ℝ) := by
    rw [Rq_Gtri]
    push_cast
    ring
  rw [h2] at h1
  linarith

/-- The `ok`-branch certificate is unavailable on the whole lower half of the interior bracket. -/
theorem no_cert_half (t : ℚ)
    (ht : t < -(QMCLeafB.EngineRuntime.Rq Gtri) / 2 - QMCLeafB.RundataCert.eps Gtri) :
    ¬ ∃ X : Matrix (Fin Gtri.n) (Fin Gtri.n) ℝ,
        QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix Gtri * X).trace
            ≤ (t : ℝ) + ((QMCLeafB.RundataCert.eps Gtri : ℚ) : ℝ) := by
  rintro ⟨X, hX, hle⟩
  refine no_ok_cert_below t ?_ X hX hle
  have h1 : (t : ℝ) < ((-(QMCLeafB.EngineRuntime.Rq Gtri) / 2
      - QMCLeafB.RundataCert.eps Gtri : ℚ) : ℝ) := by exact_mod_cast ht
  have h2 : ((-(QMCLeafB.EngineRuntime.Rq Gtri) / 2
      - QMCLeafB.RundataCert.eps Gtri : ℚ) : ℝ)
      = -(6 : ℝ) / 2 - ((QMCLeafB.RundataCert.eps Gtri : ℚ) : ℝ) := by
    rw [Rq_Gtri]
    push_cast
    ring
  rw [h2] at h1
  linarith

/-! ## 5.  Where the body is empty, the cut record is free

The complement of §4: the obstruction empties the relaxed body in the same range, and an empty body
makes the whole `RelaxCut` record (item 1's cut-round certificate) *inhabited for free* — any
normal, margin `1`.  So at the triangle the residual's crux is the dilated-cut cost `hlam2`, not
the cut separation. -/

/-- **An empty relaxed body yields a `RelaxCut` record for free.** -/
theorem relaxCut_of_empty {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) {u δ : ℚ}
    (hempty : ∀ X : Matrix (Fin n) (Fin n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
        ((δ : ℚ) : ℝ) X) :
    Nonempty (QMCLeafB.RelaxOracle.RelaxCut A cX u δ) :=
  ⟨{ normal := 1, margin := 1, margin_pos := by norm_num,
     separates := fun X hX => absurd hX (hempty X) }⟩

/-- The rational weight matrix casts to the real one at the triangle. -/
theorem castMat_wMatrixQ_Gtri :
    QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ Gtri) = QMCLeafB.wMatrix Gtri := by
  ext i j
  rw [QMCLeafB.wMatrix, Matrix.of_apply]
  simp only [QMCLeafB.SepOracle.castMat]
  fin_cases i <;> fin_cases j <;> simp [Gtri]

/-- **The relaxed body at the triangle is empty below `-3`** (with the tolerance bookkeeping):
for `0 ≤ δ`, no point has `trace(wMatrix Gtri · X) ≤ u + δ/2` when `u + δ/2 < -3 - 9δ/4`. -/
theorem body_empty_below (u δ : ℝ) (hδ : 0 ≤ δ) (hu : u + δ / 2 < -3 - 9 * δ / 4)
    (X : Matrix (Fin Gtri.n) (Fin Gtri.n) ℝ)
    (hX : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix Gtri) u δ X) : False := by
  obtain ⟨hpsd, hdiag, hfr⟩ := hX
  have hcard : Fintype.card (Fin Gtri.n) = 3 := by
    show Fintype.card (Fin 3) = 3
    simp
  -- the relaxed quadratic form at the all-ones vector
  have hsum : -3 * δ / 2 ≤ ∑ i, ∑ j, X i j := by
    have h := hpsd (fun _ : Fin Gtri.n => (1 : ℝ))
    have hsq : ∑ i : Fin Gtri.n, ((1 : ℝ)) ^ 2 = 3 := by
      simp [hcard]
    have hqf : QMCLeafB.BallFloor.qfR X (fun _ : Fin Gtri.n => (1 : ℝ)) = ∑ i, ∑ j, X i j := by
      simp [QMCLeafB.BallFloor.qfR, dotProduct, Matrix.mulVec, Matrix.cons_val']
    rw [hsq, hqf] at h
    linarith
  -- the diagonal ledger
  have htrX : ∑ i, X i i ≤ 3 + 3 * δ / 4 := by
    have h1 : ∀ i : Fin Gtri.n, X i i ≤ 1 + δ / 4 := by
      intro i
      have h2 := hdiag i
      rw [abs_le] at h2
      linarith [h2.2]
    have h4 : ∑ i : Fin Gtri.n, X i i ≤ ∑ _i : Fin Gtri.n, (1 + δ / 4) :=
      Finset.sum_le_sum (fun i _ => h1 i)
    have h5 : ∑ _i : Fin Gtri.n, (1 + δ / 4) = 3 + 3 * δ / 4 := by
      rw [Finset.sum_const, Finset.card_univ, hcard]
      norm_num
      ring
    linarith
  -- the pairing decomposes as `∑∑ X - ∑ᵢ Xᵢᵢ`
  have hfrob : QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix Gtri) X
      = (∑ i, ∑ j, X i j) - ∑ i, X i i := by
    rw [wMatrix_Gtri]
    simp only [QMCLeafB.BallFloor.frob]
    have step : ∀ i : Fin Gtri.n,
        (∑ j, (Jm - 1) i j * X i j) = (∑ j, X i j) - X i i := by
      intro i
      have h : ∀ j : Fin Gtri.n,
          (Jm - 1) i j * X i j = X i j - (if i = j then X i j else 0) := by
        intro j
        simp only [Jm, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply]
        by_cases hh : i = j <;> simp [hh]
      rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_sub_distrib]
      have h2 : (∑ j, (if i = j then X i j else 0)) = X i i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [Ne.symm hb]
        · intro hmem
          exact absurd (Finset.mem_univ i) hmem
      rw [h2]
    rw [Finset.sum_congr rfl (fun i _ => step i), Finset.sum_sub_distrib]
  rw [hfrob] at hfr
  linarith

/-- The oracle tolerance is positive at the triangle. -/
theorem dq_Gtri_pos : 0 < (QMCLeafB.UnionShallow.paramsKbc2 Gtri).dq := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
  exact QMCLeafB.RundataParams.dqShallow_pos Gtri

/-- **The cut record is free at the triangle below `-Rq/2`**: for any threshold in the range where
the body is empty, every rational centre `cX` carries a `RelaxCut` certificate. -/
theorem relaxCut_Gtri_below (t : ℚ)
    (ht : ((t - QMCLeafB.RundataCert.eps Gtri : ℚ) : ℝ)
        + (((QMCLeafB.UnionShallow.paramsKbc2 Gtri).dq : ℚ) : ℝ) / 2
      < -3 - 9 * (((QMCLeafB.UnionShallow.paramsKbc2 Gtri).dq : ℚ) : ℝ) / 4)
    (cX : Matrix (Fin Gtri.n) (Fin Gtri.n) ℚ) :
    Nonempty (QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ Gtri) cX
      (t - QMCLeafB.RundataCert.eps Gtri) (QMCLeafB.UnionShallow.paramsKbc2 Gtri).dq) := by
  refine relaxCut_of_empty _ cX ?_
  intro X hX
  rw [castMat_wMatrixQ_Gtri] at hX
  exact body_empty_below _ _ (by exact_mod_cast dq_Gtri_pos.le) ht X hX

end QMCLeafB.TriObstructionM5

/-! ## Axiom audit -/

#print axioms QMCLeafB.TriObstructionM5.Rq_Gtri
#print axioms QMCLeafB.TriObstructionM5.wMatrix_Gtri
#print axioms QMCLeafB.TriObstructionM5.trace_ge
#print axioms QMCLeafB.TriObstructionM5.no_ok_cert_below
#print axioms QMCLeafB.TriObstructionM5.anyOk_true_iff
#print axioms QMCLeafB.TriObstructionM5.no_true_verdict_below
#print axioms QMCLeafB.TriObstructionM5.no_true_verdict_half
#print axioms QMCLeafB.TriObstructionM5.no_cert_half
#print axioms QMCLeafB.TriObstructionM5.relaxCut_of_empty
#print axioms QMCLeafB.TriObstructionM5.castMat_wMatrixQ_Gtri
#print axioms QMCLeafB.TriObstructionM5.body_empty_below
#print axioms QMCLeafB.TriObstructionM5.relaxCut_Gtri_below


