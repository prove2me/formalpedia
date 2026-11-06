-- Prove2me | Definitions.Def_QMCLeafB_by35
-- name    : QMCLeafB_by35
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:46:03.582538+00:00
-- url     : https://prove2.me/theorems/9ceed111-f9a8-4d2d-a712-3c7684e2b435
-- title:
--   QMCLeafB by35
-- statement:
--   # `Check_by35_m6` — `ShallowCut` is a separation problem, not a depth problem
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thinrec34
/-
# `Check_by35_m6` — `ShallowCut` is a separation problem, not a depth problem

Phase 35, member m6, direction d8 (`bypass35 / irreducibility`).

The campaign's one analytic obligation (`ThinRec34M4.ShallowCut`, m4/ph34-d5) asks, at every round
`k < K·m`, for a nonzero rational normal `c k` and a depth `del k ≥ 0` with

    (del k)^2 ≤ rmax^2 * sigmaQ (c k) (p k)        and        c k · Cat k − c k · z ≤ del k   (all z in the relaxation),

where `p k = A_k⁻¹ c k` is the engine's own witness.  The handover reads this as a *depth* claim:
Cauchy–Schwarz bounds the violation by `√sigmaQ`, while the ledger caps the recorded depth at
`rmax·√sigmaQ` with `rmax < 1`.  This file shows the depth reading is avoidable, and decides the
obligation's shape:

**§3–§4 — the ledger is free at zero depth.**  For ANY nonzero rational normal stream the engine's
`sig_k = sigmaQ (c k) (p k)` is strictly positive (`sigmaQ_normalCut_pos`: the iterate stays positive
definite and `A_k p_k = c_k`), so `del ≡ 0` passes the squared depth check *structurally* —
`0 ≤ rmax^2·sig_k` — whatever `rmax` is.  What remains is the *separation* clause alone:

* `shallowCut_of_separating`: if the stream's own normal puts the accumulated centre on the far side
  of the WHOLE relaxation at every round (`c k ⬝ Cat k ≤ c k ⬝ z` for all body points `z`), then
  `ShallowCut` HOLDS with `del ≡ 0`.  No `rmax`, no `sigmaQ` estimate, no ellipsoid, no depth.
* `shallowCut_of_trace`: a *concrete* such certificate — the constant trace functional `diagQ`
  (the flat identity matrix) works as soon as `trace (Cat k) ≤ n·(1 − dq/4)` below the horizon,
  because every relaxation point has trace at least `n·(1 − dq/4)` (`trace_floor_of_mem`).
* `bodyRec_of_trace`, `hfalse_of_trace`, `hfalse_of_separating`: the same in the record / `hfalse`
  form the leaf consumes, at an arbitrary verdict bit.

**§6–§7 — the trace certificate is a budget, and it is the campaign's own scalar.**
`trF_Cat_succ`/`trF_Cat_eq`: the accumulated centre's trace obeys the engine's drift recursion
exactly, `tr(Cat (k+1)) − tr(Cat k) = (γ(ρ_k)/√σ_k)·tr(p_k)`, so
`tr(Cat k) = Σ_{j<k} (γ_j/√σ_j)·diagSum p_j` (`shallowCut_of_drift` states `ShallowCut` directly in
that budget form).  `trF_Cat_succ_traceStream` then shows the trace certificate is *self-limiting*:
driving with the trace normal raises the trace by exactly `γ(ρ_k)·√σ_k > 0` every round, so the
certificate survives only while its accumulated drift fits under the body's trace floor — the
mechanism of the banked `drift_overflow`.

**§5 — irreducibility, at one body point and at one round.**  `no_del_of_stretch`: if the relaxation contains the
point `a − r·u` behind the centre in the unit direction of the candidate normal, and the engine's
`sig` is at most `‖c‖²/μ`, then NO depth is both legal and separating once `μ·r² > rmax²`.
`round_fails_of_ball` upgrades this to the whole round: if the relaxation contains a ball of radius
`r` about the centre and `μ·r² > rmax²`, then NO stream at all serves at that round — the pointwise,
volume-free form of "deep violations cannot be recorded", the exact complement of the `del = 0`
regime.

**Verdict of this lane.**  `ShallowCut` is *not* an analytic depth obligation: it is the existence of
a rational supporting-hyperplane stream for the accumulated centres, with `del ≡ 0` and `rmax`
irrelevant.  The constant trace certificate is one such stream and it is dead past its drift budget
(§7), so the surviving witness must be a genuine far-side direction at the rounds where the trace has
overflowed; §5 says exactly when no direction at all can serve.  The residual is therefore a
convex-geometry statement about the trajectory, not an estimate — see `report.md`.

Discipline: `set_option autoImplicit false`; no placeholder tactics and no extra axioms;
`#print axioms` after every theorem (all exactly `[propext, Classical.choice, Quot.sound]`).
Imports: `Mathlib` + the banked `Check_thinrec34_m4`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Bypass35M6

open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates
open QMCLeafB.Boundary (unflat flat_unflat unflat_flat)
open QMCLeafB.AnswerProducer (flat)
open QMCLeafB.ThinRec34M4 (ShallowCut NormalCut relaxBallP BodyRec)

/-! ## 1.  The trace direction -/

/-- `2 ≤ n·n` in dimension at least two. -/
theorem two_le_mul_self {n : ℕ} (hn : 2 ≤ n) : 2 ≤ n * n := by
  have h : 2 ≤ n := hn
  nlinarith

#print axioms QMCLeafB.Bypass35M6.two_le_mul_self

/-- `1 ≤ n·n` in dimension at least two. -/
theorem one_le_mul_self {n : ℕ} (hn : 2 ≤ n) : 1 ≤ n * n := by
  have h : 0 < n := by omega
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_pos h h).ne'

#print axioms QMCLeafB.Bypass35M6.one_le_mul_self


/-- The trace functional in the engine's flat coordinates: the indicator of the diagonal. -/
def diagQ (n : ℕ) : Fin (n * n) → ℚ :=
  fun k => if (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm k).2 then 1 else 0

/-- The trace functional is a nonzero rational vector in positive dimension. -/
theorem diagQ_ne_zero {n : ℕ} (hn : 1 ≤ n) : diagQ n ≠ 0 := by
  intro h
  set i : Fin n := ⟨0, by omega⟩ with hi
  have h1 : diagQ n (finProdFinEquiv (i, i)) = 1 := by
    simp [diagQ]
  rw [h] at h1
  simp at h1

#print axioms QMCLeafB.Bypass35M6.diagQ_ne_zero

/-- **The trace direction pairs to the matrix's trace.** -/
theorem diagQ_dot_flat {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    (fun k => ((diagQ n k : ℚ) : ℝ)) ⬝ᵥ flat X = ∑ i, X i i := by
  rw [dotProduct, ← Equiv.sum_comp finProdFinEquiv]
  have hterm : ∀ p : Fin n × Fin n,
      (fun k => ((diagQ n k : ℚ) : ℝ)) (finProdFinEquiv p) * flat X (finProdFinEquiv p)
        = if p.1 = p.2 then X p.1 p.2 else 0 := by
    rintro ⟨i, j⟩
    by_cases h : i = j
    · subst h
      simp [diagQ, flat]
    · simp [diagQ, flat, h]
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) => hterm p), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

#print axioms QMCLeafB.Bypass35M6.diagQ_dot_flat

/-- On flat coordinates the trace direction reads the trace of the unflattened matrix. -/
theorem diagQ_dot_self {n : ℕ} (z : Fin (n * n) → ℝ) :
    (fun k => ((diagQ n k : ℚ) : ℝ)) ⬝ᵥ z = ∑ i, unflat z i i := by
  conv_lhs => rw [← flat_unflat z]
  exact diagQ_dot_flat (unflat z)

#print axioms QMCLeafB.Bypass35M6.diagQ_dot_self

/-! ## 2.  The trace floor of the relaxation -/

/-- **Every point of the relaxation has trace at least `n·(1 − dq/4)`.** -/
theorem trace_floor_of_mem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {z : Fin (G.n * G.n) → ℝ}
    (hz : z ∈ relaxBallP G t P) :
    (G.n : ℝ) * (1 - ((P.dq : ℚ) : ℝ) / 4) ≤ ∑ i, unflat z i i := by
  obtain ⟨hbody, -⟩ := hz
  have hdiag : ∀ i : Fin G.n, 1 - ((P.dq : ℚ) : ℝ) / 4 ≤ unflat z i i := by
    intro i
    have h := (abs_le.1 (hbody.2.1 i)).1
    linarith
  have hconst : ∑ _i : Fin G.n, (1 - ((P.dq : ℚ) : ℝ) / 4)
      = (G.n : ℝ) * (1 - ((P.dq : ℚ) : ℝ) / 4) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← hconst]
  exact Finset.sum_le_sum fun i _ => hdiag i

#print axioms QMCLeafB.Bypass35M6.trace_floor_of_mem

/-! ## 3.  The ledger is structurally satisfied at zero depth -/

/-- The trace stream: the same rational normal at every round. -/
def traceStream (n : ℕ) : ℕ → Fin (n * n) → ℚ := fun _ => diagQ n

theorem traceStream_ne_zero {n : ℕ} (hn : 1 ≤ n) : ∀ k, traceStream n k ≠ 0 :=
  fun _ => diagQ_ne_zero hn

/-- **`sigmaQ` is positive for the trace stream**, so `del ≡ 0` passes the ledger's squared depth
check with no estimate: the check is `0 ≤ rmax^2·σ`. -/
theorem sigmaQ_traceStream_pos {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n) (k : ℕ) :
    0 ≤ sigmaQ (traceStream G.n k)
      ((NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega)) k).p) := by
  have hM : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 := by positivity
  have hwit : ∀ j, Aat (G.n * G.n) (QMCLeafB.RunPartsDilate.A0P G P)
      (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) j
        *ᵥ ((NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega)) j).p)
      = ((NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega)) j).c) := by
    intro j
    have h := QMCLeafB.RunPartsDilate.runCut_wit G P hn (traceStream G.n)
      (traceStream_ne_zero (by omega)) j
    simpa only [NormalCut] using h
  have hA0 : (castM (QMCLeafB.RunPartsDilate.A0P G P)).PosDef := by
    rw [QMCLeafB.ThinRec34M4.initShape_eq G P]
    exact QMCLeafB.Boundary.initShapeOf_cast_posDef hM
  have hpos := Aat_cast_posDef (n := G.n * G.n) (two_le_mul_self hn) hA0 hwit
    (fun j => by
      have hρ : (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega)) j).rho
          = P.rmax := rfl
      rw [hρ]; exact P.hrmax)
    (fun j => traceStream_ne_zero (by omega) j) k
  have hcast := cast_witness hwit k
  have hcne : cutCR (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k
      ≠ 0 := cast_normal_ne (traceStream_ne_zero (by omega) k)
  have hσ : 0 < sigmaR (fun i => ((NormalCut G P hn (traceStream G.n)
        (traceStream_ne_zero (by omega)) k).c i : ℝ))
      (fun i => ((NormalCut G P hn (traceStream G.n)
        (traceStream_ne_zero (by omega)) k).p i : ℝ)) :=
    sigmaR_pos hpos (by simpa only [cutPR, cutCR] using hcast) (by simpa only [cutCR] using hcne)
  exact (sigmaQ_pos_of_cast hσ).le

#print axioms QMCLeafB.Bypass35M6.sigmaQ_traceStream_pos


/-- **`sigmaQ` is positive for ANY nonzero rational normal stream** (the engine's iterate stays
positive definite and the witness is `A_k p = c`), so `del ≡ 0` always passes the ledger's squared
depth check. -/
theorem sigmaQ_normalCut_pos {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    0 ≤ sigmaQ (c k) ((NormalCut G P hn c hc k).p) := by
  have hM : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 := by positivity
  have hwit : ∀ j, Aat (G.n * G.n) (QMCLeafB.RunPartsDilate.A0P G P) (NormalCut G P hn c hc) j
        *ᵥ ((NormalCut G P hn c hc j).p) = ((NormalCut G P hn c hc j).c) := by
    intro j
    have h := QMCLeafB.RunPartsDilate.runCut_wit G P hn c hc j
    simpa only [NormalCut] using h
  have hA0 : (castM (QMCLeafB.RunPartsDilate.A0P G P)).PosDef := by
    rw [QMCLeafB.ThinRec34M4.initShape_eq G P]
    exact QMCLeafB.Boundary.initShapeOf_cast_posDef hM
  have hpos := Aat_cast_posDef (n := G.n * G.n) (two_le_mul_self hn) hA0 hwit
    (fun j => by
      have hρ : (NormalCut G P hn c hc j).rho = P.rmax := rfl
      rw [hρ]; exact P.hrmax) hc k
  have hcast := cast_witness hwit k
  have hcne : cutCR (NormalCut G P hn c hc) k ≠ 0 := cast_normal_ne (hc k)
  have hσ : 0 < sigmaR (fun i => ((NormalCut G P hn c hc k).c i : ℝ))
      (fun i => ((NormalCut G P hn c hc k).p i : ℝ)) :=
    sigmaR_pos hpos (by simpa only [cutPR, cutCR] using hcast) (by simpa only [cutCR] using hcne)
  exact (sigmaQ_pos_of_cast hσ).le

#print axioms QMCLeafB.Bypass35M6.sigmaQ_normalCut_pos

/-- **THE SEPARATION BYPASS — `ShallowCut` with no numbers at all.**  If the stream's own normal at
every round below the horizon puts the accumulated centre on the far side of the WHOLE relaxation
(a rational supporting-hyperplane certificate: `c_k ⬝ Cat_k ≤ c_k ⬝ z` for every body point), then
`ShallowCut` holds with `del ≡ 0`.  No `rmax`, no `sigmaQ` estimate, no ellipsoid, no depth. -/
theorem shallowCut_of_separating {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (hsep : ∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (NormalCut G P hn c hc) k
        ≤ (fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ z) :
    ShallowCut G t P hn := by
  classical
  refine ⟨c, hc, fun _ => 0, fun k _ => le_refl 0, fun k => ?_, fun k hk z hz => ?_⟩
  · have h := sigmaQ_normalCut_pos (G := G) (t := t) (P := P) hn c hc k
    have h2 : (0 : ℚ) ≤ P.rmax ^ 2 * sigmaQ (c k) ((NormalCut G P hn c hc k).p) :=
      mul_nonneg (by positivity) h
    simpa using h2
  · have hcR : cutCR (NormalCut G P hn c hc) k = (fun i => ((c k i : ℚ) : ℝ)) := rfl
    have h1 := hsep k hk z hz
    rw [hcR]
    simp only [Rat.cast_zero]
    linarith

#print axioms QMCLeafB.Bypass35M6.shallowCut_of_separating

/-- **`hfalse` from separation** — the record at any bit-false point, no numerics. -/
noncomputable def hfalse_of_separating {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) (hbit : o G t = false)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (hsep : ∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (NormalCut G P hn c hc) k
        ≤ (fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ z) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  Classical.choice
    ((QMCLeafB.ThinRec34M4.hfalse_thin_residual hn hbit).2
      (QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn (shallowCut_of_separating hn c hc hsep)))

#print axioms QMCLeafB.Bypass35M6.hfalse_of_separating

/-! ## 4.  `ShallowCut` from the trace ceiling -/

/-- **THE TRACE BYPASS.**  If the accumulated engine centre's trace is at most `n·(1 − dq/4)` at
every round below the horizon, then `ShallowCut` holds — constant trace normal, `del ≡ 0`.  No
`rmax`, no depth, no ellipsoid estimate: a zero depth is cheaper than any `rmax·√σ`. -/
theorem shallowCut_of_trace {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (hTrc : ∀ k, k < P.K * P.m →
      ∑ i, unflat (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
        (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k) i i
        ≤ (G.n : ℝ) * (1 - ((P.dq : ℚ) : ℝ) / 4)) :
    ShallowCut G t P hn := by
  classical
  refine ⟨traceStream G.n, traceStream_ne_zero (by omega), fun _ => 0,
    fun k _ => le_refl 0, fun k => ?_, fun k hk z hz => ?_⟩
  · have h := sigmaQ_traceStream_pos (G := G) (t := t) (P := P) hn k
    have h2 : (0 : ℚ) ≤ P.rmax ^ 2 * sigmaQ (traceStream G.n k)
        ((NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega)) k).p) :=
      mul_nonneg (by positivity) h
    simpa using h2
  · have hcR : cutCR (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k
        = (fun i => ((traceStream G.n k i : ℚ) : ℝ)) := rfl
    have h1 : cutCR (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k
          ⬝ᵥ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k
        = ∑ i, unflat (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k) i i := by
      rw [hcR, traceStream, diagQ_dot_self]
    have h2 : cutCR (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k
          ⬝ᵥ z = ∑ i, unflat z i i := by
      rw [hcR, traceStream, diagQ_dot_self]
    have h3 := trace_floor_of_mem (G := G) (t := t) (P := P) hz
    have h4 := hTrc k hk
    rw [h1, h2]
    simp only [Rat.cast_zero]
    linarith

#print axioms QMCLeafB.Bypass35M6.shallowCut_of_trace

/-- **The thin stratum's record, from the trace ceiling.** -/
theorem bodyRec_of_trace {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (hTrc : ∀ k, k < P.K * P.m →
      ∑ i, unflat (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
        (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k) i i
        ≤ (G.n : ℝ) * (1 - ((P.dq : ℚ) : ℝ) / 4)) :
    BodyRec G t P :=
  QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn (shallowCut_of_trace hn hTrc)

#print axioms QMCLeafB.Bypass35M6.bodyRec_of_trace

/-- **The leaf's `hfalse`, from the trace ceiling** — the exact slot shape the leaf consumes, at an
arbitrary verdict bit. -/
noncomputable def hfalse_of_trace {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) (hbit : o G t = false)
    (hTrc : ∀ k, k < P.K * P.m →
      ∑ i, unflat (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
        (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k) i i
        ≤ (G.n : ℝ) * (1 - ((P.dq : ℚ) : ℝ) / 4)) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  Classical.choice
    ((QMCLeafB.ThinRec34M4.hfalse_thin_residual hn hbit).2 (bodyRec_of_trace hn hTrc))

#print axioms QMCLeafB.Bypass35M6.hfalse_of_trace


/-- **The `del = 0` witness is not vacuous: at round 0 it applies at every `(G,t)` with `dq ≤ 4`.**
The engine starts at `Cat 0 = 0`, and the trace functional is nonnegative on the whole relaxation, so
the trace direction separates the initial centre from the body with zero depth. -/
theorem round_zero_separation {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hdq : P.dq ≤ 4) {z : Fin (G.n * G.n) → ℝ}
    (hz : z ∈ relaxBallP G t P) :
    (fun k => ((diagQ G.n k : ℚ) : ℝ)) ⬝ᵥ (0 : Fin (G.n * G.n) → ℝ)
      ≤ (fun k => ((diagQ G.n k : ℚ) : ℝ)) ⬝ᵥ z := by
  have hfloor := trace_floor_of_mem (G := G) (t := t) (P := P) hz
  have hzero : (fun k => ((diagQ G.n k : ℚ) : ℝ)) ⬝ᵥ (0 : Fin (G.n * G.n) → ℝ) = 0 := by
    simp [dotProduct]
  have htr : (fun k => ((diagQ G.n k : ℚ) : ℝ)) ⬝ᵥ z = ∑ i, unflat z i i :=
    diagQ_dot_self z
  have hnn : (0 : ℝ) ≤ (G.n : ℝ) * (1 - ((P.dq : ℚ) : ℝ) / 4) := by
    have h1 : (1 : ℝ) - ((P.dq : ℚ) : ℝ) / 4 ≥ 0 := by
      have : ((P.dq : ℚ) : ℝ) ≤ 4 := by exact_mod_cast hdq
      linarith
    positivity
  rw [hzero, htr]
  linarith

#print axioms QMCLeafB.Bypass35M6.round_zero_separation

/-! ## 5.  Irreducibility: a stretch behind the centre kills every depth -/

/-- **Deep violations cannot be recorded.**  Per round and per candidate normal: if the relaxation
contains the point `a − r·u` (`u` the positive unit direction of the normal `c`) and the engine's
`sig` is at most `‖c‖²/μ`, then NO depth is both legal and separating as soon as `μ·r² > rmax²`.
The hypothesis is a *single body point* behind the centre — no ball, no volume, no trajectory. -/
theorem no_del_of_stretch {m : ℕ} {S : Set (Fin m → ℝ)} {a c u : Fin m → ℝ}
    {r del rmax sig mu : ℝ}
    (hu : u ⬝ᵥ u = 1) (hcu : c = (c ⬝ᵥ u) • u) (hcpos : 0 < c ⬝ᵥ u)
    (hz : a - r • u ∈ S) (hr : 0 < r) (hmu : 0 < mu)
    (hsig : sig ≤ (c ⬝ᵥ c) / mu)
    (hledger : del ^ 2 ≤ rmax ^ 2 * sig) (hdel0 : 0 ≤ del)
    (hsep : ∀ z ∈ S, c ⬝ᵥ a - c ⬝ᵥ z ≤ del)
    (hbig : rmax ^ 2 < mu * r ^ 2) : False := by
  have hsepz := hsep _ hz
  have hviol : c ⬝ᵥ a - c ⬝ᵥ (a - r • u) = r * (c ⬝ᵥ u) := by
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]; ring
  rw [hviol] at hsepz
  have hcu2 : c ⬝ᵥ c = (c ⬝ᵥ u) ^ 2 := by
    conv_lhs => rw [hcu]
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hu]
    ring
  have hcu2pos : 0 < (c ⬝ᵥ u) ^ 2 := sq_pos_of_ne_zero (ne_of_gt hcpos)
  have hdel2 : (r * (c ⬝ᵥ u)) ^ 2 ≤ del ^ 2 := by nlinarith [hsepz, mul_pos hr hcpos]
  have hstep : del ^ 2 ≤ rmax ^ 2 * ((c ⬝ᵥ u) ^ 2 / mu) := by
    have hrmax2 : (0 : ℝ) ≤ rmax ^ 2 := by positivity
    have h1 : rmax ^ 2 * sig ≤ rmax ^ 2 * ((c ⬝ᵥ c) / mu) :=
      mul_le_mul_of_nonneg_left hsig hrmax2
    rw [hcu2] at h1
    linarith
  have hkey : mu * (r * (c ⬝ᵥ u)) ^ 2 ≤ rmax ^ 2 * (c ⬝ᵥ u) ^ 2 := by
    have h1 : mu * (r * (c ⬝ᵥ u)) ^ 2 ≤ mu * del ^ 2 := by nlinarith [hdel2, hmu]
    have h2 : mu * (rmax ^ 2 * ((c ⬝ᵥ u) ^ 2 / mu)) = rmax ^ 2 * (c ⬝ᵥ u) ^ 2 := by
      field_simp
    have h3 : mu * del ^ 2 ≤ rmax ^ 2 * (c ⬝ᵥ u) ^ 2 := by
      rw [← h2]
      exact mul_le_mul_of_nonneg_left hstep hmu.le
    linarith
  nlinarith [hkey, hcu2pos, hbig]

#print axioms QMCLeafB.Bypass35M6.no_del_of_stretch



/-- `c ⬝ᵥ c > 0` for a nonzero real vector. -/
theorem dot_self_pos {m : ℕ} (c : Fin m → ℝ) (hc : c ≠ 0) : 0 < c ⬝ᵥ c := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
  rw [dotProduct]
  refine Finset.sum_pos' (fun j _ => mul_self_nonneg (c j)) ⟨i, Finset.mem_univ i, ?_⟩
  nlinarith [mul_self_pos.2 hi]

/-- The unit rescaling of a nonzero vector has squared length one. -/
theorem unit_smul_dot {m : ℕ} (c : Fin m → ℝ) (hc : c ≠ 0) :
    (fun i => (1 / Real.sqrt (c ⬝ᵥ c)) * c i) ⬝ᵥ
      (fun i => (1 / Real.sqrt (c ⬝ᵥ c)) * c i) = 1 := by
  have hcc := dot_self_pos c hc
  set s := Real.sqrt (c ⬝ᵥ c) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.2 hcc
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hs2 : s * s = c ⬝ᵥ c := by
    rw [hsdef, ← pow_two]; exact Real.sq_sqrt hcc.le
  have hu : (fun i => (1 / Real.sqrt (c ⬝ᵥ c)) * c i) = (1 / s) • c := by
    rw [hsdef]; rfl
  rw [hu, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hs2]
  have h : (1 / s) * s = 1 := by rw [one_div, inv_mul_cancel₀ hsne]
  calc (1 / s) * ((1 / s) * (s * s)) = ((1 / s) * s) * ((1 / s) * s) := by ring
    _ = 1 := by rw [h]; ring

/-- **The violation of the rescaled point is exactly `r·‖c‖`.** -/
theorem violation_smul {m : ℕ} (c : Fin m → ℝ) (hc : c ≠ 0) (a : Fin m → ℝ) (r : ℝ) :
    c ⬝ᵥ a - c ⬝ᵥ (a - (r / Real.sqrt (c ⬝ᵥ c)) • c) = r * Real.sqrt (c ⬝ᵥ c) := by
  have hcc := dot_self_pos c hc
  set s := Real.sqrt (c ⬝ᵥ c) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.2 hcc
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hs2 : s * s = c ⬝ᵥ c := by
    rw [hsdef, ← pow_two]; exact Real.sq_sqrt hcc.le
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ← hs2]
  have h1 : (1 / s) * (s * s) = s := by
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hsne, one_mul]
  have h2 : r / s * (s * s) = r * s := by
    rw [div_eq_mul_inv]
    calc r * s⁻¹ * (s * s) = r * ((s⁻¹ * s) * s) := by ring
      _ = r * s := by rw [inv_mul_cancel₀ hsne]; ring
  rw [hsdef]
  linarith [h2]

/-- **A round is REFUTED when the body contains a ball about the centre.**  Ball hypothesis,
direction by direction: for every nonzero `c` the relaxation contains `a − (r/‖c‖)•c` (what a
Euclidean ball of radius `r` about `a` provides).  If the stream's `sig` obeys
`sig c ≤ ‖c‖²/μ` and `μ·r² > rmax²`, then NO nonzero normal and NO depth satisfy the round's two
clauses together — the pointwise, volume-free form of "deep violations cannot be recorded", and
the exact complement of the `del = 0` regime of `shallowCut_of_separating`. -/
theorem round_fails_of_ball {m : ℕ} {S : Set (Fin m → ℝ)} {a : Fin m → ℝ} {r rmax mu : ℝ}
    {sig : (Fin m → ℝ) → ℝ}
    (hball : ∀ c : Fin m → ℝ, c ≠ 0 → a - (r / Real.sqrt (c ⬝ᵥ c)) • c ∈ S)
    (hr : 0 < r) (hmu : 0 < mu) (hbig : rmax ^ 2 < mu * r ^ 2)
    (hsig : ∀ c : Fin m → ℝ, c ≠ 0 → sig c ≤ (c ⬝ᵥ c) / mu) :
    ¬ ∃ (c : Fin m → ℝ) (del : ℝ), c ≠ 0 ∧ 0 ≤ del ∧ del ^ 2 ≤ rmax ^ 2 * sig c
      ∧ ∀ z ∈ S, c ⬝ᵥ a - c ⬝ᵥ z ≤ del := by
  rintro ⟨c, del, hc, hdel0, hledger, hsep⟩
  have hcc := dot_self_pos c hc
  set s := Real.sqrt (c ⬝ᵥ c) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.2 hcc
  have hs2 : s * s = c ⬝ᵥ c := by
    rw [hsdef, ← pow_two]; exact Real.sq_sqrt hcc.le
  have hz := hsep _ (hball c hc)
  rw [violation_smul c hc a r] at hz
  have hdel2 : (r * s) ^ 2 ≤ del ^ 2 := by
    have h1 : 0 ≤ r * s := by positivity
    nlinarith [hz, h1]
  have hstep : del ^ 2 ≤ rmax ^ 2 * ((c ⬝ᵥ c) / mu) := by
    have h1 := mul_le_mul_of_nonneg_left (hsig c hc) (by positivity : (0:ℝ) ≤ rmax ^ 2)
    linarith
  have h3 : mu * (rmax ^ 2 * ((c ⬝ᵥ c) / mu)) = rmax ^ 2 * (c ⬝ᵥ c) := by
    field_simp
  have hkey : mu * (r * s) ^ 2 ≤ rmax ^ 2 * (s * s) := by
    have h1 : mu * (r * s) ^ 2 ≤ mu * del ^ 2 := by nlinarith [hdel2, hmu]
    have h2 : mu * del ^ 2 ≤ mu * (rmax ^ 2 * ((c ⬝ᵥ c) / mu)) :=
      mul_le_mul_of_nonneg_left hstep hmu.le
    have h3' : mu * (rmax ^ 2 * ((c ⬝ᵥ c) / mu)) = rmax ^ 2 * (s * s) := by
      rw [h3, ← hs2]
    linarith
  have hsqpos : 0 < s * s := by nlinarith [hspos]
  have hfac : (mu * r ^ 2 - rmax ^ 2) * (s * s) ≤ 0 := by nlinarith [hkey]
  have hfin : mu * r ^ 2 - rmax ^ 2 ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith [hfac, hsqpos, h]
  linarith

#print axioms QMCLeafB.Bypass35M6.dot_self_pos
#print axioms QMCLeafB.Bypass35M6.unit_smul_dot
#print axioms QMCLeafB.Bypass35M6.violation_smul
#print axioms QMCLeafB.Bypass35M6.round_fails_of_ball


/-! ## 6.  The trace is the engine's own drift scalar -/

/-- The trace of a flat vector (of an `m × m` matrix). -/
def trF (m : ℕ) (z : Fin (m * m) → ℝ) : ℝ := ∑ i, unflat z i i

theorem trF_add (m : ℕ) (z w : Fin (m * m) → ℝ) : trF m (z + w) = trF m z + trF m w := by
  simp [trF, unflat, Finset.sum_add_distrib]

theorem trF_smul (m : ℕ) (a : ℝ) (z : Fin (m * m) → ℝ) : trF m (a • z) = a * trF m z := by
  simp [trF, unflat, Finset.mul_sum]

/-- **The centre's trace obeys the engine's drift recursion exactly**: one round adds
`(γ/√σ)·diagSum p`. -/
theorem trF_Cat_succ (m : ℕ) (a0 : Fin (m * m) → ℝ) (cd : ℕ → CutData (m * m)) (k : ℕ) :
    trF m (Cat (m * m) a0 cd (k + 1))
      = trF m (Cat (m * m) a0 cd k)
        + (gammaR (m * m) ((cd k).rho) / sqrtSigmaR (cutCR cd k) (cutPR cd k))
          * trF m (cutPR cd k) := by
  rw [Cat_unfold, stepCentre, trF_add, trF_smul]

#print axioms QMCLeafB.Bypass35M6.trF_Cat_succ

/-- **The cumulative form**: the centre's trace at round `k` is the accumulated drift, from
`Cat 0 = 0`. -/
theorem trF_Cat_eq (m : ℕ) (a0 : Fin (m * m) → ℝ) (cd : ℕ → CutData (m * m)) (k : ℕ) :
    trF m (Cat (m * m) a0 cd k)
      = trF m a0 + Finset.sum (Finset.range k)
          (fun j => (gammaR (m * m) ((cd j).rho) / sqrtSigmaR (cutCR cd j) (cutPR cd j))
            * trF m (cutPR cd j)) := by
  induction k with
  | zero =>
      rw [show Cat (m * m) a0 cd 0 = a0 from rfl]
      simp
  | succ k ih =>
      rw [trF_Cat_succ, ih, Finset.sum_range_succ]
      ring

#print axioms QMCLeafB.Bypass35M6.trF_Cat_eq

/-- **`ShallowCut` from the campaign's trace budget.**  The hypothesis is the cumulative drift
`Σ_{j<k} (γ_j/√σ_j)·diagSum p_j` staying below the body's own trace floor `n·(1 − dq/4)` (the start
`Cat 0 = 0` contributing nothing).  So the thin stratum's obligation is the already-named `hdriftd`
scalar, not a new analytic estimate. -/
theorem shallowCut_of_drift {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (hbudget : ∀ k, k < P.K * P.m →
      Finset.sum (Finset.range k)
        (fun j => (gammaR (G.n * G.n) (((NormalCut G P hn (traceStream G.n)
              (traceStream_ne_zero (by omega)) j)).rho)
          / sqrtSigmaR (cutCR (NormalCut G P hn (traceStream G.n)
              (traceStream_ne_zero (by omega))) j)
            (cutPR (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) j))
        * trF G.n (cutPR (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) j))
      ≤ (G.n : ℝ) * (1 - ((P.dq : ℚ) : ℝ) / 4)) :
    ShallowCut G t P hn := by
  refine shallowCut_of_trace hn (fun k hk => ?_)
  have h := trF_Cat_eq G.n (0 : Fin (G.n * G.n) → ℝ)
    (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k
  have h0 : trF G.n (0 : Fin (G.n * G.n) → ℝ) = 0 := by
    simp [trF, unflat]
  rw [h0, zero_add] at h
  rw [show (∑ i, unflat (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
      (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k) i i)
      = trF G.n (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
      (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k) from rfl, h]
  exact hbudget k hk

#print axioms QMCLeafB.Bypass35M6.shallowCut_of_drift


/-! ## 7.  The trace witness is self-limiting: its own drift is strictly positive -/

/-- `γ/√σ·σ = γ·√σ` for `σ = (√σ)² > 0` — the algebraic step of the trace drift. -/
theorem div_mul_sigma_eq (gam sig sg : ℝ) (hsq : sg * sg = sig) (hne : sg ≠ 0) :
    gam / sg * sig = gam * sg := by
  rw [← hsq]
  have h1 : (1 / sg) * (sg * sg) = sg := by
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  calc gam / sg * (sg * sg) = gam * ((1 / sg) * (sg * sg)) := by ring
    _ = gam * sg := by rw [h1]

#print axioms QMCLeafB.Bypass35M6.div_mul_sigma_eq

/-- The trace of a `p`-vector is the engine's `sigmaR` against the trace direction. -/
theorem trF_cutPR_traceStream {G : QuantumMaxCutEnergy.Input}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n) (k : ℕ) :
    trF G.n (cutPR (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k)
      = sigmaR (cutCR (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k)
          (cutPR (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k) := by
  have h := diagQ_dot_self (n := G.n)
    (cutPR (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k)
  have hcR : cutCR (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k
      = (fun i => ((traceStream G.n k i : ℚ) : ℝ)) := rfl
  rw [sigmaR, hcR, traceStream]
  exact h.symm

#print axioms QMCLeafB.Bypass35M6.trF_cutPR_traceStream

/-- **The drift of a fixed trace normal**: one round raises the centre's trace by exactly
`γ(ρ_k)·√σ_k`.  General form, at any engine stream whose `p`-vector's trace is its `sigmaR`. -/
theorem trF_drift_of_sigma {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin (n * n)) (Fin (n * n)) ℚ}
    {cd : ℕ → CutData (n * n)}
    (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat (n * n) A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0) (k : ℕ)
    (htrace : trF n (cutPR cd k) = sigmaR (cutCR cd k) (cutPR cd k)) :
    trF n (Cat (n * n) (0 : Fin (n * n) → ℝ) cd (k + 1))
        - trF n (Cat (n * n) (0 : Fin (n * n) → ℝ) cd k)
      = gammaR (n * n) ((cd k).rho) * sqrtSigmaR (cutCR cd k) (cutPR cd k) := by
  have hpos := Aat_cast_posDef (n := n * n) (two_le_mul_self hn) hA0 hwit hρ hcne k
  have hcast : castM (Aat (n * n) A0 cd k) *ᵥ cutPR cd k = cutCR cd k := cast_witness hwit k
  have hc : cutCR cd k ≠ 0 := cast_normal_ne (hcne k)
  have hsq : sqrtSigmaR (cutCR cd k) (cutPR cd k) * sqrtSigmaR (cutCR cd k) (cutPR cd k)
      = sigmaR (cutCR cd k) (cutPR cd k) := sqrtSigmaR_mul_self hpos hcast hc
  have hne : sqrtSigmaR (cutCR cd k) (cutPR cd k) ≠ 0 := ne_of_gt (sqrtSigmaR_pos hpos hcast hc)
  have hstep := div_mul_sigma_eq (gammaR (n * n) ((cd k).rho))
    (sigmaR (cutCR cd k) (cutPR cd k)) (sqrtSigmaR (cutCR cd k) (cutPR cd k)) hsq hne
  rw [trF_Cat_succ n (0 : Fin (n * n) → ℝ) cd k, htrace, hstep]
  ring

#print axioms QMCLeafB.Bypass35M6.trF_drift_of_sigma

/-- **The trace witness is self-defeating.**  Driving the engine with the constant trace normal
raises the accumulated centre's trace by exactly `γ(ρ_k)·√σ_k > 0` at every round, so the
hypothesis of `shallowCut_of_trace` is a *budget*, not a free property: the trace witness serves
only while its accumulated drift fits under the body's trace floor — the mechanism of the banked
`drift_overflow`. -/
theorem trF_Cat_succ_traceStream {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n) (k : ℕ) :
    trF G.n (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) (k + 1))
        - trF G.n (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k)
      = gammaR (G.n * G.n)
          ((NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega)) k).rho)
        * sqrtSigmaR (cutCR (NormalCut G P hn (traceStream G.n)
            (traceStream_ne_zero (by omega))) k)
          (cutPR (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) k) := by
  have hM : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 := by positivity
  have hwit : ∀ j, Aat (G.n * G.n) (QMCLeafB.RunPartsDilate.A0P G P)
      (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega))) j
        *ᵥ ((NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega)) j).p)
      = ((NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega)) j).c) := by
    intro j
    have h := QMCLeafB.RunPartsDilate.runCut_wit G P hn (traceStream G.n)
      (traceStream_ne_zero (by omega)) j
    simpa only [NormalCut] using h
  have hA0 : (castM (QMCLeafB.RunPartsDilate.A0P G P)).PosDef := by
    rw [QMCLeafB.ThinRec34M4.initShape_eq G P]
    exact QMCLeafB.Boundary.initShapeOf_cast_posDef hM
  exact trF_drift_of_sigma (n := G.n) hn hA0 hwit
    (fun j => by
      have hρ : (NormalCut G P hn (traceStream G.n) (traceStream_ne_zero (by omega)) j).rho
          = P.rmax := rfl
      rw [hρ]; exact P.hrmax)
    (fun j => traceStream_ne_zero (by omega) j) k (trF_cutPR_traceStream hn k)

#print axioms QMCLeafB.Bypass35M6.trF_Cat_succ_traceStream

end QMCLeafB.Bypass35M6


