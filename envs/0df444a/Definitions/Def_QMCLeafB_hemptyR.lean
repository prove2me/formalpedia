-- Prove2me | Definitions.Def_QMCLeafB_hemptyR
-- name    : QMCLeafB_hemptyR
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T09:24:30.925259+00:00
-- url     : https://prove2.me/theorems/74e07ffb-16a4-4823-8804-677fab70caf7
-- title:
--   QMCLeafB hemptyR
-- statement:
--   # `Check_hemptyR_m3` — the load-bearing bridge `hemptyR`, proved
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thrice
/-
# `Check_hemptyR_m3` — the load-bearing bridge `hemptyR`, proved

Every accepted closing stroke carries the hypothesis

    hemptyR : real relaxed body empty at (G,t) → no RATIONAL member `RelaxMem` at (G,t)

(`Check_audit2_m5.solution_of_split`, and `Check_thrice_m3.solution_of_triple`).  It is not a
consequence of the other hypotheses and no module in the library proves it: `RelaxMem.psd_margin`
quantifies over **rational** vectors only, while `BallFloor.relaxBodyLE`'s first slot quantifies
over **real** vectors.  Swarm direction `bridge-hemptyR` was registered for this and abandoned
unfinished.

This file proves it, in the general form:

* `relaxBodyLE_of_relaxMem` — a rational member casts to a real member:
  `RelaxMem A Q u δ → relaxBodyLE (castMat A) ↑u ↑δ (castMat Q)`;
* `hemptyR_campaign` — hence the campaign's `hemptyR` at `paramsKbc2`, for every `(G,t)`;
* `solution_of_triple'` — the verbatim d9f601e5 stroke with `hemptyR` **deleted**.

The only real work is the quantitative slot: rational nonnegativity of `xᵀQx + (δ/2)‖x‖²` implies
the real one, by continuity of the quadratic form and density of `ℚⁿ` in `ℝⁿ` (`DenseRange.piMap`
+ `Rat.denseRange_cast`), exactly the closure argument of `Check_CastBridge.posSemidef_of_rat_tests`
re-run for the library's own `SepOracle.qf`/`BallFloor.qfR`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.HemptyR_M3

open QuantumMaxCutEnergy

variable {n : ℕ}

/-! ## 1.  The cast bridges for the quadratic form and the objective -/

theorem cast_qf (Q : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    ((QMCLeafB.SepOracle.qf Q x : ℚ) : ℝ)
      = QMCLeafB.BallFloor.qfR (QMCLeafB.SepOracle.castMat Q) (fun i => (x i : ℝ)) := by
  simp [QMCLeafB.SepOracle.qf, QMCLeafB.BallFloor.qfR, QMCLeafB.SepOracle.castMat,
    dotProduct, Matrix.mulVec, Finset.mul_sum]

#print axioms QMCLeafB.HemptyR_M3.cast_qf

theorem cast_frob (A Q : Matrix (Fin n) (Fin n) ℚ) :
    ((QMCLeafB.SepOracle.frob A Q : ℚ) : ℝ)
      = QMCLeafB.BallFloor.frob (QMCLeafB.SepOracle.castMat A)
          (QMCLeafB.SepOracle.castMat Q) := by
  simp [QMCLeafB.SepOracle.frob, QMCLeafB.BallFloor.frob, QMCLeafB.SepOracle.castMat]

#print axioms QMCLeafB.HemptyR_M3.cast_frob

/-! ## 2.  Rational tests are complete for the real PSD margin -/

theorem denseRange_rat_pi :
    DenseRange (fun x : Fin n → ℚ => fun i => (x i : ℝ)) :=
  DenseRange.piMap (ι := Fin n) (X := fun _ => ℚ) (Y := fun _ => ℝ)
    (f := fun _ => (Rat.cast : ℚ → ℝ)) (fun _ => Rat.denseRange_cast (𝕜 := ℝ))

#print axioms QMCLeafB.HemptyR_M3.denseRange_rat_pi

theorem continuous_qfR (M : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun x : Fin n → ℝ => QMCLeafB.BallFloor.qfR M x := by
  have h : (fun x : Fin n → ℝ => QMCLeafB.BallFloor.qfR M x)
      = fun x => ∑ i, ∑ j, x i * (M i j * x j) := by
    funext x
    simp [QMCLeafB.BallFloor.qfR, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [h]
  continuity

#print axioms QMCLeafB.HemptyR_M3.continuous_qfR

/-- **Rational tests imply the real PSD margin.** -/
theorem psd_margin_real {Q : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ}
    (h : ∀ x : Fin n → ℚ, -(δ / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf Q x) :
    ∀ x : Fin n → ℝ,
      -(((δ : ℚ) : ℝ) / 2) * (∑ i, x i ^ 2)
        ≤ QMCLeafB.BallFloor.qfR (QMCLeafB.SepOracle.castMat Q) x := by
  intro x
  set F : (Fin n → ℝ) → ℝ := fun y =>
    QMCLeafB.BallFloor.qfR (QMCLeafB.SepOracle.castMat Q) y
      + (((δ : ℚ) : ℝ) / 2) * ∑ i, y i ^ 2 with hF
  have hcont : Continuous F := by
    have h1 : Continuous fun y : Fin n → ℝ =>
        QMCLeafB.BallFloor.qfR (QMCLeafB.SepOracle.castMat Q) y := continuous_qfR _
    have h2 : Continuous fun y : Fin n → ℝ => (((δ : ℚ) : ℝ) / 2) * ∑ i, y i ^ 2 := by
      continuity
    exact h1.add h2
  have hclosed : IsClosed {y : Fin n → ℝ | 0 ≤ F y} :=
    isClosed_le continuous_const hcont
  have hsub : Set.range (fun y : Fin n → ℚ => fun i => (y i : ℝ))
      ⊆ {y : Fin n → ℝ | 0 ≤ F y} := by
    rintro _ ⟨y, rfl⟩
    have h1 : ((-(δ / 2) * (∑ i, y i ^ 2) : ℚ) : ℝ)
        ≤ QMCLeafB.BallFloor.qfR (QMCLeafB.SepOracle.castMat Q) (fun i => (y i : ℝ)) := by
      rw [← cast_qf]
      exact_mod_cast h y
    have h2 : (((∑ i, y i ^ 2 : ℚ)) : ℝ) = ∑ i, ((y i : ℚ) : ℝ) ^ 2 := by
      push_cast
      rfl
    have h3 : (((-(δ / 2) * (∑ i, y i ^ 2) : ℚ)) : ℝ)
        = -(((δ : ℚ) : ℝ) / 2) * ∑ i, ((y i : ℚ) : ℝ) ^ 2 := by
      push_cast
      ring
    simp only [Set.mem_ofPred_eq, hF]
    rw [h3] at h1
    linarith
  have huniv : Set.univ ⊆ {y : Fin n → ℝ | 0 ≤ F y} := by
    have := closure_minimal hsub hclosed
    rwa [denseRange_rat_pi.closure_range] at this
  have hx := huniv (Set.mem_univ x)
  simp only [Set.mem_ofPred_eq, hF] at hx
  linarith

#print axioms QMCLeafB.HemptyR_M3.psd_margin_real

/-! ## 3.  A rational member casts to a real member -/

/-- **The cast bridge for membership.**  `RelaxMem`'s three slots transport to `relaxBodyLE`'s
three slots at the entrywise cast; the quantitative slot is §2. -/
theorem relaxBodyLE_of_relaxMem {A Q : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (h : QMCLeafB.RelaxOracle.RelaxMem A Q u δ) :
    QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
      ((δ : ℚ) : ℝ) (QMCLeafB.SepOracle.castMat Q) := by
  refine ⟨psd_margin_real h.psd_margin, ?_, ?_⟩
  · intro i
    have h1 := h.diag_near i
    rw [abs_le] at h1
    have hlow : ((-(δ / 4) : ℚ) : ℝ) ≤ ((Q i i - 1 : ℚ) : ℝ) := by exact_mod_cast h1.1
    have hhigh : ((Q i i - 1 : ℚ) : ℝ) ≤ ((δ / 4 : ℚ) : ℝ) := by exact_mod_cast h1.2
    push_cast at hlow hhigh
    rw [QMCLeafB.SepOracle.castMat_apply, abs_le]
    exact ⟨hlow, hhigh⟩
  · have h1 := h.trace_le
    have h2 : (((QMCLeafB.SepOracle.frob A Q : ℚ)) : ℝ) ≤ (((u + δ / 2 : ℚ)) : ℝ) := by
      exact_mod_cast h1
    rw [cast_frob] at h2
    push_cast at h2
    exact h2

#print axioms QMCLeafB.HemptyR_M3.relaxBodyLE_of_relaxMem

/-! ## 4.  The campaign's `hemptyR`, discharged -/

/-- The engine's real weight matrix is the cast of its rational one. -/
theorem castMat_wMatrixQ (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G) = QMCLeafB.wMatrix G := by
  ext i j
  by_cases h : i < j
  · rw [QMCLeafB.SepOracle.castMat_apply, QMCLeafB.Finalization.wMatrixQ_apply_of_lt h,
      QMCLeafB.wMatrix_apply_of_lt h]
    norm_num
  · by_cases h2 : j < i
    · rw [QMCLeafB.SepOracle.castMat_apply, QMCLeafB.Finalization.wMatrixQ_apply_of_gt h2,
        QMCLeafB.wMatrix_apply_of_gt h2]
      norm_num
    · rw [QMCLeafB.SepOracle.castMat_apply, QMCLeafB.Finalization.wMatrixQ_apply,
        QMCLeafB.wMatrix_apply, dif_neg h, dif_neg h2, dif_neg h, dif_neg h2]
      norm_num

#print axioms QMCLeafB.HemptyR_M3.castMat_wMatrixQ

/-- **`hemptyR` at the campaign family, unconditionally.**  The real relaxed body is empty only
where no rational `RelaxMem` member exists — the hypothesis every closing stroke carried. -/
theorem hemptyR_campaign (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
    ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq := by
  intro hbody Q hQ
  have h := relaxBodyLE_of_relaxMem hQ
  rw [castMat_wMatrixQ] at h
  refine hbody (QMCLeafB.SepOracle.castMat Q) ?_
  simpa only [QMCLeafB.RundataCert.eps, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] using h

#print axioms QMCLeafB.HemptyR_M3.hemptyR_campaign

/-! ## 5.  The closing stroke with `hemptyR` deleted -/

/-- **The verbatim `d9f601e5` sentence from the triple residual, with no `hemptyR`.**  Compare
`Check_thrice_m3.solution_of_triple`: one hypothesis fewer. -/
theorem solution_of_triple'
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hdia : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) (i : Fin G.n),
      cXp G t k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (H : QMCLeafB.ThriceM3.TripleSupply QMCLeafB.Audit2M5.campaignBit
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
  QMCLeafB.ThriceM3.solution_of_triple rb cXp hbit hokp hdia
    (fun G t hbody => hemptyR_campaign G t hbody) H

#print axioms QMCLeafB.HemptyR_M3.solution_of_triple'


/-- **The audit's accepted stroke `Check_audit2_m5.solution_of_split`, with `hemptyR` deleted.** -/
theorem solution_of_split'
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : QMCLeafB.Audit2M5.ResidSplit QMCLeafB.Audit2M5.campaignBit
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
  QMCLeafB.Audit2M5.solution_of_split rb cXp hbit hokp
    (fun G t hbody => hemptyR_campaign G t hbody) H

#print axioms QMCLeafB.HemptyR_M3.solution_of_split'

/-- **The exemplar's real body is nonempty, from the banked rational member** — the same fact
`Check_thriceG1_m3.not_bodyEmpty_G₁` obtains by an explicit witness, here as a one-liner off the
general bridge.  Two independent proofs of the stratum's inhabitant. -/
theorem not_bodyEmpty_G₁_via_bridge :
    ¬ QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁) :=
  fun h => hemptyR_campaign QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000) h
    QMCLeafB.EmptyBodyM5.Q₁ QMCLeafB.EmptyBodyM5.body_nonempty_G₁

#print axioms QMCLeafB.HemptyR_M3.not_bodyEmpty_G₁_via_bridge

end QMCLeafB.HemptyR_M3


