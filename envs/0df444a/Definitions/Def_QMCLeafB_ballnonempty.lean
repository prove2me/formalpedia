-- Prove2me | Definitions.Def_QMCLeafB_ballnonempty
-- name    : QMCLeafB_ballnonempty
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:34:58.587063+00:00
-- url     : https://prove2.me/theorems/86031f4e-3458-411d-adb1-edd139ab09f9
-- title:
--   QMCLeafB ballnonempty
-- statement:
--   # m1 — the residual's ball slot is never vacuous on a nonempty body
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_boundary_m2
import Definitions.Def_QMCLeafB_final_stroke_m7
/-
# m1 — the residual's ball slot is never vacuous on a nonempty body

`QMCLeafB.FinalStroke.RunParts.hcut` quantifies over

    relaxBall (wMatrix G) (t - Rq/40000) P.dq (2·G.n² + 2·P.dq²)
      = {z | relaxBodyLE A u δ (unflat z) ∧ ∑ zᵢ² ≤ 2n² + 2δ²},

while `PartsM2.ResidParts`'s hypothesis is only `∃ X, relaxBodyLE A u δ X` — **without** the norm
bound.  If the norm-bounded set were empty at a nonempty body, `hcut` would be vacuous and the
`ok ≡ false` branch of the residual would need no geometry at all at the sliver.  It is not:

* `relaxBodyLE A u δ X → relaxBodyLE A u δ (symm X)` for symmetric `A`: all three clauses see only
  the symmetric part (`frob A X = frob A (symm X)` uses `Aᵀ = A`);
* a body member's symmetric part has `‖symm X‖_F² ≤ n²(1 + 3δ/4)²`: `symm X + (δ/2)·1` is positive
  semidefinite, so its 2×2 principal minors are nonnegative, and the diagonal is `≤ 1 + 3δ/4`;
* hence `flat (symm X) ∈ relaxBall A u δ (2n² + 2δ²)` for `δ ≤ 1/2` — the campaign's `dq` is
  `eps/(9·cAq+1) ≈ 1/360000`.

Consequences proved here:

* `relaxBall_nonempty_of_bodyLE` — the ball is nonempty on every nonempty-body stratum;
* `runParts_hcut_at_body_point` — `hcut` is a genuine inequality at an **explicit** point, namely
  the flattened symmetric part of any body member (not just at the abstract ball).

So the sliver `RunParts` cannot be discharged by ball emptiness: the cut contract must hold at a
point of the body itself.  `not_relaxBall_of_emptyBody` (the empty stratum) is the exact complement.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QMCLeafB.BallNonemptyM1

open QMCLeafB

variable {n : ℕ}

/-! ## 1.  The symmetric part -/

/-- The symmetric part of a real matrix. -/
def symm (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ)⁻¹ • (X + Xᵀ)

theorem symm_apply (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    symm X i j = (X i j + X j i) / 2 := by
  simp [symm, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  ring

theorem symm_transpose (X : Matrix (Fin n) (Fin n) ℝ) : (symm X)ᵀ = symm X := by
  ext i j
  simp only [Matrix.transpose_apply, symm_apply]
  ring

theorem symm_diag (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : symm X i i = X i i := by
  simp [symm_apply]

/-- `qfR` only sees the symmetric part. -/
theorem qfR_symm (X : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    BallFloor.qfR (symm X) x = BallFloor.qfR X x := by
  have hpoint : ∀ i j : Fin n, x i * symm X i j * x j
      = x i * X i j * x j * (1 / 2) + x j * X j i * x i * (1 / 2) := by
    intro i j
    rw [symm_apply]
    ring
  have hswap : ∑ i, ∑ j, x j * X j i * x i * (1 / 2)
      = ∑ i, ∑ j, x i * X i j * x j * (1 / 2) := by
    rw [Finset.sum_comm]
  rw [BallFloor.qfR_eq_sum, BallFloor.qfR_eq_sum]
  have key : (∑ i, ∑ j, x i * X i j * x j * (1 / 2))
      + (∑ i, ∑ j, x i * X i j * x j * (1 / 2)) = ∑ i, ∑ j, x i * X i j * x j := by
    have hinner : ∀ i : Fin n, (∑ j, x i * X i j * x j * (1 / 2))
        + (∑ j, x i * X i j * x j * (1 / 2)) = ∑ j, x i * X i j * x j := by
      intro i
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hinner i
  simp only [hpoint, Finset.sum_add_distrib]
  rw [hswap, key]

/-- `frob` only sees the symmetric part, for a symmetric pairing matrix. -/
theorem frob_symm {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    BallFloor.frob A (symm X) = BallFloor.frob A X := by
  have hpoint : ∀ i j : Fin n, A i j * symm X i j
      = A i j * X i j * (1 / 2) + A i j * X j i * (1 / 2) := by
    intro i j
    rw [symm_apply]
    ring
  have hswap : ∑ i, ∑ j, A i j * X j i * (1 / 2) = ∑ i, ∑ j, A i j * X i j * (1 / 2) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      have h := congrFun (congrFun hA j) i
      simp only [Matrix.transpose_apply] at h
      rw [← h]
  have key : (∑ i, ∑ j, A i j * X i j * (1 / 2))
      + (∑ i, ∑ j, A i j * X i j * (1 / 2)) = ∑ i, ∑ j, A i j * X i j := by
    have hinner : ∀ i : Fin n, (∑ j, A i j * X i j * (1 / 2))
        + (∑ j, A i j * X i j * (1 / 2)) = ∑ j, A i j * X i j := by
      intro i
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hinner i
  simp only [BallFloor.frob, hpoint, Finset.sum_add_distrib]
  rw [hswap, key]

/-- **Body membership is unchanged by symmetrising.** -/
theorem relaxBodyLE_symm {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) {u δ : ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} (h : BallFloor.relaxBodyLE A u δ X) :
    BallFloor.relaxBodyLE A u δ (symm X) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [qfR_symm]
    exact h1 x
  · intro i
    rw [symm_diag]
    exact h2 i
  · rw [frob_symm hA]
    exact h3

/-! ## 2.  The positive semidefinite shift `symm X + (δ/2)·1` -/

/-- For a symmetric `Y` whose quadratic form is bounded below by `-(δ/2)‖x‖²`, the shift
`Y + (δ/2)·1` is positive semidefinite. -/
theorem posSemidef_shift {Y : Matrix (Fin n) (Fin n) ℝ} (hY : Yᵀ = Y) {δ : ℝ} (hδ : 0 ≤ δ)
    (hq : ∀ x : Fin n → ℝ, -(δ / 2) * (∑ i, x i ^ 2) ≤ BallFloor.qfR Y x) :
    (Y + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  have hsym : (Y + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ))ᵀ
      = Y + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [Matrix.transpose_add, Matrix.transpose_smul, hY, Matrix.transpose_one]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian]
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsym
  · intro x
    have hqfR_one : BallFloor.qfR (1 : Matrix (Fin n) (Fin n) ℝ) x = ∑ i, x i ^ 2 := by
      rw [BallFloor.qfR_eq_sum]
      simp [Matrix.one_apply, mul_ite, Finset.sum_ite_eq, sq]
    have hnonneg : 0 ≤ BallFloor.qfR (Y + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ)) x := by
      rw [BallFloor.qfR_add, BallFloor.qfR_smul, hqfR_one]
      have := hq x
      linarith
    simpa [BallFloor.qfR, star_trivial] using hnonneg

/-- A positive semidefinite matrix has nonnegative 2×2 principal minors. -/
theorem sq_entry_le_of_posSemidef {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.PosSemidef)
    (i j : Fin n) : Z i j ^ 2 ≤ Z i i * Z j j := by
  set e : Fin 2 → Fin n := fun a => if a = 0 then i else j with he
  have hsub := hZ.submatrix e
  have hdet := hsub.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  have h00 : (Z.submatrix e e) 0 0 = Z i i := by simp [Matrix.submatrix, he]
  have h01 : (Z.submatrix e e) 0 1 = Z i j := by simp [Matrix.submatrix, he]
  have h10 : (Z.submatrix e e) 1 0 = Z j i := by simp [Matrix.submatrix, he]
  have h11 : (Z.submatrix e e) 1 1 = Z j j := by simp [Matrix.submatrix, he]
  rw [h00, h01, h10, h11] at hdet
  have hji : Z j i = Z i j := by
    simpa using hZ.isHermitian.apply i j
  rw [hji] at hdet
  nlinarith

/-! ## 3.  The entrywise and Frobenius bounds -/

/-- **Every entry of a body member's symmetric part is at most `1 + 3δ/4` in modulus.** -/
theorem abs_entry_symm_le {Y : Matrix (Fin n) (Fin n) ℝ} (hY : Yᵀ = Y) {δ : ℝ}
    (hδ : 0 ≤ δ) (hq : ∀ x : Fin n → ℝ, -(δ / 2) * (∑ i, x i ^ 2) ≤ BallFloor.qfR Y x)
    (hd : ∀ i, |Y i i - 1| ≤ δ / 4) (i : Fin n) : |Y i i| ≤ 1 + 3 * δ / 4 := by
  have h1 := hd i
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

theorem sq_entry_symm_le {Y : Matrix (Fin n) (Fin n) ℝ} (hY : Yᵀ = Y) {δ : ℝ}
    (hδ : 0 ≤ δ) (hq : ∀ x : Fin n → ℝ, -(δ / 2) * (∑ i, x i ^ 2) ≤ BallFloor.qfR Y x)
    (hd : ∀ i, |Y i i - 1| ≤ δ / 4) (i j : Fin n) :
    Y i j ^ 2 ≤ (1 + 3 * δ / 4) ^ 2 := by
  have hZ := posSemidef_shift hY hδ hq
  have hmin := sq_entry_le_of_posSemidef hZ i j
  have hii : |Y i i - 1| ≤ δ / 4 := hd i
  have hjj : |Y j j - 1| ≤ δ / 4 := hd j
  have hZii : (Y + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ)) i i = Y i i + δ / 2 := by
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hZjj : (Y + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ)) j j = Y j j + δ / 2 := by
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hZii, hZjj] at hmin
  rw [abs_le] at hii hjj
  by_cases hij : i = j
  · subst hij
    have h1 : Y i i ≤ 1 + δ / 4 := by linarith [hii.2]
    have h2 : -(1 + δ / 4) ≤ Y i i := by linarith [hii.1]
    nlinarith [h1, h2]
  · have hYij : (Y + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ)) i j = Y i j := by
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hij]
    rw [hYij] at hmin
    have h1 : Y i i + δ / 2 ≤ 1 + 3 * δ / 4 := by linarith [hii.2]
    have h2 : Y j j + δ / 2 ≤ 1 + 3 * δ / 4 := by linarith [hjj.2]
    have h3 : 0 ≤ Y i i + δ / 2 := by linarith [hii.1]
    have h4 : 0 ≤ Y j j + δ / 2 := by linarith [hjj.1]
    nlinarith [hmin, h1, h2, h3, h4]

/-- **A body member's symmetric part has Frobenius norm-squared at most `n²(1 + 3δ/4)²`.** -/
theorem frobNormSq_symm_le {Y : Matrix (Fin n) (Fin n) ℝ} (hY : Yᵀ = Y) {δ : ℝ}
    (hδ : 0 ≤ δ) (hq : ∀ x : Fin n → ℝ, -(δ / 2) * (∑ i, x i ^ 2) ≤ BallFloor.qfR Y x)
    (hd : ∀ i, |Y i i - 1| ≤ δ / 4) :
    BallFloor.frobNormSq Y ≤ (n : ℝ) ^ 2 * (1 + 3 * δ / 4) ^ 2 := by
  have hbound : ∀ i j : Fin n, Y i j ^ 2 ≤ (1 + 3 * δ / 4) ^ 2 :=
    fun i j => sq_entry_symm_le hY hδ hq hd i j
  have h1 : BallFloor.frobNormSq Y ≤ ∑ _i : Fin n, ∑ _j : Fin n, (1 + 3 * δ / 4) ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hbound i j
  have h2 : ∑ _i : Fin n, ∑ _j : Fin n, (1 + 3 * δ / 4) ^ 2
      = (n : ℝ) ^ 2 * (1 + 3 * δ / 4) ^ 2 := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  linarith [h1, h2.le, h2.ge]

/-! ## 4.  The ball is nonempty on every nonempty-body stratum -/

/-- The constant of the residual's ball: `2n² + 2δ²`. -/
theorem ninv_le_ball {δ : ℝ} (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2) :
    (n : ℝ) ^ 2 * (1 + 3 * δ / 4) ^ 2 ≤ 2 * (n : ℝ) ^ 2 + 2 * δ ^ 2 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have hb : (1 + 3 * δ / 4) ^ 2 ≤ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hb hn, sq_nonneg δ]

/-- **A body member's symmetric part lies in the engine's norm-bounded ball**, for any radius `M`
above `n²(1 + 3δ/4)²`. -/
theorem flat_symm_mem_relaxBall {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) {u δ M : ℝ}
    (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2) (hM : (n : ℝ) ^ 2 * (1 + 3 * δ / 4) ^ 2 ≤ M)
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : BallFloor.relaxBodyLE A u δ X) :
    AnswerProducer.flat (symm X) ∈ Boundary.relaxBall A u δ M := by
  have hbody := relaxBodyLE_symm hA hX
  obtain ⟨h1, h2, h3⟩ := hbody
  refine ⟨?_, ?_⟩
  · rw [Boundary.unflat_flat]
    exact ⟨h1, h2, h3⟩
  · rw [Boundary.sum_sq_flat]
    exact (frobNormSq_symm_le (symm_transpose X) hδ h1 h2).trans hM

/-- **The residual's ball slot is never vacuous on a nonempty body.**  The complement of
`RefutedM3.not_relaxBall_of_emptyBody`. -/
theorem relaxBall_nonempty_of_bodyLE {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) {u δ : ℝ}
    (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : BallFloor.relaxBodyLE A u δ X) :
    (Boundary.relaxBall A u δ (2 * (n : ℝ) ^ 2 + 2 * δ ^ 2)).Nonempty :=
  ⟨AnswerProducer.flat (symm X),
    flat_symm_mem_relaxBall hA hδ hδ2 (ninv_le_ball hδ hδ2) hX⟩

/-! ## 5.  `hcut` has an explicit test point: the body witness itself -/

theorem relaxBall_nonempty_of_body (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : FinalStroke.RunParams G) (hδ2 : ((P.dq : ℚ) : ℝ) ≤ 1 / 2)
    (hbody : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      BallFloor.relaxBodyLE (wMatrix G)
        ((t : ℝ) - (((EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (((P.dq : ℚ) : ℝ)) X) :
    (Boundary.relaxBall (wMatrix G) ((t : ℝ) - (((EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
      (((P.dq : ℚ) : ℝ))
      (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ)).Nonempty := by
  obtain ⟨X, hX⟩ := hbody
  have hdq0 : (0 : ℝ) ≤ ((P.dq : ℚ) : ℝ) := by exact_mod_cast (le_of_lt P.hdq)
  refine ⟨AnswerProducer.flat (symm X),
    flat_symm_mem_relaxBall (wMatrix_symm G) hdq0 hδ2 ?_ hX⟩
  have hcast : (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ)
      = 2 * (G.n : ℝ) ^ 2 + 2 * (((P.dq : ℚ) : ℝ)) ^ 2 := by
    push_cast
    ring
  rw [hcast]
  exact ninv_le_ball hdq0 hδ2

/-- **`RunParts.hcut` evaluated at the body witness.**  At every cut round of a `RunParts` bundle
over a nonempty body, the cut contract holds at the flattened symmetric part of any body member:
the residual's cut slot is a genuine inequality, not a vacuous quantification. -/
theorem runParts_hcut_at_body_point {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : FinalStroke.RunParams G}
    (B : FinalStroke.RunParts o G t P) (hδ2 : ((P.dq : ℚ) : ℝ) ≤ 1 / 2)
    {X : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hX : BallFloor.relaxBodyLE (wMatrix G)
        ((t : ℝ) - (((EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (((P.dq : ℚ) : ℝ)) X)
    (k : ℕ) (hk : k < P.K * P.m) (hok : B.ok k = false) :
    -(((B.del k : ℚ)) : ℝ) ≤ EngineIterates.cutCR B.cd k
      ⬝ᵥ (AnswerProducer.flat (symm X)
        - EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd k) := by
  refine B.hcut k hk hok _ ?_
  have hdq0 : (0 : ℝ) ≤ ((P.dq : ℚ) : ℝ) := by exact_mod_cast (le_of_lt P.hdq)
  refine flat_symm_mem_relaxBall (wMatrix_symm G) hdq0 hδ2 ?_ hX
  have hcast : (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ)
      = 2 * (G.n : ℝ) ^ 2 + 2 * (((P.dq : ℚ) : ℝ)) ^ 2 := by
    push_cast
    ring
  rw [hcast]
  exact ninv_le_ball hdq0 hδ2

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.BallNonemptyM1.qfR_symm
#print axioms QMCLeafB.BallNonemptyM1.frob_symm
#print axioms QMCLeafB.BallNonemptyM1.relaxBodyLE_symm
#print axioms QMCLeafB.BallNonemptyM1.posSemidef_shift
#print axioms QMCLeafB.BallNonemptyM1.sq_entry_le_of_posSemidef
#print axioms QMCLeafB.BallNonemptyM1.sq_entry_symm_le
#print axioms QMCLeafB.BallNonemptyM1.frobNormSq_symm_le
#print axioms QMCLeafB.BallNonemptyM1.flat_symm_mem_relaxBall
#print axioms QMCLeafB.BallNonemptyM1.relaxBall_nonempty_of_bodyLE
#print axioms QMCLeafB.BallNonemptyM1.relaxBall_nonempty_of_body
#print axioms QMCLeafB.BallNonemptyM1.runParts_hcut_at_body_point

end QMCLeafB.BallNonemptyM1


