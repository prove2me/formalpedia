-- Prove2me | Definitions.Def_QMCLeafB_ratdense33
-- name    : QMCLeafB_ratdense33
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:49:57.671834+00:00
-- url     : https://prove2.me/theorems/70a5bd0c-80a6-478b-af26-7daca7ce437e
-- title:
--   QMCLeafB ratdense33
-- statement:
--   # `Check_ratdense33_m3` — phase 33, member m3, direction `rounding` (A), second module
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_round33_m3
/-
# `Check_ratdense33_m3` — phase 33, member m3, direction `rounding` (A), second module

**The real⟹rational bridge at the campaign's constants, and the resulting dichotomy.**

`Round33M3.RatDense` (module 1) is the last named residual of direction (A): a *real* member of the
relaxed body at `(t − eps, dqShallow)` should yield an exact unit-diagonal PSD witness at `t + eps`.
Module 1 shows this holds for a *rational* member (`hcert_of_relaxMem`).  Here the gap is closed by
density, in three cheap moves — no square roots, no port of the ℚ-rounding estimates:

* a real member `X` is first symmetrised (all three `relaxBodyLE` fields see only the symmetric part);
* `X` is approximated **entrywise by rationals with the SIGN of `A` respected**: `Qᵢⱼ` is chosen in
  `[Xᵢⱼ − η, Xᵢⱼ]` where `Aᵢⱼ ≥ 0` and in `[Xᵢⱼ, Xᵢⱼ + η]` where `Aᵢⱼ < 0`, so that
  `frob A Q ≤ frob A X` **exactly** — the trace ceiling survives at the *same* level, which a naive
  absolute-value approximation would break by `η·Rq` (and `Rq` is unbounded, so no renormalisation of
  the budget could absorb it);
* the approximation error costs `nη` in the quadratic form and `η` in the diagonal, so `Q` is a member
  at tolerance `3δ/2`; the rounding budget at `3δ/2` still fits (`≈ (3/4)eps + (3/4)eps ≤ 2eps`).

So the charter's case (iii) — "relaxed body non-empty but no exact witness at `t + eps`" — is **empty
as a geometric stratum**, and with it `RatDense`.  Consequently the two record lanes are exact
complements of one predicate (`EmptyBody`), and the whole leaf reduces to {a `Poly` bit} plus {that
bit decides `EmptyBody`} (`solution_of_exactBit'` below).

Discipline as in module 1: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; published imports
only; `#print axioms` receipts at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

noncomputable section

namespace Round33M3

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-- The request coding of the leaf (local, as in the templates). -/
local instance instRequestCodingRound33B : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  Over `ℝ` too, the body sees only the symmetric part -/

/-- The real symmetric part. -/
def symmMatR {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (X i j + X j i) / 2

theorem symmMatR_transpose {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    (symmMatR X)ᵀ = symmMatR X := by
  ext i j
  simp [symmMatR, add_comm]

theorem symmMatR_self {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    symmMatR X i i = X i i := by
  simp [symmMatR]

theorem qfR_transpose33 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    QMCLeafB.BallFloor.qfR Mᵀ x = QMCLeafB.BallFloor.qfR M x := by
  simp only [QMCLeafB.BallFloor.qfR]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

theorem qfR_smul33 {n : ℕ} (c : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    QMCLeafB.BallFloor.qfR (c • M) x = c * QMCLeafB.BallFloor.qfR M x :=
  QMCLeafB.BallFloor.qfR_smul c M x

theorem qfR_symmMatR {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    QMCLeafB.BallFloor.qfR (symmMatR X) x = QMCLeafB.BallFloor.qfR X x := by
  have hsplit : symmMatR X = (1 / 2 : ℝ) • (X + Xᵀ) := by
    ext i j
    simp [symmMatR, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply]
    ring
  rw [hsplit, qfR_smul33, QMCLeafB.BallFloor.qfR_add, qfR_transpose33]
  ring

theorem frob_smulR33 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.BallFloor.frob A (c • M) = c * QMCLeafB.BallFloor.frob A M := by
  simp only [QMCLeafB.BallFloor.frob, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem frob_transposeR33 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.BallFloor.frob A Mᵀ = QMCLeafB.BallFloor.frob Aᵀ M := by
  simp only [QMCLeafB.BallFloor.frob, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem frob_symmMatR {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.BallFloor.frob A (symmMatR X) = QMCLeafB.BallFloor.frob A X := by
  have hsplit : symmMatR X = (1 / 2 : ℝ) • (X + Xᵀ) := by
    ext i j
    simp [symmMatR, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply]
    ring
  rw [hsplit, frob_smulR33, QMCLeafB.BallFloor.frob_add, frob_transposeR33, hA]
  ring

/-- **The relaxed body is invariant under symmetrisation.** -/
theorem relaxBodyLE_symmMatR {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) {u δ : ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} (h : QMCLeafB.BallFloor.relaxBodyLE A u δ X) :
    QMCLeafB.BallFloor.relaxBodyLE A u δ (symmMatR X) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x; rw [qfR_symmMatR]; exact h1 x
  · intro i; rw [symmMatR_self]; exact h2 i
  · rw [frob_symmMatR A hA]; exact h3

#print axioms Round33M3.qfR_symmMatR
#print axioms Round33M3.frob_symmMatR
#print axioms Round33M3.relaxBodyLE_symmMatR


/-! ## 2.  Sign-controlled rational approximation -/

theorem exists_rat_approx {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ Q : Matrix (Fin n) (Fin n) ℚ,
      (∀ i j, |QMCLeafB.CastBridge.castM Q i j - X i j| < η) ∧
      (∀ i j, A i j * (QMCLeafB.CastBridge.castM Q i j) ≤ A i j * X i j) := by
  classical
  have hchoose : ∀ i j : Fin n, ∃ q : ℚ,
      |((q : ℚ) : ℝ) - X i j| < η ∧ A i j * ((q : ℚ) : ℝ) ≤ A i j * X i j := by
    intro i j
    rcases lt_or_ge (A i j) 0 with h | h
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show X i j < X i j + η by linarith)
      refine ⟨q, ?_, ?_⟩
      · rw [abs_lt]; constructor <;> linarith
      · exact mul_le_mul_of_nonpos_left hq1.le h.le
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show X i j - η < X i j by linarith)
      refine ⟨q, ?_, ?_⟩
      · rw [abs_lt]; constructor <;> linarith
      · exact mul_le_mul_of_nonneg_left hq2.le h
  refine ⟨Matrix.of (fun i j => Classical.choose (hchoose i j)), ?_, ?_⟩
  · intro i j
    exact (Classical.choose_spec (hchoose i j)).1
  · intro i j
    exact (Classical.choose_spec (hchoose i j)).2

#print axioms Round33M3.exists_rat_approx

theorem castM_symmMat {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    QMCLeafB.CastBridge.castM (symmMat Q) i j
      = (QMCLeafB.CastBridge.castM Q i j + QMCLeafB.CastBridge.castM Q j i) / 2 := by
  simp only [symmMat, QMCLeafB.CastBridge.castM_apply, Matrix.of_apply]
  push_cast
  ring

/-- **The sign-controlled approximation, symmetrised.**  Symmetrising a sign-controlled approximation
preserves both the error bound and the sign condition. -/
theorem exists_rat_approx_symm {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) (hX : Xᵀ = X)
    {η : ℝ} (hη : 0 < η) :
    ∃ Q : Matrix (Fin n) (Fin n) ℚ, Qᵀ = Q ∧
      (∀ i j, |QMCLeafB.CastBridge.castM Q i j - X i j| < η) ∧
      (∀ i j, A i j * (QMCLeafB.CastBridge.castM Q i j) ≤ A i j * X i j) := by
  obtain ⟨Q0, hclose, hsign⟩ := exists_rat_approx A X hη
  refine ⟨symmMat Q0, symmMat_transpose Q0, ?_, ?_⟩
  · intro i j
    rw [castM_symmMat]
    have h1 := hclose i j
    have h2 := hclose j i
    have hXji : X j i = X i j := by
      have h := congrFun (congrFun hX j) i
      simp only [Matrix.transpose_apply] at h
      exact h.symm
    rw [hXji] at h2
    have hkey : (QMCLeafB.CastBridge.castM Q0 i j + QMCLeafB.CastBridge.castM Q0 j i) / 2 - X i j
        = ((QMCLeafB.CastBridge.castM Q0 i j - X i j)
            + (QMCLeafB.CastBridge.castM Q0 j i - X i j)) / 2 := by ring
    have h3 : |(QMCLeafB.CastBridge.castM Q0 i j - X i j)
        + (QMCLeafB.CastBridge.castM Q0 j i - X i j)|
        ≤ |QMCLeafB.CastBridge.castM Q0 i j - X i j|
          + |QMCLeafB.CastBridge.castM Q0 j i - X i j| := abs_add_le _ _
    rw [abs_lt] at h1 h2
    rw [hkey, abs_div, abs_two, div_lt_iff₀ (by norm_num : (0:ℝ) < 2), abs_lt]
    constructor <;> linarith
  · intro i j
    rw [castM_symmMat]
    have h1 := hsign i j
    have h2 := hsign j i
    have hAji : A j i = A i j := by
      have h := congrFun (congrFun hA j) i
      simp only [Matrix.transpose_apply] at h
      exact h.symm
    have hXji : X j i = X i j := by
      have h := congrFun (congrFun hX j) i
      simp only [Matrix.transpose_apply] at h
      exact h.symm
    rw [hAji, hXji] at h2
    nlinarith

#print axioms Round33M3.exists_rat_approx_symm

/-! ## 3.  Deviations: the quadratic form and the trace -/

theorem frobNormSq_sub_le {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {X : Matrix (Fin n) (Fin n) ℝ}
    {η : ℝ} (h : ∀ i j, |QMCLeafB.CastBridge.castM Q i j - X i j| < η) (hη : 0 ≤ η) :
    QMCLeafB.BallFloor.frobNormSq (QMCLeafB.CastBridge.castM Q - X) ≤ ((n : ℝ) * η) ^ 2 := by
  have hterm : ∀ i j : Fin n, (QMCLeafB.CastBridge.castM Q - X) i j ^ 2 ≤ η ^ 2 := by
    intro i j
    have h1 := h i j
    rw [abs_lt] at h1
    have hentry : (QMCLeafB.CastBridge.castM Q - X) i j
        = QMCLeafB.CastBridge.castM Q i j - X i j := rfl
    rw [hentry]
    nlinarith [h1.1, h1.2]
  have hstep : QMCLeafB.BallFloor.frobNormSq (QMCLeafB.CastBridge.castM Q - X)
      ≤ ∑ i : Fin n, ∑ j : Fin n, η ^ 2 := by
    simp only [QMCLeafB.BallFloor.frobNormSq]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  have hsum : (∑ i : Fin n, ∑ j : Fin n, η ^ 2) = ((n : ℝ) * η) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  linarith [hstep, hsum ▸ hstep]

#print axioms Round33M3.frobNormSq_sub_le

theorem qfR_diff_le {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {X : Matrix (Fin n) (Fin n) ℝ} {η : ℝ}
    (h : ∀ i j, |QMCLeafB.CastBridge.castM Q i j - X i j| < η) (hη : 0 ≤ η) (x : Fin n → ℝ) :
    QMCLeafB.BallFloor.qfR X x - (n : ℝ) * η * (∑ i, x i ^ 2)
      ≤ QMCLeafB.BallFloor.qfR (QMCLeafB.CastBridge.castM Q) x := by
  set E : Matrix (Fin n) (Fin n) ℝ := QMCLeafB.CastBridge.castM Q - X with hE
  have hEbound : QMCLeafB.BallFloor.frobNormSq E ≤ ((n : ℝ) * η) ^ 2 := frobNormSq_sub_le h hη
  have hdev : |QMCLeafB.BallFloor.qfR E x| ≤ (n : ℝ) * η * (∑ i, x i ^ 2) :=
    QMCLeafB.BallFloor.abs_qfR_le_of_frobNormSq_le (by positivity) hEbound
  have hsplit : QMCLeafB.CastBridge.castM Q = X + E := by
    rw [hE]; abel
  rw [hsplit, QMCLeafB.BallFloor.qfR_add]
  have h1 := (abs_le.mp hdev).1
  linarith

#print axioms Round33M3.qfR_diff_le

/-- Fubini for the two index orders the library states the two quadratic forms in. -/
theorem sum_swap33 {n : ℕ} (F : Fin n → Fin n → ℝ) :
    (∑ j, ∑ i, F j i) = ∑ i, ∑ j, F j i :=
  Finset.sum_comm

#print axioms Round33M3.sum_swap33

/-- The rational quadratic form is the real one at the cast vector. -/
theorem qf_castM {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    QMCLeafB.SepOracle.qf Q x = QMCLeafB.BallFloor.qfR (QMCLeafB.CastBridge.castM Q)
      (fun i => ((x i : ℚ) : ℝ)) := by
  have hval : (((QMCLeafB.SepOracle.qf Q x : ℚ)) : ℝ)
      = ∑ i : Fin n, ∑ j : Fin n, (x i : ℝ) * ((Q i j : ℚ) : ℝ) * (x j : ℝ) := by
    rw [QMCLeafB.SepOracle.qf_eq_sum]
    push_cast
    simp only [mul_assoc]
  have hval2 : QMCLeafB.BallFloor.qfR (QMCLeafB.CastBridge.castM Q)
      (fun i => ((x i : ℚ) : ℝ))
      = ∑ i : Fin n, ∑ j : Fin n, (x i : ℝ) * ((Q i j : ℚ) : ℝ) * (x j : ℝ) := by
    rw [QMCLeafB.BallFloor.qfR_eq_sum]
    rfl
  rw [hval2, hval]

#print axioms Round33M3.qf_castM

/-- The rational trace pairing is the real one at the cast matrices. -/
theorem frob_castM {n : ℕ} (A Q : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.frob A Q = QMCLeafB.BallFloor.frob (QMCLeafB.CastBridge.castM A)
      (QMCLeafB.CastBridge.castM Q) := by
  simp only [QMCLeafB.SepOracle.frob, QMCLeafB.BallFloor.frob, QMCLeafB.CastBridge.castM_apply]
  push_cast
  rfl

#print axioms Round33M3.frob_castM

theorem frob_le_of_sign {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {Q : Matrix (Fin n) (Fin n) ℚ}
    {X : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i j, A i j * (QMCLeafB.CastBridge.castM Q i j) ≤ A i j * X i j) :
    QMCLeafB.BallFloor.frob A (QMCLeafB.CastBridge.castM Q) ≤ QMCLeafB.BallFloor.frob A X := by
  simp only [QMCLeafB.BallFloor.frob]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j

#print axioms Round33M3.frob_le_of_sign


/-! ## 4.  The rounding lemma at tolerance `3δ/2` -/

/-- **A real member gives a rational one at tolerance `3δ/2`**, with the level unchanged: the
sign-controlled approximation keeps `frob A Q ≤ frob A X` exactly, so the trace ceiling survives, and
the quadratic-form error `nη = δ/4` is paid by the enlarged tolerance. -/
theorem relaxMem_of_real_member {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {X : Matrix (Fin G.n) (Fin G.n) ℝ} (hn : 2 ≤ G.n)
    (hX : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
      ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
      (((QMCLeafB.RundataParams.dqShallow G : ℚ)) : ℝ) X) :
    ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) (3 * QMCLeafB.RundataParams.dqShallow G / 2) := by
  classical
  have hA : (QMCLeafB.wMatrix G)ᵀ = QMCLeafB.wMatrix G := QMCLeafB.wMatrix_symm G
  obtain ⟨hpsd, hdiag, htr⟩ := relaxBodyLE_symmMatR hA hX
  have hXR : (symmMatR X)ᵀ = symmMatR X := symmMatR_transpose X
  set δq : ℚ := QMCLeafB.RundataParams.dqShallow G with hδq
  have hδpos : 0 < δq := QMCLeafB.RundataParams.dqShallow_pos G
  have hδR : (0 : ℝ) < ((δq : ℚ) : ℝ) := by exact_mod_cast hδpos
  have hnR : (0 : ℝ) < (G.n : ℝ) := by
    have h : 0 < G.n := by omega
    exact_mod_cast h
  set η : ℝ := ((δq : ℚ) : ℝ) / (4 * (G.n : ℝ)) with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  have hnη : (G.n : ℝ) * η = ((δq : ℚ) : ℝ) / 4 := by
    rw [hηdef]; field_simp
  obtain ⟨Q, _hQsym, hclose, hsign⟩ := exists_rat_approx_symm hA hXR hη
  refine ⟨Q, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- positivity of the new tolerance
    show (0 : ℚ) < 3 * δq / 2
    linarith
  · -- the psd margin, at the enlarged tolerance
    intro x
    set xr : Fin G.n → ℝ := fun i => ((x i : ℚ) : ℝ) with hxr
    have hsum : ((∑ i, x i ^ 2 : ℚ) : ℝ) = ∑ i, xr i ^ 2 := by
      simp only [hxr]; push_cast; rfl
    have hdiff := qfR_diff_le (n := G.n) hclose hη.le xr
    rw [hnη] at hdiff
    have h1 := hpsd xr
    have hmain : ((-(3 * δq / 2 / 2) * (∑ i, x i ^ 2) : ℚ) : ℝ)
        ≤ ((QMCLeafB.SepOracle.qf Q x : ℚ) : ℝ) := by
      rw [qf_castM]
      push_cast
      linarith
    exact_mod_cast hmain
  · -- the diagonal
    intro i
    have hc : |((Q i i : ℚ) : ℝ) - X i i| < η := by
      have h := hclose i i
      rwa [symmMatR_self] at h
    have hd : |X i i - 1| ≤ ((δq : ℚ) : ℝ) / 4 := by
      have h := hdiag i
      rwa [symmMatR_self] at h
    have hηle : η ≤ ((δq : ℚ) : ℝ) / 8 := by
      have hn2 : (2 : ℝ) ≤ (G.n : ℝ) := by exact_mod_cast hn
      have h2η : (2 : ℝ) * η ≤ (G.n : ℝ) * η := by nlinarith [hn2, hη]
      rw [hnη] at h2η
      linarith
    have hR : |((Q i i : ℚ) : ℝ) - 1| ≤ ((3 * δq / 2 : ℚ) : ℝ) / 4 := by
      have hsplit : ((Q i i : ℚ) : ℝ) - 1 = (((Q i i : ℚ) : ℝ) - X i i) + (X i i - 1) := by ring
      rw [hsplit]
      have hlt := abs_lt.mp hc
      have hle' := abs_le.mp hd
      push_cast
      rw [abs_le]
      constructor <;> linarith [hlt.1, hlt.2, hle'.1, hle'.2, hηle, hδR]
    exact_mod_cast hR
  · -- the trace ceiling survives exactly (the sign condition is what buys this)
    have hfr : QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G) Q
        = QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G)
          (QMCLeafB.CastBridge.castM Q) := by
      rw [frob_castM, QMCLeafB.Finalization.wMatrix_castM]
    have hXs : QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G) (symmMatR X)
        = QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G) X := frob_symmMatR _ hA X
    rw [hXs] at htr
    have hle := frob_le_of_sign (QMCLeafB.wMatrix G) hsign
    have hR : ((QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G) Q : ℚ) : ℝ)
        ≤ (((t - QMCLeafB.RundataCert.eps G) + (3 * δq / 2) / 2 : ℚ) : ℝ) := by
      rw [hfr]
      push_cast
      simp only [QMCLeafB.RundataCert.eps]
      linarith
    exact_mod_cast hR

#print axioms Round33M3.relaxMem_of_real_member

/-! ## 5.  The rounding budget at tolerance `3δ/2` still fits -/

/-- **The budget at the enlarged tolerance**: `roundCost A (3·(3δ/2)/4) + (3δ/2)/2 ≤ 2·eps`.  The cost
is at most `(27/4)·δ·Rq ≤ (27/4)·(eps/9) = (3/4)·eps` and the tolerance half is `≤ (3/4)·eps`. -/
theorem budget_three_halves (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * (3 * QMCLeafB.RundataParams.dqShallow G / 2) / 4)
      + (3 * QMCLeafB.RundataParams.dqShallow G / 2) / 2
      ≤ 2 * QMCLeafB.RundataCert.eps G := by
  have heps := QMCLeafB.RundataCert.eps_pos G hRq
  have hRq0 : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G := hRq.le
  have hδeq : QMCLeafB.RundataParams.dqShallow G
      = QMCLeafB.RundataCert.eps G / (9 * QMCLeafB.EngineRuntime.Rq G + 1) := by
    simp only [QMCLeafB.RundataParams.dqShallow, QMCLeafB.RundataParams.dqShallowCore,
      if_neg (ne_of_gt hRq)]
  have hden : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1 := by linarith
  have hδsmall : QMCLeafB.RundataParams.dqShallow G ≤ 8 / 9 := by
    rw [hδeq, QMCLeafB.RundataCert.eps, div_div, div_le_iff₀ (by linarith : (0 : ℚ) < 40000 * (9 * QMCLeafB.EngineRuntime.Rq G + 1))]
    nlinarith [hRq0]
  have hδpos := QMCLeafB.RundataParams.dqShallow_pos G
  have hν0 : (0 : ℚ) ≤ 3 * (3 * QMCLeafB.RundataParams.dqShallow G / 2) / 4 := by linarith
  have hν1 : 3 * (3 * QMCLeafB.RundataParams.dqShallow G / 2) / 4 ≤ 1 := by linarith
  have hcost := QMCLeafB.RundataParams.roundCost_le G hν0 hν1
  have hδRq : QMCLeafB.RundataParams.dqShallow G * QMCLeafB.EngineRuntime.Rq G
      ≤ QMCLeafB.RundataCert.eps G / 9 := by
    rw [hδeq, div_mul_eq_mul_div, div_le_iff₀ hden]
    linarith [heps]
  have hδeps : QMCLeafB.RundataParams.dqShallow G ≤ QMCLeafB.RundataCert.eps G := by
    rw [hδeq, div_le_iff₀ hden]
    nlinarith [heps, hRq0]
  have hcost' : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
      (3 * (3 * QMCLeafB.RundataParams.dqShallow G / 2) / 4)
      ≤ 3 * QMCLeafB.RundataCert.eps G / 4 := by
    refine le_trans hcost ?_
    have h1 : 6 * (3 * (3 * QMCLeafB.RundataParams.dqShallow G / 2) / 4)
        * QMCLeafB.EngineRuntime.Rq G
        = (27 / 4) * (QMCLeafB.RundataParams.dqShallow G * QMCLeafB.EngineRuntime.Rq G) := by ring
    rw [h1]
    linarith
  have hhalf : (3 * QMCLeafB.RundataParams.dqShallow G / 2) / 2
      ≤ 3 * QMCLeafB.RundataCert.eps G / 4 := by linarith
  linarith

#print axioms Round33M3.budget_three_halves

/-! ## 6.  The dichotomy, unconditionally -/

/-- **Case (iii) of the charter is empty**: a non-empty real relaxed body at `(t − eps, dqShallow)`
already carries a genuine unit-diagonal PSD witness at `t + eps`.  So a bit that reads `false` at a
non-empty body is a *search* failure, never a geometric necessity. -/
theorem memberAt_of_not_emptyBody {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (hne : ¬ EmptyBody G t (P G)) :
    MemberAt G t := by
  have hmem : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((P G).dq : ℚ) : ℝ) X := by
    by_contra h
    exact hne (fun X hX => h ⟨X, hX⟩)
  obtain ⟨X, hX⟩ := hmem
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq] at hX
  obtain ⟨Q, hQ⟩ := relaxMem_of_real_member hn hX
  have hbudget := budget_three_halves G hn hRq
  exact hcert_of_relaxMem_budget (G := G) (t := t) (δ := 3 * QMCLeafB.RundataParams.dqShallow G / 2)
    (symmMat_transpose Q) (relaxMem_symmMat (wMatrixQ_transpose G) hQ) hbudget

#print axioms Round33M3.memberAt_of_not_emptyBody

/-- **The dichotomy**: at every point of order `≥ 2` in the bracket, the relaxed body is empty or an
exact witness exists.  `RatDense` is discharged. -/
theorem emptyBody_or_memberAt' {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) :
    EmptyBody G t (P G) ∨ MemberAt G t := by
  by_cases hE : EmptyBody G t (P G)
  · exact Or.inl hE
  · refine Or.inr ?_
    rcases lt_or_eq_of_le (QMCLeafB.EngineRuntime.Rq_nonneg G) with hpos | hzero
    · exact memberAt_of_not_emptyBody hn hpos hE
    · exact memberAt_of_neg_eps_le hlo

#print axioms Round33M3.emptyBody_or_memberAt'

/-- **The leaf from an EXACT bit, with no cut content anywhere.**  The bit must decide `EmptyBody`;
`hFsmall` is the degenerate `n ≤ 1` slice only (there the published empty-body record's cut stream is
not available, but the identity supplies the witness for the `true` side — `memberAt_of_neg_eps_le`). -/
theorem solution_of_exactBit' (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (ho : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m)
    (hexact : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = true ↔ ¬ EmptyBody G t (P G))
    (hFsmall : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), G.n ≤ 1 → o G t = false →
      QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hlo : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = true →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) :
    QMCLeafB.FinishLine.SolutionStatement := by
  refine solution_of_lanes o ho hKm ?_ ?_
  · intro G t hbit
    rcases Nat.lt_or_ge G.n 2 with hlt | hn
    · exact memberAt_of_neg_eps_le (hlo G t hbit)
    · rcases emptyBody_or_memberAt' hn (hlo G t hbit) with hE | hM
      · exact absurd hE ((hexact G t).mp hbit)
      · exact hM
  · intro G t hbit
    by_cases hn : 2 ≤ G.n
    · refine falseLane_of_emptyBody (fun G' t' hb => ?_) G t hn hbit
      by_contra hne
      have h1 : o G' t' = true := (hexact G' t').mpr hne
      rw [hb] at h1
      exact Bool.noConfusion h1
    · exact hFsmall G t (by omega) hbit

#print axioms Round33M3.solution_of_exactBit'



/-- **`solution_of_exactBit'` with the round-count hypothesis discharged.**  The residual of the whole
direction, verbatim: a `Poly` bit that decides the emptiness of the relaxed body, plus the degenerate
`n ≤ 1` false-bit slice. -/
theorem solution_of_exactBit_final (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (ho : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hexact : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = true ↔ ¬ EmptyBody G t (P G))
    (hFsmall : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), G.n ≤ 1 → o G t = false →
      QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hlo : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = true →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_exactBit' o ho paramsKbc2_Km_pos hexact hFsmall hlo

#print axioms Round33M3.solution_of_exactBit_final

end Round33M3


