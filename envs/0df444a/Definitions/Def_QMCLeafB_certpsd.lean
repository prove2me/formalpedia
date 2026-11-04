-- Prove2me | Definitions.Def_QMCLeafB_certpsd
-- name    : QMCLeafB_certpsd
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:10:33.336769+00:00
-- url     : https://prove2.me/theorems/c6dfa312-bf73-422a-bed8-d3517a1dcc7f
-- title:
--   QMCLeafB certpsd
-- statement:
--   # `brick-certpsd` — exact rational Gram/PSD certificates (leaf B, phase 2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
/-
# `brick-certpsd` — exact rational Gram/PSD certificates (leaf B, phase 2)

## The problem

`QMCLeafB.IntegrationProbe.rat_sandwich` (merged, `MergeAll3_m8.lean`) turns rational primal/dual
data into the real sandwich `lowerValue ≤ S ≤ lowerValue + V/20000` **provided** the two premises

  `hXtest : ∀ x : Fin n → ℚ, 0 ≤ CastBridge.qf X x`
  `hytest : ∀ x : Fin n → ℚ, 0 ≤ CastBridge.qf (diagonal y + A) x`

hold.  Those are *infinite* checks: no engine can return them pointwise.  This file replaces them
by a **finite, exactly computable certificate**, and proves the replacement is *lossless*.

## The certificate

`GramCert n m` is the data `(V : Matrix (Fin n) (Fin m) ℚ, c : Fin m → ℚ)` certifying
`V * diagonal c * Vᵀ`.  `GramCert.check` (a `Bool`-valued `decide`) verifies the `n²` entrywise
rational equalities `V diag c Vᵀ = X` and the `m` sign tests `0 ≤ c k`.  It is a plain computable
function of rational data, hence `PolyProgram`-plumbable; `codeMat`/`checkCode` give the same
checker on the row-major `List ℚ` codes the runtime emits.

`qf` below has verbatim the body of `CastBridge.qf` (`fun M x => x ⬝ᵥ (M *ᵥ x)`), so every
statement here is *definitionally* a statement about the object `rat_sandwich` consumes.

## Main results

* `GramCert.qf_mat` : `qf (V diag c Vᵀ) x = ∑ k, c k * (∑ i, x i * V i k)^2` — the `L D Lᵀ`
  sum-of-squares identity, pure `ℚ`-algebra: no spectra, no limits, no reals.
* `premise_of_check`, `symm_of_check`, `primal_premise`, `dual_premise`,
  `integrationProbe_premise` : a passing check *implies* every `rat_sandwich` premise, including
  the symmetry halves (`Xᵀ = X`, `(diagonal y + A)ᵀ = diagonal y + A`) for free.
* `exists_gram` : **completeness** — every symmetric rational matrix whose quadratic form is
  nonnegative on all of `ℚⁿ` has a certificate.  Cholesky/`L D Lᵀ` by induction on `n`, with the
  zero-pivot skip rule `headRow_eq_zero` (a zero diagonal entry forces the row to vanish: the
  family `x ↦ 2 t b + c` cannot be nonnegative in `t` when `b ≠ 0`) and the Schur transfer
  `schur_nonneg` (`qf X (Fin.cons (-(b ⬝ᵥ y)/a) y) = qf (schur X a) y`).
* `premise_iff_exists_cert` : therefore the infinite premise is *equivalent* to the existence of a
  finite certificate — the engine can always produce one, and verification is exact arithmetic.
* `premise_of_check_shifted`, `abs_qf_le_of_entrywise_le` : the margin/robustness form (if `X` is
  entrywise `ε`-close to a certified `X₀` then `-ε·n·∑x² ≤ qf X x`), the `LeafB.ErrProp` shape.
* `premise_add_diagonal`, `exists_cert_add_diagonal` : adding a *nonnegative* diagonal shift keeps
  a certificate (`qf (diagonal y) x = ∑ y i x i²`), so a margin certificate for `X - δ·1`
  (`X ⪰ δ·1`) converts into an exact certificate for `X`.  This is the engine's margin→exact step.
* `c4_check`, `c4_premise` : a non-vacuous worked certificate, the dual slack `2·1 + A(C₄)` of the
  4-cycle Max-Cut SDP (eigenvalues `4, 2, 2, 0`: singular, so the zero-pivot path is exercised).

Self-contained (`import Mathlib` only), sorry-free, no axioms beyond Lean's own (audit at the end).
-/

open scoped BigOperators
open Matrix

namespace QMCLeafB.CertPSD

variable {n m : ℕ}


def qf (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) : ℚ := x ⬝ᵥ (M *ᵥ x)

/-- `qf` written out: verbatim the body of `QMCLeafB.CastBridge.qf`, hence definitionally the
object `QMCLeafB.IntegrationProbe.rat_sandwich` consumes.  A consumer that has `CastBridge.qf`
available only has to `rfl`-convert. -/
theorem qf_eq_dotProduct (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf M x = x ⬝ᵥ (M *ᵥ x) := rfl

theorem qf_eq_sum (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf M x = ∑ i, ∑ j, x i * (M i j * x j) := by
  simp only [qf, dotProduct, mulVec, Finset.mul_sum]

theorem qf_sub (M N : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf (M - N) x = qf M x - qf N x := by
  simp only [qf, sub_mulVec, dotProduct_sub]

theorem qf_smul (c : ℚ) (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf (c • M) x = c * qf M x := by
  rw [qf, Matrix.smul_mulVec, qf]
  simp only [dotProduct, Pi.smul_apply, Finset.mul_sum, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)


/-- `diagonal c *ᵥ y` is the pointwise product (point-free form of `Matrix.mulVec_diagonal`). -/
theorem diagonal_mulVec (c y : Fin m → ℚ) :
    diagonal c *ᵥ y = fun k => c k * y k := by
  funext k
  exact Matrix.mulVec_diagonal c y k

theorem qf_add (M N : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf (M + N) x = qf M x + qf N x := by
  simp only [qf, add_mulVec, dotProduct_add]

theorem qf_vecMulVec (u v x : Fin n → ℚ) :
    qf (vecMulVec u v) x = (u ⬝ᵥ x) * (v ⬝ᵥ x) := by
  rw [qf_eq_sum]
  simp only [vecMulVec_apply, dotProduct]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

def delta {n : ℕ} (j : Fin n) : Fin n → ℚ := fun i => if i = j then 1 else 0

theorem dotProduct_delta {n : ℕ} (b : Fin n → ℚ) (j : Fin n) : b ⬝ᵥ delta j = b j := by
  rw [dotProduct, Finset.sum_eq_single j]
  · simp [delta]
  · intro i _ hij
    simp [delta, hij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem qf_delta {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (j : Fin n) :
    qf M (delta j) = M j j := by
  rw [qf_eq_sum]
  have h1 : ∀ i, ∑ x, delta j i * (M i x * delta j x) = delta j i * M i j := by
    intro i
    rw [Finset.sum_eq_single j]
    · simp [delta]
    · intro b _ hbj
      simp [delta, hbj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  simp only [h1]
  rw [Finset.sum_eq_single j]
  · simp [delta]
  · intro b _ hbj
    simp [delta, hbj]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

variable {k : ℕ}

def tail (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) : Matrix (Fin k) (Fin k) ℚ :=
  X.submatrix Fin.succ Fin.succ

def headRow (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) : Fin k → ℚ := fun j => X 0 j.succ

theorem qf_cons (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (hsym : ∀ i j, X i j = X j i)
    (x0 : ℚ) (y : Fin k → ℚ) :
    qf X (Fin.cons x0 y) = X 0 0 * x0 ^ 2 + 2 * x0 * (headRow X ⬝ᵥ y) + qf (tail X) y := by
  rw [qf_eq_sum, qf_eq_sum]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ, tail, submatrix_apply,
    headRow, dotProduct]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ i, x0 * (X 0 i.succ * y i)) = x0 * ∑ i, X 0 i.succ * y i := by
    rw [Finset.mul_sum]
  have h2 : (∑ i, y i * (X i.succ 0 * x0)) = x0 * ∑ i, X 0 i.succ * y i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hsym i.succ 0]; ring)
  rw [h1, h2]
  ring

def schur (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (a : ℚ) : Matrix (Fin k) (Fin k) ℚ :=
  tail X - a⁻¹ • vecMulVec (headRow X) (headRow X)

theorem qf_schur (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (hsym : ∀ i j, X i j = X j i)
    {a : ℚ} (ha : X 0 0 = a) (ha0 : a ≠ 0) (y : Fin k → ℚ) :
    qf X (Fin.cons (-(headRow X ⬝ᵥ y) / a) y) = qf (schur X a) y := by
  rw [qf_cons X hsym, schur, qf_sub, qf_smul, qf_vecMulVec, ha]
  field_simp
  ring

theorem schur_transpose (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (hsym : ∀ i j, X i j = X j i)
    (a : ℚ) : (schur X a)ᵀ = schur X a := by
  ext i j
  simp only [transpose_apply, schur, tail, headRow, submatrix_apply, vecMulVec_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hsym i.succ j.succ]
  ring

theorem tail_transpose (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (hsym : ∀ i j, X i j = X j i) :
    (tail X)ᵀ = tail X := by
  ext i j
  simp only [transpose_apply, tail, submatrix_apply]
  exact hsym _ _

theorem schur_nonneg (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (hsym : ∀ i j, X i j = X j i)
    {a : ℚ} (ha : X 0 0 = a) (ha0 : a ≠ 0) (hX : ∀ x, 0 ≤ qf X x) :
    ∀ y, 0 ≤ qf (schur X a) y := by
  intro y
  rw [← qf_schur X hsym ha ha0 y]
  exact hX _

theorem tail_nonneg (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (hsym : ∀ i j, X i j = X j i)
    (hX : ∀ x, 0 ≤ qf X x) (h00 : X 0 0 = 0) : ∀ y, 0 ≤ qf (tail X) y := by
  intro y
  have h1 := hX (Fin.cons 0 y)
  rw [qf_cons X hsym, h00, zero_mul, zero_add] at h1
  simpa using h1

theorem headRow_eq_zero (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (hsym : ∀ i j, X i j = X j i)
    (hX : ∀ x, 0 ≤ qf X x) (h00 : X 0 0 = 0) : ∀ j, headRow X j = 0 := by
  intro j
  by_contra hb
  have h1 := hX (Fin.cons (-((tail X j j) + 1) / (2 * headRow X j)) (delta j))
  rw [qf_cons X hsym, h00, zero_mul, zero_add, dotProduct_delta, qf_delta] at h1
  have h2 : 2 * (-((tail X j j) + 1) / (2 * headRow X j)) * headRow X j
      = -((tail X j j) + 1) := by
    field_simp
  linarith

/-! ## The certificate structure (recap) -/

structure GramCert (n m : ℕ) where
  V : Matrix (Fin n) (Fin m) ℚ
  c : Fin m → ℚ

namespace GramCert

variable (C : GramCert n m)

def mat : Matrix (Fin n) (Fin n) ℚ := C.V * diagonal C.c * C.Vᵀ

theorem mat_apply (i j : Fin n) :
    C.mat i j = ∑ k, C.V i k * (C.c k * C.V j k) := by
  rw [mat, Matrix.mul_apply]
  simp only [mul_diagonal, transpose_apply]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem mat_transpose : C.matᵀ = C.mat := by
  ext i j
  simp only [transpose_apply, mat_apply]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **The sum-of-squares identity.**  The quadratic form of a Gram matrix is a nonnegative
combination of squares of the linear forms `x ↦ ∑ i, x i * V i k`. -/
theorem qf_mat (x : Fin n → ℚ) :
    qf C.mat x = ∑ k, C.c k * (∑ i, x i * C.V i k) ^ 2 := by
  rw [qf, mat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose,
    diagonal_mulVec, Matrix.dotProduct_mulVec]
  simp only [dotProduct, vecMul]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- Nonnegative weights ⟹ the certified form is nonnegative everywhere. -/
theorem qf_mat_nonneg (hc : ∀ k, 0 ≤ C.c k) (x : Fin n → ℚ) : 0 ≤ qf C.mat x := by
  rw [qf_mat]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hc k) (sq_nonneg _))

/-- The executable check: `n²` exact rational equalities and `m` exact sign tests. -/
def check (X : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  decide (C.mat = X ∧ ∀ k, 0 ≤ C.c k)

theorem check_spec (X : Matrix (Fin n) (Fin n) ℚ) :
    C.check X = true ↔ C.mat = X ∧ ∀ k, 0 ≤ C.c k := by
  simp [check]



end GramCert

/-! ## Lifting a certificate by one dimension -/

/-- Add a leading rank-one term: column `0` is `v` with weight `c0`, the rest is `W` lifted. -/
def liftCert (v : Fin (k+1) → ℚ) (c0 : ℚ) (W : GramCert k m) : GramCert (k+1) (m+1) :=
  ⟨fun i l => Fin.cases (v i) (fun l' => Fin.cases 0 (fun i' => W.V i' l') i) l,
   Fin.cons c0 W.c⟩

theorem liftCert_mat_00 (v : Fin (k+1) → ℚ) (c0 : ℚ) (W : GramCert k m) :
    (liftCert v c0 W).mat 0 0 = c0 * (v 0 * v 0) := by
  rw [GramCert.mat_apply, Fin.sum_univ_succ]
  simp [liftCert, Fin.cases_zero, Fin.cases_succ]
  ring

theorem liftCert_mat_0s (v : Fin (k+1) → ℚ) (c0 : ℚ) (W : GramCert k m) (q : Fin k) :
    (liftCert v c0 W).mat 0 q.succ = c0 * (v 0 * v q.succ) := by
  rw [GramCert.mat_apply, Fin.sum_univ_succ]
  simp [liftCert, Fin.cases_zero, Fin.cases_succ]
  ring

theorem liftCert_mat_s0 (v : Fin (k+1) → ℚ) (c0 : ℚ) (W : GramCert k m) (p : Fin k) :
    (liftCert v c0 W).mat p.succ 0 = c0 * (v p.succ * v 0) := by
  rw [GramCert.mat_apply, Fin.sum_univ_succ]
  simp [liftCert, Fin.cases_zero, Fin.cases_succ]
  ring

theorem liftCert_mat_ss (v : Fin (k+1) → ℚ) (c0 : ℚ) (W : GramCert k m) (p q : Fin k) :
    (liftCert v c0 W).mat p.succ q.succ = c0 * (v p.succ * v q.succ) + W.mat p q := by
  rw [GramCert.mat_apply, Fin.sum_univ_succ, GramCert.mat_apply]
  simp [liftCert, Fin.cases_zero, Fin.cases_succ]
  ring

theorem liftCert_c_nonneg (v : Fin (k+1) → ℚ) {c0 : ℚ} (hc0 : 0 ≤ c0)
    {W : GramCert k m} (hc : ∀ k, 0 ≤ W.c k) : ∀ l, 0 ≤ (liftCert v c0 W).c l := by
  intro l
  refine Fin.cases ?_ ?_ l
  · simpa [liftCert] using hc0
  · intro l'
    simpa [liftCert] using hc l'

/-! ## Completeness -/

theorem exists_gram : ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℚ), Xᵀ = X →
    (∀ x : Fin n → ℚ, 0 ≤ qf X x) →
      ∃ (m : ℕ) (C : GramCert n m), C.mat = X ∧ ∀ k : Fin m, 0 ≤ C.c k := by
  intro n
  induction n with
  | zero =>
    intro X hsym hX
    refine ⟨0, ⟨fun i => Fin.elim0 i, fun k => Fin.elim0 k⟩, ?_, ?_⟩
    · ext i
      exact Fin.elim0 i
    · intro k
      exact Fin.elim0 k
  | succ k ih =>
    intro X hsym hX
    have hsym' : ∀ i j, X i j = X j i := by
      intro i j
      have h := congrFun (congrFun hsym i) j
      simpa [Matrix.transpose_apply] using h.symm
    have h00nn : 0 ≤ X 0 0 := by
      have h := hX (delta (0 : Fin (k+1)))
      rwa [qf_delta] at h
    by_cases h00 : X 0 0 = 0
    · have hb : ∀ j, headRow X j = 0 := headRow_eq_zero X hsym' hX h00
      obtain ⟨m, W, hW, hc⟩ := ih (tail X) (tail_transpose X hsym')
        (tail_nonneg X hsym' hX h00)
      refine ⟨m+1, liftCert (fun _ => 0) 0 W, ?_, ?_⟩
      · ext i j
        refine Fin.cases ?_ ?_ i
        · refine Fin.cases ?_ ?_ j
          · rw [liftCert_mat_00]
            simp [h00]
          · intro q
            have hbq : X 0 q.succ = 0 := hb q
            rw [liftCert_mat_0s]
            simp [hbq]
        · intro p
          refine Fin.cases ?_ ?_ j
          · have hbp : X p.succ 0 = 0 := by rw [hsym' p.succ 0]; exact hb p
            rw [liftCert_mat_s0]
            simp [hbp]
          · intro q
            rw [liftCert_mat_ss]
            simp [hW, tail, submatrix_apply]
      · exact liftCert_c_nonneg (fun _ => 0) le_rfl hc
    · have ha : 0 < X 0 0 := lt_of_le_of_ne h00nn (Ne.symm h00)
      obtain ⟨m, W, hW, hc⟩ := ih (schur X (X 0 0)) (schur_transpose X hsym' _)
        (schur_nonneg X hsym' rfl h00 hX)
      refine ⟨m+1, liftCert (fun i => X i 0) (X 0 0)⁻¹ W, ?_, ?_⟩
      · ext i j
        refine Fin.cases ?_ ?_ i
        · refine Fin.cases ?_ ?_ j
          · rw [liftCert_mat_00]
            field_simp
          · intro q
            rw [liftCert_mat_0s, hsym' q.succ 0]
            field_simp
        · intro p
          refine Fin.cases ?_ ?_ j
          · rw [liftCert_mat_s0]
            field_simp
          · intro q
            rw [liftCert_mat_ss, hW]
            simp only [schur, tail, headRow, submatrix_apply, Matrix.sub_apply,
              Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
            rw [hsym' p.succ 0, hsym' q.succ 0]
            field_simp
            ring
      · exact liftCert_c_nonneg (fun i => X i 0) (inv_nonneg.mpr (le_of_lt ha)) hc



/-! ## 3. Soundness: the certificate gives the IntegrationProbe premise -/

/-- **Main soundness.**  A passing check gives the infinite premise of `rat_sandwich`. -/
theorem premise_of_check (C : GramCert n m) (X : Matrix (Fin n) (Fin n) ℚ)
    (h : C.check X = true) : ∀ x : Fin n → ℚ, 0 ≤ qf X x := by
  obtain ⟨rfl, hc⟩ := (GramCert.check_spec C X).mp h
  exact GramCert.qf_mat_nonneg C hc

/-- The symmetry half of the premise also comes for free from the certificate. -/
theorem symm_of_check (C : GramCert n m) (X : Matrix (Fin n) (Fin n) ℚ)
    (h : C.check X = true) : Xᵀ = X := by
  obtain ⟨rfl, -⟩ := (GramCert.check_spec C X).mp h
  exact GramCert.mat_transpose C

/-- The full premise triple for a primal point: symmetry, rational PSD, unit diagonal. -/
theorem primal_premise (C : GramCert n m) (X : Matrix (Fin n) (Fin n) ℚ)
    (h : C.check X = true) (hdiag : ∀ i, X i i = 1) :
    Xᵀ = X ∧ (∀ x : Fin n → ℚ, 0 ≤ qf X x) ∧ ∀ i, X i i = 1 :=
  ⟨symm_of_check C X h, premise_of_check C X h, hdiag⟩

/-- The premise pair for the dual slack `diagonal y + A`. -/
theorem dual_premise (C : GramCert n m) (A : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ)
    (h : C.check (diagonal y + A) = true) :
    (diagonal y + A)ᵀ = diagonal y + A ∧
      ∀ x : Fin n → ℚ, 0 ≤ qf (diagonal y + A) x :=
  ⟨symm_of_check C _ h, premise_of_check C _ h⟩

/-! ## 4. Both premises at once, in `rat_sandwich`'s exact shape -/

/-- **The two certificate-checked premises of `QMCLeafB.IntegrationProbe.rat_sandwich`.**  The
consumer supplies one `GramCert` for the primal point and one for the dual slack; the infinite
`∀ x : Fin n → ℚ` quantifiers are discharged by exact computation. -/
theorem integrationProbe_premise (CX CY : GramCert n m) (A X : Matrix (Fin n) (Fin n) ℚ)
    (y : Fin n → ℚ) (hX : CX.check X = true) (hY : CY.check (diagonal y + A) = true)
    (hdiag : ∀ i, X i i = 1) :
    Xᵀ = X ∧ (∀ x : Fin n → ℚ, 0 ≤ qf X x) ∧ (∀ i, X i i = 1) ∧
      (diagonal y + A)ᵀ = diagonal y + A ∧
        ∀ x : Fin n → ℚ, 0 ≤ qf (diagonal y + A) x :=
  ⟨symm_of_check CX X hX, premise_of_check CX X hX, hdiag,
    symm_of_check CY _ hY, premise_of_check CY _ hY⟩

/-! ## 5. Margins (the `LeafB.ErrProp` robustness shape)

If the *exact* certificate is for a nearby matrix, the certified form still bounds the
quadratic form of the actual matrix from below, with the standard `ε · n · ∑ x²` degradation. -/

/-- Entrywise perturbation bound: `|qf R x| ≤ ε * n * ∑ x²` when `|R i j| ≤ ε`. -/
theorem abs_qf_le_of_entrywise_le (R : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) {ε : ℚ}
    (hR : ∀ i j, |R i j| ≤ ε) (hε : 0 ≤ ε) :
    |qf R x| ≤ ε * (n : ℚ) * ∑ i, x i ^ 2 := by
  rw [qf_eq_sum]
  have h1 : |∑ i, ∑ j, x i * (R i j * x j)| ≤ ∑ i, ∑ j, |x i| * (ε * |x j|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    calc |x i * (R i j * x j)| = |x i| * (|R i j| * |x j|) := by rw [abs_mul, abs_mul]
      _ ≤ |x i| * (ε * |x j|) := by gcongr; exact hR i j
  have h2 : ∑ i, ∑ j, |x i| * (ε * |x j|) = ε * (∑ i, |x i|) * (∑ i, |x i|) := by
    have hinner : ∀ i, ∑ j, |x i| * (ε * |x j|) = |x i| * (ε * ∑ j, |x j|) := by
      intro i
      rw [Finset.mul_sum, Finset.mul_sum]
    simp only [hinner]
    rw [← Finset.sum_mul]
    ring
  have h3 : (∑ i, |x i|) * (∑ i, |x i|) ≤ (n : ℚ) * ∑ i, x i ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i => |x i|) (fun _ => (1 : ℚ))
    have hsq : (∑ i, |x i|) ^ 2 ≤ (n : ℚ) * ∑ i, x i ^ 2 := by
      simpa [Finset.sum_const, sq_abs, mul_comm] using h
    nlinarith [hsq]
  rw [h2] at h1
  have h4 : ε * (∑ i, |x i|) * (∑ i, |x i|) ≤ ε * ((n : ℚ) * ∑ i, x i ^ 2) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h3 hε
  nlinarith [h1, h4]

/-- **Robust soundness.**  If the certificate is exact for `X₀` and `X` differs from `X₀`
entrywise by at most `ε`, then `-ε n ∑ x² ≤ qf X x`: the margin form consumed by
`LeafB.ErrProp`. -/
theorem premise_of_check_shifted (C : GramCert n m) (X₀ X R : Matrix (Fin n) (Fin n) ℚ)
    (hX : C.check X₀ = true) (hXR : X = X₀ + R) {ε : ℚ}
    (hR : ∀ i j, |R i j| ≤ ε) (hε : 0 ≤ ε) :
    ∀ x : Fin n → ℚ, -(ε * (n : ℚ) * ∑ i, x i ^ 2) ≤ qf X x := by
  intro x
  have h0 := premise_of_check C X₀ hX x
  have h1 := abs_qf_le_of_entrywise_le R x hR hε
  have h2 : qf X x = qf X₀ x + qf R x := by
    rw [hXR, qf_add]
  rw [h2]
  have := neg_abs_le (qf R x)
  linarith



/-! ## 6. The characterization: the infinite premise is *equivalent* to a finite certificate -/

/-- **Completeness direction.**  A symmetric rational matrix with a nonnegative quadratic form has
a Gram certificate.  (This is the `L D Lᵀ` / Cholesky construction of `exists_gram`; the engine can
therefore always produce the data it must output.) -/
theorem exists_check_of_premise (X : Matrix (Fin n) (Fin n) ℚ) (hsym : Xᵀ = X)
    (h : ∀ x : Fin n → ℚ, 0 ≤ qf X x) :
    ∃ (m : ℕ) (C : GramCert n m), C.check X = true := by
  obtain ⟨m, C, hC, hc⟩ := exists_gram n X hsym h
  exact ⟨m, C, (GramCert.check_spec C X).mpr ⟨hC, hc⟩⟩

/-- **The infinite premise is exactly a finite certificate check.**  For a symmetric rational
matrix, `∀ x : Fin n → ℚ, 0 ≤ xᵀ M x` holds iff some `n × m` rational factor `V` and weights
`c ≥ 0` pass the executable check `V diag c Vᵀ = X`.  Nothing is lost by certifying. -/
theorem premise_iff_exists_cert (X : Matrix (Fin n) (Fin n) ℚ) (hsym : Xᵀ = X) :
    (∀ x : Fin n → ℚ, 0 ≤ qf X x) ↔ ∃ (m : ℕ) (C : GramCert n m), C.check X = true :=
  ⟨exists_check_of_premise X hsym, by
    rintro ⟨m, C, hC⟩
    exact premise_of_check C X hC⟩

/-- Engine-facing form: the certificate output is a *sound and complete* substitute for the
premise pair `(Xᵀ = X, ∀ x, 0 ≤ qf X x)`. -/
theorem premise_pair_of_cert (X : Matrix (Fin n) (Fin n) ℚ)
    (h : ∃ (m : ℕ) (C : GramCert n m), C.check X = true) :
    Xᵀ = X ∧ ∀ x : Fin n → ℚ, 0 ≤ qf X x := by
  obtain ⟨m, C, hC⟩ := h
  exact ⟨symm_of_check C X hC, premise_of_check C X hC⟩


/-! ## 6b. Margins → exact certificates (adding a nonnegative diagonal)

The engine's natural intermediate object is not exactly PSD but PSD *with a margin*: it can certify
`X - δ·1` (or `X` plus something), and needs the exact premise for `X`.  Adding a nonnegative
diagonal shift never destroys certifiability, and the shift is itself a certificate, so this is
free. -/

theorem qf_diagonal (d x : Fin n → ℚ) : qf (diagonal d) x = ∑ i, d i * x i ^ 2 := by
  rw [qf_eq_sum]
  have h1 : ∀ i, ∑ j, x i * (diagonal d i j * x j) = d i * x i ^ 2 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp [pow_two]; ring
    · intro b _ hbi
      rw [Matrix.diagonal_apply_ne d (Ne.symm hbi)]
      ring
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simp only [h1]

theorem diagonal_transpose (d : Fin n → ℚ) : (diagonal d)ᵀ = diagonal d := by
  ext i j
  simp only [transpose_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- A certified matrix plus a nonnegative diagonal still satisfies the premise. -/
theorem premise_add_diagonal (C : GramCert n m) (X : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ)
    (hX : C.check X = true) (hy : ∀ i, 0 ≤ y i) :
    ∀ x : Fin n → ℚ, 0 ≤ qf (diagonal y + X) x := by
  intro x
  rw [qf_add, qf_diagonal]
  have h0 := premise_of_check C X hX x
  have h1 : 0 ≤ ∑ i, y i * x i ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hy i) (sq_nonneg _))
  linarith

/-- Therefore the shifted matrix also has an exact certificate.  This is the step the engine uses
to turn a margin certificate (`X ⪰ δ·1`, i.e. a certificate for `X - δ·1`) into the exact premise
that `rat_sandwich` demands. -/
theorem exists_cert_add_diagonal (C : GramCert n m) (X : Matrix (Fin n) (Fin n) ℚ)
    (y : Fin n → ℚ) (hX : C.check X = true) (hy : ∀ i, 0 ≤ y i) :
    ∃ (m' : ℕ) (C' : GramCert n m'), C'.check (diagonal y + X) = true := by
  have hsym : (diagonal y + X)ᵀ = diagonal y + X := by
    rw [Matrix.transpose_add, diagonal_transpose, symm_of_check C X hX]
  exact exists_check_of_premise (diagonal y + X) hsym (premise_add_diagonal C X y hX hy)

/-! ## 7. Row-major `List ℚ` codes — the `PolyProgram` output shape

The engine emits rational matrices as row-major `List ℚ` (`MatQ` of `LeafB_MatQ`).  The checker
below is a plain computable function of that code: `List.getD` reads, `n²` exact rational
equalities, `m` sign tests.  Nothing in the definition is noncomputable, so the whole
verification is `PolyProgram`-plumbable (`matVec`/`dot`/`decide` on `List ℚ`). -/

/-- Row-major `List ℚ` code of an `n × n` rational matrix (out-of-range reads are `0`). -/
def codeMat (xs : List ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => xs.getD (i.val * n + j.val) 0

/-- The checker, as a computable function of the row-major code. -/
def checkCode (C : GramCert n m) (xs : List ℚ) : Bool := C.check (codeMat xs n)

theorem premise_of_checkCode (C : GramCert n m) (xs : List ℚ) (h : C.check (codeMat xs n) = true) :
    ∀ x : Fin n → ℚ, 0 ≤ qf (codeMat xs n) x :=
  premise_of_check C _ h

/-! ## 8. A worked, non-vacuous certificate

`X = 2·1 + A(C₄)` is the dual slack of the Max-Cut SDP for the 4-cycle with unit weights (take
`y = (2,2,2,2)`).  It is positive *semi*definite and singular (eigenvalues `4, 2, 2, 0`), so it is
only certifiable through the zero-pivot path of `exists_gram`.  Its Gram factor is the edge
incidence matrix: `∑_{edges} (eᵢ + eⱼ)(eᵢ + eⱼ)ᵀ = 2·1 + A(C₄)`. -/

/-- Edge-incidence factor of `2·1 + A(C₄)`. -/
def c4V : Matrix (Fin 4) (Fin 4) ℚ := !![1, 0, 0, 1; 1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1]

/-- Unit weights. -/
def c4c : Fin 4 → ℚ := fun _ => 1

/-- The dual slack `2·1 + A(C₄)` of the 4-cycle. -/
def c4X : Matrix (Fin 4) (Fin 4) ℚ := !![2, 1, 0, 1; 1, 2, 1, 0; 0, 1, 2, 1; 1, 0, 1, 2]

/-- The certificate verifies by exact rational arithmetic. -/
theorem c4_check : (⟨c4V, c4c⟩ : GramCert 4 4).check c4X = true := by
  rw [GramCert.check_spec]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GramCert.mat_apply, c4V, c4c, c4X, Fin.sum_univ_succ] <;> norm_num
  · intro k
    simp [c4c]

/-- Hence the premise holds for the 4-cycle dual slack, by pure computation. -/
theorem c4_premise : ∀ x : Fin 4 → ℚ, 0 ≤ qf c4X x :=
  premise_of_check ⟨c4V, c4c⟩ c4X c4_check

/-- And the checker really is an executable evaluator (`#eval` prints `true` below). -/
example : (⟨c4V, c4c⟩ : GramCert 4 4).check c4X = true := c4_check


/-! ## 9. Axiom audit -/

#print axioms QMCLeafB.CertPSD.premise_of_check
#print axioms QMCLeafB.CertPSD.symm_of_check
#print axioms QMCLeafB.CertPSD.integrationProbe_premise
#print axioms QMCLeafB.CertPSD.exists_gram
#print axioms QMCLeafB.CertPSD.premise_iff_exists_cert
#print axioms QMCLeafB.CertPSD.exists_cert_add_diagonal
#print axioms QMCLeafB.CertPSD.premise_of_check_shifted
#print axioms QMCLeafB.CertPSD.c4_premise


end QMCLeafB.CertPSD


