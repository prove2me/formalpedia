-- Prove2me | Definitions.Def_RPLib_S1_Hecke
-- name    : RPLib_S1_Hecke
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:18:35.659477+00:00
-- url     : https://prove2.me/theorems/cfe49e7b-44e9-4358-af5c-586854ba525c
-- title:
--   Hecke operators $T_p$ and $U_p$ on $S_k(\Gamma_1(M))$
-- statement:
--   For a prime $p$ the Hecke operator on $S_k(\Gamma_1(M))$ is $$T_p f = \sum_{j=0}^{p-1} f|_k\begin{pmatrix}1&j\\0&p\end{pmatrix} + [p \nmid M]\, (\langle p\rangle f)|_k\begin{pmatrix}p&0\\0&1\end{pmatrix},$$ written $U_p$ when $p \mid M$. The file proves that $T_p f$ is again a cusp form on $\Gamma_1(M)$, that $T_p$ commutes with the diamond operators and preserves each $S_k(M,\chi)$, and the coefficient formula $a_n(T_p f) = a_{np}(f) + \chi(p)p^{k-1}a_{n/p}(f)$ on $S_k(M,\chi)$.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 5.3

import Mathlib
import Definitions.Def_RPLib_S1_Diamond
import Definitions.Def_RPLib_S1_QExp

/-!
# S1-HECKE: Hecke operators `T_p` (`p ∤ M`) and `U_p` (`p ∣ M`) on `S_k(Γ₁(M))`

`heckeT p k f = Σ_{j<p} f ∣[k] [[1, j], [0, p]] + (if p ∤ M then (⟨p⟩ f) ∣[k] diag(p, 1) else 0)`
(Mathlib slash normalisation `det^(k-1)`). Invariance under `Γ₁(M)` is proved by the coset permutation
`β_r γ = γ' β_σ(r)` (`γ' ∈ Γ₁(M)`), for every `γ ∈ Γ₀(M)` at once; this also gives `T_p ⟨d⟩ = ⟨d⟩ T_p`.
-/

open UpperHalfPlane ModularForm MatrixGroups CongruenceSubgroup ConjAct
open scoped Pointwise

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.Hecke

open RamanujanPetersson.Diamond RamanujanPetersson.QExp

/-! ### Integer matrices in `GL(2, ℝ)` -/

/-- An integer matrix with nonzero determinant, in `GL(2, ℚ)`. -/
def toGLQ (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (A.map (Int.castRingHom ℚ)) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Int.cast_ne_zero).mpr hA)

/-- An integer matrix with nonzero determinant, in `GL(2, ℝ)`. -/
def toGL (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (toGLQ A hA)

lemma toGL_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) (i j : Fin 2) :
    (toGL A hA : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := by
  simp [toGL, toGLQ, Matrix.GeneralLinearGroup.map_apply]

lemma toGL_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (hAB : (A * B).det ≠ 0) : toGL (A * B) hAB = toGL A hA * toGL B hB := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, toGL_apply, Matrix.mul_apply]
  simp only [toGL_apply]
  push_cast
  rfl

lemma toGL_SL (γ : SL(2, ℤ)) (h : (γ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0) :
    toGL (γ : Matrix (Fin 2) (Fin 2) ℤ) h = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [toGL_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  simp

lemma toGL_injective (A B : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (h : toGL A hA = toGL B hB) : A = B := by
  ext i j
  have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  simp only [toGL_apply] at this
  exact_mod_cast this

lemma det_SL_ne (γ : SL(2, ℤ)) : (γ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  rw [Matrix.SpecialLinearGroup.det_coe]; exact one_ne_zero

lemma det_SL_mul_ne (γ : SL(2, ℤ)) {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) :
    ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul]; exact hA

lemma mapGL_mul_toGL (γ : SL(2, ℤ)) (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) :
    Matrix.SpecialLinearGroup.mapGL ℝ γ * toGL A hA =
      toGL ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A) (det_SL_mul_ne γ hA) := by
  rw [toGL_mul _ _ (det_SL_ne γ) hA, toGL_SL]

lemma toGL_mul_mapGL (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) (γ : SL(2, ℤ)) :
    toGL A hA * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      toGL (A * (γ : Matrix (Fin 2) (Fin 2) ℤ))
        (by rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one]; exact hA) := by
  rw [toGL_mul _ _ hA (det_SL_ne γ), toGL_SL]

lemma toGL_congr {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) (h : A = B) :
    toGL A hA = toGL B hB := by
  subst h; rfl

lemma smul_slash_of_det_pos (k : ℤ) (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (c : ℂ) (F : ℍ → ℂ) :
    (c • F) ∣[k] g = c • (F ∣[k] g) := by
  rw [smul_slash, σ, if_pos hg]
  rfl

/-! ### The set `Δ_p(M)` and coset representatives -/

variable {M p : ℕ}

/-- `Δ_p(M)`: integer matrices of determinant `p`, congruent to `[[1, *], [0, *]]` mod `M`. -/
def IsDelta (M p : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  A.det = p ∧ ((A 1 0 : ℤ) : ZMod M) = 0 ∧ ((A 0 0 : ℤ) : ZMod M) = 1

lemma isDelta_conj {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsDelta M p A) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 M) :
    IsDelta M p (((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * A * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
  obtain ⟨hdet, h10, h00⟩ := hA
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.1 hγ
  have hdγ : ((γ 0 0 : ℤ) : ZMod M) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod M)) h
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe,
      Matrix.SpecialLinearGroup.det_coe, hdet, one_mul, mul_one]
  · simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    rw [hc, h10]
    ring
  · simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    rw [hc, h10, h00]
    rw [hc] at hdγ
    linear_combination hdγ

/-- `[[1, j], [0, p]]`. -/
def repU (p j : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, (j : ℤ); 0, (p : ℤ)]

/-- `σ_p diag(p, 1) = [[x p, y], [M p, p]]` for `x p - y M = 1`. -/
def repInf (M p : ℕ) (x y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![x * p, y; (M : ℤ) * p, p]

lemma det_repU (p j : ℕ) : (repU p j).det = p := by
  simp [repU, Matrix.det_fin_two_of]

lemma det_repInf (x y : ℤ) (hxy : x * p - y * M = 1) : (repInf M p x y).det = p := by
  rw [repInf, Matrix.det_fin_two_of]; linear_combination (p : ℤ) * hxy

lemma isDelta_repU (p j : ℕ) : IsDelta M p (repU p j) :=
  ⟨det_repU p j, by simp [repU], by simp [repU]⟩

lemma isDelta_repInf (x y : ℤ) (hxy : x * p - y * M = 1) : IsDelta M p (repInf M p x y) := by
  refine ⟨det_repInf x y hxy, by simp [repInf], ?_⟩
  have h := congrArg (fun z : ℤ => (z : ZMod M)) hxy
  simp only [repInf, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast at h ⊢
  rw [ZMod.natCast_self, mul_zero, sub_zero] at h
  exact h

/-- Column condition for `A ∈ Γ₁ [[1, j], [0, p]]`. -/
def CondU (p : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) (j : ℕ) : Prop :=
  ((A 0 1 : ℤ) : ZMod p) = (A 0 0 : ZMod p) * j ∧ ((A 1 1 : ℤ) : ZMod p) = (A 1 0 : ZMod p) * j

/-- Column condition for `A ∈ Γ₁ σ_p diag(p, 1)`. -/
def CondInf (p : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ((A 0 0 : ℤ) : ZMod p) = 0 ∧ ((A 1 0 : ℤ) : ZMod p) = 0

section prime

variable [hp : Fact p.Prime]

lemma not_all_zero {A : Matrix (Fin 2) (Fin 2) ℤ} (hdet : A.det = p)
    (h00 : ((A 0 0 : ℤ) : ZMod p) = 0) (h01 : ((A 0 1 : ℤ) : ZMod p) = 0)
    (h10 : ((A 1 0 : ℤ) : ZMod p) = 0) (h11 : ((A 1 1 : ℤ) : ZMod p) = 0) : False := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h00 h01 h10 h11
  obtain ⟨a, ha⟩ := h00; obtain ⟨b, hb⟩ := h01; obtain ⟨c, hc⟩ := h10; obtain ⟨d, hd⟩ := h11
  rw [Matrix.det_fin_two, ha, hb, hc, hd] at hdet
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h1 : (p : ℤ) * (a * d - b * c) = 1 := by
    apply mul_left_cancel₀ hp0; linear_combination hdet
  have h2 : (p : ℤ) ∣ 1 := ⟨_, h1.symm⟩
  have h3 : p ∣ 1 := by exact_mod_cast h2
  exact hp.out.not_dvd_one h3

lemma condU_unique {A : Matrix (Fin 2) (Fin 2) ℤ} (hdet : A.det = p) {i j : ℕ} (hi : i < p)
    (hj : j < p) (h1 : CondU p A i) (h2 : CondU p A j) : i = j := by
  by_contra hij
  have hne : ((i : ZMod p) - j) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hij
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  have ha : ((A 0 0 : ℤ) : ZMod p) = 0 := by
    have : ((A 0 0 : ℤ) : ZMod p) * ((i : ZMod p) - j) = 0 := by
      linear_combination h2.1 - h1.1
    exact (mul_eq_zero.mp this).resolve_right hne
  have hc : ((A 1 0 : ℤ) : ZMod p) = 0 := by
    have : ((A 1 0 : ℤ) : ZMod p) * ((i : ZMod p) - j) = 0 := by
      linear_combination h2.2 - h1.2
    exact (mul_eq_zero.mp this).resolve_right hne
  exact not_all_zero hdet ha (by rw [h1.1, ha, zero_mul]) hc (by rw [h1.2, hc, zero_mul])

lemma condU_condInf {A : Matrix (Fin 2) (Fin 2) ℤ} (hdet : A.det = p) {i : ℕ}
    (h1 : CondU p A i) (h2 : CondInf p A) : False :=
  not_all_zero hdet h2.1 (by rw [h1.1, h2.1, zero_mul]) h2.2 (by rw [h1.2, h2.2, zero_mul])

lemma exists_condU {A : Matrix (Fin 2) (Fin 2) ℤ} (hdet : A.det = p) (h : ¬ CondInf p A) :
    ∃ j < p, CondU p A j := by
  have hd : ((A 0 0 : ℤ) : ZMod p) * (A 1 1 : ℤ) - (A 0 1 : ℤ) * (A 1 0 : ℤ) = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) hdet
    rw [Matrix.det_fin_two] at this
    push_cast at this
    rw [this, ZMod.natCast_self]
  by_cases ha : ((A 0 0 : ℤ) : ZMod p) = 0
  · have hc : ((A 1 0 : ℤ) : ZMod p) ≠ 0 := fun hc => h ⟨ha, hc⟩
    refine ⟨(((A 1 1 : ℤ) : ZMod p) * ((A 1 0 : ℤ) : ZMod p)⁻¹).val, ZMod.val_lt _, ?_, ?_⟩
    · rw [ZMod.natCast_zmod_val, ha, zero_mul]
      rw [ha, zero_mul, zero_sub, neg_eq_zero] at hd
      exact (mul_eq_zero.mp hd).resolve_right hc
    · rw [ZMod.natCast_zmod_val]
      field_simp
  · refine ⟨(((A 0 1 : ℤ) : ZMod p) * ((A 0 0 : ℤ) : ZMod p)⁻¹).val, ZMod.val_lt _, ?_, ?_⟩
    · rw [ZMod.natCast_zmod_val]
      field_simp
    · rw [ZMod.natCast_zmod_val]
      field_simp
      linear_combination hd

lemma mem_Gamma1_of (δ : SL(2, ℤ)) (h00 : ((δ 0 0 : ℤ) : ZMod M) = 1)
    (h10 : ((δ 1 0 : ℤ) : ZMod M) = 0) : δ ∈ Gamma1 M := by
  have h := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at h
  have h' := congrArg (fun z : ℤ => (z : ZMod M)) h
  push_cast at h'
  rw [h00, h10, one_mul, mul_zero, sub_zero] at h'
  exact (Gamma1_mem M δ).2 ⟨h00, h', h10⟩

omit hp in
lemma condU_of_mul (δ : Matrix (Fin 2) (Fin 2) ℤ) (j : ℕ) : CondU p (δ * repU p j) j := by
  simp only [CondU, repU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    ]
  push_cast
  simp

omit hp in
lemma condInf_of_mul (δ : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℤ) : CondInf p (δ * repInf M p x y) := by
  simp only [CondInf, repInf, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    ]
  push_cast
  simp

lemma factor_U {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsDelta M p A) {j : ℕ} (hc : CondU p A j) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧ (δ : Matrix (Fin 2) (Fin 2) ℤ) * repU p j = A := by
  obtain ⟨hdet, h10, h00⟩ := hA
  have hu : (p : ℤ) ∣ A 0 1 - A 0 0 * j := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hc.1]; ring
  have hv : (p : ℤ) ∣ A 1 1 - A 1 0 * j := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hc.2]; ring
  obtain ⟨u, hu⟩ := hu
  obtain ⟨v, hv⟩ := hv
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [Matrix.det_fin_two] at hdet
  have hδ : A 0 0 * v - u * A 1 0 = 1 := by
    apply mul_left_cancel₀ hp0
    linear_combination (-A 0 0) * hv + A 1 0 * hu + hdet
  let δ : SL(2, ℤ) := ⟨!![A 0 0, u; A 1 0, v], by rw [Matrix.det_fin_two_of]; exact hδ⟩
  refine ⟨δ, mem_Gamma1_of δ (by simpa [δ] using h00) (by simpa [δ] using h10), ?_⟩
  ext i j'
  fin_cases i <;> fin_cases j' <;>
    simp [δ, repU, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -hu
  · linear_combination -hv

lemma factor_Inf {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsDelta M p A) (hc : CondInf p A) (x y : ℤ)
    (hxy : x * p - y * M = 1) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧ (δ : Matrix (Fin 2) (Fin 2) ℤ) * repInf M p x y = A := by
  obtain ⟨hdet, h10, h00⟩ := hA
  obtain ⟨a', ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hc.1
  obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hc.2
  let D : Matrix (Fin 2) (Fin 2) ℤ :=
    !![A 0 0 - A 0 1 * M, A 0 1 * x - a' * y; A 1 0 - A 1 1 * M, A 1 1 * x - c' * y]
  have hprod : D * repInf M p x y = A := by
    ext i j'
    fin_cases i <;> fin_cases j' <;> simp [D, repInf, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (x * (p : ℤ) - 1) * ha + (p : ℤ) * a' * hxy
    · linear_combination (A 0 1) * hxy + y * ha
    · linear_combination (x * (p : ℤ) - 1) * hc' + (p : ℤ) * c' * hxy
    · linear_combination (A 1 1) * hxy + y * hc'
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hD : D.det = 1 := by
    have h := congrArg Matrix.det hprod
    rw [Matrix.det_mul, det_repInf x y hxy, hdet] at h
    exact mul_right_cancel₀ hp0 (by rw [h, one_mul])
  let δ : SL(2, ℤ) := ⟨D, hD⟩
  refine ⟨δ, mem_Gamma1_of δ ?_ ?_, hprod⟩
  · simp only [δ, D, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast; rw [h00, ZMod.natCast_self]; ring
  · simp only [δ, D, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons]
    push_cast; rw [h10, ZMod.natCast_self]; ring

end prime

/-! ### Coset permutation and the slash identity -/

/-- If `β` is a set of representatives of `Γ₁(M) \ Δ` stable under `Γ₀(M)`-conjugation, then for every
`γ ∈ Γ₀(M)` and every `Γ₁(M)`-invariant `F`, `(Σ_r F ∣ β_r) ∣ γ = Σ_r (F ∣ γ) ∣ β_r`. -/
theorem sum_slash_Gamma0 {R : Type*} [Fintype R] (β : R → GL (Fin 2) ℝ)
    (hE : ∀ r (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ∃ s, ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧
      Matrix.SpecialLinearGroup.mapGL ℝ δ * β s =
        (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ * β r * Matrix.SpecialLinearGroup.mapGL ℝ γ)
    (hU : ∀ r s (δ : SL(2, ℤ)), β r = Matrix.SpecialLinearGroup.mapGL ℝ δ * β s → r = s)
    (k : ℤ) (F : ℍ → ℂ)
    (hF : ∀ δ : SL(2, ℤ), δ ∈ Gamma1 M → F ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ δ = F)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    (∑ r, F ∣[k] β r) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ =
      ∑ r, (F ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ) ∣[k] β r := by
  choose σ δ hδ1 hδeq using fun r => hE r γ hγ
  set G := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hβ : ∀ r, β r = G * Matrix.SpecialLinearGroup.mapGL ℝ (δ r) * β (σ r) * G⁻¹ := by
    intro r
    rw [mul_assoc G, hδeq r]
    group
  have hinj : Function.Injective σ := by
    intro r r' h
    apply hU r r' (γ * δ r * (δ r')⁻¹ * γ⁻¹)
    rw [hβ r, hβ r', h]
    simp only [map_mul, map_inv, ← hG]
    group
  have hFG : ∀ r, F ∣[k] (β r * G) = (F ∣[k] G) ∣[k] β (σ r) := by
    intro r
    have e : β r * G = G * Matrix.SpecialLinearGroup.mapGL ℝ (δ r) * β (σ r) := by
      rw [hβ r]; group
    rw [e, SlashAction.slash_mul, SlashAction.slash_mul]
    congr 1
    have e2 : G * Matrix.SpecialLinearGroup.mapGL ℝ (δ r) =
        Matrix.SpecialLinearGroup.mapGL ℝ (γ * δ r * γ⁻¹) * G := by
      simp only [map_mul, map_inv, ← hG]; group
    rw [← SlashAction.slash_mul, e2, SlashAction.slash_mul,
      hF _ (conj_mem_Gamma1 hγ (hδ1 r))]
  rw [SlashAction.sum_slash]
  simp only [← SlashAction.slash_mul, hFG]
  exact Fintype.sum_bijective σ (Finite.injective_iff_bijective.mp hinj) _ _ (fun r => rfl)

/-- Representatives indexed by `R`, with a matching column condition, give `hE` and `hU`. -/
theorem reps_spec {R : Type*} (β : R → Matrix (Fin 2) (Fin 2) ℤ) (hβ : ∀ r, (β r).det ≠ 0)
    (Cond : Matrix (Fin 2) (Fin 2) ℤ → R → Prop)
    (c1 : ∀ A, IsDelta M p A → ∃ r, Cond A r)
    (c2 : ∀ A r, IsDelta M p A → Cond A r → ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧
      (δ : Matrix (Fin 2) (Fin 2) ℤ) * β r = A)
    (c3 : ∀ (δ : Matrix (Fin 2) (Fin 2) ℤ) r, Cond (δ * β r) r)
    (c4 : ∀ A r s, A.det = (p : ℤ) → Cond A r → Cond A s → r = s)
    (c5 : ∀ r, IsDelta M p (β r)) :
    (∀ r (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ∃ s, ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧
      Matrix.SpecialLinearGroup.mapGL ℝ δ * toGL (β s) (hβ s) =
        (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ * toGL (β r) (hβ r) *
          Matrix.SpecialLinearGroup.mapGL ℝ γ) ∧
    (∀ r s (δ : SL(2, ℤ)), toGL (β r) (hβ r) =
      Matrix.SpecialLinearGroup.mapGL ℝ δ * toGL (β s) (hβ s) → r = s) := by
  refine ⟨fun r γ hγ => ?_, fun r s δ h => ?_⟩
  · have hA := isDelta_conj (c5 r) hγ
    obtain ⟨s, hs⟩ := c1 _ hA
    obtain ⟨δ, hδ, he⟩ := c2 _ s hA hs
    refine ⟨s, δ, hδ, ?_⟩
    rw [mapGL_mul_toGL, ← map_inv (Matrix.SpecialLinearGroup.mapGL ℝ) γ, mapGL_mul_toGL,
      toGL_mul_mapGL]
    exact toGL_congr _ _ he
  · rw [mapGL_mul_toGL] at h
    have h' := toGL_injective _ _ _ _ h
    have hr : Cond (β r) r := by simpa using c3 1 r
    have hs : Cond (β r) s := by rw [h']; exact c3 _ s
    exact c4 _ r s (c5 r).1 hr hs

end RamanujanPetersson.Hecke

/-! ## Part 2: the Hecke operator `T_p` on `S_k(Γ₁(M))` -/

namespace RamanujanPetersson.Hecke

open RamanujanPetersson.Diamond RamanujanPetersson.QExp
open scoped Manifold

section hecke

variable {M : ℕ} (p : ℕ) [hp : Fact p.Prime]

lemma prime_pos : 0 < p := hp.out.pos

lemma hadU : (1 : ℝ) * p ≠ 0 := by
  rw [one_mul]; exact_mod_cast hp.out.ne_zero

lemma hadD : (p : ℝ) * 1 ≠ 0 := by
  rw [mul_one]; exact_mod_cast hp.out.ne_zero

/-- `diag(p, 1)` as an integer matrix. -/
def diagP : Matrix (Fin 2) (Fin 2) ℤ := !![(p : ℤ), 0; 0, 1]

variable {p}

lemma coprime_of_not_dvd (h : ¬ p ∣ M) : p.Coprime M :=
  (Nat.Prime.coprime_iff_not_dvd hp.out).2 h

/-- `p` as a unit mod `M`, for `p ∤ M`. -/
abbrev unitP (h : ¬ p ∣ M) : (ZMod M)ˣ := ZMod.unitOfCoprime p (coprime_of_not_dvd h)

lemma isDelta_det_ne {A : Matrix (Fin 2) (Fin 2) ℤ} (h : IsDelta M p A) : A.det ≠ 0 := by
  rw [h.1]; exact_mod_cast hp.out.ne_zero

lemma det_repU_ne (j : ℕ) : (repU p j).det ≠ 0 := by
  rw [det_repU]; exact_mod_cast hp.out.ne_zero

lemma det_diagP_ne : (diagP p).det ≠ 0 := by
  rw [diagP, Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero]; exact_mod_cast hp.out.ne_zero

lemma upperTri_U_eq (j : ℕ) : upperTri 1 j p (hadU p) = toGL (repU p j) (det_repU_ne j) := by
  refine Matrix.GeneralLinearGroup.ext fun i l => ?_
  rw [toGL_apply, upperTri_val]
  fin_cases i <;> fin_cases l <;> simp [repU]

lemma upperTri_D_eq : upperTri p 0 1 (hadD p) = toGL (diagP p) det_diagP_ne := by
  refine Matrix.GeneralLinearGroup.ext fun i l => ?_
  rw [toGL_apply, upperTri_val]
  fin_cases i <;> fin_cases l <;> simp [diagP]

/-- `σ_p = [[x, y], [M, p]] ∈ Γ₀(M)` for `x p - y M = 1`. -/
def sigmaP (M p : ℕ) (x y : ℤ) (hxy : x * p - y * M = 1) : SL(2, ℤ) :=
  ⟨!![x, y; (M : ℤ), p], by rw [Matrix.det_fin_two_of]; exact hxy⟩

omit hp in
lemma sigmaP_mem (x y : ℤ) (hxy : x * p - y * M = 1) : sigmaP M p x y hxy ∈ Gamma0 M := by
  rw [Gamma0_mem]; simp [sigmaP]

lemma det_repInf_ne (x y : ℤ) (hxy : x * p - y * M = 1) : (repInf M p x y).det ≠ 0 := by
  rw [det_repInf x y hxy]; exact_mod_cast hp.out.ne_zero

lemma sigmaP_mul_diag (x y : ℤ) (hxy : x * p - y * M = 1) :
    Matrix.SpecialLinearGroup.mapGL ℝ (sigmaP M p x y hxy) * upperTri p 0 1 (hadD p) =
      toGL (repInf M p x y) (det_repInf_ne x y hxy) := by
  rw [← toGL_SL _ (det_SL_ne _), upperTri_D_eq,
    ← toGL_mul ((sigmaP M p x y hxy : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (diagP p) (det_SL_ne _)
      det_diagP_ne (by rw [Matrix.det_mul]; exact mul_ne_zero (det_SL_ne _) det_diagP_ne)]
  apply toGL_congr
  ext i l
  fin_cases i <;> fin_cases l <;> simp [sigmaP, diagP, repInf, Matrix.mul_apply, Fin.sum_univ_two]

lemma not_condInf_of_dvd (hpM : p ∣ M) {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsDelta M p A) :
    ¬ CondInf p A := by
  intro h
  have h1 : ((A 0 0 : ℤ) : ZMod p) = 1 := by
    have := congrArg (ZMod.castHom hpM (ZMod p)) hA.2.2
    rwa [map_intCast, map_one] at this
  rw [h.1] at h1
  exact zero_ne_one h1

/-- Representatives for `p ∤ M`: `none ↦ σ_p diag(p, 1)`, `some j ↦ [[1, j], [0, p]]`. -/
def betaOpt (M p : ℕ) (x y : ℤ) : Option (Fin p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => repInf M p x y
  | some j => repU p j

/-- Column conditions for `p ∤ M`. -/
def condOpt (p : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) : Option (Fin p) → Prop
  | none => CondInf p A
  | some j => CondU p A j

omit hp in
lemma isDelta_betaOpt (x y : ℤ) (hxy : x * p - y * M = 1) :
    ∀ r, IsDelta M p (betaOpt M p x y r)
  | none => isDelta_repInf x y hxy
  | some j => isDelta_repU p j

variable [NeZero M]

variable (p) in
/-- The Hecke operator on functions:
`Σ_{j<p} f ∣[k] [[1, j], [0, p]] + [p ∤ M] (⟨p⟩ f) ∣[k] diag(p, 1)`. -/
def heckeFun (k : ℤ) (f : S1 M k) : ℍ → ℂ :=
  (∑ j ∈ Finset.range p, ⇑f ∣[k] upperTri 1 j p (hadU p)) +
    (if h : p ∣ M then 0 else ⇑(diamond k (unitP h) f) ∣[k] upperTri p 0 1 (hadD p))

lemma coe_diamond_unitP (k : ℤ) (h : ¬ p ∣ M) (x y : ℤ) (hxy : x * p - y * M = 1) (f : S1 M k) :
    ⇑(diamond k (unitP h) f) = ⇑f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ (sigmaP M p x y hxy) :=
  coe_diamond_of_mem k (sigmaP_mem x y hxy) _ (by simp [sigmaP, unitP]) f

lemma heckeFun_eq_sum_dvd (k : ℤ) (hpM : p ∣ M) (g : S1 M k) :
    heckeFun p k g = ∑ j : Fin p, ⇑g ∣[k] toGL (repU p j) (det_repU_ne j) := by
  rw [heckeFun, dif_pos hpM, add_zero, Finset.sum_range]
  exact Finset.sum_congr rfl fun j _ => by rw [upperTri_U_eq]

lemma heckeFun_eq_sum_ndvd (k : ℤ) (hpM : ¬ p ∣ M) (x y : ℤ) (hxy : x * p - y * M = 1)
    (g : S1 M k) :
    heckeFun p k g = ∑ r : Option (Fin p),
      ⇑g ∣[k] toGL (betaOpt M p x y r) (isDelta_det_ne (isDelta_betaOpt x y hxy r)) := by
  rw [Fintype.sum_option, heckeFun, dif_neg hpM, add_comm, Finset.sum_range]
  congr 1
  · show _ = ⇑g ∣[k] toGL (repInf M p x y) _
    rw [coe_diamond_unitP k hpM x y hxy, ← SlashAction.slash_mul, sigmaP_mul_diag]
  · refine Finset.sum_congr rfl fun j _ => ?_
    show _ = ⇑g ∣[k] toGL (repU p j) _
    rw [upperTri_U_eq]

/-- The generic `Γ₀(M)`-equivariance, from any set of representatives. -/
theorem heckeFun_slash_of_reps (k : ℤ) {R : Type} [Fintype R] (β : R → Matrix (Fin 2) (Fin 2) ℤ)
    (hβ : ∀ r, (β r).det ≠ 0) (Cond : Matrix (Fin 2) (Fin 2) ℤ → R → Prop)
    (c1 : ∀ A, IsDelta M p A → ∃ r, Cond A r)
    (c2 : ∀ A r, IsDelta M p A → Cond A r → ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧
      (δ : Matrix (Fin 2) (Fin 2) ℤ) * β r = A)
    (c3 : ∀ (δ : Matrix (Fin 2) (Fin 2) ℤ) r, Cond (δ * β r) r)
    (c4 : ∀ A r s, A.det = (p : ℤ) → Cond A r → Cond A s → r = s)
    (c5 : ∀ r, IsDelta M p (β r))
    (H : ∀ g : S1 M k, heckeFun p k g = ∑ r, ⇑g ∣[k] toGL (β r) (hβ r))
    (f : S1 M k) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    heckeFun p k f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ =
      heckeFun p k (slashG0 k ⟨γ, hγ⟩ f) := by
  obtain ⟨hE, hU⟩ := reps_spec β hβ Cond c1 c2 c3 c4 c5
  rw [H, sum_slash_Gamma0 _ hE hU k _ (fun δ hδ => slash_Gamma1 k f hδ) hγ, H]
  rfl

/-- **Key identity**: `(T_p f) ∣[k] γ = T_p (f ∣[k] γ)` for every `γ ∈ Γ₀(M)`. -/
theorem heckeFun_slash (k : ℤ) (f : S1 M k) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    heckeFun p k f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ =
      heckeFun p k (slashG0 k ⟨γ, hγ⟩ f) := by
  by_cases hpM : p ∣ M
  · refine heckeFun_slash_of_reps k (fun j : Fin p => repU p j) (fun j => det_repU_ne j)
      (fun A j => CondU p A j) ?_ ?_ ?_ ?_ ?_ (heckeFun_eq_sum_dvd k hpM) f hγ
    · intro A hA
      obtain ⟨j, hj, hc⟩ := exists_condU hA.1 (not_condInf_of_dvd hpM hA)
      exact ⟨⟨j, hj⟩, hc⟩
    · intro A j hA hc; exact factor_U hA hc
    · intro δ j; exact condU_of_mul δ j
    · intro A i j hdet hi hj; exact Fin.ext (condU_unique hdet i.isLt j.isLt hi hj)
    · intro j; exact isDelta_repU p j
  · obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (coprime_of_not_dvd hpM)
    have hxy : u * p - (-v) * M = 1 := by linear_combination huv
    refine heckeFun_slash_of_reps k (betaOpt M p u (-v))
      (fun r => isDelta_det_ne (isDelta_betaOpt u (-v) hxy r)) (condOpt p) ?_ ?_ ?_ ?_
      (isDelta_betaOpt u (-v) hxy) (heckeFun_eq_sum_ndvd k hpM u (-v) hxy) f hγ
    · intro A hA
      by_cases hc : CondInf p A
      · exact ⟨none, hc⟩
      · obtain ⟨j, hj, hcj⟩ := exists_condU hA.1 hc
        exact ⟨some ⟨j, hj⟩, hcj⟩
    · intro A r hA hc
      cases r with
      | none => exact factor_Inf hA hc u (-v) hxy
      | some j => exact factor_U hA hc
    · intro δ r
      cases r with
      | none => exact condInf_of_mul δ u (-v)
      | some j => exact condU_of_mul δ j
    · intro A r s hdet hr hs
      cases r with
      | none =>
        cases s with
        | none => rfl
        | some j => exact (condU_condInf hdet hs hr).elim
      | some i =>
        cases s with
        | none => exact (condU_condInf hdet hr hs).elim
        | some j => exact congrArg some (Fin.ext (condU_unique hdet i.isLt j.isLt hr hs))

/-! ### Holomorphy and vanishing at the cusps -/

/-- A slash of `f ∈ S_k(Γ₁(M))` by an integer matrix vanishes at every cusp of `Γ₁(M)`. -/
lemma isZeroAt_slash_toGL (k : ℤ) (f : S1 M k) (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0)
    {c : OnePoint ℝ} (hc : IsCusp c (G1 M)) : c.IsZeroAt (⇑f ∣[k] toGL A hA) k := by
  have harith : (toConjAct (toGL A hA)⁻¹ • G1 M).IsArithmetic := by
    have e : (toGL A hA)⁻¹ = ((toGLQ A hA)⁻¹).map (Rat.castHom ℝ) := by
      rw [toGL, map_inv]
    rw [e]
    exact Subgroup.IsArithmetic.conj (G1 M) (toGLQ A hA)⁻¹
  have hc' : IsCusp c (toConjAct (toGL A hA)⁻¹ • G1 M) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    exact hc
  exact CuspFormClass.zero_at_cusps (CuspForm.translate f (toGL A hA)) hc'

omit [NeZero M] in
lemma isZeroAt_zero (k : ℤ) (c : OnePoint ℝ) : c.IsZeroAt (0 : ℍ → ℂ) k := fun g _ => by
  rw [SlashAction.zero_slash]; exact Filter.zero_zeroAtFilter _

lemma heckeFun_holo (k : ℤ) (f : S1 M k) : MDiff (heckeFun p k f) := by
  unfold heckeFun
  refine MDifferentiable.add ?_ ?_
  · refine Finset.sum_induction _ (fun F : ℍ → ℂ => MDiff F) (fun _ _ ha hb => ha.add hb)
      (fun _ => mdifferentiableAt_const) fun j _ => ?_
    exact (CuspFormClass.holo f).slash k _
  · split_ifs with h
    · exact fun _ => mdifferentiableAt_const
    · exact (CuspFormClass.holo _).slash k _

lemma heckeFun_zeroAt (k : ℤ) (f : S1 M k) {c : OnePoint ℝ} (hc : IsCusp c (G1 M)) :
    c.IsZeroAt (heckeFun p k f) k := by
  unfold heckeFun
  refine OnePoint.IsZeroAt.add ?_ ?_
  · refine Finset.sum_induction _ (fun F : ℍ → ℂ => c.IsZeroAt F k) (fun _ _ ha hb => ha.add hb)
      (isZeroAt_zero k c) fun j _ => ?_
    rw [upperTri_U_eq]
    exact isZeroAt_slash_toGL k f _ _ hc
  · split_ifs with h
    · exact isZeroAt_zero k c
    · rw [upperTri_D_eq]
      exact isZeroAt_slash_toGL k _ _ _ hc

variable (p) in
/-- `T_p f` as an element of `S_k(Γ₁(M))`. -/
def heckeCF (k : ℤ) (f : S1 M k) : S1 M k where
  toFun := heckeFun p k f
  slash_action_eq' γ hγ := by
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    rw [heckeFun_slash k f (Gamma1_in_Gamma0 M hγ₀),
      slashG0_of_mem_Gamma1 k ⟨γ₀, Gamma1_in_Gamma0 M hγ₀⟩ hγ₀]
  holo' := heckeFun_holo k f
  zero_at_cusps' hc := heckeFun_zeroAt k f hc

@[simp] lemma coe_heckeCF (k : ℤ) (f : S1 M k) : ⇑(heckeCF p k f) = heckeFun p k f := rfl

lemma heckeFun_add (k : ℤ) (f g : S1 M k) :
    heckeFun p k (f + g) = heckeFun p k f + heckeFun p k g := by
  unfold heckeFun
  split_ifs with h
  · simp only [FunLike.coe_add, SlashAction.add_slash, Finset.sum_add_distrib, add_zero]
  · simp only [map_add, FunLike.coe_add, SlashAction.add_slash, Finset.sum_add_distrib]
    abel

lemma heckeFun_smul (k : ℤ) (c : ℂ) (f : S1 M k) :
    heckeFun p k (c • f) = c • heckeFun p k f := by
  unfold heckeFun
  have h1 : ∀ (G : ℍ → ℂ) (j : ℕ), (c • G) ∣[k] upperTri 1 j p (hadU p) =
      c • (G ∣[k] upperTri 1 j p (hadU p)) := fun G j =>
    smul_slash_of_det_pos k _ (by rw [upperTri_det, one_mul]; exact_mod_cast prime_pos p) c G
  have h2 : ∀ (G : ℍ → ℂ), (c • G) ∣[k] upperTri p 0 1 (hadD p) =
      c • (G ∣[k] upperTri p 0 1 (hadD p)) := fun G =>
    smul_slash_of_det_pos k _ (by rw [upperTri_det, mul_one]; exact_mod_cast prime_pos p) c G
  split_ifs with h
  · simp only [FunLike.coe_smul, h1, Finset.smul_sum, add_zero]
  · simp only [map_smul, FunLike.coe_smul, h1, h2, Finset.smul_sum, smul_add]

variable (p) in
/-- **The Hecke operator** `T_p` (`= U_p` when `p ∣ M`) on `S_k(Γ₁(M))`. -/
def heckeT (k : ℤ) : S1 M k →ₗ[ℂ] S1 M k where
  toFun := heckeCF p k
  map_add' f g := DFunLike.coe_injective (by
    rw [coe_heckeCF, FunLike.coe_add, coe_heckeCF, coe_heckeCF, heckeFun_add])
  map_smul' c f := DFunLike.coe_injective (by
    rw [coe_heckeCF, FunLike.coe_smul, RingHom.id_apply, coe_heckeCF, heckeFun_smul])

@[simp] lemma coe_heckeT (k : ℤ) (f : S1 M k) : ⇑(heckeT p k f) = heckeFun p k f := rfl

/-! ### Commutation with the diamond operators -/

theorem heckeT_diamond (k : ℤ) (d : (ZMod M)ˣ) (f : S1 M k) :
    heckeT p k (diamond k d f) = diamond k d (heckeT p k f) := by
  apply DFunLike.coe_injective
  rw [coe_heckeT, diamond_apply, diamond_apply, coe_slashG0, coe_heckeT]
  exact (heckeFun_slash k f (lift0 d).2).symm

theorem heckeT_commute_diamond (k : ℤ) (d : (ZMod M)ˣ) : Commute (heckeT p k) (diamond k d) := by
  rw [Commute, SemiconjBy]
  refine LinearMap.ext fun f => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  exact heckeT_diamond k d f

/-- `T_p` preserves `S_k(M, χ)`. -/
theorem heckeT_mem_chiSubspace (k : ℤ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) : heckeT p k f ∈ chiSubspace k χ :=
  map_mem_chiSubspace_of_commute k (heckeT p k) (fun d => heckeT_commute_diamond k d) hf

/-! ### The coefficient formula -/

omit [NeZero M] hp in
lemma _root_.RamanujanPetersson.QExp.HasQExpansion.add' {F G : ℍ → ℂ} {a b : ℕ → ℂ}
    (hF : HasQExpansion F a) (hG : HasQExpansion G b) :
    HasQExpansion (F + G) (fun n => a n + b n) := fun τ => by
  simpa [add_mul] using (hF τ).add (hG τ)

omit [NeZero M] hp in
lemma _root_.RamanujanPetersson.QExp.HasQExpansion.const_smul {F : ℍ → ℂ} {a : ℕ → ℂ}
    (hF : HasQExpansion F a) (c : ℂ) : HasQExpansion (c • F) (fun n => c * a n) := fun τ => by
  simpa [mul_assoc] using (hF τ).mul_left c

theorem hasQExpansion_heckeFun_dvd (k : ℤ) (hpM : p ∣ M) (f : S1 M k) :
    HasQExpansion (heckeFun p k f) (fun n => (qExpansion 1 f).coeff (p * n)) := by
  rw [heckeFun, dif_pos hpM, add_zero, sum_slash_U_eq p (prime_pos p) (hadU p)]
  exact (hasQExpansion_cuspForm_Gamma1 M k f).U p (prime_pos p) _
    (fun j τ => upperTri_U_smul p (prime_pos p) (hadU p) j τ)

theorem hasQExpansion_heckeFun_ndvd (k : ℤ) (hpM : ¬ p ∣ M) (f : S1 M k) :
    HasQExpansion (heckeFun p k f) (fun n => (qExpansion 1 f).coeff (p * n) +
      (p : ℂ) ^ (k - 1) *
        (if p ∣ n then (qExpansion 1 (diamond k (unitP hpM) f)).coeff (n / p) else 0)) := by
  rw [heckeFun, dif_neg hpM, sum_slash_U_eq p (prime_pos p) (hadU p)]
  refine HasQExpansion.add' ((hasQExpansion_cuspForm_Gamma1 M k f).U p (prime_pos p) _
    (fun j τ => upperTri_U_smul p (prime_pos p) (hadU p) j τ)) ?_
  set G : S1 M k := diamond k (unitP hpM) f
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have e2 : ⇑G ∣[k] upperTri p 0 1 (hadD p) =
      (p : ℂ) ^ (k - 1) • fun τ ↦ G (upperTri p 0 1 (hadD p) • τ) := by
    rw [← slash_diag_eq p (prime_pos p) (hadD p), smul_smul, ← zpow_add₀ hp0,
      show k - 1 + (1 - k) = 0 by ring, zpow_zero, one_smul]
  rw [e2]
  exact ((hasQExpansion_cuspForm_Gamma1 M k G).comp_mul p (prime_pos p) _
    (upperTri_diag_smul p (prime_pos p) (hadD p))).const_smul _

/-- `U_p` (`p ∣ M`): `a_n(U_p f) = a_{pn}(f)`. -/
theorem coeff_heckeT_of_dvd (k : ℤ) (hpM : p ∣ M) (f : S1 M k) (n : ℕ) :
    (qExpansion 1 (heckeT p k f)).coeff n = (qExpansion 1 f).coeff (p * n) :=
  (hasQExpansion_heckeFun_dvd k hpM f).qExpansion_coeff n

/-- `T_p` (`p ∤ M`): `a_n(T_p f) = a_{pn}(f) + p^(k-1) [p ∣ n] a_{n/p}(⟨p⟩ f)`. -/
theorem coeff_heckeT_of_not_dvd (k : ℤ) (hpM : ¬ p ∣ M) (f : S1 M k) (n : ℕ) :
    (qExpansion 1 (heckeT p k f)).coeff n = (qExpansion 1 f).coeff (p * n) +
      (p : ℂ) ^ (k - 1) *
        (if p ∣ n then (qExpansion 1 (diamond k (unitP hpM) f)).coeff (n / p) else 0) :=
  (hasQExpansion_heckeFun_ndvd k hpM f).qExpansion_coeff n

/-- **Coefficient formula** (both cases at once). -/
theorem coeff_heckeT (k : ℤ) (f : S1 M k) (n : ℕ) :
    (qExpansion 1 (heckeT p k f)).coeff n = (qExpansion 1 f).coeff (p * n) +
      (if h : p ∣ M then 0 else (p : ℂ) ^ (k - 1) *
        (if p ∣ n then (qExpansion 1 (diamond k (unitP h) f)).coeff (n / p) else 0)) := by
  by_cases hpM : p ∣ M
  · rw [dif_pos hpM, add_zero, coeff_heckeT_of_dvd k hpM]
  · rw [dif_neg hpM, coeff_heckeT_of_not_dvd k hpM]

omit hp [NeZero M] in
lemma coeff_smul_Gamma1 (k : ℤ) (c : ℂ) (f : S1 M k) (m : ℕ) :
    (qExpansion 1 ⇑(c • f)).coeff m = c * (qExpansion 1 ⇑f).coeff m := by
  have := congrArg (PowerSeries.coeff m) (map_smul (qExpansionGamma1 M k) c f)
  rwa [qExpansionGamma1_apply, qExpansionGamma1_apply, map_smul, smul_eq_mul] at this

/-- **Coefficient formula on `S_k(M, χ)`**: `a_n(T_p f) = a_{pn} + χ(p) p^(k-1) [p ∣ n] a_{n/p}`
(`χ(p) = 0` when `p ∣ M`). -/
theorem coeff_heckeT_chi (k : ℤ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) (n : ℕ) :
    (qExpansion 1 (heckeT p k f)).coeff n = (qExpansion 1 f).coeff (p * n) +
      χ p * (p : ℂ) ^ (k - 1) * (if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0) := by
  by_cases hpM : p ∣ M
  · have hχ : χ p = 0 := by
      apply MulChar.map_nonunit
      rw [ZMod.isUnit_iff_coprime]
      exact fun h => (Nat.Prime.coprime_iff_not_dvd hp.out).1 h hpM
    rw [coeff_heckeT_of_dvd k hpM, hχ, zero_mul, zero_mul, add_zero]
  · rw [coeff_heckeT_of_not_dvd k hpM, (mem_chiSubspace_iff_diamond k χ f).1 hf (unitP hpM)]
    have hu : ((unitP hpM : (ZMod M)ˣ) : ZMod M) = p := ZMod.coe_unitOfCoprime _ _
    rw [hu]
    split_ifs with hn
    · rw [coeff_smul_Gamma1]; ring
    · ring

end hecke

end RamanujanPetersson.Hecke


