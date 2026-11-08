-- Prove2me | Definitions.Def_EntangledPIR_copyComplete
-- name    : EntangledPIR_copyComplete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:36.468103+00:00
-- url     : https://prove2.me/theorems/ddb1220d-1790-4f13-b5d7-b447d07db21b
-- title:
--   Completeness of the measurements on one copy
-- statement:
--   The operation of A with mask $a$, the test, the measurement of $\mathsf Y_z$, and the computation of B are complete on one copy:
--
--   $$\sum_e(H_eU_gX^a)^\dagger(H_eU_gX^a)=1,\quad \sum_f(\Pi^a_f)^\dagger\Pi^a_f=1,\quad \sum_u|u\rangle\langle u|_{\mathsf Y_z}=1,$$
--
--   and likewise for the computation of B, with $H_e=(H^{\otimes d}|e\rangle\langle e|H^{\otimes d})_{\mathsf P}$. The paper states these as "mutually orthogonal projectors with sum 1" (p.21). This module holds structural lemmas only.
--
--   **Formalization Note** These lemmas supply the completeness field of the honest instruments.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), §4, pp.19–21

import Definitions.Def_EntangledPIR_testProj

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), §4, pp.19–21:
the completeness relations of the honest operations on one copy. The test projectors "are mutually
orthogonal projectors with sum 1", p.21, and likewise for the other measurements.
-/

open Matrix
open scoped Kronecker

namespace EntangledPIR

section Perm
variable {S : Type} [DecidableEq S]

/-- The permutation matrix of an involution is its own conjugate transpose. -/
theorem perm_conjTranspose (φ : S → S) (hφ : ∀ s, φ (φ s) = s) :
    (Matrix.of fun s s' => if s = φ s' then (1 : ℂ) else 0)ᴴ =
      Matrix.of fun s s' => if s = φ s' then (1 : ℂ) else 0 := by
  ext s s'
  have : (s' = φ s) ↔ (s = φ s') := ⟨fun h => by rw [h, hφ], fun h => by rw [h, hφ]⟩
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : s = φ s'
  · rw [if_pos (this.mpr h), if_pos h]; simp
  · have h' : ¬ s' = φ s := fun e => h (this.mp e)
    rw [if_neg h', if_neg h]; simp

/-- The permutation matrix of an involution squares to one. -/
theorem perm_mul_self [Fintype S] (φ : S → S) (hφ : ∀ s, φ (φ s) = s) :
    (Matrix.of fun s s' => if s = φ s' then (1 : ℂ) else 0) *
      (Matrix.of fun s s' => if s = φ s' then (1 : ℂ) else 0) = 1 := by
  ext s s'
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (φ s)]
  · simp only [hφ, if_true, one_mul]
    by_cases h : s = s'
    · subst h; simp
    · have : ¬ φ s = φ s' := fun e => h (by rw [← hφ s, e, hφ])
      simp [h, this]
  · intro b _ hb
    have : ¬ s = φ b := fun e => hb (by rw [e, hφ])
    simp [this]
  · simp

end Perm

variable {d m : ℕ}

theorem bxor_bxor_right (a b : Bits d) : bxor (bxor a b) b = a := by
  funext i; simp [bxor]

theorem UgFun_invol (g : Bits d → Bits m) (s : CopyReg d m) : UgFun g (UgFun g s) = s := by
  refine Prod.ext rfl ?_
  funext z
  simp [UgFun, bxor_bxor_right]

theorem Ug_conjTranspose (g : Bits d → Bits m) : (Ug g)ᴴ = Ug g :=
  perm_conjTranspose (UgFun g) (UgFun_invol g)

theorem Ug_mul_self (g : Bits d → Bits m) : Ug g * Ug g = 1 :=
  perm_mul_self (UgFun g) (UgFun_invol g)

theorem pauliXs_conjTranspose (a : Bits d) : (pauliXs a)ᴴ = pauliXs a :=
  perm_conjTranspose (fun q => bxor q a) (fun s => bxor_bxor_right s a)

theorem pauliXs_mul_self (a : Bits d) : pauliXs a * pauliXs a = 1 :=
  perm_mul_self (fun q => bxor q a) (fun s => bxor_bxor_right s a)

theorem onAddr_mul (A B : Matrix (Bits d) (Bits d) ℂ) :
    (onAddr A : Matrix (CopyReg d m) (CopyReg d m) ℂ) * onAddr B = onAddr (A * B) := by
  simp [onAddr, ← Matrix.mul_kronecker_mul]

theorem onAddr_one : (onAddr (1 : Matrix (Bits d) (Bits d) ℂ) : Matrix (CopyReg d m) (CopyReg d m) ℂ) = 1 := by
  simp [onAddr]

theorem onAddr_conjTranspose (A : Matrix (Bits d) (Bits d) ℂ) :
    (onAddr A : Matrix (CopyReg d m) (CopyReg d m) ℂ)ᴴ = onAddr Aᴴ := by
  simp [onAddr, Matrix.conjTranspose_kronecker]

theorem onAddr_sum {ι : Type} [Fintype ι] (A : ι → Matrix (Bits d) (Bits d) ℂ) :
    ∑ i, (onAddr (A i) : Matrix (CopyReg d m) (CopyReg d m) ℂ) = onAddr (∑ i, A i) := by
  ext p q
  simp [onAddr, Matrix.sum_apply, Finset.sum_mul]

/-- `(-1)^{a·b}` is the product of the coordinates' signs. -/
theorem sign_bdot (a b : Bits d) :
    (-1 : ℂ) ^ bdot a b = ∏ i, (-1 : ℂ) ^ (if a i && b i then 1 else 0) := by
  rw [Finset.prod_pow_eq_pow_sum]; rfl

/-- Orthogonality of the characters of `{0,1}^d`. -/
theorem sum_sign (p q : Bits d) :
    ∑ e : Bits d, (-1 : ℂ) ^ bdot e p * (-1 : ℂ) ^ bdot e q = if p = q then 2 ^ d else 0 := by
  have h1 : ∀ e : Bits d, (-1 : ℂ) ^ bdot e p * (-1 : ℂ) ^ bdot e q =
      ∏ i, ((-1 : ℂ) ^ (if e i && p i then 1 else 0) * (-1 : ℂ) ^ (if e i && q i then 1 else 0)) := by
    intro e
    rw [sign_bdot, sign_bdot, Finset.prod_mul_distrib]
  simp only [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset Bool))
    (fun i b => (-1 : ℂ) ^ (if b && p i then 1 else 0) * (-1 : ℂ) ^ (if b && q i then 1 else 0))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  have h3 : ∀ i, ∑ b : Bool, (-1 : ℂ) ^ (if b && p i then 1 else 0) *
      (-1 : ℂ) ^ (if b && q i then 1 else 0) = if p i = q i then 2 else 0 := by
    intro i
    cases hp : p i <;> cases hq : q i <;> simp
    all_goals norm_num
  simp only [h3]
  by_cases hpq : p = q
  · subst hpq; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hpq
    rw [if_neg hpq]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem sqrt2_inv_sq : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 2 = 1 / 2 := by
  have : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [inv_pow, this]; norm_num

theorem star_sign (k : ℕ) : star ((-1 : ℂ) ^ k) = (-1 : ℂ) ^ k := by
  simp

theorem hadProj_apply (f p q : Bits d) :
    hadProj f p q = (1 / 2 : ℂ) ^ d * ((-1) ^ bdot f p * (-1) ^ bdot f q) := by
  have hs : star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    simp [Complex.conj_ofReal]
  simp only [hadProj, Matrix.vecMulVec_apply, hadVec, Pi.star_apply, star_mul', star_pow, hs,
    star_neg, star_one]
  rw [← sqrt2_inv_sq, ← pow_mul, mul_comm 2 d, pow_mul]
  ring

theorem hadProj_sum : ∑ f : Bits d, hadProj f = 1 := by
  ext p q
  simp only [Matrix.sum_apply, hadProj_apply, ← Finset.mul_sum, sum_sign, Matrix.one_apply]
  by_cases h : p = q
  · simp only [h, if_true, ← mul_pow]; norm_num
  · simp [h]

theorem hadProj_conjTranspose (f : Bits d) : (hadProj f)ᴴ = hadProj f := by
  ext p q
  simp only [Matrix.conjTranspose_apply, hadProj_apply, star_mul', star_pow, star_neg, star_one]
  simp [mul_comm]

theorem sign_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
  rw [← mul_pow]; simp

theorem hadProj_mul_self (f : Bits d) : hadProj f * hadProj f = hadProj f := by
  ext p q
  simp only [Matrix.mul_apply, hadProj_apply]
  have : ∀ r : Bits d, (1 / 2 : ℂ) ^ d * ((-1) ^ bdot f p * (-1) ^ bdot f r) *
      ((1 / 2 : ℂ) ^ d * ((-1) ^ bdot f r * (-1) ^ bdot f q)) =
      (1 / 2 : ℂ) ^ d * (1 / 2 : ℂ) ^ d * ((-1) ^ bdot f p * (-1) ^ bdot f q) := by
    intro r
    have := sign_mul_self (bdot f r)
    linear_combination (1 / 2 : ℂ) ^ d * (1 / 2 : ℂ) ^ d * ((-1) ^ bdot f p * (-1) ^ bdot f q) * this
  simp only [this, Finset.sum_const, Finset.card_univ]
  have hc : Fintype.card (Bits d) = 2 ^ d := by simp
  rw [hc, nsmul_eq_mul]
  push_cast
  have h2 : (2 : ℂ) ^ d * (1 / 2 : ℂ) ^ d = 1 := by rw [← mul_pow]; norm_num
  linear_combination (1 / 2 : ℂ) ^ d * ((-1) ^ bdot f p * (-1) ^ bdot f q) * h2

/-- Completeness for a projective measurement followed after an isometry. -/
theorem complete_proj_mul {X V : Type} [Fintype X] [DecidableEq X] [Fintype V]
    (P : V → Matrix X X ℂ) (W : Matrix X X ℂ) (hW : Wᴴ * W = 1)
    (hH : ∀ v, (P v)ᴴ = P v) (hI : ∀ v, P v * P v = P v) (hS : ∑ v, P v = 1) :
    ∑ v, (P v * W)ᴴ * (P v * W) = 1 := by
  have : ∀ v, (P v * W)ᴴ * (P v * W) = Wᴴ * P v * W := by
    intro v
    rw [Matrix.conjTranspose_mul, hH, Matrix.mul_assoc, ← Matrix.mul_assoc (P v), hI,
      Matrix.mul_assoc]
  simp only [this]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hS, Matrix.mul_one, hW]

theorem Va_conj_mul (g : Bits d → Bits m) (a : Bits d) : (Va g a)ᴴ * Va g a = 1 := by
  simp only [Va, Matrix.conjTranspose_mul, Ug_conjTranspose, onAddr_conjTranspose,
    pauliXs_conjTranspose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Ug g), Ug_mul_self, Matrix.one_mul, onAddr_mul,
    pauliXs_mul_self, onAddr_one]

theorem Va_mul_conj (g : Bits d → Bits m) (a : Bits d) : Va g a * (Va g a)ᴴ = 1 := by
  simp only [Va, Matrix.conjTranspose_mul, Ug_conjTranspose, onAddr_conjTranspose,
    pauliXs_conjTranspose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onAddr (pauliXs a)), onAddr_mul, pauliXs_mul_self,
    onAddr_one, Matrix.one_mul, Ug_mul_self]

/-- Completeness of the operation of A on one copy. -/
theorem opKraus_complete (g : Bits d → Bits m) (a : Bits d) :
    ∑ e, (opKraus g a e)ᴴ * opKraus g a e = 1 := by
  have := complete_proj_mul (fun e : Bits d => (onAddr (hadProj e) : Matrix (CopyReg d m) _ ℂ))
    (Va g a) (Va_conj_mul g a)
    (fun e => by rw [onAddr_conjTranspose, hadProj_conjTranspose])
    (fun e => by rw [onAddr_mul, hadProj_mul_self])
    (by rw [onAddr_sum, hadProj_sum, onAddr_one])
  simpa [opKraus, Va, Matrix.mul_assoc] using this

/-- Completeness of the test on one copy: the Lüders operators `Π^a_f` satisfy `∑_f Π^a_f = 1`. -/
theorem testProj_complete (g : Bits d → Bits m) (a : Bits d) :
    ∑ f, (testProj g a f)ᴴ * testProj g a f = 1 := by
  have h : ∀ f, (testProj g a f)ᴴ * testProj g a f =
      (Va g a)ᴴ * (onAddr (hadProj f) * Va g a) := by
    intro f
    have hc : (testProj g a f)ᴴ = testProj g a f := by
      simp only [testProj, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        onAddr_conjTranspose, hadProj_conjTranspose, Matrix.mul_assoc]
    rw [hc]
    simp only [testProj]
    calc (Va g a)ᴴ * onAddr (hadProj f) * Va g a * ((Va g a)ᴴ * onAddr (hadProj f) * Va g a)
        = (Va g a)ᴴ * onAddr (hadProj f) * (Va g a * (Va g a)ᴴ) * onAddr (hadProj f) * Va g a := by
          simp only [Matrix.mul_assoc]
      _ = (Va g a)ᴴ * (onAddr (hadProj f) * Va g a) := by
          rw [Va_mul_conj, Matrix.mul_one, Matrix.mul_assoc (Va g a)ᴴ, onAddr_mul, hadProj_mul_self,
            Matrix.mul_assoc]
  simp only [h]
  rw [← Finset.mul_sum, ← Finset.sum_mul, onAddr_sum, hadProj_sum, onAddr_one, Matrix.one_mul,
    Va_conj_mul]

theorem onAddr_basisProj (J : Bits d) :
    (onAddr (basisProj J) : Matrix (CopyReg d m) (CopyReg d m) ℂ) =
      Matrix.diagonal fun s => if s.1 = J then 1 else 0 := by
  ext p q
  simp only [onAddr, Matrix.kroneckerMap_apply, basisProj, Matrix.of_apply, Matrix.one_apply,
    Matrix.diagonal_apply]
  by_cases hp : p = q
  · subst hp; by_cases h : p.1 = J <;> simp [h]
  · rw [if_neg hp]
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hp (Prod.ext h1 h2)
      simp [h2]
    · have : ¬ (p.1 = J ∧ q.1 = J) := fun h => h1 (h.1.trans h.2.symm)
      simp [this]

/-- Completeness of the measurement of `Y_z` on one copy. -/
theorem outProj_complete (z : Bits d) :
    ∑ u : Bits m, (outProj z u : Matrix (CopyReg d m) (CopyReg d m) ℂ)ᴴ * outProj z u = 1 := by
  ext p q
  simp only [outProj, Matrix.sum_apply, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.one_apply, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    simp only [if_true]
    rw [Finset.sum_eq_single (p.2 z)]
    · simp
    · intro u _ hu
      have : ¬ p.2 z = u := fun e => hu e.symm
      simp [this]
    · simp
  · simp [h]

/-- Completeness of the computation of B on one copy. -/
theorem computeKraus_complete (b : Bits d) :
    ∑ o : Bits d × Bits m,
      (computeKraus b o.1 o.2 : Matrix (CopyReg d m) (CopyReg d m) ℂ)ᴴ * computeKraus b o.1 o.2 = 1 := by
  ext p q
  simp only [computeKraus, outProj, onAddr_basisProj, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_conjTranspose, Matrix.sum_apply, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    simp only [if_true]
    rw [Finset.sum_eq_single (p.1, p.2 (bxor p.1 b))]
    · simp
    · rintro ⟨J, v⟩ _ hu
      by_cases hJ : p.1 = J
      · subst hJ
        have : ¬ p.2 (bxor p.1 b) = v := fun e => hu (by rw [e])
        simp [this]
      · simp [hJ]
    · simp
  · simp [h]

/-- Completeness of a trivial outcome on a copy that the operation does not touch. -/
theorem trivial_complete {V X : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] (v0 : V) :
    ∑ v : V, (if v = v0 then (1 : Matrix X X ℂ) else 0)ᴴ * (if v = v0 then 1 else 0) = 1 := by
  rw [Finset.sum_eq_single v0]
  · simp
  · intro v _ hv; simp [hv]
  · simp

end EntangledPIR


