-- Prove2me | solution 1 for AutomorphicForm.bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/07f0ca37-d3b6-561e-9926-bd5d5560dc6d

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one

set_option autoImplicit false

noncomputable section

namespace R4BorelClassParam

set_option maxHeartbeats 1600000

open Function Set AutomorphicForm

section GL2

variable {A : Type*} [CommRing A]

def diag2 (p q : Aˣ) : GL (Fin 2) A where
  val := !![(p : A), 0; 0, (q : A)]
  inv := !![((p⁻¹ : Aˣ) : A), 0; 0, ((q⁻¹ : Aˣ) : A)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem diag2_val (p q : Aˣ) :
    ((diag2 p q : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(p : A), 0; 0, (q : A)] := rfl

theorem diag2_inv (p q : Aˣ) : (diag2 p q)⁻¹ = diag2 p⁻¹ q⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Units.ext
  rw [Units.val_mul, diag2_val, diag2_val, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diag2_mul_diag2 (p q p' q' : Aˣ) : diag2 p q * diag2 p' q' = diag2 (p * p') (q * q') := by
  apply Units.ext
  rw [Units.val_mul, diag2_val, diag2_val, diag2_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diag2_one_one : (diag2 1 1 : GL (Fin 2) A) = 1 := by
  apply Units.ext
  rw [diag2_val, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem diag2_comm (p q p' q' : Aˣ) : diag2 p q * diag2 p' q' = diag2 p' q' * diag2 p q := by
  rw [diag2_mul_diag2, diag2_mul_diag2, mul_comm p, mul_comm q]

theorem scalar_eq_diag2 (z : Aˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) z = diag2 z z := by
  apply Units.ext
  rw [diag2_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem unipotentGL2_neg (t : A) : unipotentGL2 (-t) = (unipotentGL2 t)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]

theorem diag2_mul_unipotent (p q : Aˣ) (t : A) :
    diag2 p q * unipotentGL2 t = unipotentGL2 ((p : A) * ((q⁻¹ : Aˣ) : A) * t) * diag2 p q := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, diag2_val, unipotentGL2_coe, unipotentGL2_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [mul_assoc, mul_assoc, mul_left_comm ((q⁻¹ : Aˣ) : A), Units.inv_mul, mul_one]

theorem unipotent_mul_diag2 (p q : Aˣ) (t : A) :
    unipotentGL2 t * diag2 p q = diag2 p q * unipotentGL2 (((p⁻¹ : Aˣ) : A) * (q : A) * t) := by
  rw [diag2_mul_unipotent]
  congr 2
  rw [show (p : A) * ((q⁻¹ : Aˣ) : A) * (((p⁻¹ : Aˣ) : A) * (q : A) * t) =
    ((p : A) * ((p⁻¹ : Aˣ) : A)) * (((q⁻¹ : Aˣ) : A) * (q : A)) * t by ring, Units.mul_inv, Units.inv_mul, one_mul,
    one_mul]

theorem diag2_inv_mul_unipotent (p q : Aˣ) (t : A) :
    (diag2 p q)⁻¹ * unipotentGL2 t = unipotentGL2 (((p⁻¹ : Aˣ) : A) * (q : A) * t) * (diag2 p q)⁻¹ := by
  rw [diag2_inv, diag2_mul_unipotent, inv_inv]

theorem val_diag2_mul_unipotent_mul_diag2 (a b c d : Aˣ) (t : A) :
    ((diag2 a b * unipotentGL2 t * diag2 c d : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      !![(a : A) * c, (a : A) * t * d; 0, (b : A) * d] := by
  rw [Units.val_mul, Units.val_mul, diag2_val, diag2_val, unipotentGL2_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_diag2_mul_unipotent_mul_diag2 (a b c d : Aˣ) (t : A) :
    (diag2 a b * unipotentGL2 t * diag2 c d)⁻¹ = diag2 c⁻¹ d⁻¹ * unipotentGL2 (-t) * diag2 a⁻¹ b⁻¹ := by
  rw [mul_inv_rev, mul_inv_rev, diag2_inv, diag2_inv, unipotentGL2_neg, mul_assoc]

variable [TopologicalSpace A]

omit [CommRing A] in
theorem continuous_matrix_two {X : Type*} [TopologicalSpace X] {f : X → Matrix (Fin 2) (Fin 2) A}
    (h00 : Continuous fun x => f x 0 0) (h01 : Continuous fun x => f x 0 1)
    (h10 : Continuous fun x => f x 1 0) (h11 : Continuous fun x => f x 1 1) : Continuous f := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

theorem continuous_unipotentGL2' [IsTopologicalRing A] : Continuous fun x : A => (unipotentGL2 x : GL (Fin 2) A) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun x : A => !![(1 : A), x; 0, 1]
    exact continuous_matrix_two (by simpa using continuous_const) (by simp; exact continuous_id)
      (by simpa using continuous_const) (by simpa using continuous_const)
  · show Continuous fun x : A => !![(1 : A), -x; 0, 1]
    exact continuous_matrix_two (by simpa using continuous_const) (by simpa using continuous_neg)
      (by simpa using continuous_const) (by simpa using continuous_const)

theorem continuous_diag2_self : Continuous fun z : Aˣ => (diag2 z z : GL (Fin 2) A) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun c : Aˣ => !![(c : A), 0; 0, (c : A)]
    exact continuous_matrix_two (by simpa using Units.continuous_val) (by simpa using continuous_const)
      (by simpa using continuous_const) (by simpa using Units.continuous_val)
  · show Continuous fun c : Aˣ => !![((c⁻¹ : Aˣ) : A), 0; 0, ((c⁻¹ : Aˣ) : A)]
    exact continuous_matrix_two (by simpa using Units.continuous_coe_inv) (by simpa using continuous_const)
      (by simpa using continuous_const) (by simpa using Units.continuous_coe_inv)

theorem continuous_val_apply (i j : Fin 2) :
    Continuous fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A) i j :=
  Units.continuous_val.matrix_elem i j

theorem continuous_val_inv_apply (i j : Fin 2) :
    Continuous fun g : GL (Fin 2) A => ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j :=
  Units.continuous_coe_inv.matrix_elem i j

end GL2

section FieldGL2

variable {L : Type*} [Field L]

theorem det_ne_zero_entries (d : GL (Fin 2) L) (h10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (d : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧ (d : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  have hdet : (d : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det d).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

def e0 (d : GL (Fin 2) L) (h10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : Lˣ :=
  Units.mk0 _ (det_ne_zero_entries d h10).1

def e1 (d : GL (Fin 2) L) (h10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : Lˣ :=
  Units.mk0 _ (det_ne_zero_entries d h10).2

@[scoped simp] theorem coe_e0 (d : GL (Fin 2) L) (h10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((e0 d h10 : Lˣ) : L) = (d : Matrix (Fin 2) (Fin 2) L) 0 0 := rfl

@[scoped simp] theorem coe_e1 (d : GL (Fin 2) L) (h10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((e1 d h10 : Lˣ) : L) = (d : Matrix (Fin 2) (Fin 2) L) 1 1 := rfl

theorem eq_diag2_of_diag (d : GL (Fin 2) L) (h10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (h01 : (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) : d = diag2 (e0 d h10) (e1 d h10) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [diag2_val]
  fin_cases i <;> fin_cases j <;> simp [h10, h01]

theorem eq_diag2_mul_unipotent_of_upper (b : GL (Fin 2) L) (h10 : (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    b = diag2 (e0 b h10) (e1 b h10) * unipotentGL2 ((b : Matrix (Fin 2) (Fin 2) L) 0 1 / (b : Matrix (Fin 2) (Fin 2) L) 0 0) := by
  have h0 := (det_ne_zero_entries b h10).1
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, diag2_val, unipotentGL2_coe]
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
      zero_mul, add_zero, coe_e0]
    rw [mul_div_cancel₀ _ h0]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, h10]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

variable {K : Type*} [Field K] [Algebra K L] (σ : L ≃ₐ[K] L)

abbrev σG : GL (Fin 2) L →* GL (Fin 2) L := Matrix.GeneralLinearGroup.map (σ : L →+* L)

theorem σG_apply (g : GL (Fin 2) L) (i j : Fin 2) :
    ((σG σ g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = σ ((g : Matrix (Fin 2) (Fin 2) L) i j) := rfl

theorem σG_diag2 (p q : Lˣ) : σG σ (diag2 p q) = diag2 (Units.map (σ : L →* L) p) (Units.map (σ : L →* L) q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [σG_apply, diag2_val, diag2_val]
  fin_cases i <;> fin_cases j <;> simp

theorem σG_unipotent (s : L) : σG σ (unipotentGL2 s) = unipotentGL2 (σ s) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [σG_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem σG_scalar (u : Lˣ) :
    σG σ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (σ : L →* L) u) := by
  rw [scalar_eq_diag2, scalar_eq_diag2, σG_diag2]

omit [Algebra K L] in
theorem scalar_comm (u : Lˣ) (g : GL (Fin 2) L) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (u : L) (fun r' => Commute.all _ r') _).eq

omit [Algebra K L] in
theorem scalar_mem_center (u : Lˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ Subgroup.center (GL (Fin 2) L) :=
  Subgroup.mem_center_iff.mpr fun g => (scalar_comm u g).symm

omit [Algebra K L] in

theorem exists_scalar_of_mem_center {s : GL (Fin 2) L} (hs : s ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ u : Lˣ, s = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨u, hu⟩ := hs
  exact ⟨u, hu.symm⟩

omit [Algebra K L] in
theorem scalar_injective : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Lˣ → GL (Fin 2) L) := by
  intro u v h
  have := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L) 0 0) h
  simpa using Units.ext_iff.mpr (by simpa [Matrix.scalar_apply] using this)

omit [Algebra K L] in
theorem diag2_injective {p q p' q' : Lˣ} (h : (diag2 p q : GL (Fin 2) L) = diag2 p' q') : p = p' ∧ q = q' := by
  have h0 := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L) 0 0) h
  have h1 := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L) 1 1) h
  simp only [diag2_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val'] at h0 h1
  exact ⟨Units.ext h0, Units.ext h1⟩

theorem bijective_sub_smul [FiniteDimensional K L] (c : L) (hc : Algebra.norm K c ≠ 1) :
    Function.Bijective fun v : L => σ v - c * v := by
  let T : L →ₗ[K] L := (σ : L ≃ₐ[K] L).toLinearMap - LinearMap.mulLeft K c
  have hT : ∀ s : L, T s = σ s - c * s := fun s => rfl
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    rw [hT, sub_eq_zero] at hs
    by_contra hs0
    have hnorm := congrArg (Algebra.norm K) hs
    rw [map_mul, Algebra.norm_eq_of_algEquiv] at hnorm
    have hns : Algebra.norm K s ≠ 0 := Algebra.norm_ne_zero_iff.mpr hs0
    exact hc ((mul_eq_right₀ hns).mp hnorm.symm)
  have hsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hinj
  exact ⟨fun a b h => hinj (by rw [hT, hT]; exact h), fun y => by
    obtain ⟨s, hs⟩ := hsurj y
    exact ⟨s, by rw [hT] at hs; exact hs⟩⟩

end FieldGL2

section Param

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)
variable (t' : GL (Fin 2) L) (M : Subgroup (GL (Fin 2) L)) {κ : Type*} (a : κ → GL (Fin 2) L)

def param (p : κ × Lˣ × L) : GL (Fin 2) L :=
  a p.1 * t' * σG σ (unipotentGL2 p.2.2) * Matrix.GeneralLinearGroup.scalar (Fin 2) p.2.1 * (σG σ (a p.1))⁻¹

def cratio : L := (t' : Matrix (Fin 2) (Fin 2) L) 1 1 / (t' : Matrix (Fin 2) (Fin 2) L) 0 0

theorem norm_cratio_ne_one
    (hreg : Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t' : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1) :
    Algebra.norm K (cratio t') ≠ 1 := by
  intro h
  apply hreg
  have : (t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t' : Matrix (Fin 2) (Fin 2) L) 1 1 = (cratio t')⁻¹ := by
    rw [cratio, inv_div]
  rw [this]
  rcases eq_or_ne (cratio t') 0 with h0 | h0
  · rw [h0, inv_zero]; rwa [h0] at h
  · have h2 := map_mul (Algebra.norm K) (cratio t') (cratio t')⁻¹
    rw [mul_inv_cancel₀ h0, map_one, h, one_mul] at h2
    exact h2.symm

omit [Algebra K L] in

theorem unipotent_mul_t' (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (v : L) : unipotentGL2 v * t' = t' * unipotentGL2 (cratio t' * v) := by
  conv_lhs => rw [eq_diag2_of_diag t' ht'u ht'l]
  rw [unipotent_mul_diag2, ← eq_diag2_of_diag t' ht'u ht'l]
  congr 2
  simp only [cratio, Units.val_inv_eq_inv_val, coe_e0, coe_e1]
  rw [div_eq_mul_inv, mul_comm ((t' : Matrix (Fin 2) (Fin 2) L) 1 1)]

omit [Algebra K L] in

theorem diag2_mul_t' (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (μ₀ μ₁ : Lˣ) : diag2 μ₀ μ₁ * t' = t' * diag2 μ₀ μ₁ := by
  conv_lhs => rw [eq_diag2_of_diag t' ht'u ht'l]
  rw [diag2_comm, ← eq_diag2_of_diag t' ht'u ht'l]

theorem diag2_mem_M_iff (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hM : ∀ m, m ∈ M ↔ ((m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (m : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      t'⁻¹ * (m * t' * (Matrix.GeneralLinearGroup.map (σ : L →+* L) m)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    (μ₀ μ₁ : Lˣ) :
    diag2 μ₀ μ₁ ∈ M ↔ diag2 μ₀ μ₁ * (σG σ (diag2 μ₀ μ₁))⁻¹ ∈ Subgroup.center (GL (Fin 2) L) := by
  rw [hM]
  have hd : ((diag2 μ₀ μ₁ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      ((diag2 μ₀ μ₁ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by simp
  have key : t'⁻¹ * (diag2 μ₀ μ₁ * t' * (σG σ (diag2 μ₀ μ₁))⁻¹) = diag2 μ₀ μ₁ * (σG σ (diag2 μ₀ μ₁))⁻¹ := by
    rw [diag2_mul_t' t' ht'u ht'l, mul_assoc, inv_mul_cancel_left]
  simp only [hd, true_and, key]

omit [Algebra K L] in

theorem eq_of_inv_mul_mem
    (haD : ∀ j, (a j : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a j : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (ha : ∀ d : GL (Fin 2) L, (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      ∃! j, (a j)⁻¹ * d ∈ M)
    {j k : κ} (h : (a k)⁻¹ * a j ∈ M) : j = k := by
  obtain ⟨i, -, hi⟩ := ha (a j) (haD j).1 (haD j).2
  have hj : j = i := hi j (show (a j)⁻¹ * a j ∈ M by rw [inv_mul_cancel]; exact M.one_mem)
  have hk : k = i := hi k h
  rw [hj, hk]

theorem param_eq (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (haD : ∀ j, (a j : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a j : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (j : κ) (ζ : Lˣ) (s : L) :
    param σ t' a (j, ζ, s) =
      diag2 (e0 (a j) (haD j).1 * e0 t' ht'u) (e1 (a j) (haD j).1 * e1 t' ht'u) * unipotentGL2 (σ s) *
        diag2 (ζ * (Units.map (σ : L →* L) (e0 (a j) (haD j).1))⁻¹) (ζ * (Units.map (σ : L →* L) (e1 (a j) (haD j).1))⁻¹) := by
  have h1 : param σ t' a (j, ζ, s) =
      a j * t' * σG σ (unipotentGL2 s) * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * (σG σ (a j))⁻¹ := rfl
  rw [h1]
  conv_lhs => rw [eq_diag2_of_diag (a j) (haD j).1 (haD j).2, eq_diag2_of_diag t' ht'u ht'l]
  rw [σG_unipotent, σG_diag2, diag2_inv, scalar_eq_diag2, diag2_mul_diag2, mul_assoc, diag2_mul_diag2]

theorem param_mem [FiniteDimensional K L]
    (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t' : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (J : Set (GL (Fin 2) L))
    (hJ : ∀ γ, γ ∈ J ↔ ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t'⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L))
    (haD : ∀ j, (a j : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a j : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (p : κ × Lˣ × L) : param σ t' a p ∈ J := by
  obtain ⟨j, ζ, s⟩ := p
  rw [hJ]

  obtain ⟨v, hv⟩ := (bijective_sub_smul σ (cratio t') (norm_cratio_ne_one t' hreg)).2 (-σ s)
  have hv' : σ v - cratio t' * v = -σ s := hv
  refine ⟨a j * unipotentGL2 v, ?_, ?_⟩
  · rw [eq_diag2_of_diag (a j) (haD j).1 (haD j).2, Matrix.GeneralLinearGroup.coe_mul, diag2_val, unipotentGL2_coe]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have key : (a j * unipotentGL2 v)⁻¹ * param σ t' a (j, ζ, s) * σG σ (a j * unipotentGL2 v) =
        t' * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ := by
      have h1 : param σ t' a (j, ζ, s) =
          a j * t' * σG σ (unipotentGL2 s) * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * (σG σ (a j))⁻¹ := rfl
      rw [h1, mul_inv_rev, map_mul, σG_unipotent, σG_unipotent, ← unipotentGL2_neg]
      calc unipotentGL2 (-v) * (a j)⁻¹ *
            (a j * t' * unipotentGL2 (σ s) * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * (σG σ (a j))⁻¹) *
            (σG σ (a j) * unipotentGL2 (σ v))
          = (unipotentGL2 (-v) * t') * unipotentGL2 (σ s) *
              (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * unipotentGL2 (σ v)) := by
            simp only [mul_assoc, inv_mul_cancel_left]
        _ = t' * (unipotentGL2 (cratio t' * -v) * unipotentGL2 (σ s) * unipotentGL2 (σ v)) *
              Matrix.GeneralLinearGroup.scalar (Fin 2) ζ := by
            rw [scalar_comm, unipotent_mul_t' t' ht'u ht'l]
            simp only [mul_assoc]
        _ = t' * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ := by
            rw [← unipotentGL2_add, ← unipotentGL2_add]
            have : cratio t' * -v + σ s + σ v = 0 := by linear_combination hv'
            rw [this, unipotentGL2_zero, mul_one]
    rw [key, inv_mul_cancel_left]
    exact scalar_mem_center ζ

theorem param_entries (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (haD : ∀ j, (a j : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a j : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (j : κ) (ζ : Lˣ) (s : L) :
    ((param σ t' a (j, ζ, s) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
        (a j : Matrix (Fin 2) (Fin 2) L) 0 0 * (t' : Matrix (Fin 2) (Fin 2) L) 0 0 *
          ((ζ : L) * (σ ((a j : Matrix (Fin 2) (Fin 2) L) 0 0))⁻¹) ∧
      ((param σ t' a (j, ζ, s) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 =
        (a j : Matrix (Fin 2) (Fin 2) L) 0 0 * (t' : Matrix (Fin 2) (Fin 2) L) 0 0 * σ s *
          ((ζ : L) * (σ ((a j : Matrix (Fin 2) (Fin 2) L) 1 1))⁻¹) ∧
      ((param σ t' a (j, ζ, s) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
        (a j : Matrix (Fin 2) (Fin 2) L) 1 1 * (t' : Matrix (Fin 2) (Fin 2) L) 1 1 *
          ((ζ : L) * (σ ((a j : Matrix (Fin 2) (Fin 2) L) 1 1))⁻¹) := by
  rw [param_eq σ t' a ht'u ht'l haD, val_diag2_mul_unipotent_mul_diag2]
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.empty_val', Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, coe_e0, coe_e1]

theorem fst_eq_of_param_eq
    (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hM : ∀ m, m ∈ M ↔ ((m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (m : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      t'⁻¹ * (m * t' * (Matrix.GeneralLinearGroup.map (σ : L →+* L) m)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    (haD : ∀ j, (a j : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a j : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (ha : ∀ d : GL (Fin 2) L, (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      ∃! j, (a j)⁻¹ * d ∈ M)
    {j k : κ} {ζ η : Lˣ} {s r : L} (h : param σ t' a (j, ζ, s) = param σ t' a (k, η, r)) : j = k := by
  obtain ⟨hj00, -, hj11⟩ := param_entries σ t' a ht'u ht'l haD j ζ s
  obtain ⟨hk00, -, hk11⟩ := param_entries σ t' a ht'u ht'l haD k η r
  rw [h, hk00] at hj00
  rw [h, hk11] at hj11
  have hpj0 := (det_ne_zero_entries (a j) (haD j).1).1
  have hqj0 := (det_ne_zero_entries (a j) (haD j).1).2
  have hpk0 := (det_ne_zero_entries (a k) (haD k).1).1
  have hqk0 := (det_ne_zero_entries (a k) (haD k).1).2
  have ht00 := (det_ne_zero_entries t' ht'u).1
  have ht10 := (det_ne_zero_entries t' ht'u).2
  have hσpj : σ ((a j : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ 0 := (map_ne_zero σ).mpr hpj0
  have hσqj : σ ((a j : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 := (map_ne_zero σ).mpr hqj0
  have hσpk : σ ((a k : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ 0 := (map_ne_zero σ).mpr hpk0
  have hσqk : σ ((a k : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 := (map_ne_zero σ).mpr hqk0
  have hζ0 : (ζ : L) ≠ 0 := ζ.ne_zero
  have hη0 : (η : L) ≠ 0 := η.ne_zero
  refine eq_of_inv_mul_mem M a haD ha ?_
  have hmeq : (a k)⁻¹ * a j = diag2 ((e0 (a k) (haD k).1)⁻¹ * e0 (a j) (haD j).1)
      ((e1 (a k) (haD k).1)⁻¹ * e1 (a j) (haD j).1) := by
    conv_lhs => rw [eq_diag2_of_diag (a k) (haD k).1 (haD k).2, eq_diag2_of_diag (a j) (haD j).1 (haD j).2]
    rw [diag2_inv, diag2_mul_diag2]
  rw [hmeq, diag2_mem_M_iff σ t' M ht'u ht'l hM]

  have hsc : diag2 ((e0 (a k) (haD k).1)⁻¹ * e0 (a j) (haD j).1) ((e1 (a k) (haD k).1)⁻¹ * e1 (a j) (haD j).1) *
      (σG σ (diag2 ((e0 (a k) (haD k).1)⁻¹ * e0 (a j) (haD j).1) ((e1 (a k) (haD k).1)⁻¹ * e1 (a j) (haD j).1)))⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (η * ζ⁻¹) := by
    rw [σG_diag2, diag2_inv, diag2_mul_diag2, scalar_eq_diag2]
    congr 1
    · refine Units.ext ?_
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, coe_e0, map_mul,
        map_inv₀]
      field_simp
      field_simp at hj00
      linear_combination (-1 : L) * hj00
    · refine Units.ext ?_
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, coe_e1, map_mul,
        map_inv₀]
      field_simp
      field_simp at hj11
      linear_combination (-1 : L) * hj11
  rw [hsc]
  exact scalar_mem_center _

theorem param_injective
    (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hM : ∀ m, m ∈ M ↔ ((m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (m : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      t'⁻¹ * (m * t' * (Matrix.GeneralLinearGroup.map (σ : L →+* L) m)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    (haD : ∀ j, (a j : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a j : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (ha : ∀ d : GL (Fin 2) L, (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      ∃! j, (a j)⁻¹ * d ∈ M) :
    Function.Injective (param σ t' a) := by
  rintro ⟨j, ζ, s⟩ ⟨k, η, r⟩ h
  obtain rfl : j = k := fst_eq_of_param_eq σ t' M a ht'u ht'l hM haD ha h
  obtain ⟨hj00, hj01, -⟩ := param_entries σ t' a ht'u ht'l haD j ζ s
  obtain ⟨hk00, hk01, -⟩ := param_entries σ t' a ht'u ht'l haD j η r
  rw [h, hk00] at hj00
  rw [h, hk01] at hj01
  have hpj0 := (det_ne_zero_entries (a j) (haD j).1).1
  have hqj0 := (det_ne_zero_entries (a j) (haD j).1).2
  have ht00 := (det_ne_zero_entries t' ht'u).1
  have hσpj : σ ((a j : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ 0 := (map_ne_zero σ).mpr hpj0
  have hσqj : σ ((a j : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 := (map_ne_zero σ).mpr hqj0

  have hζη : (ζ : L) = η := by
    have h1 := mul_left_cancel₀ (mul_ne_zero hpj0 ht00) hj00
    exact mul_right_cancel₀ (inv_ne_zero hσpj) h1.symm
  obtain rfl : ζ = η := Units.ext hζη

  have hsr : σ s = σ r := by
    have h1 := mul_right_cancel₀ (mul_ne_zero ζ.ne_zero (inv_ne_zero hσqj)) hj01
    exact (mul_left_cancel₀ (mul_ne_zero hpj0 ht00) h1).symm
  obtain rfl : s = r := σ.injective hsr
  rfl

theorem param_surjOn
    (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (J : Set (GL (Fin 2) L))
    (hJ : ∀ γ, γ ∈ J ↔ ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t'⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L))
    (hM : ∀ m, m ∈ M ↔ ((m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (m : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      t'⁻¹ * (m * t' * (Matrix.GeneralLinearGroup.map (σ : L →+* L) m)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    (ha : ∀ d : GL (Fin 2) L, (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      ∃! j, (a j)⁻¹ * d ∈ M) :
    Set.SurjOn (param σ t' a) Set.univ J := by
  intro γ hγ
  rw [hJ] at hγ
  obtain ⟨b, hb10, hb⟩ := hγ
  obtain ⟨η', hη'⟩ := exists_scalar_of_mem_center hb

  set v : L := (b : Matrix (Fin 2) (Fin 2) L) 0 1 / (b : Matrix (Fin 2) (Fin 2) L) 0 0 with hv
  set d : GL (Fin 2) L := diag2 (e0 b hb10) (e1 b hb10) with hd
  have hbd : b = d * unipotentGL2 v := eq_diag2_mul_unipotent_of_upper b hb10
  have hd10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by simp [hd]
  have hd01 : (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by simp [hd]
  obtain ⟨j, hjm, -⟩ := ha d hd10 hd01
  set m : GL (Fin 2) L := (a j)⁻¹ * d with hm
  have hdm : d = a j * m := by rw [hm, mul_inv_cancel_left]
  have hmM : m ∈ M := hjm
  rw [hM] at hmM
  obtain ⟨⟨hm10, hm01⟩, hmc⟩ := hmM
  obtain ⟨μ', hμ'⟩ := exists_scalar_of_mem_center hmc
  have hmeq : m = diag2 (e0 m hm10) (e1 m hm10) := eq_diag2_of_diag m hm10 hm01

  have hmσ : m * (σG σ m)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) μ' := by
    have hmt : m * t' * (σG σ m)⁻¹ = t' * Matrix.GeneralLinearGroup.scalar (Fin 2) μ' := by
      rw [← hμ', mul_inv_cancel_left]
    have h1 : m * t' * (σG σ m)⁻¹ = t' * (m * (σG σ m)⁻¹) := by
      rw [hmeq, diag2_mul_t' t' ht'u ht'l, mul_assoc]
    rw [h1] at hmt
    exact mul_left_cancel hmt

  set v₁ : L := ((e0 m hm10 : Lˣ) : L) * (((e1 m hm10)⁻¹ : Lˣ) : L) * v with hv₁
  have hmu : m * unipotentGL2 v = unipotentGL2 v₁ * m := by
    conv_lhs => rw [hmeq]
    rw [diag2_mul_unipotent, ← hmeq]
  clear_value v₁ m d v
  refine ⟨(j, μ' * η', σ.symm (cratio t' * v₁ - σ v₁)), Set.mem_univ _, ?_⟩

  have hγ : γ = b * t' * Matrix.GeneralLinearGroup.scalar (Fin 2) η' * (σG σ b)⁻¹ := by
    have : b⁻¹ * γ * σG σ b = t' * Matrix.GeneralLinearGroup.scalar (Fin 2) η' := by
      rw [← hη', mul_inv_cancel_left]
    calc γ = b * (b⁻¹ * γ * σG σ b) * (σG σ b)⁻¹ := by group
      _ = _ := by rw [this, ← mul_assoc]
  have h1 : param σ t' a (j, μ' * η', σ.symm (cratio t' * v₁ - σ v₁)) =
      a j * t' * σG σ (unipotentGL2 (σ.symm (cratio t' * v₁ - σ v₁))) *
        Matrix.GeneralLinearGroup.scalar (Fin 2) (μ' * η') * (σG σ (a j))⁻¹ := rfl
  rw [h1, σG_unipotent, AlgEquiv.apply_symm_apply, hγ, hbd, hdm, map_mul (σG σ), map_mul (σG σ), mul_inv_rev,
    mul_inv_rev, σG_unipotent, ← unipotentGL2_neg]
  symm

  have hc2 : m * unipotentGL2 v * t' = t' * unipotentGL2 (cratio t' * v₁) * m := by
    rw [hmu, mul_assoc, hmeq, diag2_mul_t' t' ht'u ht'l, ← mul_assoc, unipotent_mul_t' t' ht'u ht'l]
  have hc3 : m * unipotentGL2 (-σ v) * (σG σ m)⁻¹ = unipotentGL2 (-σ v₁) * Matrix.GeneralLinearGroup.scalar (Fin 2) μ' := by
    have e1' : σG σ (m * unipotentGL2 v) = σG σ (unipotentGL2 v₁ * m) := by rw [hmu]
    rw [map_mul (σG σ), map_mul (σG σ), σG_unipotent, σG_unipotent] at e1'

    have e2 : unipotentGL2 (-σ v) * (σG σ m)⁻¹ = (σG σ m)⁻¹ * unipotentGL2 (-σ v₁) := by
      rw [unipotentGL2_neg, unipotentGL2_neg, ← mul_inv_rev, ← mul_inv_rev, e1']
    rw [mul_assoc, e2, ← mul_assoc, hmσ, scalar_comm]
  calc a j * m * unipotentGL2 v * t' * Matrix.GeneralLinearGroup.scalar (Fin 2) η' *
        (unipotentGL2 (-σ v) * ((σG σ m)⁻¹ * (σG σ (a j))⁻¹))
      = a j * (m * unipotentGL2 v * t') * (Matrix.GeneralLinearGroup.scalar (Fin 2) η' *
          (unipotentGL2 (-σ v) * (σG σ m)⁻¹)) * (σG σ (a j))⁻¹ := by simp only [mul_assoc]
    _ = a j * (t' * unipotentGL2 (cratio t' * v₁) * m) *
          (unipotentGL2 (-σ v) * (σG σ m)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) η') * (σG σ (a j))⁻¹ := by
        rw [hc2, scalar_comm]
    _ = a j * t' * unipotentGL2 (cratio t' * v₁) * (m * unipotentGL2 (-σ v) * (σG σ m)⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) η' * (σG σ (a j))⁻¹ := by simp only [mul_assoc]
    _ = a j * t' * (unipotentGL2 (cratio t' * v₁) * unipotentGL2 (-σ v₁)) *
          (Matrix.GeneralLinearGroup.scalar (Fin 2) μ' * Matrix.GeneralLinearGroup.scalar (Fin 2) η') *
          (σG σ (a j))⁻¹ := by
        rw [hc3]; simp only [mul_assoc]
    _ = a j * t' * unipotentGL2 (cratio t' * v₁ - σ v₁) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (μ' * η') * (σG σ (a j))⁻¹ := by
        rw [← unipotentGL2_add, ← sub_eq_add_neg, ← map_mul]

theorem param_bijOn [FiniteDimensional K L]
    (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t' : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (J : Set (GL (Fin 2) L))
    (hJ : ∀ γ, γ ∈ J ↔ ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t'⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L))
    (hM : ∀ m, m ∈ M ↔ ((m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (m : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      t'⁻¹ * (m * t' * (Matrix.GeneralLinearGroup.map (σ : L →+* L) m)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    (haD : ∀ j, (a j : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a j : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (ha : ∀ d : GL (Fin 2) L, (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      ∃! j, (a j)⁻¹ * d ∈ M) :
    Set.BijOn (param σ t' a) Set.univ J :=
  ⟨fun p _ => param_mem σ t' a ht'u ht'l hreg J hJ haD p, (param_injective σ t' M a ht'u ht'l hM haD ha).injOn,
    param_surjOn σ t' M a ht'u ht'l J hJ hM ha⟩

end Param

end R4BorelClassParam
p2m_reactivate "P2MW.S_AutomorphicForm_bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one.R4BorelClassParam"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one.R4BorelClassParam"

section

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (t' : GL (Fin 2) L)
    (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t' : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (J : Set (GL (Fin 2) L))
    (hJ : ∀ γ, γ ∈ J ↔ ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t'⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L))
    (M : Subgroup (GL (Fin 2) L))
    (hM : ∀ m, m ∈ M ↔ ((m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (m : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      t'⁻¹ * (m * t' * (Matrix.GeneralLinearGroup.map (σ : L →+* L) m)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {κ : Type*} (a : κ → GL (Fin 2) L)
    (haD : ∀ j, ((a j : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      ((a j : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (ha : ∀ d : GL (Fin 2) L, (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      ∃! j, (a j)⁻¹ * d ∈ M) :
    Set.BijOn (fun p : κ × Lˣ × L =>
        a p.1 * t' * Matrix.GeneralLinearGroup.map (σ : L →+* L) (AutomorphicForm.unipotentGL2 p.2.2) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) p.2.1 * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (a p.1))⁻¹)
      Set.univ J :=
  R4BorelClassParam.param_bijOn σ t' M a ht'u ht'l hreg J hJ hM haD ha

end
p2m_reactivate "P2MW.S_AutomorphicForm_bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one.R4BorelClassParam"

end S_AutomorphicForm_bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one
end P2MW
export P2MW.S_AutomorphicForm_bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one (solution)
