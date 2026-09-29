-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3ae12da0-1a7e-5d1e-8730-2b9598533170

import Theorems.Thm_IsArtinianRing_exists_units_eq_mul_apply_of_prod_iterate_apply_eq_one
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct TensorProduct.RightActions Pointwise IsMulCommutative
open Topology Filter Set

noncomputable section

namespace P2mTwistedTorusLocal

section Algebra

variable {R : Type*} [CommRing R]

theorem entries_of_commute (g X : Matrix (Fin 2) (Fin 2) R) (h : X * g = g * X) (u : R)
    (hu : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1) :
    X 0 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 0 1 ∧
    X 1 0 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 1 0 ∧
    X 0 0 - X 1 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * (g 0 0 - g 1 1) := by
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(X 0 1)) * hu + (-(u * (g 0 0 - g 1 1))) * e01
  · linear_combination (-(X 1 0)) * hu + (u * (g 0 0 - g 1 1)) * e10 +
      (-(4 * u * g 1 0)) * e00
  · linear_combination (-(X 0 0 - X 1 1)) * hu + (4 * u * g 1 0) * e01

theorem disc_eq (g : Matrix (Fin 2) (Fin 2) R) :
    g.trace ^ 2 - 4 * g.det = (g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0 := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]; ring

theorem smul_one_add_smul_apply (g : Matrix (Fin 2) (Fin 2) R) (a b : R) :
    (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) 0 0 = a + b * g 0 0 ∧
    (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) 0 1 = b * g 0 1 ∧
    (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) 1 0 = b * g 1 0 ∧
    (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) 1 1 = a + b * g 1 1 := by
  simp [Matrix.add_apply, Matrix.smul_apply]

theorem matrix_eq_of_entries {X Y : Matrix (Fin 2) (Fin 2) R} (h00 : X 0 0 = Y 0 0) (h01 : X 0 1 = Y 0 1)
    (h10 : X 1 0 = Y 1 0) (h11 : X 1 1 = Y 1 1) : X = Y := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem exists_eq_smul_one_add_smul (g X : Matrix (Fin 2) (Fin 2) R) (h : X * g = g * X)
    (hγ : IsUnit (g.trace ^ 2 - 4 * g.det)) :
    ∃ a b : R, X = a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g := by
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  rw [disc_eq] at hu
  obtain ⟨h1, h2, h3⟩ := entries_of_commute g X h u hu
  set p := u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) with hp
  refine ⟨X 0 0 - p * g 0 0, p, ?_⟩
  obtain ⟨y00, y01, y10, y11⟩ := smul_one_add_smul_apply g (X 0 0 - p * g 0 0) p
  refine matrix_eq_of_entries ?_ ?_ ?_ ?_
  · rw [y00]; ring
  · rw [y01]; exact h1
  · rw [y10]; exact h2
  · rw [y11]; linear_combination (-1 : R) * h3

theorem mul_comm_of_commute (g X Y : Matrix (Fin 2) (Fin 2) R) (hX : X * g = g * X) (hY : Y * g = g * Y)
    (hγ : IsUnit (g.trace ^ 2 - 4 * g.det)) : X * Y = Y * X := by
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  rw [disc_eq] at hu
  obtain ⟨a1, a2, a3⟩ := entries_of_commute g X hX u hu
  obtain ⟨b1, b2, b3⟩ := entries_of_commute g Y hY u hu
  set p := u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1))
  set q := u * (4 * g 1 0 * Y 0 1 + (g 0 0 - g 1 1) * (Y 0 0 - Y 1 1))
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta,
    Fin.mk_one]
  · linear_combination (Y 1 0) * a1 + (p * g 0 1) * b2 - (X 1 0) * b1 - (q * g 0 1) * a2
  · linear_combination (X 0 0 - X 1 1) * b1 + (q * g 0 1) * a3 - (Y 0 0 - Y 1 1) * a1 -
      (p * g 0 1) * b3
  · linear_combination (Y 0 0 - Y 1 1) * a2 + (p * g 1 0) * b3 - (X 0 0 - X 1 1) * b2 -
      (q * g 1 0) * a3
  · linear_combination (Y 0 1) * a2 + (p * g 1 0) * b1 - (X 0 1) * b2 - (q * g 1 0) * a1

theorem eq_zero_of_sq_eq_zero [IsReduced R] (g : Matrix (Fin 2) (Fin 2) R)
    (hγ : IsUnit (g.trace ^ 2 - 4 * g.det)) {a b : R}
    (h : (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) * (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) = 0) :
    a = 0 ∧ b = 0 := by
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  rw [disc_eq] at hu
  set X := a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g with hX
  obtain ⟨x00, x01, x10, x11⟩ := smul_one_add_smul_apply g a b
  rw [← hX] at x00 x01 x10 x11
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  have e11 := congr_fun (congr_fun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at e00 e01 e10 e11
  simp only [x00, x01, x10, x11] at e00 e01 e10 e11
  set β := b * (2 * a + b * (g 0 0 + g 1 1)) with hβ
  have c1 : β * g 0 1 = 0 := by linear_combination e01
  have c3 : β * (g 0 0 - g 1 1) = 0 := by linear_combination e00 - e11
  have c4 : β ^ 2 * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 0 := by
    linear_combination (β * (g 0 0 - g 1 1)) * c3 + (4 * β * g 1 0) * c1
  have hβ2 : β ^ 2 = 0 := by linear_combination (-(β ^ 2)) * hu + u * c4
  have c5 : b ^ 2 * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) + (2 * a + b * (g 0 0 + g 1 1)) ^ 2 = 0 := by
    linear_combination 2 * e00 + 2 * e11
  have c6 : b ^ 4 * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 0 := by
    linear_combination b ^ 2 * c5 - hβ2
  have hb4 : b ^ 4 = 0 := by linear_combination (-(b ^ 4)) * hu + u * c6
  have hb : b = 0 := IsReduced.eq_zero b ⟨4, hb4⟩
  subst hb
  have ha2 : a ^ 2 = 0 := by linear_combination e00
  exact ⟨IsReduced.eq_zero a ⟨2, ha2⟩, rfl⟩

end Algebra

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaTensor_iterate (k : ℕ) (y : L ⊗[K] A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[k] y =
      Algebra.TensorProduct.map (σ ^ k).toAlgHom (AlgHom.id K A) y := by
  induction k generalizing y with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero]
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul, pow_succ',
            AlgEquiv.mul_apply]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem sigmaTensor_iterate_tmul (k : ℕ) (l : L) (a : A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[k] (l ⊗ₜ a) = ((σ ^ k) l) ⊗ₜ a := by
  rw [sigmaTensor_iterate]; simp [Algebra.TensorProduct.map_tmul]

theorem sigmaTensor_iterate_of_pow_eq_one {m : ℕ} (hm : σ ^ m = 1) (y : L ⊗[K] A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[m] y = y := by
  rw [sigmaTensor_iterate, hm]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, hx, hy]

theorem sigmaGL_apply_val (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((AutomorphicForm.sigmaGL K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _) i j =
      AutomorphicForm.sigmaTensor K L A σ ((x : Matrix (Fin 2) (Fin 2) _) i j) := rfl

theorem sigmaGL_iterate_of_pow_eq_one {m : ℕ} (hm : σ ^ m = 1) (x : GL (Fin 2) (L ⊗[K] A)) :
    (AutomorphicForm.sigmaGL K L A σ)^[m] x = x := by
  have hentry : ∀ (k : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2),
      ((AutomorphicForm.sigmaGL K L A σ)^[k] x) i j =
        (AutomorphicForm.sigmaTensor K L A σ)^[k] (x i j) := by
    intro k
    induction k with
    | zero => intro x i j; rfl
    | succ k ih =>
        intro x i j
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', AutomorphicForm.sigmaGL,
          Matrix.GeneralLinearGroup.map_apply, ← AutomorphicForm.sigmaGL, ih]
  apply Units.ext
  ext i j
  rw [hentry, sigmaTensor_iterate_of_pow_eq_one K L A σ hm]

theorem sigmaGL_iterate_mul (k : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)) :
    (AutomorphicForm.sigmaGL K L A σ)^[k] (x * y) =
      (AutomorphicForm.sigmaGL K L A σ)^[k] x * (AutomorphicForm.sigmaGL K L A σ)^[k] y := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem sigmaGL_iterate_inv (k : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) :
    (AutomorphicForm.sigmaGL K L A σ)^[k] x⁻¹ = ((AutomorphicForm.sigmaGL K L A σ)^[k] x)⁻¹ := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_inv]

def pnorm (k : ℕ) (y : GL (Fin 2) (L ⊗[K] A)) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range k).map fun i => (AutomorphicForm.sigmaGL K L A σ)^[i] y).prod

theorem pnorm_zero (y : GL (Fin 2) (L ⊗[K] A)) : pnorm K L A σ 0 y = 1 := by
  simp [pnorm]

theorem pnorm_succ (k : ℕ) (y : GL (Fin 2) (L ⊗[K] A)) :
    pnorm K L A σ (k + 1) y = pnorm K L A σ k y * (AutomorphicForm.sigmaGL K L A σ)^[k] y := by
  simp [pnorm, List.range_succ, List.map_append, List.prod_append]

theorem normString_eq_pnorm (y : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ y = pnorm K L A σ (Module.finrank K L) y := rfl

theorem pnorm_add (a b : ℕ) (y : GL (Fin 2) (L ⊗[K] A)) :
    pnorm K L A σ (a + b) y = pnorm K L A σ a y * (AutomorphicForm.sigmaGL K L A σ)^[a] (pnorm K L A σ b y) := by
  induction b with
  | zero =>
      rw [Nat.add_zero, pnorm_zero]
      have : (AutomorphicForm.sigmaGL K L A σ)^[a] (1 : GL (Fin 2) (L ⊗[K] A)) = 1 := by
        induction a with
        | zero => rfl
        | succ a ih => rw [Function.iterate_succ_apply', ih, map_one]
      rw [this, mul_one]
  | succ b ih =>
      rw [← Nat.add_assoc, pnorm_succ, ih, pnorm_succ, sigmaGL_iterate_mul, mul_assoc,
        ← Function.iterate_add_apply]

theorem pnorm_succ' (k : ℕ) (y : GL (Fin 2) (L ⊗[K] A)) :
    pnorm K L A σ (k + 1) y = y * AutomorphicForm.sigmaGL K L A σ (pnorm K L A σ k y) := by
  rw [Nat.add_comm, pnorm_add, pnorm_succ, pnorm_zero, one_mul]
  rfl

theorem pnorm_mul_of_pow_eq_one {m : ℕ} (hm : σ ^ m = 1) (q : ℕ) (y : GL (Fin 2) (L ⊗[K] A)) :
    pnorm K L A σ (m * q) y = pnorm K L A σ m y ^ q := by
  induction q with
  | zero => rw [Nat.mul_zero, pnorm_zero, pow_zero]
  | succ q ih =>
      rw [Nat.mul_succ, pnorm_add, ih, Function.iterate_mul,
        Function.iterate_fixed (sigmaGL_iterate_of_pow_eq_one K L A σ hm _), pow_succ]

theorem pnorm_twistedConj (k : ℕ) (δ x : GL (Fin 2) (L ⊗[K] A)) :
    pnorm K L A σ k (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) =
      x⁻¹ * pnorm K L A σ k δ * (AutomorphicForm.sigmaGL K L A σ)^[k] x := by
  induction k with
  | zero => simp [pnorm_zero]
  | succ k ih =>
      rw [pnorm_succ, ih, pnorm_succ, sigmaGL_iterate_mul, sigmaGL_iterate_mul, sigmaGL_iterate_inv,
        Function.iterate_succ_apply]
      group

def theta (δ : GL (Fin 2) (L ⊗[K] A)) : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] A) :=
  (MulAut.conj δ).toMonoidHom.comp (AutomorphicForm.sigmaGL K L A σ)

theorem theta_apply (δ g : GL (Fin 2) (L ⊗[K] A)) :
    theta K L A σ δ g = δ * AutomorphicForm.sigmaGL K L A σ g * δ⁻¹ := rfl

theorem theta_iterate (δ : GL (Fin 2) (L ⊗[K] A)) (i : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) :
    (theta K L A σ δ)^[i] x = pnorm K L A σ i δ * (AutomorphicForm.sigmaGL K L A σ)^[i] x * (pnorm K L A σ i δ)⁻¹ := by
  induction i with
  | zero => simp [pnorm_zero]
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, theta_apply, map_mul, map_mul, map_inv, pnorm_succ',
        Function.iterate_succ_apply']
      group

theorem twistedConj_eq (δ z : GL (Fin 2) (L ⊗[K] A)) :
    z⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ z = z⁻¹ * theta K L A σ δ z * δ := by
  rw [theta_apply]; group

theorem mem_twistedCentralizer_iff_theta (δ t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ ↔ theta K L A σ δ t = t := by
  rw [theta_apply]; exact AutomorphicForm.mem_sigmaCentralizer_iff_fixed

end Twist

section Order

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)

include hσ

theorem orderOf_pos' : 0 < orderOf σ := by
  have h : IsOfFinOrder σ := isOfFinOrder_iff_pow_eq_one.2 ⟨Module.finrank K L, Module.finrank_pos, hσ⟩
  exact h.orderOf_pos

theorem orderOf_dvd_finrank : orderOf σ ∣ Module.finrank K L := orderOf_dvd_of_pow_eq_one hσ

theorem normString_eq_pnorm_pow (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ δ = pnorm K L A σ (orderOf σ) δ ^ (Module.finrank K L / orderOf σ) := by
  rw [normString_eq_pnorm, ← pnorm_mul_of_pow_eq_one K L A σ (pow_orderOf_eq_one σ),
    Nat.mul_div_cancel' (orderOf_dvd_finrank K L σ hσ)]

theorem pnorm_orderOf_mem_centralizer (δ : GL (Fin 2) (L ⊗[K] A)) :
    pnorm K L A σ (orderOf σ) δ ∈
      Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  rw [Subgroup.mem_centralizer_singleton_iff, normString_eq_pnorm_pow K L A σ hσ]
  exact (Commute.self_pow (pnorm K L A σ (orderOf σ) δ) (Module.finrank K L / orderOf σ)).eq

theorem theta_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    theta K L A σ δ (AutomorphicForm.normString K L A σ δ) = AutomorphicForm.normString K L A σ δ := by
  have h := pnorm_twistedConj K L A σ (Module.finrank K L) δ δ
  rw [inv_mul_cancel, one_mul, sigmaGL_iterate_of_pow_eq_one K L A σ hσ, ← normString_eq_pnorm,
    ← normString_eq_pnorm] at h

  have hNσ : ∀ (k : ℕ) (y : GL (Fin 2) (L ⊗[K] A)),
      pnorm K L A σ k (AutomorphicForm.sigmaGL K L A σ y) = AutomorphicForm.sigmaGL K L A σ (pnorm K L A σ k y) := by
    intro k y
    induction k with
    | zero => simp [pnorm_zero]
    | succ k ih =>
        rw [pnorm_succ, pnorm_succ, ih, map_mul, ← Function.iterate_succ_apply,
          Function.iterate_succ_apply']
  rw [normString_eq_pnorm, hNσ, ← normString_eq_pnorm] at h
  rw [theta_apply, h]; group

theorem theta_mem_centralizer (δ : GL (Fin 2) (L ⊗[K] A)) {z : GL (Fin 2) (L ⊗[K] A)}
    (hz : z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    theta K L A σ δ z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
  have h := congrArg (theta K L A σ δ) hz
  rw [map_mul, map_mul, theta_normString K L A σ hσ] at h
  exact h

theorem theta_iterate_mem_centralizer (δ : GL (Fin 2) (L ⊗[K] A)) (i : ℕ) {z : GL (Fin 2) (L ⊗[K] A)}
    (hz : z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    (theta K L A σ δ)^[i] z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  induction i with
  | zero => exact hz
  | succ i ih => rw [Function.iterate_succ_apply']; exact theta_mem_centralizer K L A σ hσ δ ih

theorem mul_comm_of_mem_centralizer {γ : GL (Fin 2) (L ⊗[K] A)} (hγ : AutomorphicForm.IsRegularSemisimple γ)
    {s t : GL (Fin 2) (L ⊗[K] A)} (hs : s ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] A))))
    (ht : t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] A)))) : s * t = t * s := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hs ht
  have hs' : (s : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * γ = γ * s := by
    rw [← Units.val_mul, hs, Units.val_mul]
  have ht' : (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * γ = γ * t := by
    rw [← Units.val_mul, ht, Units.val_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact mul_comm_of_commute (γ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) _ _ hs' ht' hγ

theorem theta_iterate_orderOf (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    {z : GL (Fin 2) (L ⊗[K] A)}
    (hz : z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    (theta K L A σ δ)^[orderOf σ] z = z := by
  rw [theta_iterate, sigmaGL_iterate_of_pow_eq_one K L A σ (pow_orderOf_eq_one σ),
    mul_comm_of_mem_centralizer K L A σ hσ hδ (pnorm_orderOf_mem_centralizer K L A σ hσ δ) hz]
  group

end Order

section CentralizerAlgebra

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
  (δ : GL (Fin 2) (L ⊗[K] A))

def sigmaM : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) →+* Matrix (Fin 2) (Fin 2) (L ⊗[K] A) :=
  (AutomorphicForm.sigmaTensor K L A σ).mapMatrix

theorem sigmaM_val (x : GL (Fin 2) (L ⊗[K] A)) :
    sigmaM K L A σ (x : Matrix (Fin 2) (Fin 2) _) = ((AutomorphicForm.sigmaGL K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _) := rfl

theorem sigmaM_smul_one (r : L ⊗[K] A) :
    sigmaM K L A σ (r • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) =
      (AutomorphicForm.sigmaTensor K L A σ r) • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
  ext i j
  simp only [sigmaM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs <;> simp

def thetaM : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) →+* Matrix (Fin 2) (Fin 2) (L ⊗[K] A) where
  toFun X := δ.val * sigmaM K L A σ X * δ⁻¹.val
  map_one' := by rw [map_one, mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  map_mul' X Y := by
    rw [map_mul]
    have h : (δ⁻¹.val : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * δ.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc δ.val * (sigmaM K L A σ X * sigmaM K L A σ Y) * δ⁻¹.val
        = δ.val * sigmaM K L A σ X * (δ⁻¹.val * δ.val) * sigmaM K L A σ Y * δ⁻¹.val := by
          rw [h, mul_one]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_zero' := by rw [map_zero, mul_zero, zero_mul]
  map_add' X Y := by rw [map_add, mul_add, add_mul]

theorem thetaM_apply (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    thetaM K L A σ δ X = δ.val * sigmaM K L A σ X * δ⁻¹.val := rfl

theorem thetaM_val (x : GL (Fin 2) (L ⊗[K] A)) :
    thetaM K L A σ δ (x : Matrix (Fin 2) (Fin 2) _) = ((theta K L A σ δ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _) := by
  rw [thetaM_apply, sigmaM_val, theta_apply, Units.val_mul, Units.val_mul]

theorem thetaM_iterate_val (i : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) :
    (thetaM K L A σ δ)^[i] (x : Matrix (Fin 2) (Fin 2) _) =
      (((theta K L A σ δ)^[i] x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, thetaM_val]

theorem thetaM_smul_one (r : L ⊗[K] A) :
    thetaM K L A σ δ (r • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) =
      (AutomorphicForm.sigmaTensor K L A σ r) • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
  rw [thetaM_apply, sigmaM_smul_one, Matrix.mul_smul, mul_one, Matrix.smul_mul, ← Units.val_mul,
    mul_inv_cancel, Units.val_one]

theorem thetaM_iterate_smul_one (i : ℕ) (r : L ⊗[K] A) :
    (thetaM K L A σ δ)^[i] (r • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) =
      ((AutomorphicForm.sigmaTensor K L A σ)^[i] r) • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, thetaM_smul_one]

def E : Subalgebra (L ⊗[K] A) (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
  Subalgebra.centralizer (L ⊗[K] A)
    {((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))}

theorem mem_E_iff (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    X ∈ E K L A σ δ ↔
      X * ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _) =
        ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _) * X := by
  rw [E, Subalgebra.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact eq_comm

theorem val_mem_E_iff (x : GL (Fin 2) (L ⊗[K] A)) :
    (x : Matrix (Fin 2) (Fin 2) _) ∈ E K L A σ δ ↔
      x ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  rw [mem_E_iff, Subgroup.mem_centralizer_singleton_iff, ← Units.val_mul, ← Units.val_mul, Units.val_inj]

theorem E_isMulCommutative (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ)) :
    IsMulCommutative (E K L A σ δ) :=
  IsMulCommutative.of_comm fun X Y => Subtype.ext
    (mul_comm_of_commute _ _ _ ((mem_E_iff K L A σ δ _).1 X.2) ((mem_E_iff K L A σ δ _).1 Y.2) hδ)

theorem E_moduleFinite [IsArtinianRing A] : Module.Finite (L ⊗[K] A) (E K L A σ δ) := by
  haveI : IsArtinianRing (L ⊗[K] A) := IsArtinianRing.of_finite A (L ⊗[K] A)
  haveI : IsNoetherian (L ⊗[K] A) (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  exact Module.Finite.of_injective (E K L A σ δ).val.toLinearMap Subtype.val_injective

theorem E_isArtinianRing [IsArtinianRing A] : IsArtinianRing (E K L A σ δ) := by
  haveI : IsArtinianRing (L ⊗[K] A) := IsArtinianRing.of_finite A (L ⊗[K] A)
  haveI := E_moduleFinite K L A σ δ
  exact IsArtinianRing.of_finite (L ⊗[K] A) (E K L A σ δ)

theorem E_isReduced [IsReduced (L ⊗[K] A)]
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ)) :
    IsReduced (E K L A σ δ) := by
  refine (isReduced_iff_pow_one_lt 2 one_lt_two).2 fun X hX => ?_
  obtain ⟨a, b, hab⟩ := exists_eq_smul_one_add_smul _ _ ((mem_E_iff K L A σ δ _).1 X.2) hδ
  have h2 : (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = 0 := by
    have := congrArg Subtype.val hX
    simpa [pow_two] using this
  rw [hab] at h2
  obtain ⟨ha, hb⟩ := eq_zero_of_sq_eq_zero _ hδ h2
  apply Subtype.ext
  rw [hab, ha, hb, zero_smul, zero_smul, add_zero]
  rfl

include hσ in

theorem thetaM_mem_E {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)} (hX : X ∈ E K L A σ δ) :
    thetaM K L A σ δ X ∈ E K L A σ δ := by
  rw [mem_E_iff] at hX ⊢
  have h := congrArg (thetaM K L A σ δ) hX
  rw [map_mul, map_mul, thetaM_val, theta_normString K L A σ hσ] at h
  exact h

include hσ in

def thetaE : E K L A σ δ →+* E K L A σ δ :=
  (thetaM K L A σ δ).restrict (E K L A σ δ) (E K L A σ δ) fun _ hX => thetaM_mem_E K L A σ hσ δ hX

theorem thetaE_val (X : E K L A σ δ) : ((thetaE K L A σ hσ δ X : E K L A σ δ) : Matrix (Fin 2) (Fin 2) _) = thetaM K L A σ δ X := rfl

theorem thetaE_iterate_val (i : ℕ) (X : E K L A σ δ) :
    (((thetaE K L A σ hσ δ)^[i] X : E K L A σ δ) : Matrix (Fin 2) (Fin 2) _) = (thetaM K L A σ δ)^[i] X := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', thetaE_val, ih]

def unitOfE (z : GL (Fin 2) (L ⊗[K] A))
    (hz : z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    (E K L A σ δ)ˣ where
  val := ⟨(z : Matrix (Fin 2) (Fin 2) _), (val_mem_E_iff K L A σ δ z).2 hz⟩
  inv := ⟨((z⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _), (val_mem_E_iff K L A σ δ z⁻¹).2 (Subgroup.inv_mem _ hz)⟩
  val_inv := Subtype.ext (by simp)
  inv_val := Subtype.ext (by simp)

def ofUnitE : (E K L A σ δ)ˣ →* GL (Fin 2) (L ⊗[K] A) where
  toFun w :=
    { val := ((w : E K L A σ δ) : Matrix (Fin 2) (Fin 2) _)
      inv := (((w⁻¹ : (E K L A σ δ)ˣ) : E K L A σ δ) : Matrix (Fin 2) (Fin 2) _)
      val_inv := by rw [← Subalgebra.coe_mul, ← Units.val_mul, mul_inv_cancel]; rfl
      inv_val := by rw [← Subalgebra.coe_mul, ← Units.val_mul, inv_mul_cancel]; rfl }
  map_one' := Units.ext rfl
  map_mul' v w := Units.ext rfl

theorem ofUnitE_val (w : (E K L A σ δ)ˣ) :
    ((ofUnitE K L A σ δ w : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      ((w : E K L A σ δ) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := rfl

theorem ofUnitE_mem (w : (E K L A σ δ)ˣ) :
    ofUnitE K L A σ δ w ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) :=
  (val_mem_E_iff K L A σ δ _).1 (w : E K L A σ δ).2

theorem ofUnitE_unitOfE (z : GL (Fin 2) (L ⊗[K] A))
    (hz : z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    ofUnitE K L A σ δ (unitOfE K L A σ δ z hz) = z := Units.ext rfl

theorem theta_ofUnitE (w : (E K L A σ δ)ˣ) :
    theta K L A σ δ (ofUnitE K L A σ δ w) = ofUnitE K L A σ δ (Units.map (thetaE K L A σ hσ δ).toMonoidHom w) := by
  apply Units.ext
  rw [← thetaM_val, ofUnitE_val, ofUnitE_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    thetaE_val]

end CentralizerAlgebra

section Free

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
  (δ : GL (Fin 2) (L ⊗[K] A))

theorem thetaE_iterate_orderOf (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    (X : E K L A σ δ) : (thetaE K L A σ hσ δ)^[orderOf σ] X = X := by
  apply Subtype.ext
  rw [thetaE_iterate_val]

  have hgen : ∀ (i : ℕ) (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)),
      (thetaM K L A σ δ)^[i] Y = (pnorm K L A σ i δ : Matrix (Fin 2) (Fin 2) _) * (sigmaM K L A σ)^[i] Y *
        (((pnorm K L A σ i δ)⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _) := by
    intro i
    induction i with
    | zero => intro Y; simp [pnorm_zero]
    | succ i ih =>
        intro Y
        rw [Function.iterate_succ_apply', ih, thetaM_apply, map_mul, map_mul, sigmaM_val, sigmaM_val, map_inv,
          pnorm_succ', Function.iterate_succ_apply', mul_inv_rev, Units.val_mul, Units.val_mul]
        simp only [mul_assoc]
  have hσM : (sigmaM K L A σ)^[orderOf σ] (X : Matrix (Fin 2) (Fin 2) _) = X := by
    have : ∀ (i : ℕ) (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (a b : Fin 2),
        ((sigmaM K L A σ)^[i] Y) a b = (AutomorphicForm.sigmaTensor K L A σ)^[i] (Y a b) := by
      intro i
      induction i with
      | zero => intro Y a b; rfl
      | succ i ih => intro Y a b; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl
    ext a b
    rw [this, sigmaTensor_iterate_of_pow_eq_one K L A σ (pow_orderOf_eq_one σ)]
  rw [hgen, hσM]
  have hP := pnorm_orderOf_mem_centralizer K L A σ hσ δ
  have hcomm : ((pnorm K L A σ (orderOf σ) δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
      (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * ((pnorm K L A σ (orderOf σ) δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    mul_comm_of_commute _ _ _ ((mem_E_iff K L A σ δ _).1 ((val_mem_E_iff K L A σ δ _).2 hP))
      ((mem_E_iff K L A σ δ _).1 X.2) hδ
  rw [hcomm, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

theorem thetaE_free (e : E K L A σ δ) (he : IsIdempotentElem e) (he0 : e ≠ 0) (i : ℕ) (hi : 0 < i)
    (hik : i < orderOf σ) : ¬ ∀ x : E K L A σ δ, (thetaE K L A σ hσ δ)^[i] (e * x) = e * x := by
  intro h

  have hσi : σ ^ i ≠ 1 := pow_ne_one_of_lt_orderOf hi.ne' hik
  obtain ⟨l, hl⟩ : ∃ l : L, (σ ^ i) l ≠ l := by
    by_contra hall
    push Not at hall
    exact hσi (AlgEquiv.ext hall)
  set u : L := (σ ^ i) l - l with hu
  have hu0 : u ≠ 0 := sub_ne_zero.2 hl

  set r : L ⊗[K] A := l ⊗ₜ 1 with hr
  have hθe : (thetaM K L A σ δ)^[i] (e : Matrix (Fin 2) (Fin 2) _) = e := by
    have := congrArg Subtype.val (h 1)
    rw [mul_one, thetaE_iterate_val] at this
    exact this
  have h1 := congrArg Subtype.val (h (algebraMap (L ⊗[K] A) (E K L A σ δ) r))
  rw [thetaE_iterate_val] at h1
  have hcoe : ((e * algebraMap (L ⊗[K] A) (E K L A σ δ) r : E K L A σ δ) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (e : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * (r • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) := by
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one]
  rw [hcoe] at h1
  rw [← RingHom.coe_pow, map_mul, RingHom.coe_pow, hθe, thetaM_iterate_smul_one, hr,
    sigmaTensor_iterate_tmul, Matrix.mul_smul, Matrix.mul_smul, mul_one] at h1

  have h2 : (u ⊗ₜ[K] (1 : A)) • (e : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = 0 := by
    rw [hu, TensorProduct.sub_tmul, sub_smul, h1, sub_self]
  have hunit : IsUnit (u ⊗ₜ[K] (1 : A) : L ⊗[K] A) :=
    (isUnit_iff_ne_zero.2 hu0).map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
  apply he0
  apply Subtype.ext
  have h3 := congrArg (fun Y => ((hunit.unit⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) • Y) h2
  simp only [smul_zero, smul_smul, IsUnit.val_inv_mul, one_smul] at h3
  exact h3

end Free

section ThetaNorm

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
  (δ : GL (Fin 2) (L ⊗[K] A))

def ptheta (i : ℕ) (c : GL (Fin 2) (L ⊗[K] A)) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range i).map fun j => (theta K L A σ δ)^[j] c).prod

theorem ptheta_zero (c : GL (Fin 2) (L ⊗[K] A)) : ptheta K L A σ δ 0 c = 1 := by simp [ptheta]

theorem ptheta_succ (i : ℕ) (c : GL (Fin 2) (L ⊗[K] A)) :
    ptheta K L A σ δ (i + 1) c = ptheta K L A σ δ i c * (theta K L A σ δ)^[i] c := by
  simp [ptheta, List.range_succ]

theorem ptheta_succ' (i : ℕ) (c : GL (Fin 2) (L ⊗[K] A)) :
    ptheta K L A σ δ (i + 1) c = c * ptheta K L A σ δ i (theta K L A σ δ c) := by
  unfold ptheta
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  congr 1

theorem theta_iterate_one (j : ℕ) : (theta K L A σ δ)^[j] 1 = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, map_one]

theorem ptheta_one' (i : ℕ) : ptheta K L A σ δ i 1 = 1 := by
  induction i with
  | zero => exact ptheta_zero K L A σ δ 1
  | succ i ih => rw [ptheta_succ, ih, one_mul, theta_iterate_one]

include hσ

theorem ptheta_mem (i : ℕ) {c : GL (Fin 2) (L ⊗[K] A)}
    (hc : c ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    ptheta K L A σ δ i c ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  induction i with
  | zero => rw [ptheta_zero]; exact Subgroup.one_mem _
  | succ i ih => rw [ptheta_succ]; exact Subgroup.mul_mem _ ih (theta_iterate_mem_centralizer K L A σ hσ δ i hc)

theorem ptheta_mul (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ)) (i : ℕ)
    {y z : GL (Fin 2) (L ⊗[K] A)}
    (hy : y ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))))
    (hz : z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    ptheta K L A σ δ i (y * z) = ptheta K L A σ δ i y * ptheta K L A σ δ i z := by
  induction i with
  | zero => simp [ptheta_zero]
  | succ i ih =>
      have hmul : ∀ (j : ℕ) (a b : GL (Fin 2) (L ⊗[K] A)),
          (theta K L A σ δ)^[j] (a * b) = (theta K L A σ δ)^[j] a * (theta K L A σ δ)^[j] b := by
        intro j a b
        induction j with
        | zero => rfl
        | succ j ihj => simp only [Function.iterate_succ_apply', ihj, map_mul]
      rw [ptheta_succ, ptheta_succ, ptheta_succ, ih, hmul]
      have hc := mul_comm_of_mem_centralizer K L A σ hσ hδ (ptheta_mem K L A σ hσ δ i hz)
        (theta_iterate_mem_centralizer K L A σ hσ δ i hy)
      calc ptheta K L A σ δ i y * ptheta K L A σ δ i z * ((theta K L A σ δ)^[i] y * (theta K L A σ δ)^[i] z)
          = ptheta K L A σ δ i y * (ptheta K L A σ δ i z * (theta K L A σ δ)^[i] y) * (theta K L A σ δ)^[i] z := by
            simp only [mul_assoc]
        _ = ptheta K L A σ δ i y * ((theta K L A σ δ)^[i] y * ptheta K L A σ δ i z) * (theta K L A σ δ)^[i] z := by
            rw [hc]
        _ = ptheta K L A σ δ i y * (theta K L A σ δ)^[i] y * (ptheta K L A σ δ i z * (theta K L A σ δ)^[i] z) := by
            simp only [mul_assoc]

theorem ptheta_inv (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ)) (i : ℕ)
    {z : GL (Fin 2) (L ⊗[K] A)}
    (hz : z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    ptheta K L A σ δ i z⁻¹ = (ptheta K L A σ δ i z)⁻¹ := by
  have h := ptheta_mul K L A σ hσ δ hδ i hz (Subgroup.inv_mem _ hz)
  rw [mul_inv_cancel, ptheta_one'] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem ptheta_theta (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    {z : GL (Fin 2) (L ⊗[K] A)}
    (hz : z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    ptheta K L A σ δ (orderOf σ) (theta K L A σ δ z) = ptheta K L A σ δ (orderOf σ) z := by
  have h1 := ptheta_succ' K L A σ δ (orderOf σ) z
  rw [ptheta_succ, theta_iterate_orderOf K L A σ hσ δ hδ hz] at h1
  have hc := mul_comm_of_mem_centralizer K L A σ hσ hδ (ptheta_mem K L A σ hσ δ (orderOf σ) hz) hz
  rw [hc] at h1
  exact (mul_left_cancel h1).symm

theorem ptheta_psi (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    {z : GL (Fin 2) (L ⊗[K] A)}
    (hz : z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    ptheta K L A σ δ (orderOf σ) (z⁻¹ * theta K L A σ δ z) = 1 := by
  rw [ptheta_mul K L A σ hσ δ hδ _ (Subgroup.inv_mem _ hz) (theta_mem_centralizer K L A σ hσ δ hz),
    ptheta_inv K L A σ hσ δ hδ _ hz, ptheta_theta K L A σ hσ δ hδ hz, inv_mul_cancel]

theorem psi_mul (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    {y z : GL (Fin 2) (L ⊗[K] A)}
    (hy : y ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))))
    (hz : z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    (y * z)⁻¹ * theta K L A σ δ (y * z) = (y⁻¹ * theta K L A σ δ y) * (z⁻¹ * theta K L A σ δ z) := by
  have hc := mul_comm_of_mem_centralizer K L A σ hσ hδ (Subgroup.inv_mem _ hz)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) (theta_mem_centralizer K L A σ hσ δ hy))
  rw [map_mul, mul_inv_rev]
  calc z⁻¹ * y⁻¹ * (theta K L A σ δ y * theta K L A σ δ z)
      = (z⁻¹ * (y⁻¹ * theta K L A σ δ y)) * theta K L A σ δ z := by simp only [mul_assoc]
    _ = ((y⁻¹ * theta K L A σ δ y) * z⁻¹) * theta K L A σ δ z := by rw [hc]
    _ = (y⁻¹ * theta K L A σ δ y) * (z⁻¹ * theta K L A σ δ z) := by simp only [mul_assoc]

end ThetaNorm

section H90

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [IsArtinianRing A] [IsReduced (L ⊗[K] A)]
  (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1) (δ : GL (Fin 2) (L ⊗[K] A))

include hσ

theorem exists_psi_eq (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    {c : GL (Fin 2) (L ⊗[K] A)}
    (hc : c ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))))
    (hN : ptheta K L A σ δ (orderOf σ) c = 1) :
    ∃ z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))),
      z⁻¹ * theta K L A σ δ z = c := by
  classical
  set k := orderOf σ with hk_def
  have hk : 0 < k := orderOf_pos' K L σ hσ
  haveI : IsMulCommutative (E K L A σ δ) := E_isMulCommutative K L A σ δ hδ
  haveI : IsArtinianRing (E K L A σ δ) := E_isArtinianRing K L A σ δ
  haveI : IsReduced (E K L A σ δ) := E_isReduced K L A σ δ hδ
  set θE := thetaE K L A σ hσ δ with hθE
  have hθ : ∀ x : E K L A σ δ, θE^[k] x = x := thetaE_iterate_orderOf K L A σ hσ δ hδ
  have hfree : ∀ e : E K L A σ δ, IsIdempotentElem e → e ≠ 0 → ∀ i : ℕ, 0 < i → i < k →
      ¬ ∀ x : E K L A σ δ, θE^[i] (e * x) = e * x := thetaE_free K L A σ hσ δ

  have hcinv := Subgroup.inv_mem _ hc
  set cu : (E K L A σ δ)ˣ := unitOfE K L A σ δ c⁻¹ hcinv with hcu
  have hval : ∀ i : ℕ, (((θE^[i] (cu : E K L A σ δ)) : E K L A σ δ) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      ((((theta K L A σ δ)^[i] c⁻¹) : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := fun i => by
    rw [hθE, thetaE_iterate_val]
    exact thetaM_iterate_val K L A σ δ i c⁻¹
  have hlist : ((List.range k).map fun i => θE^[i] (cu : E K L A σ δ)).prod = 1 := by
    apply Subtype.val_injective
    have h1 := map_list_prod ((E K L A σ δ).val) ((List.range k).map fun i => θE^[i] (cu : E K L A σ δ))
    rw [List.map_map] at h1
    have h2 : ((E K L A σ δ).val ∘ fun i => θE^[i] (cu : E K L A σ δ)) =
        (Units.coeHom (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) ∘ fun i => (theta K L A σ δ)^[i] c⁻¹ := by
      funext i
      exact hval i
    rw [h2, ← List.map_map, ← map_list_prod] at h1
    change (((List.range k).map fun i => θE^[i] (cu : E K L A σ δ)).prod : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = 1
    rw [show (((List.range k).map fun i => θE^[i] (cu : E K L A σ δ)).prod : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (E K L A σ δ).val ((List.range k).map fun i => θE^[i] (cu : E K L A σ δ)).prod from rfl, h1]
    change (((ptheta K L A σ δ k c⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) = 1
    rw [ptheta_inv K L A σ hσ δ hδ k hc, hN, inv_one, Units.val_one]
  obtain ⟨z, hz⟩ :=
    IsArtinianRing.exists_units_eq_mul_apply_of_prod_iterate_apply_eq_one (E K L A σ δ) θE k hk hθ hfree cu hlist
  refine ⟨ofUnitE K L A σ δ z, ofUnitE_mem K L A σ δ z, ?_⟩

  have hzu : z = cu * Units.map θE.toMonoidHom z := Units.ext hz
  have hψ : z⁻¹ * Units.map θE.toMonoidHom z = cu⁻¹ := by
    calc z⁻¹ * Units.map θE.toMonoidHom z = z⁻¹ * (cu⁻¹ * (cu * Units.map θE.toMonoidHom z)) := by
          rw [inv_mul_cancel_left]
      _ = z⁻¹ * (cu⁻¹ * z) := by rw [← hzu]
      _ = cu⁻¹ := by rw [mul_comm cu⁻¹ z, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcu' : ofUnitE K L A σ δ cu⁻¹ = c := by
    rw [map_inv, hcu, ofUnitE_unitOfE, inv_inv]
  rw [theta_ofUnitE K L A σ hσ δ, ← map_inv, ← map_mul, hψ, hcu']

end H90

section Topology

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem t2Space_GL [T2Space A] : T2Space (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.t2Space

theorem secondCountableTopology_GL [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem locallyCompactSpace_GL [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end Topology

section TensorTopology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem secondCountableTopology_tensor [SecondCountableTopology A] :
    SecondCountableTopology (L ⊗[K] A) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  let ι := Module.Free.ChooseBasisIndex A (L ⊗[K] A)
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype A (L ⊗[K] A)
  let b : Module.Basis ι A (L ⊗[K] A) := Module.Free.chooseBasis A (L ⊗[K] A)
  let e : (L ⊗[K] A) ≃ₗ[A] (ι → A) := b.equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : (L ⊗[K] A) ≃ₜ (ι → A) :=
    { toEquiv := e.toEquiv, continuous_toFun := h1, continuous_invFun := h2 }
  exact eh.isInducing.secondCountableTopology

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaTensor K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h := IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
  exact h

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

theorem continuous_theta (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) : Continuous (theta K L A σ δ) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  have h : (theta K L A σ δ : GL (Fin 2) (L ⊗[K] A) → GL (Fin 2) (L ⊗[K] A)) =
      fun g => δ * AutomorphicForm.sigmaGL K L A σ g * δ⁻¹ := funext fun g => theta_apply K L A σ δ g
  rw [h]
  exact (continuous_const.mul (continuous_sigmaGL K L A σ)).mul continuous_const

theorem continuous_theta_iterate (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (i : ℕ) :
    Continuous ((theta K L A σ δ)^[i]) := by
  induction i with
  | zero => exact continuous_id
  | succ i ih => rw [Function.iterate_succ']; exact (continuous_theta K L A σ δ).comp ih

theorem continuous_ptheta (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (i : ℕ) :
    Continuous (ptheta K L A σ δ i) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  induction i with
  | zero =>
      have h : ptheta K L A σ δ 0 = fun _ => 1 := funext fun c => ptheta_zero K L A σ δ c
      rw [h]; exact continuous_const
  | succ i ih =>
      have h : ptheta K L A σ δ (i + 1) = fun c => ptheta K L A σ δ i c * (theta K L A σ δ)^[i] c :=
        funext fun c => ptheta_succ K L A σ δ i c
      rw [h]; exact ih.mul (continuous_theta_iterate K L A σ δ i)

end TensorTopology

section Main

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [IsArtinianRing A] [IsReduced (L ⊗[K] A)]
  (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1) (δ : GL (Fin 2) (L ⊗[K] A))
  (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))

abbrev Zc : Subgroup (GL (Fin 2) (L ⊗[K] A)) :=
  Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))

include hσ hδ in

def Z1 : Subgroup (GL (Fin 2) (L ⊗[K] A)) where
  carrier := {c | c ∈ Zc K L A σ δ ∧ ptheta K L A σ δ (orderOf σ) c = 1}
  one_mem' := ⟨Subgroup.one_mem _, ptheta_one' K L A σ δ _⟩
  mul_mem' {y z} hy hz := ⟨Subgroup.mul_mem _ hy.1 hz.1, by
    rw [ptheta_mul K L A σ hσ δ hδ _ hy.1 hz.1, hy.2, hz.2, one_mul]⟩
  inv_mem' {z} hz := ⟨Subgroup.inv_mem _ hz.1, by rw [ptheta_inv K L A σ hσ δ hδ _ hz.1, hz.2, inv_one]⟩

theorem mem_Z1_iff (c : GL (Fin 2) (L ⊗[K] A)) :
    c ∈ Z1 K L A σ hσ δ hδ ↔ c ∈ Zc K L A σ δ ∧ ptheta K L A σ δ (orderOf σ) c = 1 := Iff.rfl

def psiHom : Zc K L A σ δ →* Z1 K L A σ hσ δ hδ where
  toFun z := ⟨(z : GL (Fin 2) (L ⊗[K] A))⁻¹ * theta K L A σ δ z,
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ z.2) (theta_mem_centralizer K L A σ hσ δ z.2),
      ptheta_psi K L A σ hσ δ hδ z.2⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' y z := Subtype.ext (by
    change ((y : GL (Fin 2) (L ⊗[K] A)) * z)⁻¹ * theta K L A σ δ (y * z) = _
    rw [psi_mul K L A σ hσ δ hδ y.2 z.2]
    rfl)

theorem psiHom_apply (z : Zc K L A σ δ) :
    ((psiHom K L A σ hσ δ hδ z : Z1 K L A σ hσ δ hδ) : GL (Fin 2) (L ⊗[K] A)) =
      (z : GL (Fin 2) (L ⊗[K] A))⁻¹ * theta K L A σ δ z := rfl

theorem psiHom_surjective : Function.Surjective (psiHom K L A σ hσ δ hδ) := by
  intro c
  obtain ⟨z, hz, hzc⟩ := exists_psi_eq K L A σ hσ δ hδ c.2.1 c.2.2
  exact ⟨⟨z, hz⟩, Subtype.ext hzc⟩

include hσ hδ in

theorem main {C : Set (GL (Fin 2) (L ⊗[K] A))} (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] A)), IsCompact D ∧
      {z : GL (Fin 2) (L ⊗[K] A) | z ∈ Zc K L A σ δ ∧
          z⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ z ∈ C} ⊆
        (AutomorphicForm.twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) * D := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.t2Space_tensor K L A
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L A
  haveI := secondCountableTopology_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := t2Space_GL (L ⊗[K] A)
  haveI := secondCountableTopology_GL (L ⊗[K] A)
  haveI := locallyCompactSpace_GL (L ⊗[K] A)
  haveI : SigmaCompactSpace (GL (Fin 2) (L ⊗[K] A)) := sigmaCompactSpace_of_locallyCompact_secondCountable

  have hZc : IsClosed ((Zc K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) := by
    change IsClosed (Set.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))))
    exact Set.isClosed_centralizer _
  have hZ1c : IsClosed ((Z1 K L A σ hσ δ hδ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) := by
    have : ((Z1 K L A σ hσ δ hδ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) =
        ((Zc K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) ∩ (ptheta K L A σ δ (orderOf σ)) ⁻¹' {1} := by
      ext c; rfl
    rw [this]
    exact hZc.inter ((isClosed_singleton).preimage (continuous_ptheta K L A σ δ _))
  haveI : SigmaCompactSpace (Zc K L A σ δ) := hZc.sigmaCompactSpace
  haveI : LocallyCompactSpace (Zc K L A σ δ) := hZc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (Z1 K L A σ hσ δ hδ) := hZ1c.isClosedEmbedding_subtypeVal.locallyCompactSpace

  have hcont : Continuous (psiHom K L A σ hσ δ hδ) := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.inv).mul ((continuous_theta K L A σ δ).comp continuous_subtype_val)
  have hopen : IsOpenMap (psiHom K L A σ hσ δ hδ) :=
    MonoidHom.isOpenMap_of_sigmaCompact _ (psiHom_surjective K L A σ hσ δ hδ) hcont

  set C' : Set (GL (Fin 2) (L ⊗[K] A)) := C * {δ⁻¹} with hC'
  have hC'c : IsCompact C' := hC.mul isCompact_singleton
  set K1 : Set (Z1 K L A σ hσ δ hδ) := ((↑) : Z1 K L A σ hσ δ hδ → GL (Fin 2) (L ⊗[K] A)) ⁻¹' C' with hK1
  have hK1c : IsCompact K1 := hZ1c.isClosedEmbedding_subtypeVal.isCompact_preimage hC'c

  have hN : ∀ x : Zc K L A σ δ, ∃ N : Set (Zc K L A σ δ), IsCompact N ∧ N ∈ 𝓝 x := fun x =>
    exists_compact_mem_nhds x
  choose N hNc hNn using hN
  have hcover : K1 ⊆ ⋃ x : Zc K L A σ δ, (psiHom K L A σ hσ δ hδ) '' interior (N x) := by
    intro y _
    obtain ⟨x, hx⟩ := psiHom_surjective K L A σ hσ δ hδ y
    exact Set.mem_iUnion.2 ⟨x, x, mem_interior_iff_mem_nhds.2 (hNn x), hx⟩
  obtain ⟨t, ht⟩ := hK1c.elim_finite_subcover (fun x => (psiHom K L A σ hσ δ hδ) '' interior (N x))
    (fun x => hopen _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ t, ((↑) : Zc K L A σ δ → GL (Fin 2) (L ⊗[K] A)) '' (N x),
    t.isCompact_biUnion fun x _ => (hNc x).image continuous_subtype_val, ?_⟩
  rintro z ⟨hzZ, hzC⟩

  have hψ : psiHom K L A σ hσ δ hδ ⟨z, hzZ⟩ ∈ K1 := by
    change z⁻¹ * theta K L A σ δ z ∈ C'
    have h : z⁻¹ * theta K L A σ δ z = (z⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ z) * δ⁻¹ := by
      rw [twistedConj_eq]; group
    rw [h]
    exact Set.mul_mem_mul hzC (Set.mem_singleton _)
  obtain ⟨x, hxt, n, hn, hnz⟩ : ∃ x ∈ t, ∃ n ∈ interior (N x),
      psiHom K L A σ hσ δ hδ n = psiHom K L A σ hσ δ hδ ⟨z, hzZ⟩ := by
    have := ht hψ
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at this
    obtain ⟨x, hxt, n, hn, hnz⟩ := this
    exact ⟨x, hxt, n, hn, hnz⟩
  have hval : (n : GL (Fin 2) (L ⊗[K] A))⁻¹ * theta K L A σ δ n = z⁻¹ * theta K L A σ δ z := by
    have := congrArg (fun y : Z1 K L A σ hσ δ hδ => (y : GL (Fin 2) (L ⊗[K] A))) hnz
    simpa only [psiHom_apply] using this

  have hT : z * (n : GL (Fin 2) (L ⊗[K] A))⁻¹ ∈ AutomorphicForm.twistedCentralizer K L A σ δ := by
    rw [mem_twistedCentralizer_iff_theta, map_mul, map_inv]
    have h1 : theta K L A σ δ n = (n : GL (Fin 2) (L ⊗[K] A)) * (z⁻¹ * theta K L A σ δ z) := by
      rw [← hval, mul_inv_cancel_left]
    rw [h1, mul_inv_rev, mul_inv_rev, inv_inv]
    group
  refine Set.mem_mul.2 ⟨z * (n : GL (Fin 2) (L ⊗[K] A))⁻¹, hT, (n : GL (Fin 2) (L ⊗[K] A)), ?_, by group⟩
  exact Set.mem_iUnion₂.2 ⟨x, hxt, n, interior_subset hn, rfl⟩

end Main

end P2mTwistedTorusLocal

end

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [IsArtinianRing A]
    [IsReduced (L ⊗[K] A)]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    (C : Set (GL (Fin 2) (L ⊗[K] A))) (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] A)), IsCompact D ∧
      {z : GL (Fin 2) (L ⊗[K] A) |
          z ∈ Subgroup.centralizer
              ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) ∧
            z⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ z ∈ C} ⊆
        (AutomorphicForm.twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) * D :=
  P2mTwistedTorusLocal.main K L A σ hσ δ hδ hC

end S_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing (solution)
