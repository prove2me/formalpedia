-- Prove2me | solution 1 for AutomorphicForm.isSigmaConjugate_adeleRing_of_normString_eq_of_normString_mem_center_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3d320653-4557-5d9c-a952-22a2a79297e5

import Theorems.Thm_RingEquiv_exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free
import Theorems.Thm_NumberField_AdeleRing_free_of_pi_linearEquiv_pi
import Theorems.Thm_AutomorphicForm_sigmaTensor_apply_eq_self_iff
import Theorems.Thm_NumberField_AdeleRing_exists_completeOrthogonalIdempotents_and_isUnit_sum_mul_of_span_range_eq_top
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isSigmaConjugate_adeleRing_of_normString_eq_of_normString_mem_center_of_finrank_eq_two

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace P2mH90Inner

open scoped TensorProduct

section Core

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

local notation "S" => L ⊗[K] A
local notation "M" => Matrix (Fin 2) (Fin 2) (L ⊗[K] A)

abbrev sT : (L ⊗[K] A) →+* (L ⊗[K] A) := AutomorphicForm.sigmaTensor K L A σ

abbrev sM : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) →+* Matrix (Fin 2) (Fin 2) (L ⊗[K] A) :=
  (AutomorphicForm.sigmaTensor K L A σ).mapMatrix

abbrev sG : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] A) := AutomorphicForm.sigmaGL K L A σ

theorem sM_coe (g : GL (Fin 2) S) : sM K L A σ (g : M) = ((sG K L A σ g : GL (Fin 2) S) : M) := rfl

theorem sT_tmul (l : L) (a : A) : sT K L A σ (l ⊗ₜ a) = σ l ⊗ₜ a := by
  simp [AutomorphicForm.sigmaTensor]

theorem sT_sT (hσ : ∀ l : L, σ (σ l) = l) (t : S) : sT K L A σ (sT K L A σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sT_tmul, sT_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sM_sM (hσ : ∀ l : L, σ (σ l) = l) (c : M) : sM K L A σ (sM K L A σ c) = c := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  exact sT_sT K L A σ hσ _

def sE (hσ : ∀ l : L, σ (σ l) = l) : (L ⊗[K] A) ≃+* (L ⊗[K] A) :=
  RingEquiv.ofRingHom (sT K L A σ) (sT K L A σ) (RingHom.ext (sT_sT K L A σ hσ))
    (RingHom.ext (sT_sT K L A σ hσ))

theorem sT_includeRight (a : A) :
    sT K L A σ ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a := by
  simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.includeRight_apply]

variable (y δ : GL (Fin 2) (L ⊗[K] A))

def T (c : M) : M := (y : M) * sM K L A σ c * ((δ⁻¹ : GL (Fin 2) S) : M)

theorem T_add (c c' : M) : T K L A σ y δ (c + c') = T K L A σ y δ c + T K L A σ y δ c' := by
  simp only [T, map_add, Matrix.mul_add, Matrix.add_mul]

theorem T_zero : T K L A σ y δ 0 = 0 := by simp [T]

theorem T_neg (c : M) : T K L A σ y δ (-c) = -T K L A σ y δ c := by
  simp only [T, map_neg, Matrix.mul_neg, Matrix.neg_mul]

theorem T_sub (c c' : M) : T K L A σ y δ (c - c') = T K L A σ y δ c - T K L A σ y δ c' := by
  rw [sub_eq_add_neg, T_add, T_neg, ← sub_eq_add_neg]

def TA : M →+ M where
  toFun := T K L A σ y δ
  map_zero' := T_zero K L A σ y δ
  map_add' := T_add K L A σ y δ

theorem TA_apply (c : M) : TA K L A σ y δ c = T K L A σ y δ c := rfl

theorem T_smul (a : S) (c : M) : T K L A σ y δ (a • c) = sT K L A σ a • T K L A σ y δ c := by
  simp only [T]
  have : sM K L A σ (a • c) = sT K L A σ a • sM K L A σ c := by
    ext i j; simp [Matrix.map_apply, smul_eq_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem T_T (hσ : ∀ l : L, σ (σ l) = l)
    (hN : y * sG K L A σ y = δ * sG K L A σ δ)
    (hz : ∀ m : M, ((δ * sG K L A σ δ : GL (Fin 2) S) : M) * m = m * ((δ * sG K L A σ δ : GL (Fin 2) S) : M))
    (c : M) : T K L A σ y δ (T K L A σ y δ c) = c := by
  set z : GL (Fin 2) S := δ * sG K L A σ δ with hzdef
  simp only [T]
  rw [map_mul, map_mul, sM_sM K L A σ hσ, sM_coe, sM_coe, map_inv]
  have h1 : ((y : M) * (((sG K L A σ y : GL (Fin 2) S) : M) * c *
      (((sG K L A σ δ)⁻¹ : GL (Fin 2) S) : M))) * ((δ⁻¹ : GL (Fin 2) S) : M) =
      ((y * sG K L A σ y : GL (Fin 2) S) : M) * c * (((δ * sG K L A σ δ)⁻¹ : GL (Fin 2) S) : M) := by
    simp only [Units.val_mul, mul_inv_rev, Matrix.mul_assoc]
  rw [h1, hN, ← hzdef, hz c, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

theorem isSigmaConjugate_of_fixed (x : GL (Fin 2) S) (hx : T K L A σ y δ (x : M) = (x : M)) :
    AutomorphicForm.IsSigmaConjugate K L A σ δ y := by
  refine ⟨x⁻¹, ?_⟩
  have hG : y * sG K L A σ x * δ⁻¹ = x := by
    apply Units.ext
    simpa only [T, sM_coe, Units.val_mul] using hx
  rw [map_inv, inv_inv]
  calc y = y * sG K L A σ x * δ⁻¹ * δ * (sG K L A σ x)⁻¹ := by group
    _ = x * δ * (sG K L A σ x)⁻¹ := by rw [hG]

theorem det_of_fixed (c : M) (hc : T K L A σ y δ c = c) :
    c.det = (y : M).det * sT K L A σ c.det * ((δ⁻¹ : GL (Fin 2) S) : M).det := by
  conv_lhs => rw [← hc]
  simp only [T, Matrix.det_mul]
  rw [RingHom.map_det, RingHom.mapMatrix_apply]

theorem exists_fixed_add_smul_fixed [Invertible (2 : L ⊗[K] A)]
    (hT : ∀ c : M, T K L A σ y δ (T K L A σ y δ c) = c)
    (lam : (L ⊗[K] A)ˣ) (hlam : sT K L A σ (lam : S) = -(lam : S)) (c : M) :
    ∃ a b : M, T K L A σ y δ a = a ∧ T K L A σ y δ b = b ∧ c = a + (lam : S) • b := by
  have h2 : sT K L A σ (⅟(2 : S)) = ⅟(2 : S) := by
    have h : sT K L A σ (⅟(2 : S)) * 2 = 1 := by
      have := congrArg (sT K L A σ) (invOf_mul_self (2 : S))
      rwa [map_mul, map_ofNat, map_one] at this
    calc sT K L A σ (⅟(2 : S)) = sT K L A σ (⅟(2 : S)) * 2 * ⅟(2 : S) := by
          rw [mul_assoc, mul_invOf_self, mul_one]
      _ = ⅟(2 : S) := by rw [h, one_mul]
  have hlinv : sT K L A σ ((lam⁻¹ : (L ⊗[K] A)ˣ) : S) = -((lam⁻¹ : (L ⊗[K] A)ˣ) : S) := by
    have e' : -(lam : S) * sT K L A σ ((lam⁻¹ : (L ⊗[K] A)ˣ) : S) = 1 := by
      rw [← hlam, ← map_mul, Units.mul_inv, map_one]
    rw [neg_mul] at e'
    have h3 : (lam : S) * sT K L A σ ((lam⁻¹ : (L ⊗[K] A)ˣ) : S) = -1 := neg_eq_iff_eq_neg.mp e'
    calc sT K L A σ ((lam⁻¹ : (L ⊗[K] A)ˣ) : S)
        = ((lam⁻¹ : (L ⊗[K] A)ˣ) : S) * ((lam : S) * sT K L A σ ((lam⁻¹ : (L ⊗[K] A)ˣ) : S)) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = -((lam⁻¹ : (L ⊗[K] A)ˣ) : S) := by rw [h3, mul_neg, mul_one]
  refine ⟨⅟(2 : S) • (c + T K L A σ y δ c),
    (⅟(2 : S) * ((lam⁻¹ : (L ⊗[K] A)ˣ) : S)) • (c - T K L A σ y δ c), ?_, ?_, ?_⟩
  · rw [T_smul, h2, T_add, hT, add_comm]
  · rw [T_smul, map_mul, h2, hlinv, T_sub, hT]
    rw [show ⅟(2 : S) * -((lam⁻¹ : (L ⊗[K] A)ˣ) : S) = -(⅟(2 : S) * ((lam⁻¹ : (L ⊗[K] A)ˣ) : S)) by ring]
    rw [neg_smul, ← smul_neg, neg_sub]
  · rw [smul_smul, ← mul_assoc, mul_comm (lam : S), mul_assoc, Units.mul_inv, mul_one,
      smul_add, smul_sub]
    have : (⅟(2 : S)) • c + (⅟(2 : S)) • c = c := by
      rw [← add_smul, invOf_two_add_invOf_two, one_smul]
    calc c = (⅟(2 : S)) • c + (⅟(2 : S)) • c := this.symm
      _ = _ := by abel

theorem span_fixed_eq_top [Invertible (2 : L ⊗[K] A)]
    (hT : ∀ c : M, T K L A σ y δ (T K L A σ y δ c) = c)
    (lam : (L ⊗[K] A)ˣ) (hlam : sT K L A σ (lam : S) = -(lam : S)) :
    Submodule.span S {c : M | T K L A σ y δ c = c} = ⊤ := by
  rw [eq_top_iff]
  intro c _
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_fixed_add_smul_fixed K L A σ y δ hT lam hlam c
  exact Submodule.add_mem _ (Submodule.subset_span ha)
    (Submodule.smul_mem _ _ (Submodule.subset_span hb))

def polar (c c' : M) : S := c 0 0 * c' 1 1 + c' 0 0 * c 1 1 - c 0 1 * c' 1 0 - c' 0 1 * c 1 0

theorem det_add (c c' : M) : (c + c').det = c.det + c'.det + polar K L A c c' := by
  simp only [Matrix.det_fin_two, Matrix.add_apply, polar]
  ring

def polarL : M →ₗ[S] M →ₗ[S] S :=
  LinearMap.mk₂ S (polar K L A)
    (fun c₁ c₂ c' => by simp only [polar, Matrix.add_apply]; ring)
    (fun a c c' => by simp only [polar, Matrix.smul_apply, smul_eq_mul]; ring)
    (fun c c₁ c₂ => by simp only [polar, Matrix.add_apply]; ring)
    (fun a c c' => by simp only [polar, Matrix.smul_apply, smul_eq_mul]; ring)

theorem polarL_apply (c c' : M) : polarL K L A c c' = polar K L A c c' := rfl

theorem polar_single : polar K L A (Matrix.single 0 0 (1 : S)) (Matrix.single 1 1 (1 : S)) = 1 := by
  simp [polar, Matrix.single]

theorem one_mem_span_det_fixed
    (hspan : Submodule.span S {c : M | T K L A σ y δ c = c} = ⊤) :
    (1 : S) ∈ Ideal.span (Matrix.det '' {c : M | T K L A σ y δ c = c}) := by
  set F : Set M := {c : M | T K L A σ y δ c = c} with hF
  set I : Ideal S := Ideal.span (Matrix.det '' F) with hI
  have hdetI : ∀ c ∈ F, c.det ∈ I := fun c hc => Ideal.subset_span ⟨c, hc, rfl⟩

  have hpol : ∀ c ∈ F, ∀ c' ∈ F, polar K L A c c' ∈ I := by
    intro c hc c' hc'
    have hcc' : c + c' ∈ F := by
      show T K L A σ y δ (c + c') = c + c'
      rw [T_add, show T K L A σ y δ c = c from hc, show T K L A σ y δ c' = c' from hc']
    have h := det_add K L A c c'
    have : polar K L A c c' = (c + c').det - c.det - c'.det := by rw [h]; ring
    rw [this]
    exact I.sub_mem (I.sub_mem (hdetI _ hcc') (hdetI _ hc)) (hdetI _ hc')

  let π : S →ₗ[S] S ⧸ I := I.mkQ
  let P : M →ₗ[S] M →ₗ[S] S ⧸ I := (polarL K L A).compr₂ π
  have hP : ∀ c c', P c c' = π (polar K L A c c') := fun _ _ => rfl
  have hleft : ∀ c' ∈ F, P.flip c' = 0 := by
    intro c' hc'
    refine LinearMap.ext_on hspan fun c hc => ?_
    rw [LinearMap.flip_apply, hP, LinearMap.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero I).2 (hpol c hc c' hc')
  have hall : P = 0 := by
    refine LinearMap.ext fun c => ?_
    refine LinearMap.ext_on hspan fun c' hc' => ?_
    have := congrArg (fun f : M →ₗ[S] S ⧸ I => f c) (hleft c' hc')
    simpa only [LinearMap.flip_apply, LinearMap.zero_apply] using this
  have h := congrArg (fun f : M →ₗ[S] M →ₗ[S] S ⧸ I => f (Matrix.single 0 0 1) (Matrix.single 1 1 1)) hall
  simp only [hP, polar_single, LinearMap.zero_apply] at h
  exact (Submodule.Quotient.mk_eq_zero I).1 h

theorem det_sum_smul {ι : Type} (s : Finset ι) (ε : ι → S) (c : ι → M)
    (hidem : ∀ i, ε i * ε i = ε i) (hortho : ∀ i j, i ≠ j → ε i * ε j = 0) :
    (∑ i ∈ s, ε i • c i).det = ∑ i ∈ s, ε i * (c i).det := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.det_fin_two]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, det_add, ih, Matrix.det_smul, Fintype.card_fin,
      pow_two, hidem]
    have h0 : polar K L A (ε a • c a) (∑ i ∈ s, ε i • c i) = 0 := by
      have hlin : polar K L A (ε a • c a) (∑ i ∈ s, ε i • c i) =
          ∑ i ∈ s, polar K L A (ε a • c a) (ε i • c i) := by
        rw [← polarL_apply, map_sum]
        rfl
      rw [hlin]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hia : a ≠ i := fun h => ha (h ▸ hi)
      have : polar K L A (ε a • c a) (ε i • c i) = ε a * ε i * polar K L A (c a) (c i) := by
        simp only [polar, Matrix.smul_apply, smul_eq_mul]; ring
      rw [this, hortho a i hia, zero_mul]
    rw [h0, add_zero]

omit σ y δ in

theorem center_mul_comm (z : GL (Fin 2) S) (hz : z ∈ Subgroup.center (GL (Fin 2) S)) (m : M) :
    (z : M) * m = m * (z : M) := by
  have hzc : ∀ g : GL (Fin 2) S, (z : M) * (g : M) = (g : M) * (z : M) := fun g => by
    rw [← Units.val_mul, ← Units.val_mul, (Subgroup.mem_center_iff.mp hz g)]
  have hoff : ∀ i j : Fin 2, i ≠ j → (z : M) * Matrix.single i j (1 : S) = Matrix.single i j 1 * (z : M) := by
    intro i j hij
    have hnil : Matrix.single i j (1 : S) * Matrix.single i j (1 : S) = 0 := by
      rw [Matrix.single_mul_single_of_ne]
      exact Ne.symm hij
    let u : GL (Fin 2) S :=
      ⟨1 + Matrix.single i j 1, 1 - Matrix.single i j 1,
        by rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
              Matrix.mul_one, hnil, sub_zero]; abel,
        by rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
              Matrix.mul_one, hnil, add_zero]; abel⟩
    have h := hzc u
    change (z : M) * (1 + Matrix.single i j 1) = (1 + Matrix.single i j 1) * (z : M) at h
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  have hdiag : ∀ i : Fin 2, (z : M) * Matrix.single i i (1 : S) = Matrix.single i i 1 * (z : M) := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j : Fin 2, j ≠ i := ⟨i + 1, by fin_omega⟩
    have hE : Matrix.single i i (1 : S) = Matrix.single i j 1 * Matrix.single j i 1 := by
      rw [Matrix.single_mul_single_same, mul_one]
    rw [hE, ← Matrix.mul_assoc, hoff i j (Ne.symm hj), Matrix.mul_assoc, hoff j i hj, Matrix.mul_assoc]
  have hsingle : ∀ i j : Fin 2, ∀ a : S, (z : M) * Matrix.single i j a = Matrix.single i j a * (z : M) := by
    intro i j a
    have : Matrix.single i j a = a • Matrix.single i j (1 : S) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
    by_cases hij : i = j
    · subst hij; rw [hdiag]
    · rw [hoff i j hij]
  rw [Matrix.matrix_eq_sum_single m]
  simp only [Matrix.mul_sum, Matrix.sum_mul, hsingle]

end Core

section Transport

theorem forall_free_of_ringEquiv {A R : Type} [CommRing A] [CommRing R] (e : A ≃+* R) (m n : ℕ)
    (hA : ∀ (P : Type) [AddCommGroup P] [Module A P],
      ((Fin n → P) ≃ₗ[A] (Fin (m * n) → A)) → Module.Free A P)
    (P : Type) [AddCommGroup P] [Module R P]
    (f : (Fin n → P) ≃ₗ[R] (Fin (m * n) → R)) : Module.Free R P := by
  letI instA : Module A P := Module.compHom P e.toRingHom
  have hsmul : ∀ (a : A) (p : P), (a • p : P) = (e a • p : P) := fun _ _ => rfl
  let g : (Fin n → P) ≃ₗ[A] (Fin (m * n) → A) :=
    { toFun := fun v i => e.symm (f v i)
      invFun := fun w => f.symm (fun i => e (w i))
      map_add' := by
        intro v w
        funext i
        show e.symm (f (v + w) i) = e.symm (f v i) + e.symm (f w i)
        rw [map_add, Pi.add_apply, map_add]
      map_smul' := by
        intro a v
        funext i
        show e.symm (f (a • v) i) = a * e.symm (f v i)
        have hv : (a • v : Fin n → P) = ((e a) • v : Fin n → P) := by
          funext j
          exact hsmul a (v j)
        rw [hv, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
      left_inv := by
        intro v
        show f.symm (fun i => e (e.symm (f v i))) = v
        have : (fun i => e (e.symm (f v i))) = f v := by
          funext i; exact e.apply_symm_apply _
        rw [this, LinearEquiv.symm_apply_apply]
      right_inv := by
        intro w
        funext i
        show e.symm (f (f.symm (fun j => e (w j))) i) = w i
        rw [LinearEquiv.apply_symm_apply, RingEquiv.symm_apply_apply] }
  haveI hfreeA : Module.Free A P := hA P g
  let b := Module.Free.chooseBasis A P
  let b' : Module.Basis _ R P := b.mapCoeffs e (fun c p => (hsmul c p).symm)
  exact Module.Free.of_basis b'

theorem exchange_of_ringEquiv {A R : Type} [CommRing A] [CommRing R] (e : A ≃+* R)
    (hA : ∀ (ι : Type) [Fintype ι] (t : ι → A), Ideal.span (Set.range t) = ⊤ →
      ∃ ε : ι → A, CompleteOrthogonalIdempotents ε ∧ IsUnit (∑ i, ε i * t i))
    (ι : Type) [Fintype ι] (t : ι → R) (c : ι → R) (h : ∑ i, c i * t i = 1) :
    ∃ ε : ι → R, CompleteOrthogonalIdempotents ε ∧ IsUnit (∑ i, ε i * t i) := by
  have h' : Ideal.span (Set.range (fun i => e.symm (t i))) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : ∑ i, e.symm (c i) * e.symm (t i) = 1 := by
      have := congrArg e.symm h
      simpa [map_sum, map_mul] using this
    rw [← h1]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  obtain ⟨ε, hε, hu⟩ := hA ι (fun i => e.symm (t i)) h'
  refine ⟨fun i => e (ε i), ?_, ?_⟩
  · have := hε.map e.toRingHom
    exact this
  · have := hu.map e
    simpa [map_sum, map_mul] using this

end Transport

section Adelic

open NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "S𝔸" => L ⊗[K] AdeleRing (𝓞 K) K
local notation "M𝔸" => Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)

theorem sigma_sigma (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (l : L) : σ (σ l) = l := by
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  have hpow : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have := congrArg (fun τ : L ≃ₐ[K] L => τ l) hpow
  simpa [pow_two, AlgEquiv.mul_apply] using this

theorem orderOf_sigma (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) : orderOf σ = 2 :=
  (orderOf_eq_card_of_forall_mem_zpowers hgen).trans ((IsGalois.card_aut_eq_finrank K L).trans h2)

theorem mem_range_of_fixed (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x : L) (hx : σ x = x) : x ∈ (algebraMap K L).range := by
  have hall : ∀ τ : L ≃ₐ[K] L, τ x = x := by
    intro τ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
    have hnat : ∀ j : ℕ, (σ ^ j) x = x := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
    cases k with
    | ofNat j => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact hnat j
    | negSucc j =>
        rw [zpow_negSucc]
        have h1 := hnat (j + 1)
        calc (σ ^ (j + 1))⁻¹ x = (σ ^ (j + 1))⁻¹ ((σ ^ (j + 1)) x) := by rw [h1]
          _ = x := by rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
  obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed x).2 hall
  exact ⟨k, hk⟩

theorem exists_anti (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) : ∃ μ : L, μ ≠ 0 ∧ σ μ = -μ := by
  have hσ1 : σ ≠ 1 := by
    intro h
    have := orderOf_sigma K L h2 σ hgen
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hex : ∃ l : L, σ l ≠ l := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (AlgEquiv.ext hcon)
  obtain ⟨l, hl⟩ := hex
  refine ⟨l - σ l, sub_ne_zero.2 (Ne.symm hl), ?_⟩
  rw [map_sub, sigma_sigma K L h2 σ, neg_sub]

theorem normString_of_finrank_eq_two (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    AutomorphicForm.normString K L 𝔸 σ δ = δ * AutomorphicForm.sigmaGL K L 𝔸 σ δ := by
  unfold AutomorphicForm.normString
  rw [h2]
  simp [List.range_succ]

@[reducible] def invertibleTwo : Invertible (2 : L ⊗[K] AdeleRing (𝓞 K) K) := by
  have h : IsUnit ((algebraMap K S𝔸) 2) := (isUnit_iff_ne_zero.2 (two_ne_zero (α := K))).map _
  rw [map_ofNat] at h
  exact h.invertible

abbrev Rfix (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) : Subring (L ⊗[K] AdeleRing (𝓞 K) K) :=
  RingHom.eqLocus (sE K L 𝔸 σ (sigma_sigma K L h2 σ)).toRingHom (RingHom.id _)

def adeleEquivRfix (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) : AdeleRing (𝓞 K) K ≃+* Rfix K L h2 σ := by
  let f : 𝔸 →+* S𝔸 := (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[K] S𝔸).toRingHom
  have hf : ∀ a, f a ∈ Rfix K L h2 σ := fun a => sT_includeRight K L 𝔸 σ a
  refine RingEquiv.ofBijective (f.codRestrict (Rfix K L h2 σ) hf) ⟨?_, ?_⟩
  · intro a b hab
    have hab' : f a = f b := congrArg Subtype.val hab
    exact Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective hab'
  · rintro ⟨t, ht⟩
    have ht' : sT K L 𝔸 σ t = t := ht
    obtain ⟨a, ha⟩ := (AutomorphicForm.sigmaTensor_apply_eq_self_iff K L 𝔸 σ
      (mem_range_of_fixed K L σ hgen) t).1 ht'
    exact ⟨a, Subtype.ext ha⟩

theorem exists_eq_inv_mul_sT (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (u : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (hu : (u : S𝔸) * sT K L 𝔸 σ u = 1) :
    ∃ w : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ, (u : S𝔸) = (w⁻¹ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) * sT K L 𝔸 σ w := by
  classical
  have hσ := sigma_sigma K L h2 σ
  set θ : S𝔸 ≃+* S𝔸 := sE K L 𝔸 σ hσ with hθdef
  have hord : orderOf σ = 2 := orderOf_sigma K L h2 σ hgen
  have hn : 0 < orderOf σ := by rw [hord]; exact two_pos
  letI : Algebra L S𝔸 := (Algebra.TensorProduct.includeLeftRingHom : L →+* S𝔸).toAlgebra
  have hθ : ∀ l : L, θ (algebraMap L S𝔸 l) = algebraMap L S𝔸 (σ l) := fun l =>
    sT_tmul K L 𝔸 σ l 1
  have hθn : θ ^ orderOf σ = 1 := by
    rw [hord, pow_two]
    apply RingEquiv.ext
    intro t
    exact sT_sT K L 𝔸 σ hσ t

  have hfree : ∀ (P : Type) [AddCommGroup P] [Module (RingHom.eqLocus θ.toRingHom (RingHom.id S𝔸)) P],
      ((Fin (orderOf σ) → P) ≃ₗ[RingHom.eqLocus θ.toRingHom (RingHom.id S𝔸)]
          (Fin (1 * orderOf σ) → RingHom.eqLocus θ.toRingHom (RingHom.id S𝔸))) →
        Module.Free (RingHom.eqLocus θ.toRingHom (RingHom.id S𝔸)) P := by
    intro P _ _ f
    exact forall_free_of_ringEquiv (adeleEquivRfix K L h2 σ hgen) 1 (orderOf σ)
      (fun Q _ _ g => NumberField.AdeleRing.free_of_pi_linearEquiv_pi K 1 (orderOf σ) hn Q g) P f

  let x : GL (Fin 1) S𝔸 := Units.map (Matrix.scalar (Fin 1) : S𝔸 →+* Matrix (Fin 1) (Fin 1) S𝔸).toMonoidHom u
  have hxval : ∀ v : S𝔸ˣ, ((Units.map (Matrix.scalar (Fin 1) : S𝔸 →+* Matrix (Fin 1) (Fin 1) S𝔸).toMonoidHom v :
      GL (Fin 1) S𝔸) : Matrix (Fin 1) (Fin 1) S𝔸) = Matrix.scalar (Fin 1) (v : S𝔸) := fun _ => rfl
  have hmapx : Matrix.GeneralLinearGroup.map (θ : S𝔸 →+* S𝔸) x =
      Units.map (Matrix.scalar (Fin 1) : S𝔸 →+* Matrix (Fin 1) (Fin 1) S𝔸).toMonoidHom
        (Units.map (θ : S𝔸 →+* S𝔸).toMonoidHom u) := by
    apply Units.ext
    ext i j
    obtain rfl : i = j := Subsingleton.elim i j
    change θ ((x : Matrix (Fin 1) (Fin 1) S𝔸) i i) = Matrix.scalar (Fin 1) (θ (u : S𝔸)) i i
    rw [hxval]
    simp
  have hx : ((List.range (orderOf σ)).map
      fun k => Matrix.GeneralLinearGroup.map ((θ ^ k : S𝔸 ≃+* S𝔸) : S𝔸 →+* S𝔸) x).prod = 1 := by
    rw [hord]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, pow_zero, pow_one, List.map_append, List.prod_append]
    have h0 : Matrix.GeneralLinearGroup.map ((1 : S𝔸 ≃+* S𝔸) : S𝔸 →+* S𝔸) x = x := by
      apply Units.ext; ext i j; rfl
    rw [h0, hmapx, ← map_mul]
    apply Units.ext
    ext i j
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mul,
      Units.val_one]
    rw [show ((θ : S𝔸 →+* S𝔸) : S𝔸 → S𝔸) (u : S𝔸) = sT K L 𝔸 σ u from rfl, hu, map_one]
  obtain ⟨Y, hY⟩ :=
    RingEquiv.exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free
      K L σ hn S𝔸 θ hθ hθn 1 hfree x hx
  refine ⟨Matrix.GeneralLinearGroup.det Y, ?_⟩
  have hdet := congrArg (fun g : GL (Fin 1) S𝔸 => Matrix.det (g : Matrix (Fin 1) (Fin 1) S𝔸)) hY
  simp only [Units.val_mul, Matrix.det_mul] at hdet
  have hdx : Matrix.det (x : Matrix (Fin 1) (Fin 1) S𝔸) = u := by
    rw [hxval]; simp
  have h1 : Matrix.det ((Y⁻¹ : GL (Fin 1) S𝔸) : Matrix (Fin 1) (Fin 1) S𝔸) =
      (((Matrix.GeneralLinearGroup.det Y)⁻¹ : S𝔸ˣ) : S𝔸) := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv]
  have h2 : Matrix.det ((Matrix.GeneralLinearGroup.map (θ : S𝔸 →+* S𝔸) Y : GL (Fin 1) S𝔸) :
      Matrix (Fin 1) (Fin 1) S𝔸) = sT K L 𝔸 σ ((Matrix.GeneralLinearGroup.det Y : S𝔸ˣ) : S𝔸) := by
    change Matrix.det ((θ : S𝔸 →+* S𝔸).mapMatrix (Y : Matrix (Fin 1) (Fin 1) S𝔸)) = _
    rw [← RingHom.map_det]
    rfl
  rw [hdx, h1, h2] at hdet
  exact hdet

theorem sT_invOf_two (σ : L ≃ₐ[K] L) [Invertible (2 : L ⊗[K] AdeleRing (𝓞 K) K)] :
    sT K L 𝔸 σ (⅟(2 : S𝔸)) = ⅟(2 : S𝔸) := by
  have h : sT K L 𝔸 σ (⅟(2 : S𝔸)) * 2 = 1 := by
    have := congrArg (sT K L 𝔸 σ) (invOf_mul_self (2 : S𝔸))
    rwa [map_mul, map_ofNat, map_one] at this
  calc sT K L 𝔸 σ (⅟(2 : S𝔸)) = sT K L 𝔸 σ (⅟(2 : S𝔸)) * 2 * ⅟(2 : S𝔸) := by
        rw [mul_assoc, mul_invOf_self, mul_one]
    _ = ⅟(2 : S𝔸) := by rw [h, one_mul]

theorem main (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hz : δ * sG K L 𝔸 σ δ ∈ Subgroup.center (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hN : y * sG K L 𝔸 σ y = δ * sG K L 𝔸 σ δ) :
    AutomorphicForm.IsSigmaConjugate K L 𝔸 σ δ y := by
  classical
  have hσ := sigma_sigma K L h2 σ
  letI := invertibleTwo K L

  have hzc : ∀ m : M𝔸, ((δ * sG K L 𝔸 σ δ : GL (Fin 2) S𝔸) : M𝔸) * m =
      m * ((δ * sG K L 𝔸 σ δ : GL (Fin 2) S𝔸) : M𝔸) :=
    center_mul_comm K L 𝔸 _ hz
  have hT : ∀ c : M𝔸, T K L 𝔸 σ y δ (T K L 𝔸 σ y δ c) = c := T_T K L 𝔸 σ y δ hσ hN hzc

  obtain ⟨μ, hμ0, hμ⟩ := exists_anti K L h2 σ hgen
  let lam : S𝔸ˣ :=
    Units.map (Algebra.TensorProduct.includeLeftRingHom : L →+* S𝔸).toMonoidHom (Units.mk0 μ hμ0)
  have hlam : sT K L 𝔸 σ (lam : S𝔸) = -(lam : S𝔸) := by
    change sT K L 𝔸 σ (μ ⊗ₜ 1) = -(μ ⊗ₜ (1 : 𝔸))
    rw [sT_tmul, hμ, TensorProduct.neg_tmul]
  have hspan := span_fixed_eq_top K L 𝔸 σ y δ hT lam hlam

  have h1 := one_mem_span_det_fixed K L 𝔸 σ y δ hspan
  obtain ⟨t, htF, μc, hsum⟩ := (Submodule.mem_span_image_iff_exists_fun S𝔸).1 h1
  simp only [smul_eq_mul] at hsum
  have hcF : ∀ i : t, T K L 𝔸 σ y δ (i : M𝔸) = (i : M𝔸) := fun i => htF i.2

  let sU : S𝔸ˣ →* S𝔸ˣ := Units.map (sT K L 𝔸 σ).toMonoidHom
  have hdetG : ∀ g : GL (Fin 2) S𝔸,
      Matrix.GeneralLinearGroup.det (sG K L 𝔸 σ g) = sU (Matrix.GeneralLinearGroup.det g) := by
    intro g
    apply Units.ext
    change Matrix.det ((sT K L 𝔸 σ).mapMatrix (g : M𝔸)) = sT K L 𝔸 σ (Matrix.det (g : M𝔸))
    rw [← RingHom.map_det]
  set dy : S𝔸ˣ := Matrix.GeneralLinearGroup.det y with hdy
  set dδ : S𝔸ˣ := Matrix.GeneralLinearGroup.det δ with hdδ
  set u : S𝔸ˣ := dy * dδ⁻¹ with hudef
  have hNdet : dy * sU dy = dδ * sU dδ := by
    have h := congrArg Matrix.GeneralLinearGroup.det hN
    rwa [map_mul, map_mul, hdetG, hdetG] at h
  have hNval : (dy : S𝔸) * sT K L 𝔸 σ (dy : S𝔸) = (dδ : S𝔸) * sT K L 𝔸 σ (dδ : S𝔸) := by
    have := congrArg (fun v : S𝔸ˣ => (v : S𝔸)) hNdet
    simpa [sU] using this
  have hp : ((dδ⁻¹ : S𝔸ˣ) : S𝔸) * (dδ : S𝔸) = 1 := Units.inv_mul _
  have hq : sT K L 𝔸 σ ((dδ⁻¹ : S𝔸ˣ) : S𝔸) * sT K L 𝔸 σ (dδ : S𝔸) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hu : (u : S𝔸) * sT K L 𝔸 σ u = 1 := by
    rw [hudef, Units.val_mul, map_mul]
    linear_combination (((dδ⁻¹ : S𝔸ˣ) : S𝔸) * sT K L 𝔸 σ ((dδ⁻¹ : S𝔸ˣ) : S𝔸)) * hNval +
      (sT K L 𝔸 σ ((dδ⁻¹ : S𝔸ˣ) : S𝔸) * sT K L 𝔸 σ (dδ : S𝔸)) * hp + hq
  obtain ⟨w, hw⟩ := exists_eq_inv_mul_sT K L h2 σ hgen u hu

  have hfixdet : ∀ c : M𝔸, T K L 𝔸 σ y δ c = c → Matrix.det c = (u : S𝔸) * sT K L 𝔸 σ (Matrix.det c) := by
    intro c hc
    have h := det_of_fixed K L 𝔸 σ y δ c hc
    have hδinv : Matrix.det ((δ⁻¹ : GL (Fin 2) S𝔸) : M𝔸) = ((dδ⁻¹ : S𝔸ˣ) : S𝔸) := by
      rw [hdδ, ← map_inv]; rfl
    rw [hδinv] at h
    have huval : (u : S𝔸) = Matrix.det (y : M𝔸) * ((dδ⁻¹ : S𝔸ˣ) : S𝔸) := by
      rw [hudef, Units.val_mul, hdy]
      rfl
    calc Matrix.det c = Matrix.det (y : M𝔸) * sT K L 𝔸 σ (Matrix.det c) * ((dδ⁻¹ : S𝔸ˣ) : S𝔸) := h
      _ = Matrix.det (y : M𝔸) * ((dδ⁻¹ : S𝔸ˣ) : S𝔸) * sT K L 𝔸 σ (Matrix.det c) := by ring
      _ = (u : S𝔸) * sT K L 𝔸 σ (Matrix.det c) := by rw [huval]
  have hfixw : ∀ c : M𝔸, T K L 𝔸 σ y δ c = c →
      sT K L 𝔸 σ ((w : S𝔸) * Matrix.det c) = (w : S𝔸) * Matrix.det c := by
    intro c hc
    have hd := hfixdet c hc
    rw [map_mul]
    conv_rhs => rw [hd, hw]
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]

  let R := Rfix K L h2 σ
  let tR : t → R := fun i => ⟨(w : S𝔸) * Matrix.det (i : M𝔸), hfixw _ (hcF i)⟩
  obtain ⟨a, ha⟩ : ∃ a : t → S𝔸, ∀ i, a i = μc i * ((w⁻¹ : S𝔸ˣ) : S𝔸) := ⟨_, fun _ => rfl⟩
  have hfixc : ∀ i, sT K L 𝔸 σ (⅟(2 : S𝔸) * (a i + sT K L 𝔸 σ (a i))) =
      ⅟(2 : S𝔸) * (a i + sT K L 𝔸 σ (a i)) := by
    intro i
    rw [map_mul, sT_invOf_two, map_add, sT_sT K L 𝔸 σ hσ, add_comm]
  let cR : t → R := fun i => ⟨⅟(2 : S𝔸) * (a i + sT K L 𝔸 σ (a i)), hfixc i⟩
  have hai : ∀ i, a i * ((w : S𝔸) * Matrix.det (i : M𝔸)) = μc i * Matrix.det (i : M𝔸) := by
    intro i
    rw [ha, mul_assoc, ← mul_assoc ((w⁻¹ : S𝔸ˣ) : S𝔸), Units.inv_mul, one_mul]
  have hSsum : ∑ i, (⅟(2 : S𝔸) * (a i + sT K L 𝔸 σ (a i))) * ((w : S𝔸) * Matrix.det (i : M𝔸)) = 1 := by
    have hterm : ∀ i, (⅟(2 : S𝔸) * (a i + sT K L 𝔸 σ (a i))) * ((w : S𝔸) * Matrix.det (i : M𝔸)) =
        ⅟(2 : S𝔸) * (μc i * Matrix.det (i : M𝔸) + sT K L 𝔸 σ (μc i * Matrix.det (i : M𝔸))) := by
      intro i
      have e1 : a i * ((w : S𝔸) * Matrix.det (i : M𝔸)) = μc i * Matrix.det (i : M𝔸) := hai i
      have e2 : sT K L 𝔸 σ (a i) * ((w : S𝔸) * Matrix.det (i : M𝔸)) =
          sT K L 𝔸 σ (μc i * Matrix.det (i : M𝔸)) := by
        rw [← e1, map_mul (sT K L 𝔸 σ) (a i), hfixw _ (hcF i)]
      rw [mul_assoc, add_mul, e1, e2]
    simp_rw [hterm]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← map_sum, hsum, map_one]
    rw [show (1 : S𝔸) + 1 = 2 by norm_num, invOf_mul_self]
  have hRsum : ∑ i, cR i * tR i = 1 := by
    apply Subtype.ext
    have hc : ((∑ i, cR i * tR i : R) : S𝔸) = ∑ i, ((cR i : S𝔸) * (tR i : S𝔸)) := by
      rw [show ((∑ i, cR i * tR i : R) : S𝔸) = R.subtype (∑ i, cR i * tR i) from rfl, map_sum]
      rfl
    rw [hc]
    exact hSsum

  obtain ⟨ε, hε, hunit⟩ := exchange_of_ringEquiv (adeleEquivRfix K L h2 σ hgen)
    (fun ι _ t' h' =>
      NumberField.AdeleRing.exists_completeOrthogonalIdempotents_and_isUnit_sum_mul_of_span_range_eq_top
        K ι t' h') (↥t) tR cR hRsum

  let c : M𝔸 := ∑ i, ((ε i : R) : S𝔸) • (i : M𝔸)
  have hcfix : T K L 𝔸 σ y δ c = c := by
    change TA K L 𝔸 σ y δ (∑ i, ((ε i : R) : S𝔸) • (i : M𝔸)) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TA_apply, T_smul, hcF i]
    congr 1
    exact (ε i).2
  have hdetc : Matrix.det c = ∑ i, ((ε i : R) : S𝔸) * Matrix.det (i : M𝔸) := by
    apply det_sum_smul K L 𝔸
    · intro i
      have := (hε.idem i).eq
      exact congrArg Subtype.val this
    · intro i j hij
      have := hε.ortho hij
      exact congrArg Subtype.val this
  have hwdetc : (w : S𝔸) * Matrix.det c = ((∑ i, ε i * tR i : R) : S𝔸) := by
    rw [hdetc, Finset.mul_sum,
      show ((∑ i, ε i * tR i : R) : S𝔸) = R.subtype (∑ i, ε i * tR i) from rfl, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (w : S𝔸) * (((ε i : R) : S𝔸) * Matrix.det (i : M𝔸)) =
      ((ε i : R) : S𝔸) * ((w : S𝔸) * Matrix.det (i : M𝔸))
    ring
  have hunitS : IsUnit ((w : S𝔸) * Matrix.det c) := by
    rw [hwdetc]
    exact hunit.map R.subtype
  have hdetunit : IsUnit (Matrix.det c) := isUnit_of_mul_isUnit_right hunitS
  obtain ⟨x, hx⟩ := (Matrix.isUnit_iff_isUnit_det c).2 hdetunit
  exact isSigmaConjugate_of_fixed K L 𝔸 σ y δ x (by rw [hx]; exact hcfix)

private theorem _root_.P2mH90Inner.card (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ ∈
      Subgroup.center (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ y =
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ) :
    AutomorphicForm.IsSigmaConjugate K L (AdeleRing (𝓞 K) K) σ δ y := by
  rw [normString_of_finrank_eq_two K L h2] at hδ
  rw [normString_of_finrank_eq_two K L h2, normString_of_finrank_eq_two K L h2] at hN
  exact main K L h2 σ hgen δ y hδ hN

p2m_export "P2mH90Inner" "card"
end Adelic

end P2mH90Inner

end

open NumberField in
open scoped TensorProduct in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ ∈
      Subgroup.center (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ y =
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ) :
    AutomorphicForm.IsSigmaConjugate K L (AdeleRing (𝓞 K) K) σ δ y :=
  P2mH90Inner.card K L h2 σ hgen δ y hδ hN

end S_AutomorphicForm_isSigmaConjugate_adeleRing_of_normString_eq_of_normString_mem_center_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_isSigmaConjugate_adeleRing_of_normString_eq_of_normString_mem_center_of_finrank_eq_two (solution)
