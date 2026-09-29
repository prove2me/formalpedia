-- Prove2me | solution 1 for AutomorphicForm.exists_linearEquiv_twistedCommutant_tensor_mulVec_tmul_of_mul_map_mem_center_of_forall_ne_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f22ca57b-4ab7-569f-a7d6-9e978b1435f3

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_linearEquiv_twistedCommutant_tensor_mulVec_tmul_of_mul_map_mem_center_of_forall_ne_scalar

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

namespace ColGeneric28

open TensorProduct

section Generic

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (δ : Matrix (Fin 2) (Fin 2) L)
  (A : Type) [CommRing A] [Algebra K A]

abbrev iL : L →+* L ⊗[K] A := Algebra.TensorProduct.includeLeftRingHom

theorem iL_apply (l : L) : iL K L A l = l ⊗ₜ[K] (1 : A) := rfl

theorem smul_tmul_right (a s : A) (l : L) : a • (l ⊗ₜ[K] s) = l ⊗ₜ[K] (a * s) := by
  rw [TensorProduct.RightActions.smul_def]
  simp [TensorProduct.smul_tmul', smul_eq_mul]

theorem sigmaTensor_tmul (l : L) (a : A) :
    AutomorphicForm.sigmaTensor K L A σ (l ⊗ₜ[K] a) = σ l ⊗ₜ[K] a := by
  show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)) (l ⊗ₜ[K] a) = σ l ⊗ₜ[K] a
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem sigmaTensor_algebraMap (a : A) :
    AutomorphicForm.sigmaTensor K L A σ (algebraMap A (L ⊗[K] A) a) = algebraMap A (L ⊗[K] A) a := by
  rw [TensorProduct.RightActions.algebraMap_eval, sigmaTensor_tmul, map_one]

theorem sigmaTensor_smul (a : A) (y : L ⊗[K] A) :
    AutomorphicForm.sigmaTensor K L A σ (a • y) = a • AutomorphicForm.sigmaTensor K L A σ y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, sigmaTensor_algebraMap]

theorem map_sigmaTensor_smul (a : A) (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    (a • x).map (AutomorphicForm.sigmaTensor K L A σ) =
      a • x.map (AutomorphicForm.sigmaTensor K L A σ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, sigmaTensor_smul]

noncomputable def phi : Matrix (Fin 2) (Fin 2) L →ₗ[K] Matrix (Fin 2) (Fin 2) L where
  toFun X := X * δ - δ * X.map σ
  map_add' X Y := by
    rw [Matrix.add_mul, Matrix.map_add _ (map_add σ), Matrix.mul_add]
    abel
  map_smul' k X := by
    have hmap : (k • X).map σ = k • X.map σ := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, map_smul]
    rw [RingHom.id_apply, Matrix.smul_mul, hmap, Matrix.mul_smul, smul_sub]

theorem phi_apply (X : Matrix (Fin 2) (Fin 2) L) : phi K L σ δ X = X * δ - δ * X.map σ := rfl

theorem mem_ker_phi (X : Matrix (Fin 2) (Fin 2) L) :
    X ∈ LinearMap.ker (phi K L σ δ) ↔ X * δ = δ * X.map σ := by
  rw [LinearMap.mem_ker, phi_apply, sub_eq_zero]

noncomputable def psi : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) →ₗ[A] Matrix (Fin 2) (Fin 2) (L ⊗[K] A) where
  toFun x := x * δ.map (iL K L A) - δ.map (iL K L A) * x.map (AutomorphicForm.sigmaTensor K L A σ)
  map_add' x y := by
    rw [Matrix.add_mul, Matrix.map_add _ (map_add (AutomorphicForm.sigmaTensor K L A σ)), Matrix.mul_add]
    abel
  map_smul' a x := by
    rw [RingHom.id_apply, Matrix.smul_mul, map_sigmaTensor_smul, Matrix.mul_smul, smul_sub]

theorem psi_apply (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    psi K L σ δ A x =
      x * δ.map (iL K L A) - δ.map (iL K L A) * x.map (AutomorphicForm.sigmaTensor K L A σ) := rfl

def colLin (S R : Type) [CommSemiring S] [CommSemiring R] [Algebra S R] (b : Fin 2 → R) :
    Matrix (Fin 2) (Fin 2) R →ₗ[S] (Fin 2 → R) where
  toFun X := X.mulVec b
  map_add' X Y := Matrix.add_mulVec X Y b
  map_smul' s X := Matrix.smul_mulVec s X b

theorem colLin_apply (S R : Type) [CommSemiring S] [CommSemiring R] [Algebra S R] (b : Fin 2 → R)
    (X : Matrix (Fin 2) (Fin 2) R) : colLin S R b X = X.mulVec b := rfl

noncomputable def Theta : A ⊗[K] Matrix (Fin 2) (Fin 2) L ≃ₗ[A] Matrix (Fin 2) (Fin 2) (L ⊗[K] A) :=
  (LinearEquiv.baseChange K A _ _ (Matrix.ofLinearEquiv K).symm) ≪≫ₗ
  (TensorProduct.piRight K A A (fun _ : Fin 2 => Fin 2 → L)) ≪≫ₗ
  (LinearEquiv.piCongrRight fun _ : Fin 2 => TensorProduct.piRight K A A (fun _ : Fin 2 => L)) ≪≫ₗ
  (LinearEquiv.piCongrRight fun _ : Fin 2 => LinearEquiv.piCongrRight fun _ : Fin 2 =>
      TensorProduct.RightActions.Module.TensorProduct.comm K A L) ≪≫ₗ
  Matrix.ofLinearEquiv A

theorem Theta_tmul (a : A) (X : Matrix (Fin 2) (Fin 2) L) :
    Theta K L A (a ⊗ₜ[K] X) = X.map (fun l => l ⊗ₜ[K] a) := by
  ext i j
  simp [Theta]

theorem map_tmul_eq_smul (a : A) (X : Matrix (Fin 2) (Fin 2) L) :
    X.map (fun l => l ⊗ₜ[K] a) = a • X.map (iL K L A) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, iL_apply, smul_tmul_right, mul_one]

theorem Theta_tmul' (a : A) (X : Matrix (Fin 2) (Fin 2) L) :
    Theta K L A (a ⊗ₜ[K] X) = a • X.map (iL K L A) := by
  rw [Theta_tmul, map_tmul_eq_smul]

theorem map_map_sigma (X : Matrix (Fin 2) (Fin 2) L) :
    (X.map σ).map (iL K L A) = (X.map (iL K L A)).map (AutomorphicForm.sigmaTensor K L A σ) := by
  ext i j
  simp only [Matrix.map_apply, iL_apply, sigmaTensor_tmul]

theorem map_phi (X : Matrix (Fin 2) (Fin 2) L) :
    (phi K L σ δ X).map (iL K L A) = psi K L σ δ A (X.map (iL K L A)) := by
  rw [phi_apply, psi_apply, Matrix.map_sub _ (map_sub (iL K L A)), Matrix.map_mul, Matrix.map_mul,
    map_map_sigma]

theorem Theta_baseChange_phi (t : A ⊗[K] Matrix (Fin 2) (Fin 2) L) :
    Theta K L A ((phi K L σ δ).baseChange A t) = psi K L σ δ A (Theta K L A t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a X =>
      rw [LinearMap.baseChange_tmul, Theta_tmul', Theta_tmul', LinearMap.map_smul, map_phi]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem exists_of_baseChange_eq_zero {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (t : A ⊗[K] V)
    (ht : f.baseChange A t = 0) :
    ∃ s : A ⊗[K] (LinearMap.ker f), (LinearMap.ker f).subtype.baseChange A s = t := by
  have h1 : t ∈ LinearMap.ker (f.lTensor A) := by
    rw [LinearMap.mem_ker, ← LinearMap.baseChange_eq_ltensor]
    exact ht
  rw [(Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map f)).linearMap_ker_eq] at h1
  obtain ⟨s, hs⟩ := h1
  refine ⟨s, ?_⟩
  rw [LinearMap.baseChange_eq_ltensor]
  exact hs

theorem baseChange_subtype_injective {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    Function.Injective ((LinearMap.ker f).subtype.baseChange A) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)

theorem baseChange_comp_subtype_eq_zero {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (s : A ⊗[K] (LinearMap.ker f)) :
    f.baseChange A ((LinearMap.ker f).subtype.baseChange A s) = 0 := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.comp_ker_subtype,
    LinearMap.baseChange_zero, LinearMap.zero_apply]

theorem mulVec_map_tmul (b : Fin 2 → L) (a : A) (X : Matrix (Fin 2) (Fin 2) L) :
    (X.map (fun l => l ⊗ₜ[K] a)).mulVec (fun k => b k ⊗ₜ[K] (1 : A)) =
      fun i => (X.mulVec b i) ⊗ₜ[K] a := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, TensorProduct.sum_tmul]

noncomputable def jmap :
    A ⊗[K] LinearMap.ker (phi K L σ δ) →ₗ[A] Matrix (Fin 2) (Fin 2) (L ⊗[K] A) :=
  (Theta K L A).toLinearMap ∘ₗ (LinearMap.ker (phi K L σ δ)).subtype.baseChange A

theorem jmap_apply (s : A ⊗[K] LinearMap.ker (phi K L σ δ)) :
    jmap K L σ δ A s = Theta K L A ((LinearMap.ker (phi K L σ δ)).subtype.baseChange A s) := rfl

theorem jmap_mem (s : A ⊗[K] LinearMap.ker (phi K L σ δ)) :
    jmap K L σ δ A s ∈ LinearMap.ker (psi K L σ δ A) := by
  rw [LinearMap.mem_ker, jmap_apply, ← Theta_baseChange_phi, baseChange_comp_subtype_eq_zero, map_zero]

noncomputable def jr :
    A ⊗[K] LinearMap.ker (phi K L σ δ) →ₗ[A] LinearMap.ker (psi K L σ δ A) :=
  (jmap K L σ δ A).codRestrict (LinearMap.ker (psi K L σ δ A)) (jmap_mem K L σ δ A)

theorem jr_apply_coe (s : A ⊗[K] LinearMap.ker (phi K L σ δ)) :
    (jr K L σ δ A s : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      Theta K L A ((LinearMap.ker (phi K L σ δ)).subtype.baseChange A s) := rfl

theorem jr_bijective : Function.Bijective (jr K L σ δ A) := by
  constructor
  · intro s t hst
    have h : (jr K L σ δ A s : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = jr K L σ δ A t := by rw [hst]
    rw [jr_apply_coe, jr_apply_coe] at h
    exact baseChange_subtype_injective K A (phi K L σ δ) ((Theta K L A).injective h)
  · intro x
    have hx : (phi K L σ δ).baseChange A ((Theta K L A).symm (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) = 0 := by
      apply (Theta K L A).injective
      rw [Theta_baseChange_phi, LinearEquiv.apply_symm_apply, map_zero]
      exact x.2
    obtain ⟨s, hs⟩ := exists_of_baseChange_eq_zero K A (phi K L σ δ) _ hx
    refine ⟨s, Subtype.ext ?_⟩
    rw [jr_apply_coe, hs, LinearEquiv.apply_symm_apply]

noncomputable def J : A ⊗[K] LinearMap.ker (phi K L σ δ) ≃ₗ[A] LinearMap.ker (psi K L σ δ A) :=
  LinearEquiv.ofBijective (jr K L σ δ A) (jr_bijective K L σ δ A)

theorem J_apply_coe (s : A ⊗[K] LinearMap.ker (phi K L σ δ)) :
    (J K L σ δ A s : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      Theta K L A ((LinearMap.ker (phi K L σ δ)).subtype.baseChange A s) := rfl

noncomputable def col0 (b : Fin 2 → L) : LinearMap.ker (phi K L σ δ) →ₗ[K] (Fin 2 → L) :=
  colLin K L b ∘ₗ (LinearMap.ker (phi K L σ δ)).subtype

theorem col0_apply (b : Fin 2 → L) (x : LinearMap.ker (phi K L σ δ)) :
    col0 K L σ δ b x = (x : Matrix (Fin 2) (Fin 2) L).mulVec b := rfl

theorem col0_bijective (b : Fin 2 → L)
    (hEU : ∀ w : Fin 2 → L, ∃! x : Matrix (Fin 2) (Fin 2) L, x * δ = δ * x.map σ ∧ x.mulVec b = w) :
    Function.Bijective (col0 K L σ δ b) := by
  constructor
  · intro x y hxy
    rw [col0_apply, col0_apply] at hxy
    apply Subtype.ext
    exact (hEU _).unique ⟨(mem_ker_phi K L σ δ _).mp x.2, rfl⟩ ⟨(mem_ker_phi K L σ δ _).mp y.2, hxy.symm⟩
  · intro w
    obtain ⟨x, ⟨hx1, hx2⟩, -⟩ := hEU w
    exact ⟨⟨x, (mem_ker_phi K L σ δ x).mpr hx1⟩, hx2⟩

theorem main (b : Fin 2 → L)
    (hEU : ∀ w : Fin 2 → L, ∃! x : Matrix (Fin 2) (Fin 2) L, x * δ = δ * x.map σ ∧ x.mulVec b = w) :
    ∃ (DA : Submodule A (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)))
      (e : DA ≃ₗ[A] (Fin 2 → L ⊗[K] A)),
      (DA : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) = {x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) |
        x * δ.map (iL K L A) = δ.map (iL K L A) * x.map (AutomorphicForm.sigmaTensor K L A σ)} ∧
      ∀ x : DA, e x = (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).mulVec (fun i => b i ⊗ₜ[K] 1) := by
  refine ⟨LinearMap.ker (psi K L σ δ A),
    (J K L σ δ A).symm ≪≫ₗ
      (LinearEquiv.baseChange K A _ _
        (LinearEquiv.ofBijective (col0 K L σ δ b) (col0_bijective K L σ δ b hEU))) ≪≫ₗ
      (TensorProduct.piRight K A A (fun _ : Fin 2 => L)) ≪≫ₗ
      (LinearEquiv.piCongrRight fun _ : Fin 2 =>
        TensorProduct.RightActions.Module.TensorProduct.comm K A L),
    ?_, ?_⟩
  · ext x
    simp only [SetLike.mem_coe, LinearMap.mem_ker, psi_apply, Set.mem_setOf_eq, sub_eq_zero]
  · intro x
    obtain ⟨s, rfl⟩ := (J K L σ δ A).surjective x
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [J_apply_coe]
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a d =>
        rw [LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply, col0_apply,
          LinearMap.baseChange_tmul, Submodule.subtype_apply, Theta_tmul, mulVec_map_tmul]
        ext i
        simp
    | add x y hx hy =>
        simp only [map_add, Matrix.add_mulVec, hx, hy]

end Generic

end ColGeneric28

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    (hδ₀ : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ ∈ Subgroup.center (GL (Fin 2) L))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (b : Fin 2 → L) (hb : b ≠ 0)
    (A : Type) [CommRing A] [Algebra K A] :
    ∃ (DA : Submodule A (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)))
      (e : DA ≃ₗ[A] (Fin 2 → L ⊗[K] A)),
      (DA : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) = {x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) |
        x * ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ :
                GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
          ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ :
                GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
            x.map (AutomorphicForm.sigmaTensor K L A σ)} ∧
      ∀ x : DA, e x = (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).mulVec (fun i => b i ⊗ₜ[K] 1) := by
  obtain ⟨z, hz⟩ : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hδ₀
    obtain ⟨z, hz⟩ := hδ₀
    exact ⟨z, hz.symm⟩
  have hEU :=
    AutomorphicForm.existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
      K L h2 σ hgen δ₀ ⟨z, hz⟩ hns b hb
  have hδA : ((Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (δ₀ : Matrix (Fin 2) (Fin 2) L).map (ColGeneric28.iL K L A) := by
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  rw [hδA]
  exact ColGeneric28.main K L σ (δ₀ : Matrix (Fin 2) (Fin 2) L) A b hEU

end S_AutomorphicForm_exists_linearEquiv_twistedCommutant_tensor_mulVec_tmul_of_mul_map_mem_center_of_forall_ne_scalar
end P2MW
export P2MW.S_AutomorphicForm_exists_linearEquiv_twistedCommutant_tensor_mulVec_tmul_of_mul_map_mem_center_of_forall_ne_scalar (solution)
