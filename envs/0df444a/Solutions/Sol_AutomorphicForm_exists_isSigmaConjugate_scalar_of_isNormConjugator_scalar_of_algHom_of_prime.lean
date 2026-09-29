-- Prove2me | solution 1 for AutomorphicForm.exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/cae7f80e-bbb3-5e1e-ac10-573cb398884d

import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct TensorProduct.RightActions

namespace P2mSplitKind

open AutomorphicForm AutomorphicForm.SplitPlace

section Shift

theorem val_finRotate : ∀ {n : ℕ} (i : Fin n), ((finRotate n i : Fin n) : ℕ) = ((i : ℕ) + 1) % n
  | 0, i => i.elim0
  | n + 1, i => by
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 i.2) with h | h
      · have hi : i = ⟨(i : ℕ), i.2⟩ := rfl
        rw [hi, finRotate_of_lt h]
        simp [Nat.mod_eq_of_lt (Nat.succ_lt_succ h)]
      · have hi : i = Fin.last n := Fin.ext h
        subst hi
        rw [finRotate_last]
        simp

theorem val_finRotate_iterate {n : ℕ} (m : ℕ) (i : Fin n) :
    ((((finRotate n : Fin n → Fin n)^[m]) i : Fin n) : ℕ) = ((i : ℕ) + m) % n := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt i.2]
  | succ m ih =>
      rw [Function.iterate_succ_apply', val_finRotate, ih, Nat.mod_add_mod, Nat.add_assoc]

end Shift

section Split

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

local notation "ℓ" => Module.finrank K L

include hdeg hσ in
theorem pow_mod_apply (n : ℕ) (x : L) : (σ ^ (n % ℓ)) x = (σ ^ n) x := by
  have hℓ := pow_finrank_eq_one hdeg σ hσ
  conv_rhs => rw [← Nat.mod_add_div n ℓ, pow_add, pow_mul, hℓ, one_pow, mul_one]

include hdeg hσ in

theorem psi_sigmaTensor (z : L ⊗[K] A) (i : Fin ℓ) :
    psi K L A σ ι (sigmaTensor K L A σ z) i = psi K L A σ ι z (finRotate _ i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
      have hs : sigmaTensor K L A σ (x ⊗ₜ[K] b) = σ x ⊗ₜ[K] b := rfl
      rw [hs, psi_tmul, psi_tmul, val_finRotate, pow_mod_apply σ hdeg hσ, pow_succ, AlgEquiv.mul_apply]
  | add z w hz hw => simp [map_add, hz, hw]

theorem psiGL_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) (k : Fin ℓ) :
    psiGL A σ ι hdeg hσ (sigmaGL K L A σ g) k = psiGL A σ ι hdeg hσ g (finRotate _ k) := by
  ext p q
  rw [psiGL_apply_val, psiGL_apply_val]
  exact psi_sigmaTensor A σ ι hdeg hσ _ k

theorem psiGL_sigmaGL_iterate (m : ℕ) (g : GL (Fin 2) (L ⊗[K] A)) (k : Fin ℓ) :
    psiGL A σ ι hdeg hσ (((sigmaGL K L A σ : _ → _))^[m] g) k =
      psiGL A σ ι hdeg hσ g (((finRotate ℓ : Fin ℓ → Fin ℓ)^[m]) k) := by
  induction m generalizing g k with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', psiGL_sigmaGL, ih, Function.iterate_succ_apply]

theorem psiGL_toTensorGL (γ : GL (Fin 2) A) (k : Fin ℓ) :
    psiGL A σ ι hdeg hσ (toTensorGL K L A γ) k = γ := by
  ext p q
  rw [psiGL_apply_val]
  change psi K L A σ ι ((1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) p q)) k = _
  rw [psi_tmul, map_one, map_one, one_mul]

theorem psiGL_normString (δ : GL (Fin 2) (L ⊗[K] A)) (k : Fin ℓ) :
    psiGL A σ ι hdeg hσ (normString K L A σ δ) k =
      ((List.range ℓ).map fun m => psiGL A σ ι hdeg hσ δ (((finRotate ℓ : Fin ℓ → Fin ℓ)^[m]) k)).prod := by
  unfold AutomorphicForm.normString
  rw [map_list_prod, List.map_map]
  rw [show ((psiGL A σ ι hdeg hσ : GL (Fin 2) (L ⊗[K] A) → Fin ℓ → GL (Fin 2) A) ∘
        (fun i => (⇑(sigmaGL K L A σ))^[i] δ)) = fun m => psiGL A σ ι hdeg hσ ((⇑(sigmaGL K L A σ))^[m] δ)
      from rfl]
  rw [Pi.list_prod_apply, List.map_map]
  congr 1
  apply List.map_congr_left
  intro m _
  exact psiGL_sigmaGL_iterate A σ ι hdeg hσ m δ k

theorem psiGL_scalar_apply (z : (L ⊗[K] A)ˣ) (k : Fin ℓ) (p q : Fin 2) :
    ((psiGL A σ ι hdeg hσ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) k : GL (Fin 2) A) :
        Matrix (Fin 2) (Fin 2) A) p q =
      if p = q then psi K L A σ ι (z : L ⊗[K] A) k else 0 := by
  rw [psiGL_apply_val]
  change psi K L A σ ι ((Matrix.scalar (Fin 2) (z : L ⊗[K] A)) p q) k = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

end Split

section Main

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

local notation "ℓ" => Module.finrank K L

include hdeg in
theorem ell_pos : 0 < ℓ := hdeg.pos

noncomputable def pprod (d : Fin ℓ → GL (Fin 2) A) (k : ℕ) : GL (Fin 2) A :=
  ((List.range k).map fun m => d ⟨m % ℓ, Nat.mod_lt _ (ell_pos hdeg)⟩).prod

theorem pprod_zero (d : Fin ℓ → GL (Fin 2) A) : pprod A hdeg d 0 = 1 := by
  simp [pprod]

theorem pprod_succ (d : Fin ℓ → GL (Fin 2) A) (k : ℕ) :
    pprod A hdeg d (k + 1) = pprod A hdeg d k * d ⟨k % ℓ, Nat.mod_lt _ (ell_pos hdeg)⟩ := by
  simp [pprod, List.range_succ, List.map_append, List.prod_append]

theorem pprod_finrank_eq (δ : GL (Fin 2) (L ⊗[K] A)) :
    pprod A hdeg (psiGL A σ ι hdeg hσ δ) ℓ =
      psiGL A σ ι hdeg hσ (normString K L A σ δ) ⟨0, ell_pos hdeg⟩ := by
  rw [psiGL_normString, pprod]
  congr 1
  apply List.map_congr_left
  intro m _
  refine congrArg _ (Fin.ext ?_)
  rw [val_finRotate_iterate]
  simp

include hdeg hσ ι in

theorem main (c : Aˣ) (δ y : GL (Fin 2) (L ⊗[K] A))
    (h : IsNormConjugator K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    ∃ z : (L ⊗[K] A)ˣ, IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
  classical
  have hℓ : 0 < ℓ := ell_pos hdeg
  set Ψ := psiGL A σ ι hdeg hσ with hΨ
  set d : Fin ℓ → GL (Fin 2) A := Ψ δ with hd

  have hN0 : Ψ (normString K L A σ δ) ⟨0, hℓ⟩ = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    unfold AutomorphicForm.IsNormConjugator at h

    have h1 : normString K L A σ δ = y * toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * y⁻¹ := by
      rw [h]; group
    rw [h1, map_mul, map_mul, map_inv, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, psiGL_toTensorGL]

    have hcomm : Ψ y ⟨0, hℓ⟩ * Matrix.GeneralLinearGroup.scalar (Fin 2) c =
        Matrix.GeneralLinearGroup.scalar (Fin 2) c * Ψ y ⟨0, hℓ⟩ := by
      refine Units.ext ?_
      change (Ψ y ⟨0, hℓ⟩ : Matrix (Fin 2) (Fin 2) A) * Matrix.scalar (Fin 2) (c : A) =
        Matrix.scalar (Fin 2) (c : A) * (Ψ y ⟨0, hℓ⟩ : Matrix (Fin 2) (Fin 2) A)
      exact ((Matrix.scalar_commute (c : A) (fun r => Commute.all _ r) _).eq).symm
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

  set X : Fin ℓ → GL (Fin 2) A := fun k => (pprod A hdeg d (k : ℕ))⁻¹ with hX

  set zvec : Fin ℓ → A := fun k => if (k : ℕ) = ℓ - 1 then (c : A) else 1 with hzvec
  set zvecInv : Fin ℓ → A := fun k => if (k : ℕ) = ℓ - 1 then ((c⁻¹ : Aˣ) : A) else 1 with hzvecInv
  have hzz : zvec * zvecInv = 1 := by
    funext k; simp only [hzvec, hzvecInv, Pi.mul_apply, Pi.one_apply]; split_ifs <;> simp
  have hzz' : zvecInv * zvec = 1 := by rw [mul_comm]; exact hzz
  set e := psiEquiv A σ ι hdeg hσ with he

  let z : (L ⊗[K] A)ˣ :=
    ⟨e.symm zvec, e.symm zvecInv, by rw [← map_mul, hzz, map_one], by rw [← map_mul, hzz', map_one]⟩
  have hz : psi K L A σ ι (z : L ⊗[K] A) = zvec := by
    change psi K L A σ ι (e.symm zvec) = zvec
    rw [← psiEquiv_apply A σ ι hdeg hσ, he, AlgEquiv.apply_symm_apply]
  refine ⟨z, Ψ.symm X, ?_⟩

  apply Ψ.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  funext k
  rw [Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, hΨ, psiGL_sigmaGL, ← hΨ, MulEquiv.apply_symm_apply, ← hd]

  have hk : (k : ℕ) < ℓ := k.2
  by_cases hlast : (k : ℕ) = ℓ - 1
  ·
    have hrot : (finRotate ℓ k) = ⟨0, hℓ⟩ := by
      apply Fin.ext
      rw [val_finRotate, hlast, Nat.sub_add_cancel hℓ, Nat.mod_self]
    have hX0 : X ⟨0, hℓ⟩ = 1 := by simp only [hX]; rw [pprod_zero, inv_one]
    have hXk : (X k)⁻¹ * d k = pprod A hdeg d ℓ := by
      simp only [hX, inv_inv]
      conv_rhs => rw [← Nat.sub_add_cancel hℓ, pprod_succ]
      congr 2
      apply Fin.ext
      simp only
      rw [← hlast, Nat.mod_eq_of_lt hk]
    have lhs : Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) k = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
      ext p q
      rw [hΨ, psiGL_scalar_apply, hz]
      simp only [hzvec, hlast, if_true]
      change _ = (Matrix.scalar (Fin 2) (c : A)) p q
      rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    rw [lhs, hrot, hX0, mul_one, hXk, hd, hΨ, pprod_finrank_eq, ← hΨ, hN0]
  ·
    have hlt : (k : ℕ) + 1 < ℓ := by omega
    have hrot : ((finRotate ℓ k : Fin ℓ) : ℕ) = (k : ℕ) + 1 := by
      rw [val_finRotate, Nat.mod_eq_of_lt hlt]
    have hXk1 : X (finRotate ℓ k) = (pprod A hdeg d ((k : ℕ) + 1))⁻¹ := by
      simp only [hX, hrot]
    have lhs : Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) k = 1 := by
      ext p q
      rw [hΨ, psiGL_scalar_apply, hz]
      simp only [hzvec, hlast, if_false]
      change _ = (1 : Matrix (Fin 2) (Fin 2) A) p q
      rw [Matrix.one_apply]
    rw [lhs, hXk1, pprod_succ]
    have hkk : (⟨(k : ℕ) % ℓ, Nat.mod_lt _ (ell_pos hdeg)⟩ : Fin ℓ) = k := by
      apply Fin.ext; simp [Nat.mod_eq_of_lt hk]
    rw [hkk]
    simp only [hX, inv_inv]
    group

end Main

end P2mSplitKind

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A] (ι : L →ₐ[K] A)
    (c : Aˣ) (δ y : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormConjugator K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    ∃ z : (L ⊗[K] A)ˣ,
      AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) :=
  P2mSplitKind.main A σ ι hdeg hσ c δ y h

end S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime
end P2MW
export P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime (solution)
