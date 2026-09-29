-- Prove2me | solution 1 for AutomorphicForm.exists_isNormConjugator_and_coupled_of_gram_of_algHom_real
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/dcc27c78-dad5-500a-b09a-bcb823a64d38

import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_of_algHom_real

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory AutomorphicForm AutomorphicForm.SplitPlace Topology
open scoped TensorProduct TensorProduct.RightActions ENNReal

noncomputable section

namespace P2mSplitGramCoupled

section ShiftToolkit

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)

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

theorem pow_mod_apply {n : ℕ} (hℓ : σ ^ Module.finrank K L = 1) (x : L) :
    (σ ^ (n % Module.finrank K L)) x = (σ ^ n) x := by
  conv_rhs => rw [← Nat.mod_add_div n (Module.finrank K L), pow_add, pow_mul, hℓ, one_pow, mul_one]

theorem psi_sigmaTensor (hℓ : σ ^ Module.finrank K L = 1) (z : L ⊗[K] A)
    (i : Fin (Module.finrank K L)) :
    psi K L A σ ι (sigmaTensor K L A σ z) i = psi K L A σ ι z (finRotate _ i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
      have hs : sigmaTensor K L A σ (x ⊗ₜ[K] b) = σ x ⊗ₜ[K] b := rfl
      rw [hs, psi_tmul, psi_tmul, val_finRotate, pow_mod_apply σ hℓ, pow_succ, AlgEquiv.mul_apply]
  | add z w hz hw => simp [map_add, hz, hw]

variable {G : Type*} [Group G] in

def shift (n : ℕ) : (Fin n → G) ≃* (Fin n → G) where
  toEquiv := Equiv.arrowCongr (finRotate n) (Equiv.refl G) |>.symm
  map_mul' _ _ := rfl

variable {G : Type*} [Group G] in
@[scoped simp] theorem shift_apply {n : ℕ} (t : Fin n → G) (i : Fin n) : shift n t i = t (finRotate n i) := rfl

variable {G : Type*} [Group G] in
theorem shift_iterate_apply {n : ℕ} (m : ℕ) (t : Fin n → G) (i : Fin n) :
    ((shift n : (Fin n → G) → Fin n → G)^[m]) t i = t (((finRotate n : Fin n → Fin n)^[m]) i) := by
  induction m generalizing t with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih, shift_apply, Function.iterate_succ_apply' (finRotate n)]

variable (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

theorem psiGL_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    psiGL A σ ι hdeg hσ (sigmaGL K L A σ g) = shift (Module.finrank K L) (psiGL A σ ι hdeg hσ g) := by
  funext i
  ext p q
  rw [psiGL_apply_val, shift_apply, psiGL_apply_val]
  exact psi_sigmaTensor A σ ι (pow_finrank_eq_one hdeg σ hσ) _ i

theorem psiGL_toTensorGL (γ : GL (Fin 2) A) :
    psiGL A σ ι hdeg hσ (toTensorGL K L A γ) = fun _ => γ := by
  funext i
  ext p q
  rw [psiGL_apply_val]
  change psi K L A σ ι ((1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) p q)) i = _
  rw [psi_tmul, map_one, map_one, one_mul]

theorem psiGL_sigmaGL_iterate (m : ℕ) (g : GL (Fin 2) (L ⊗[K] A)) :
    psiGL A σ ι hdeg hσ (((sigmaGL K L A σ : _ → _))^[m] g) =
      ((shift (Module.finrank K L) : (Fin (Module.finrank K L) → GL (Fin 2) A) → _)^[m])
        (psiGL A σ ι hdeg hσ g) :=
  Function.Semiconj.iterate_right (f := psiGL A σ ι hdeg hσ) (fun x => psiGL_sigmaGL A σ ι hdeg hσ x) m g

theorem psiGL_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    psiGL A σ ι hdeg hσ (normString K L A σ δ) =
      ((List.range (Module.finrank K L)).map fun m =>
        ((shift (Module.finrank K L) : (Fin (Module.finrank K L) → GL (Fin 2) A) → _)^[m])
          (psiGL A σ ι hdeg hσ δ)).prod := by
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro m _
  exact psiGL_sigmaGL_iterate A σ ι hdeg hσ m δ

def i0 : Fin (Module.finrank K L) := ⟨0, hdeg.pos⟩

theorem psiGL_normString_i0 (δ : GL (Fin 2) (L ⊗[K] A)) :
    psiGL A σ ι hdeg hσ (normString K L A σ δ) (i0 hdeg) =
      ((List.range (Module.finrank K L)).map fun m =>
        psiGL A σ ι hdeg hσ δ (((finRotate _ : _ → _)^[m]) (i0 hdeg))).prod := by
  rw [psiGL_normString]
  have heval : ∀ (l : List (Fin (Module.finrank K L) → GL (Fin 2) A)),
      l.prod (i0 hdeg) = (l.map fun t => t (i0 hdeg)).prod := by
    intro l
    have : l.prod (i0 hdeg) = Pi.evalMonoidHom (fun _ => GL (Fin 2) A) (i0 hdeg) l.prod := rfl
    rw [this, map_list_prod]
    rfl
  rw [heval, List.map_map]
  congr 1
  apply List.map_congr_left
  intro m _
  simp only [Function.comp_apply, shift_iterate_apply]

end ShiftToolkit

section MatrixToolkit

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

def psiM : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) ≃+* (Fin (Module.finrank K L) → Matrix (Fin 2) (Fin 2) A) :=
  (psiEquiv A σ ι hdeg hσ).toRingEquiv.mapMatrix.trans
    (Matrix.piRingEquiv (β := fun _ : Fin (Module.finrank K L) => A) (n := Fin 2))

@[scoped simp] theorem psiM_apply (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (i : Fin (Module.finrank K L))
    (p q : Fin 2) : psiM A σ ι hdeg hσ X i p q = psi K L A σ ι (X p q) i := rfl

theorem coe_psiGL (g : GL (Fin 2) (L ⊗[K] A)) (i : Fin (Module.finrank K L)) :
    ((psiGL A σ ι hdeg hσ g i : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      psiM A σ ι hdeg hσ (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i := rfl

abbrev sigM : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) →+* Matrix (Fin 2) (Fin 2) (L ⊗[K] A) :=
  (sigmaTensor K L A σ).mapMatrix

theorem sigM_apply (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) : sigM A σ X = X.map (sigmaTensor K L A σ) := rfl

theorem coe_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    ((sigmaGL K L A σ g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      sigM A σ (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := rfl

theorem psiM_sigM (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (i : Fin (Module.finrank K L)) :
    psiM A σ ι hdeg hσ (sigM A σ X) i = psiM A σ ι hdeg hσ X (finRotate _ i) := by
  ext p q
  rw [psiM_apply, psiM_apply]
  exact psi_sigmaTensor A σ ι (pow_finrank_eq_one hdeg σ hσ) _ i

def iotaM (Y : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) :=
  Y.map fun x : A => ((1 : L) ⊗ₜ[K] x : L ⊗[K] A)

theorem iotaM_apply (Y : Matrix (Fin 2) (Fin 2) A) (p q : Fin 2) : iotaM (K := K) (L := L) A Y p q = (1 : L) ⊗ₜ[K] Y p q :=
  rfl

theorem psiM_iotaM (Y : Matrix (Fin 2) (Fin 2) A) : psiM A σ ι hdeg hσ (iotaM A Y) = fun _ => Y := by
  funext i
  ext p q
  rw [psiM_apply, iotaM_apply, psi_tmul, map_one, map_one, one_mul]

theorem sigM_iotaM (Y : Matrix (Fin 2) (Fin 2) A) : sigM A σ (iotaM (K := K) (L := L) A Y) = iotaM A Y := by
  ext p q
  simp [iotaM_apply, sigmaTensor, Algebra.TensorProduct.map_tmul]

theorem eq_i0_of_forall_finRotate {α : Type*} (T : Fin (Module.finrank K L) → α)
    (hT : ∀ i, T (finRotate _ i) = T i) (i : Fin (Module.finrank K L)) : T i = T (i0 hdeg) := by
  have key : ∀ m : ℕ, T (((finRotate _ : _ → _)^[m]) (i0 hdeg)) = T (i0 hdeg) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', hT, ih]
  have hi : ((finRotate _ : _ → _)^[(i : ℕ)]) (i0 (K := K) (L := L) hdeg) = i := by
    apply Fin.ext
    rw [val_finRotate_iterate]
    simp [i0, Nat.mod_eq_of_lt i.2]
  rw [← hi]
  exact key i

include ι hdeg hσ in

theorem sigM_eq_self_iff (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    sigM A σ X = X ↔ X ∈ Set.range (iotaM (K := K) (L := L) A) := by
  constructor
  · intro h
    set T := psiM A σ ι hdeg hσ X with hT
    have hshift : ∀ i, T (finRotate _ i) = T i := fun i => by
      rw [hT, ← psiM_sigM, h]
    refine ⟨T (i0 hdeg), ?_⟩
    apply (psiM A σ ι hdeg hσ).injective
    rw [psiM_iotaM]
    funext i
    exact (eq_i0_of_forall_finRotate hdeg T hshift i).symm
  · rintro ⟨Y, rfl⟩
    exact sigM_iotaM A σ Y

include σ ι hdeg hσ in

theorem iotaM_injective : Function.Injective (iotaM (K := K) (L := L) A) := by
  intro Y Y' h
  have := congrArg (psiM A σ ι hdeg hσ) h
  rw [psiM_iotaM, psiM_iotaM] at this
  exact congrFun this (i0 hdeg)

theorem coe_toTensorGL (g : GL (Fin 2) A) :
    ((toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      iotaM A (g : Matrix (Fin 2) (Fin 2) A) := rfl

theorem central_of_psiM_scalar (Z : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (hZ : ∀ i, ∃ a : A, psiM A σ ι hdeg hσ Z i = a • (1 : Matrix (Fin 2) (Fin 2) A))
    (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) : Z * X = X * Z := by
  apply (psiM A σ ι hdeg hσ).injective
  rw [map_mul, map_mul]
  funext i
  obtain ⟨a, ha⟩ := hZ i
  rw [Pi.mul_apply, Pi.mul_apply, ha, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

end MatrixToolkit

section Hilbert90

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

def pprod (t : Fin (Module.finrank K L) → GL (Fin 2) A) (k : ℕ) : GL (Fin 2) A :=
  ((List.range k).map fun m => t (((finRotate _ : _ → _)^[m]) (i0 hdeg))).prod

theorem pprod_zero (t : Fin (Module.finrank K L) → GL (Fin 2) A) : pprod A hdeg t 0 = 1 := by
  simp [pprod]

theorem pprod_succ (t : Fin (Module.finrank K L) → GL (Fin 2) A) (k : ℕ) :
    pprod A hdeg t (k + 1) = pprod A hdeg t k * t (((finRotate _ : _ → _)^[k]) (i0 hdeg)) := by
  simp [pprod, List.range_succ, List.map_append, List.prod_append]

theorem finRotate_iterate_i0 (i : Fin (Module.finrank K L)) :
    ((finRotate _ : _ → _)^[(i : ℕ)]) (i0 (K := K) (L := L) hdeg) = i := by
  apply Fin.ext
  rw [val_finRotate_iterate]
  simp [i0, Nat.mod_eq_of_lt i.2]

def xString (t : Fin (Module.finrank K L) → GL (Fin 2) A) : Fin (Module.finrank K L) → GL (Fin 2) A :=
  fun i => pprod A hdeg t i

theorem xString_mul_mul_shift_inv (t : Fin (Module.finrank K L) → GL (Fin 2) A)
    (i : Fin (Module.finrank K L)) :
    (xString A hdeg t * t * (shift (Module.finrank K L) (xString A hdeg t))⁻¹) i =
      if (i : ℕ) + 1 = Module.finrank K L then pprod A hdeg t (Module.finrank K L) else 1 := by
  rw [Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, shift_apply]
  simp only [xString]
  have hti : t i = t (((finRotate _ : _ → _)^[(i : ℕ)]) (i0 hdeg)) := by rw [finRotate_iterate_i0]
  split_ifs with h
  ·
    have hrot : ((finRotate _ i : Fin (Module.finrank K L)) : ℕ) = 0 := by
      rw [val_finRotate, h, Nat.mod_self]
    rw [hrot, pprod_zero, inv_one, mul_one, hti, ← pprod_succ, h]
  · have hlt : (i : ℕ) + 1 < Module.finrank K L := lt_of_le_of_ne i.2 h
    have hrot : ((finRotate _ i : Fin (Module.finrank K L)) : ℕ) = (i : ℕ) + 1 := by
      rw [val_finRotate, Nat.mod_eq_of_lt hlt]
    rw [hrot, pprod_succ, hti, mul_inv_rev, ← mul_assoc, mul_inv_cancel_right, mul_inv_cancel]

include ι hdeg hσ in

theorem hilbert90_split (c : Aˣ) (δ : GL (Fin 2) (L ⊗[K] A))
    (hN : normString K L A σ δ = toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :
    ∃ x z : GL (Fin 2) (L ⊗[K] A),
      (∀ X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A),
        (z : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * X = X * z) ∧
      δ = x⁻¹ * z * sigmaGL K L A σ x := by
  set Ψ := psiGL A σ ι hdeg hσ with hΨ
  set t := Ψ δ with ht
  set x : GL (Fin 2) (L ⊗[K] A) := Ψ.symm (xString A hdeg t) with hx
  set z : GL (Fin 2) (L ⊗[K] A) := x * δ * (sigmaGL K L A σ x)⁻¹ with hz

  have hfull : pprod A hdeg t (Module.finrank K L) = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    have h1 := psiGL_normString_i0 A σ ι hdeg hσ δ
    rw [hN, psiGL_toTensorGL] at h1
    exact h1.symm

  have hzc : ∀ i, Ψ z i = if (i : ℕ) + 1 = Module.finrank K L then
      Matrix.GeneralLinearGroup.scalar (Fin 2) c else 1 := by
    intro i
    have : Ψ z = xString A hdeg t * t * (shift (Module.finrank K L) (xString A hdeg t))⁻¹ := by
      rw [hz, map_mul, map_mul, map_inv, hΨ, psiGL_sigmaGL, ← hΨ, hx, MulEquiv.apply_symm_apply]
    rw [this, xString_mul_mul_shift_inv, hfull]
  refine ⟨x, z, ?_, ?_⟩
  · intro X
    apply central_of_psiM_scalar A σ ι hdeg hσ
    intro i
    rw [← coe_psiGL, ← hΨ, hzc i]
    split_ifs
    · exact ⟨(c : A), (Matrix.smul_one_eq_diagonal (c : A)).symm⟩
    · exact ⟨1, by simp⟩
  · rw [hz]
    group

end Hilbert90

section ConjCriterion

theorem conj_criterion {R : Type*} [Monoid R] (σ : R →* R) (x z s : Rˣ)
    (hz : ∀ A : R, (z : R) * A = A * z) (hs : σ (x : R) = s) (hsi : σ ((x⁻¹ : Rˣ) : R) = ((s⁻¹ : Rˣ) : R))
    (X : R) :
    X * ((x⁻¹ : Rˣ) * z * s : R) = ((x⁻¹ : Rˣ) * z * s : R) * σ X ↔
      σ ((x : R) * X * (x⁻¹ : Rˣ)) = (x : R) * X * (x⁻¹ : Rˣ) := by
  have eσ : σ ((x : R) * X * (x⁻¹ : Rˣ)) = (s : R) * σ X * (s⁻¹ : Rˣ) := by
    rw [map_mul, map_mul, hs, hsi]
  rw [eσ]
  constructor
  · intro h
    have h2 : (x : R) * X * (x⁻¹ : Rˣ) * z * s = (z : R) * s * σ X := by
      calc (x : R) * X * (x⁻¹ : Rˣ) * z * s = (x : R) * (X * ((x⁻¹ : Rˣ) * z * s)) := by
            simp only [mul_assoc]
        _ = (x : R) * ((x⁻¹ : Rˣ) * z * s * σ X) := by rw [h]
        _ = (z : R) * s * σ X := by
            simp only [mul_assoc, Units.mul_inv_cancel_left]
    have h3 : (x : R) * X * (x⁻¹ : Rˣ) * z = (z : R) * s * σ X * (s⁻¹ : Rˣ) := by
      calc (x : R) * X * (x⁻¹ : Rˣ) * z = (x : R) * X * (x⁻¹ : Rˣ) * z * s * (s⁻¹ : Rˣ) := by
            rw [Units.mul_inv_cancel_right]
        _ = (z : R) * s * σ X * (s⁻¹ : Rˣ) := by rw [h2]
    rw [← hz] at h3
    have h4 : (z : R) * ((x : R) * X * (x⁻¹ : Rˣ)) = (z : R) * ((s : R) * σ X * (s⁻¹ : Rˣ)) := by
      simpa only [mul_assoc] using h3
    exact ((Units.mul_right_inj z).1 h4).symm
  · intro h
    have h4 : (z : R) * ((x : R) * X * (x⁻¹ : Rˣ)) = (z : R) * ((s : R) * σ X * (s⁻¹ : Rˣ)) := by rw [h]
    have h3 : (x : R) * X * (x⁻¹ : Rˣ) * z = (z : R) * s * σ X * (s⁻¹ : Rˣ) := by
      rw [← hz]; simpa only [mul_assoc] using h4
    have h2 : (x : R) * X * (x⁻¹ : Rˣ) * z * s = (z : R) * s * σ X := by
      have := congrArg (fun A : R => A * s) h3
      simpa only [mul_assoc, Units.inv_mul, mul_one] using this
    have h5 : (x : R) * (X * ((x⁻¹ : Rˣ) * z * s)) = (x : R) * ((x⁻¹ : Rˣ) * z * s * σ X) := by
      calc (x : R) * (X * ((x⁻¹ : Rˣ) * z * s)) = (x : R) * X * (x⁻¹ : Rˣ) * z * s := by
            simp only [mul_assoc]
        _ = (z : R) * s * σ X := h2
        _ = (x : R) * ((x⁻¹ : Rˣ) * z * s * σ X) := by
            simp only [mul_assoc, Units.mul_inv_cancel_left]
    exact (Units.mul_right_inj x).1 h5

end ConjCriterion

section TwistedAlgebra

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

def twAlg (δ : GL (Fin 2) (L ⊗[K] A)) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
  {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
    (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * X.map (sigmaTensor K L A σ)}

def conjM (x : GL (Fin 2) (L ⊗[K] A)) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    Matrix (Fin 2) (Fin 2) (L ⊗[K] A) :=
  (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * X * ((x⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix _ _ _)

include ι hdeg hσ in

theorem mem_twAlg_iff (x z δ : GL (Fin 2) (L ⊗[K] A))
    (hzc : ∀ X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A), (z : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * X = X * z)
    (hδ : δ = x⁻¹ * z * sigmaGL K L A σ x)
    (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    X ∈ twAlg A σ δ ↔ conjM A x X ∈ Set.range (iotaM (K := K) (L := L) A) := by
  rw [← sigM_eq_self_iff A σ ι hdeg hσ]
  have hcoe : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      ((x⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix _ _ _) * (z : Matrix _ _ _) *
        ((sigmaGL K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix _ _ _) := by
    rw [hδ, Units.val_mul, Units.val_mul]
  have hsi : sigM A σ ((x⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix _ _ _) =
      (((sigmaGL K L A σ x)⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix _ _ _) := by
    rw [← map_inv]; rfl
  have key := conj_criterion (sigM A σ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) →+* _).toMonoidHom x z
    (sigmaGL K L A σ x) hzc rfl hsi X
  rw [twAlg, Set.mem_setOf_eq, hcoe]
  exact key

theorem conjM_injective (x : GL (Fin 2) (L ⊗[K] A)) : Function.Injective (conjM (K := K) (L := L) A x) := by
  intro X Y h
  have h1 := (Units.mul_left_inj x⁻¹).1 h
  exact (Units.mul_right_inj x).1 h1

include ι hdeg hσ in

theorem image_conjM_twAlg (x z δ : GL (Fin 2) (L ⊗[K] A))
    (hzc : ∀ X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A), (z : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * X = X * z)
    (hδ : δ = x⁻¹ * z * sigmaGL K L A σ x) :
    conjM A x '' twAlg A σ δ = Set.range (iotaM (K := K) (L := L) A) := by
  ext U
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact (mem_twAlg_iff A σ ι hdeg hσ x z δ hzc hδ X).1 hX
  · intro hU
    refine ⟨((x⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix _ _ _) * U * (x : Matrix _ _ _), ?_, ?_⟩
    · rw [mem_twAlg_iff A σ ι hdeg hσ x z δ hzc hδ]
      convert hU using 1
      simp only [conjM, mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]
    · simp only [conjM, mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

end TwistedAlgebra

section Gram

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [MeasurableSpace V] [BorelSpace V]

def coordMap {n : ℕ} (e : Fin n → V) : (Fin n → ℝ) → V := fun c => ∑ i, c i • e i

theorem continuous_coordMap {n : ℕ} (e : Fin n → V) : Continuous (coordMap e) := by
  unfold coordMap
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_apply i).smul continuous_const

theorem measurable_coordMap {n : ℕ} (e : Fin n → V) : Measurable (coordMap e) :=
  (continuous_coordMap e).measurable

def gramDet (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e : Fin n → V) : ℝ :=
  (Matrix.of fun i j : Fin n => B (e i) (e j)).det

def gramMeasure (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e : Fin n → V) : Measure V :=
  ENNReal.ofReal (Real.sqrt |gramDet B e|) • Measure.map (coordMap e) volume

theorem coordMap_eq_comp {n : ℕ} (e e' : Fin n → V) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ j, e' j = ∑ i, P i j • e i) :
    coordMap e' = coordMap e ∘ (Matrix.toLin' P) := by
  funext c
  simp only [coordMap, Function.comp_apply, Matrix.toLin'_apply]
  calc ∑ j, c j • e' j = ∑ j, ∑ i, (c j * P i j) • e i := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hP j, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
    _ = ∑ i, ∑ j, (c j * P i j) • e i := Finset.sum_comm
    _ = ∑ i, (P.mulVec c) i • e i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        change ∑ j, c j * P i j = ∑ j, P i j * c j
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem gramDet_eq_of_comp (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e e' : Fin n → V)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ j, e' j = ∑ i, P i j • e i) :
    gramDet B e' = P.det ^ 2 * gramDet B e := by
  have hG : (Matrix.of fun i j : Fin n => B (e' i) (e' j)) =
      P.transpose * (Matrix.of fun i j : Fin n => B (e i) (e j)) * P := by
    ext j k
    have hjk : B (e' j) (e' k) = ∑ i, ∑ l, P i j * P l k * B (e i) (e l) := by
      have h1 : B (e' j) = ∑ i, P i j • B (e i) := by rw [hP j, map_sum]; simp only [map_smul]
      rw [h1, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, hP k, map_sum, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, smul_eq_mul]
      ring
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [hjk, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [gramDet, gramDet, hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem gramMeasure_eq_of_comp (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e e' : Fin n → V)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ j, e' j = ∑ i, P i j • e i) (hdet : P.det ≠ 0) :
    gramMeasure B e' = gramMeasure B e := by
  rw [gramMeasure, gramMeasure, coordMap_eq_comp e e' P hP, gramDet_eq_of_comp B e e' P hP,
    ← Measure.map_map (measurable_coordMap e) (Matrix.toLin' P).continuous_of_finiteDimensional.measurable,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, Measure.map_smul, smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), abs_mul, abs_pow, Real.sqrt_mul' _ (abs_nonneg _),
    Real.sqrt_sq (abs_nonneg _), abs_inv]
  congr 1
  rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hdet), one_mul]

theorem exists_matrix_of_span_eq {n : ℕ} (e e' : Fin n → V) (he : LinearIndependent ℝ e)
    (he' : LinearIndependent ℝ e')
    (hspan : Submodule.span ℝ (Set.range e') ≤ Submodule.span ℝ (Set.range e)) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, (∀ j, e' j = ∑ i, P i j • e i) ∧ P.det ≠ 0 := by
  have hmem : ∀ j, e' j ∈ Submodule.span ℝ (Set.range e) := fun j =>
    hspan (Submodule.subset_span ⟨j, rfl⟩)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hmem j)
  refine ⟨Matrix.of fun i j => c j i, fun j => ?_, ?_⟩
  · simp only [Matrix.of_apply]; exact (hc j).symm
  · intro hdet
    obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hP : ∀ j, e' j = ∑ i, (Matrix.of fun i j => c j i) i j • e i := fun j => by
      simp only [Matrix.of_apply]; exact (hc j).symm
    have h0 : coordMap e' v = 0 := by
      rw [coordMap_eq_comp e e' _ hP, Function.comp_apply, Matrix.toLin'_apply, hPv]
      simp [coordMap]
    apply hv
    funext j
    exact Fintype.linearIndependent_iff.mp he' v h0 j

theorem card_eq_of_span_eq {n n' : ℕ} (e : Fin n → V) (e' : Fin n' → V) (he : LinearIndependent ℝ e)
    (he' : LinearIndependent ℝ e')
    (hspan : Submodule.span ℝ (Set.range e') = Submodule.span ℝ (Set.range e)) : n' = n := by
  have h1 := finrank_span_eq_card he
  have h2 := finrank_span_eq_card he'
  rw [hspan, h1, Fintype.card_fin, Fintype.card_fin] at h2
  exact h2.symm

theorem map_gramMeasure (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (T : V →ₗ[ℝ] V) (hT : Continuous T)
    (hB : ∀ u v, B (T u) (T v) = B u v) {n : ℕ} (e : Fin n → V) :
    Measure.map T (gramMeasure B e) = gramMeasure B (T ∘ e) := by
  rw [gramMeasure, gramMeasure, Measure.map_smul, Measure.map_map hT.measurable (measurable_coordMap e)]
  have h1 : (T : V → V) ∘ coordMap e = coordMap (T ∘ e) := by
    funext c
    simp [coordMap, map_sum, map_smul]
  have h2 : gramDet B (T ∘ e) = gramDet B e := by
    unfold gramDet
    congr 1
    ext i j
    simp [hB]
  rw [h1, h2]

theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (μ : Measure α) {ρ : β → ℝ≥0∞} (hρ : Measurable ρ) :
    Measure.map f (μ.withDensity (ρ ∘ f)) = (Measure.map f μ).withDensity ρ := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hρ hf]
  rfl

theorem map_injective_of_measurableEmbedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) {μ ν : Measure α}
    (h : Measure.map f μ = Measure.map f ν) : μ = ν := by
  ext s hs
  have h1 : μ s = Measure.map f μ (f '' s) := by
    rw [hf.map_apply, hf.injective.preimage_image]
  have h2 : ν s = Measure.map f ν (f '' s) := by
    rw [hf.map_apply, hf.injective.preimage_image]
  rw [h1, h2, h]

end Gram

section Arch

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra K ℝ]

abbrev Esp : Type := L ⊗[K] ℝ

abbrev Msp : Type := Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ)

abbrev Gsp : Type := GL (Fin 2) (L ⊗[K] ℝ)

local instance instIsTopologicalRingEsp : IsTopologicalRing (Esp K L) := isTopologicalRing_tensor K L ℝ
local instance instT2Esp : T2Space (Esp K L) := t2Space_tensor K L ℝ
local instance instT2Msp : T2Space (Msp K L) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → Esp K L))
local instance instMeasMsp : MeasurableSpace (Msp K L) := borel _
local instance instBorelMsp : BorelSpace (Msp K L) := ⟨rfl⟩
local instance instMeasGsp : MeasurableSpace (Gsp K L) := glBorelOf (Esp K L)
local instance instBorelGsp : BorelSpace (Gsp K L) := borelSpace_glBorelOf (Esp K L)
local instance instTopGroupGsp : IsTopologicalGroup (Gsp K L) := isTopologicalGroup_tensorGL K L ℝ
local instance instT2Gsp : T2Space (Gsp K L) := t2Space_tensorGL K L ℝ

theorem rsmul_eq (r : ℝ) (z : Esp K L) : r • z = algebraMap ℝ (Esp K L) r * z := Algebra.smul_def r z

local instance instIsScalarTowerEsp : IsScalarTower ℝ (Esp K L) (Esp K L) :=
  ⟨fun r x y => by simp only [smul_eq_mul, rsmul_eq, mul_assoc]⟩

local instance instSMulCommClassEsp : SMulCommClass ℝ (Esp K L) (Esp K L) :=
  ⟨fun r x y => by simp only [smul_eq_mul, rsmul_eq]; rw [mul_left_comm]⟩

def coordHomeo {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [ContinuousSMul ℝ W] [T2Space W] {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ W) : W ≃ₜ (ι → ℝ) :=
  haveI : FiniteDimensional ℝ W := Module.Finite.of_basis b
  { toEquiv := b.equivFun.toEquiv
    continuous_toFun := b.equivFun.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun := b.equivFun.symm.toLinearMap.continuous_of_finiteDimensional }

theorem polishSpace_Msp : PolishSpace (Msp K L) :=
  (coordHomeo (Module.finBasis ℝ (Msp K L))).isClosedEmbedding.polishSpace

theorem polishSpace_Gsp : PolishSpace (Gsp K L) := by
  haveI : PolishSpace (Msp K L) := polishSpace_Msp K L
  haveI : PolishSpace (Msp K L)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.polishSpace
  exact Units.isClosedEmbedding_embedProduct.polishSpace

theorem measurableEmbedding_val : MeasurableEmbedding (Units.val : Gsp K L → Msp K L) := by
  haveI := polishSpace_Gsp K L
  exact Units.continuous_val.measurableEmbedding Units.val_injective

theorem measurable_val : Measurable (Units.val : Gsp K L → Msp K L) := Units.continuous_val.measurable

theorem continuous_iotaE : Continuous fun a : ℝ => ((1 : L) ⊗ₜ[K] a : Esp K L) := by
  have : (fun a : ℝ => ((1 : L) ⊗ₜ[K] a : Esp K L)) = algebraMap ℝ (Esp K L) := rfl
  rw [this]
  exact continuous_algebraMap ℝ (Esp K L)

theorem continuous_toTensorGL : Continuous (toTensorGL K L ℝ : GL (Fin 2) ℝ → Gsp K L) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_iotaE K L))

theorem continuous_algebraNorm : Continuous (Algebra.norm ℝ : Esp K L → ℝ) := by
  classical
  set b := Module.finBasis ℝ (Esp K L)
  have h : (Algebra.norm ℝ : Esp K L → ℝ) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h]
  have hc : Continuous fun x : Esp K L => Algebra.leftMulMatrix b x :=
    (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional
  exact hc.matrix_det

def Bsp : Msp K L →ₗ[ℝ] Msp K L →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X Y : Msp K L => Algebra.trace ℝ (Esp K L) (Matrix.trace (X * Y)))
    (fun X₁ X₂ Y => by simp only [add_mul, Matrix.trace_add, map_add])
    (fun r X Y => by rw [Matrix.smul_mul, Matrix.trace_smul, map_smul, smul_eq_mul])
    (fun X Y₁ Y₂ => by simp only [mul_add, Matrix.trace_add, map_add])
    (fun r X Y => by rw [Matrix.mul_smul, Matrix.trace_smul, map_smul, smul_eq_mul])

theorem Bsp_apply (X Y : Msp K L) : Bsp K L X Y = Algebra.trace ℝ (Esp K L) (Matrix.trace (X * Y)) := rfl

def conjL (x : Gsp K L) : Msp K L →ₗ[ℝ] Msp K L where
  toFun := conjM ℝ x
  map_add' X Y := by simp only [conjM, mul_add, add_mul]
  map_smul' r X := by
    simp only [conjM, RingHom.id_apply]
    rw [Matrix.mul_smul, Matrix.smul_mul]

theorem conjL_apply (x : Gsp K L) (X : Msp K L) :
    conjL K L x X = (x : Msp K L) * X * ((x⁻¹ : Gsp K L) : Msp K L) := rfl

theorem coe_conjL (x : Gsp K L) : (conjL K L x : Msp K L → Msp K L) = conjM ℝ x := rfl

theorem continuous_conjL (x : Gsp K L) : Continuous (conjL K L x) :=
  (continuous_const.mul continuous_id).mul continuous_const

theorem ker_conjL (x : Gsp K L) : LinearMap.ker (conjL K L x) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (conjM_injective ℝ x)

theorem Bsp_conjL (x : Gsp K L) (X Y : Msp K L) : Bsp K L (conjL K L x X) (conjL K L x Y) = Bsp K L X Y := by
  rw [Bsp_apply, Bsp_apply, conjL_apply, conjL_apply]
  have : (x : Msp K L) * X * ((x⁻¹ : Gsp K L) : Msp K L) * ((x : Msp K L) * Y * ((x⁻¹ : Gsp K L) : Msp K L)) =
      (x : Msp K L) * (X * Y) * ((x⁻¹ : Gsp K L) : Msp K L) := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [this, Matrix.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

def rho (X : Msp K L) : ℝ≥0∞ := (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹

theorem measurable_rho : Measurable (rho K L) := by
  have hc : Continuous fun X : Msp K L => |Algebra.norm ℝ (Matrix.det X)| :=
    continuous_abs.comp ((continuous_algebraNorm K L).comp (continuous_id.matrix_det))
  exact (ENNReal.continuous_ofReal.comp hc).measurable.inv

theorem rho_conjL (x : Gsp K L) (X : Msp K L) : rho K L (conjL K L x X) = rho K L X := by
  rw [rho, rho, conjL_apply, Matrix.coe_units_inv, Matrix.det_conj x.isUnit]

theorem rho_comp_conjL (x : Gsp K L) : rho K L ∘ (conjL K L x) = rho K L := funext (rho_conjL K L x)

variable {K L}

theorem main
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (ι : L →ₐ[K] ℝ)
    (c : ℝˣ)
    (δ y : GL (Fin 2) (L ⊗[K] ℝ))
    (hδ : IsNormConjugator K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
        (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ))
    (hgram : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ)) := borel _
       letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       letI := twistedCentralizerBorel K L ℝ σ δ
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ)) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
               Y.map (fun x : ℝ => ((1 : L) ⊗ₜ[K] x : L ⊗[K] ℝ))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ)) =
               (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ)) * X.map (sigmaTensor K L ℝ σ)} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer
               ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
             ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
               (fun x : ℝ => ((1 : L) ⊗ₜ[K] x : L ⊗[K] ℝ))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (L ⊗[K] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer K L ℝ σ δ) =>
             ((t : GL (Fin 2) (L ⊗[K] ℝ)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (L ⊗[K] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    ∃ y' : GL (Fin 2) (L ⊗[K] ℝ),
      IsNormConjugator K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' ∧
      Coupled K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' τ τ' := by
  letI : MeasurableSpace (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) :=
    centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
  haveI : BorelSpace (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩
  letI : MeasurableSpace (twistedCentralizer K L ℝ σ δ) := twistedCentralizerBorel K L ℝ σ δ
  haveI : BorelSpace (twistedCentralizer K L ℝ σ δ) := ⟨rfl⟩

  have hZc : ∀ g : Gsp K L, toTensorGL K L ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * g = g * toTensorGL K L ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
    intro g
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_toTensorGL]
    apply central_of_psiM_scalar ℝ σ ι hdeg hσ
    intro i
    rw [psiM_iotaM]
    exact ⟨(c : ℝ), (Matrix.smul_one_eq_diagonal (c : ℝ)).symm⟩
  have hN : normString K L ℝ σ δ = toTensorGL K L ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
    have h2 : toTensorGL K L ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = y⁻¹ * normString K L ℝ σ δ * y := hδ
    have h3 : normString K L ℝ σ δ = y * toTensorGL K L ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * y⁻¹ := by
      rw [h2]; group
    rw [h3, ← hZc, mul_assoc, mul_inv_cancel, mul_one]

  obtain ⟨x, z, hzc, hx⟩ := hilbert90_split ℝ σ ι hdeg hσ c δ hN
  refine ⟨x⁻¹, ?_, ?_⟩
  ·
    show toTensorGL K L ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = (x⁻¹)⁻¹ * normString K L ℝ σ δ * x⁻¹
    rw [hN, inv_inv, ← hZc, mul_assoc, mul_inv_cancel, mul_one]
  ·
    dsimp only [Coupled]
    rw [inv_inv]
    obtain ⟨n₁, n₂, e₁, e₂, s, hs0, hstop, hli₁, hsp₁, hli₂, hsp₂, hτe, hτ'e⟩ := hgram

    have hF₁ : Measurable (fun t : twistedCentralizer K L ℝ σ δ => x * (t : Gsp K L) * x⁻¹) :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    have hF₂ : Measurable (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)) =>
        toTensorGL K L ℝ (t : GL (Fin 2) ℝ)) :=
      ((continuous_toTensorGL K L).comp continuous_subtype_val).measurable
    apply map_injective_of_measurableEmbedding (measurableEmbedding_val K L)
    rw [Measure.map_map (measurable_val K L) hF₁, Measure.map_map (measurable_val K L) hF₂]
    have eL : (Units.val ∘ fun t : twistedCentralizer K L ℝ σ δ => x * (t : Gsp K L) * x⁻¹) =
        (conjL K L x) ∘ (fun t : twistedCentralizer K L ℝ σ δ => ((t : Gsp K L) : Msp K L)) := by
      funext t; rfl
    have eR : (Units.val ∘ fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)) =>
        toTensorGL K L ℝ (t : GL (Fin 2) ℝ)) =
        fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)) =>
          ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
            (fun x : ℝ => ((1 : L) ⊗ₜ[K] x : L ⊗[K] ℝ)) := by
      funext t; rfl
    have hval' : Measurable (fun t : twistedCentralizer K L ℝ σ δ => ((t : Gsp K L) : Msp K L)) :=
      (measurable_val K L).comp continuous_subtype_val.measurable
    rw [eL, eR, ← Measure.map_map (continuous_conjL K L x).measurable hval', hτ'e, hτe]

    change Measure.map (conjL K L x) (s • (gramMeasure (Bsp K L) e₂).withDensity (rho K L)) =
      s • (gramMeasure (Bsp K L) e₁).withDensity (rho K L)
    rw [Measure.map_smul]
    congr 1
    conv_lhs => rw [← rho_comp_conjL K L x]
    rw [map_withDensity_comp (continuous_conjL K L x).measurable _ (measurable_rho K L),
      map_gramMeasure (Bsp K L) (conjL K L x) (continuous_conjL K L x) (Bsp_conjL K L x) e₂]
    congr 1

    have hspan : Submodule.span ℝ (Set.range ((conjL K L x) ∘ e₂)) = Submodule.span ℝ (Set.range e₁) := by
      apply SetLike.coe_injective
      rw [Set.range_comp, Submodule.span_image, Submodule.map_coe, hsp₂, hsp₁, coe_conjL]
      exact image_conjM_twAlg ℝ σ ι hdeg hσ x z δ hzc hx
    have hli₂' : LinearIndependent ℝ ((conjL K L x) ∘ e₂) := hli₂.map' (conjL K L x) (ker_conjL K L x)
    have hn := card_eq_of_span_eq e₁ ((conjL K L x) ∘ e₂) hli₁ hli₂' hspan
    subst hn
    obtain ⟨P, hP, hdet⟩ := exists_matrix_of_span_eq e₁ ((conjL K L x) ∘ e₂) hli₁ hli₂' hspan.le
    exact gramMeasure_eq_of_comp (Bsp K L) e₁ _ P hP hdet

end Arch

end P2mSplitGramCoupled
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_of_algHom_real.P2mSplitGramCoupled"

open P2mSplitGramCoupled in
theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℝ] (ι : L →ₐ[K] ℝ)
    (c : ℝˣ)
    (δ y : GL (Fin 2) (L ⊗[K] ℝ))
    (hδ : IsNormConjugator K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
        (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ')
    (hgram : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ)) := borel _
       letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       letI := twistedCentralizerBorel K L ℝ σ δ
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ)) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
               Y.map (fun x : ℝ => ((1 : L) ⊗ₜ[K] x : L ⊗[K] ℝ))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ)) =
               (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ)) * X.map (sigmaTensor K L ℝ σ)} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer
               ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
             ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
               (fun x : ℝ => ((1 : L) ⊗ₜ[K] x : L ⊗[K] ℝ))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (L ⊗[K] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer K L ℝ σ δ) =>
             ((t : GL (Fin 2) (L ⊗[K] ℝ)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (L ⊗[K] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    ∃ y' : GL (Fin 2) (L ⊗[K] ℝ),
      IsNormConjugator K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' ∧
      Coupled K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' τ τ' :=
  main hdeg σ hσ ι c δ y hδ τ τ' hgram

end
end S_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_of_algHom_real
end P2MW
export P2MW.S_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_of_algHom_real (solution)
