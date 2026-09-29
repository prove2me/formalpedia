-- Prove2me | solution 1 for AutomorphicForm.exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/eaaa01c5-6526-5fe0-86ce-c7442e6f2774

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2

set_option autoImplicit false

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct in

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (A : Type) [CommRing A] [Algebra K A]
    (a b : Aˣ) (hab : IsUnit ((a : A) - (b : A)))
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.normString K L A σ δ = AutomorphicForm.toTensorGL K L A (diagUnits2 a b)) :
    ∃ α β : (L ⊗[K] A)ˣ, δ = diagUnits2 α β := by
  classical

  set f : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] A) := AutomorphicForm.sigmaGL K L A σ with hf
  set g : L ⊗[K] A →+* L ⊗[K] A := AutomorphicForm.sigmaTensor K L A σ with hg
  set D : GL (Fin 2) (L ⊗[K] A) := AutomorphicForm.toTensorGL K L A (diagUnits2 a b) with hD

  have hfent : ∀ (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2),
      ((f x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
        g (((x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := fun x i j => rfl
  have hgt : ∀ (l : L) (x : A), g (l ⊗ₜ[K] x) = σ l ⊗ₜ[K] x := fun l x => rfl

  have htel : ∀ n : ℕ, δ * f (((List.range n).map fun i => (⇑f)^[i] δ).prod) =
      ((List.range n).map fun i => (⇑f)^[i] δ).prod * (⇑f)^[n] δ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
        map_mul, ← mul_assoc, ih, Function.iterate_succ_apply']

  have hσℓ : σ ^ Module.finrank K L = 1 := by
    rw [← IsGalois.card_aut_eq_finrank K L]
    exact pow_card_eq_one'
  have hgiter : ∀ (n : ℕ) (l : L) (x : A), (⇑g)^[n] (l ⊗ₜ[K] x) = ((⇑σ)^[n] l) ⊗ₜ[K] x := by
    intro n
    induction n with
    | zero => intro l x; rfl
    | succ n ih => intro l x; rw [Function.iterate_succ_apply', ih, hgt, Function.iterate_succ_apply']
  have hgℓ : ∀ z : L ⊗[K] A, (⇑g)^[Module.finrank K L] z = z := by
    intro z
    rw [← RingHom.coe_pow]
    induction z using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul l x =>
      rw [RingHom.coe_pow, hgiter, ← AlgEquiv.coe_pow, hσℓ]
      rfl
    | add x y hx hy => rw [map_add, hx, hy]
  have hfiter : ∀ (n : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2),
      (((⇑f)^[n] x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
        (⇑g)^[n] ((((x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j)) := by
    intro n
    induction n with
    | zero => intro x i j; rfl
    | succ n ih => intro x i j; rw [Function.iterate_succ_apply', hfent, ih, ← Function.iterate_succ_apply' (⇑g)]
  have hfℓ : (⇑f)^[Module.finrank K L] δ = δ :=
    Matrix.GeneralLinearGroup.ext fun i j => by rw [hfiter, hgℓ]

  have hDent : ∀ i j : Fin 2, ((D : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (1 : L) ⊗ₜ[K] (((diagUnits2 a b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j) := fun i j => rfl
  have hfD : f D = D :=
    Matrix.GeneralLinearGroup.ext fun i j => by rw [hfent, hDent, hgt, map_one]

  have hN : AutomorphicForm.normString K L A σ δ =
      ((List.range (Module.finrank K L)).map fun i => (⇑f)^[i] δ).prod := rfl
  have hcomm : δ * D = D * δ := by
    have h := htel (Module.finrank K L)
    rw [← hN, hfℓ, hδ, hfD] at h
    exact h

  have hd00 : (((diagUnits2 a b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0) = (a : A) := rfl
  have hd01 : (((diagUnits2 a b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1) = 0 := rfl
  have hd10 : (((diagUnits2 a b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0) = 0 := rfl
  have hd11 : (((diagUnits2 a b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1) = (b : A) := rfl
  set M : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := ((δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) with hM
  have hunit : IsUnit ((1 : L) ⊗ₜ[K] ((a : A) - (b : A))) := by
    have := hab.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
    simpa [Algebra.TensorProduct.includeRight_apply] using this
  have hent : ∀ i j : Fin 2, (((δ * D : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) =
      (((D * δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := fun i j => by rw [hcomm]
  have h01 : M 0 1 = 0 := by
    have h := hent 0 1
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hDent, hd00, hd01, hd10, hd11,
      TensorProduct.tmul_zero, mul_zero, zero_mul, add_zero, zero_add] at h

    have h' : M 0 1 * ((1 : L) ⊗ₜ[K] ((a : A) - (b : A))) = 0 := by
      rw [TensorProduct.tmul_sub, mul_sub, sub_eq_zero, mul_comm (M 0 1) ((1 : L) ⊗ₜ[K] (a : A))]
      exact h.symm
    exact (hunit.mul_left_eq_zero).1 h'
  have h10 : M 1 0 = 0 := by
    have h := hent 1 0
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hDent, hd00, hd01, hd10, hd11,
      TensorProduct.tmul_zero, mul_zero, zero_mul, add_zero, zero_add] at h

    have h' : M 1 0 * ((1 : L) ⊗ₜ[K] ((a : A) - (b : A))) = 0 := by
      rw [TensorProduct.tmul_sub, mul_sub, sub_eq_zero, mul_comm (M 1 0) ((1 : L) ⊗ₜ[K] (b : A))]
      exact h
    exact (hunit.mul_left_eq_zero).1 h'
  have hdet : IsUnit (M 0 0 * M 1 1) := by
    have hu : IsUnit M.det := by
      rw [hM]
      exact (Matrix.GeneralLinearGroup.det δ).isUnit
    rw [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hu
    exact hu
  obtain ⟨hα, hβ⟩ := IsUnit.mul_iff.1 hdet
  refine ⟨hα.unit, hβ.unit, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
  fin_cases i <;> fin_cases j
  · exact (hα.unit_spec).symm
  · exact h01
  · exact h10
  · exact (hβ.unit_spec).symm

end S_AutomorphicForm_exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2
end P2MW
export P2MW.S_AutomorphicForm_exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2 (solution)
