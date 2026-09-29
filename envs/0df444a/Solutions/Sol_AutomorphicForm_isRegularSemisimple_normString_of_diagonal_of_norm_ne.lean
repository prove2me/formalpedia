-- Prove2me | solution 1 for AutomorphicForm.isRegularSemisimple_normString_of_diagonal_of_norm_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/fb1c5bd3-92be-5e32-b021-0a43696f0b14

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_congr_apply_of_isGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isRegularSemisimple_normString_of_diagonal_of_norm_ne

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

namespace C0NS

section Generic

variable {R : Type} [CommRing R] (s : R →+* R)

theorem iterate_map_apply (i : ℕ) (g : GL (Fin 2) R) (p q : Fin 2) :
    ((((⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) s))^[i]) g : GL (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R) p q =
      ((⇑s)^[i]) ((g : Matrix (Fin 2) (Fin 2) R) p q) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih,
      Matrix.GeneralLinearGroup.map_apply]

omit s in
theorem list_prod_diag (l : List (GL (Fin 2) R))
    (hl : ∀ g ∈ l, (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) :
    ((l.prod : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
    ((l.prod : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧
    ((l.prod : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 =
      (l.map fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 0 0).prod ∧
    ((l.prod : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 =
      (l.map fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 1 1).prod := by
  induction l with
  | nil => simp
  | cons g l ih =>
    obtain ⟨h10, h01⟩ := hl g List.mem_cons_self
    obtain ⟨i10, i01, i00, i11⟩ := ih (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg'))
    simp only [List.prod_cons, List.map_cons, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      h10, h01, i10, i01, i00, i11, mul_zero, zero_mul, add_zero, zero_add, and_self]

theorem list_prod_range {M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

end Generic

section Sigma

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaTensor_iterate_eq_congr (i : ℕ) (x : L ⊗[K] A) :
    ((⇑(AutomorphicForm.sigmaTensor K L A σ))^[i]) x =
      Algebra.TensorProduct.congr (σ ^ i) (AlgEquiv.refl : A ≃ₐ[K] A) x := by
  induction i generalizing x with
  | zero =>
    rw [Function.iterate_zero, pow_zero]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a => rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, ← hx, ← hy]; rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      show Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) (_ ⊗ₜ _) = _
      rw [Algebra.TensorProduct.map_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

variable [FiniteDimensional K L] [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
include hgen

theorem prod_range_pow_eq_prod_univ {M : Type} [CommMonoid M] (f : (L ≃ₐ[K] L) → M) :
    ∏ i ∈ Finset.range (Module.finrank K L), f (σ ^ i) = ∏ τ : L ≃ₐ[K] L, f τ := by
  have hord : orderOf σ = Nat.card (L ≃ₐ[K] L) := orderOf_eq_card_of_forall_mem_zpowers hgen
  have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  rw [← hcard, ← hord, Finset.prod_range (fun i => f (σ ^ i))]
  have hinj : Function.Injective (fun i : Fin (orderOf σ) => σ ^ (i : ℕ)) := by
    intro i j h
    exact Fin.ext (pow_injOn_Iio_orderOf (by simp) (by simp) h)
  have hbij : Function.Bijective (fun i : Fin (orderOf σ) => σ ^ (i : ℕ)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, by rw [Fintype.card_fin, hord, Nat.card_eq_fintype_card]⟩
  exact hbij.prod_comp f

end Sigma

end C0NS

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0)
    (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0)
    (hN : Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) ≠
        Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ) := by
  classical

  set A := v.adicCompletion K with hA
  set P : L ⊗[K] v.adicCompletion K → L ⊗[K] v.adicCompletion K :=
    fun y => ∏ i ∈ Finset.range (Module.finrank K L),
      ((⇑(AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ))^[i]) y with hP

  have hPnorm : ∀ y : L ⊗[K] v.adicCompletion K,
      P y = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (Algebra.norm (v.adicCompletion K) y) := by
    intro y
    simp only [hP]
    rw [Algebra.TensorProduct.algebraMap_norm_eq_prod_congr_apply_of_isGalois K L (v.adicCompletion K) y,
      ← C0NS.prod_range_pow_eq_prod_univ K L σ hgen
        (fun τ => Algebra.TensorProduct.congr τ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K) y)]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact C0NS.sigmaTensor_iterate_eq_congr K L (v.adicCompletion K) σ i y

  have hdiag : ∀ g ∈ (List.range (Module.finrank K L)).map
      (fun i => ((⇑(Matrix.GeneralLinearGroup.map (n := Fin 2)
        (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)))^[i]) δ),
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 := by
    intro g hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
    refine ⟨?_, ?_⟩
    · rw [C0NS.iterate_map_apply, h10, ← RingHom.coe_pow, map_zero]
    · rw [C0NS.iterate_map_apply, h01, ← RingHom.coe_pow, map_zero]
  obtain ⟨p10, p01, p00, p11⟩ := C0NS.list_prod_diag _ hdiag
  rw [List.map_map] at p00 p11
  have hN00 : ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
      GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0 =
      P ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) := by
    unfold AutomorphicForm.normString AutomorphicForm.sigmaGL
    rw [p00, C0NS.list_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp_apply]
    rw [C0NS.iterate_map_apply]
  have hN11 : ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
      GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1 =
      P ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) := by
    unfold AutomorphicForm.normString AutomorphicForm.sigmaGL
    rw [p11, C0NS.list_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp_apply]
    rw [C0NS.iterate_map_apply]
  have hN10 : ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
      GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 := by
    unfold AutomorphicForm.normString AutomorphicForm.sigmaGL; exact p10
  have hN01 : ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
      GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 := by
    unfold AutomorphicForm.normString AutomorphicForm.sigmaGL; exact p01

  set n0 := Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) with hn0
  set n1 := Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) with hn1
  unfold AutomorphicForm.IsRegularSemisimple
  rw [Matrix.trace_fin_two, Matrix.det_fin_two, hN00, hN11, hN10, hN01, hPnorm, hPnorm]
  have key : ∀ (R : Type) [CommRing R] (a b : R), (a + b) ^ 2 - 4 * (a * b - 0 * 0) = (a - b) ^ 2 := by
    intro R _ a b; ring
  rw [key, ← map_sub, ← map_pow]
  exact ((pow_ne_zero 2 (sub_ne_zero.mpr hN)).isUnit).map _

#print axioms solution

end S_AutomorphicForm_isRegularSemisimple_normString_of_diagonal_of_norm_ne
end P2MW
export P2MW.S_AutomorphicForm_isRegularSemisimple_normString_of_diagonal_of_norm_ne (solution)
