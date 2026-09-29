-- Prove2me | solution 1 for AutomorphicForm.isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/4b674e3e-4f1b-5d76-b847-e24ed2bcbed1

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

namespace K42REG

open scoped TensorProduct

section Generic

variable {R : Type*} [CommRing R] (s : R →+* R)

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

theorem list_prod_range {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

end Generic

variable (K L : Type) [Field K] [Field L] [Algebra K L]

theorem sigmaTensor_iterate_tmul_one (σ : L ≃ₐ[K] L) (A : Type) [CommRing A] [Algebra K A]
    (i : ℕ) (l : L) :
    ((⇑(AutomorphicForm.sigmaTensor K L A σ))^[i]) (l ⊗ₜ[K] (1 : A)) = ((σ ^ i) l) ⊗ₜ[K] (1 : A) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', AlgEquiv.mul_apply]
    show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)) (_ ⊗ₜ _) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl

theorem prod_pow_apply_eq_norm [FiniteDimensional K L] [IsGalois K L] (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (x : L) :
    ∏ i ∈ Finset.range (Module.finrank K L), (σ ^ i) x = algebraMap K L (Algebra.norm K x) := by
  rw [Algebra.norm_eq_prod_automorphisms]
  have hord : orderOf σ = Nat.card (L ≃ₐ[K] L) := orderOf_eq_card_of_forall_mem_zpowers hgen
  have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  rw [← hcard, ← hord, Finset.prod_range (fun i => (σ ^ i) x)]
  have hinj : Function.Injective (fun i : Fin (orderOf σ) => σ ^ (i : ℕ)) := by
    intro i j h
    exact Fin.ext (pow_injOn_Iio_orderOf (by simp) (by simp) h)
  have hbij : Function.Bijective (fun i : Fin (orderOf σ) => σ ^ (i : ℕ)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, by rw [Fintype.card_fin, hord, Nat.card_eq_fintype_card]⟩
  exact hbij.prod_comp (fun τ : L ≃ₐ[K] L => τ x)

end K42REG

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ) := by

  have hent : ∀ i j : Fin 2, (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) i j =
      ((t : Matrix (Fin 2) (Fin 2) L) i j) ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K) := by
    intro i j
    have h := congrArg
      (fun g : GL (Fin 2) (AdeleRing (𝓞 L) L) => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) hδ
    change AutomorphicForm.baseChangeEquiv K L ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) i j) =
      algebraMap L (AdeleRing (𝓞 L) L) ((t : Matrix (Fin 2) (Fin 2) L) i j) at h
    rw [← AutomorphicForm.baseChangeEquiv_tmul_one K L] at h
    exact (AutomorphicForm.baseChangeEquiv K L).injective h

  have hdet := Matrix.GeneralLinearGroup.det_ne_zero t
  rw [Matrix.det_fin_two, ht₁, mul_zero, sub_zero] at hdet
  have ha : (t : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hb : (t : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have hne : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) := by
    intro heq
    apply hreg
    have hmul : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) *
        Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) := by
      rw [← map_mul, div_mul_cancel₀ _ hb, heq]
    exact (mul_left_eq_self₀.mp hmul).resolve_right (Algebra.norm_ne_zero_iff.mpr hb)

  rw [AutomorphicForm.isRegularSemisimple_iff]
  unfold AutomorphicForm.normString AutomorphicForm.sigmaGL
  have hdiag : ∀ g ∈ (List.range (Module.finrank K L)).map
      (fun i => ((⇑(Matrix.GeneralLinearGroup.map (n := Fin 2)
        (AutomorphicForm.sigmaTensor K L (AdeleRing (𝓞 K) K) σ)))^[i]) δ),
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 0 1 = 0 := by
    intro g hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
    refine ⟨?_, ?_⟩
    · rw [K42REG.iterate_map_apply, hent, ht₁, TensorProduct.zero_tmul, ← RingHom.coe_pow, map_zero]
    · rw [K42REG.iterate_map_apply, hent, ht₂, TensorProduct.zero_tmul, ← RingHom.coe_pow, map_zero]
  obtain ⟨p10, p01, p00, p11⟩ := K42REG.list_prod_diag _ hdiag
  set ι : L →+* L ⊗[K] AdeleRing (𝓞 K) K := Algebra.TensorProduct.includeLeftRingHom with hι
  have hιapp : ∀ l : L, ι l = l ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K) := fun l => rfl
  have hentry : ∀ p : Fin 2,
      ((List.range (Module.finrank K L)).map
        ((fun g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) => (g : Matrix (Fin 2) (Fin 2) _) p p) ∘
        (fun i => ((⇑(Matrix.GeneralLinearGroup.map (n := Fin 2)
          (AutomorphicForm.sigmaTensor K L (AdeleRing (𝓞 K) K) σ)))^[i]) δ))).prod =
      ι (algebraMap K L (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) p p))) := by
    intro p
    rw [K42REG.list_prod_range, ← K42REG.prod_pow_apply_eq_norm K L σ hgen, map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [Function.comp_apply]
    rw [K42REG.iterate_map_apply, hent, K42REG.sigmaTensor_iterate_tmul_one, hιapp]
  rw [List.map_map] at p00 p11
  rw [Matrix.trace_fin_two, Matrix.det_fin_two, p10, p01, p00, p11, hentry 0, hentry 1]
  have key : (ι (algebraMap K L (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0))) +
        ι (algebraMap K L (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)))) ^ 2 -
      4 * (ι (algebraMap K L (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0))) *
        ι (algebraMap K L (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1))) - 0 * 0) =
      (ι (algebraMap K L (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) -
        Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)))) ^ 2 := by
    rw [map_sub, map_sub]
    ring
  rw [key]
  exact ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)).map (algebraMap K L)).map ι |>.pow 2

end S_AutomorphicForm_isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one
end P2MW
export P2MW.S_AutomorphicForm_isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one (solution)
