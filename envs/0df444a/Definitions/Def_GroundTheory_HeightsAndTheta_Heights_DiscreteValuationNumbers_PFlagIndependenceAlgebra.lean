-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:57.020994+00:00
-- url     : https://prove2.me/theorems/9c66b748-b272-4bca-a3e8-0feae6f2f076
-- title:
--   PFlag Independence Algebra
-- statement:
--   Definitions and structural lemmas for PFlag Independence Algebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
section Finiteness
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
  [IsNoetherianRing R]
theorem divCycle_finite_support (P : Ideal (MRing ι R)) (f : MRing ι R) :
    (Function.support (divCycle P f)).Finite := by
  refine ((P ⊔ Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing).subset ?_
  intro W hW
  by_contra h
  rw [Function.mem_support] at hW
  unfold divCycle at hW
  rw [dif_neg (fun h' => h h'.1)] at hW
  exact hW rfl
theorem ratDiv_finite_support (P : Ideal (MRing ι R)) (f g : MRing ι R) :
    (Function.support (ratDiv P f g)).Finite :=
  ((divCycle_finite_support P f).union (divCycle_finite_support P g)).subset
    (Function.support_sub (divCycle P f) (divCycle P g))
end Finiteness
section CycEval
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
theorem cycEval_eq_sum {Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite)
    (n : Ideal (MRing ι R) → ℤ) : cycEval n Z = ∑ W ∈ hZ.toFinset, Z W * n W := by
  unfold cycEval
  apply finsum_eq_sum_of_support_subset
  intro W hW
  rw [Set.Finite.coe_toFinset]
  exact Function.support_mul_subset_left _ _ hW
end CycEval
section ClassNum
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
theorem classNum_eq_sum {σ : Type*} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) {S : Finset (σ →₀ ℕ)} (hS : H.support ⊆ S) :
    classNum cls H Q W = ∑ μ ∈ S, H.coeff μ * vNumL W (classList cls μ ++ Q) :=
  Finset.sum_subset hS fun μ _ hμ => by rw [notMem_support_iff.mp hμ, zero_mul]
theorem classNum_zero_poly {σ : Type*} (cls : σ → K → ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (0 : MvPolynomial σ ℤ) Q W = 0 := by
  simp [classNum]
theorem classNum_add_poly {σ : Type*} [DecidableEq σ] (cls : σ → K → ℤ) (H₁ H₂ : MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (H₁ + H₂) Q W = classNum cls H₁ Q W + classNum cls H₂ Q W := by
  rw [classNum_eq_sum cls (H₁ + H₂) Q W support_add,
    classNum_eq_sum cls H₁ Q W (S := H₁.support ∪ H₂.support) Finset.subset_union_left,
    classNum_eq_sum cls H₂ Q W (S := H₁.support ∪ H₂.support) Finset.subset_union_right]
  simp only [coeff_add, add_mul, Finset.sum_add_distrib]
def classNumAddHom {σ : Type*} [DecidableEq σ] (cls : σ → K → ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    MvPolynomial σ ℤ →+ ℤ where
  toFun H := classNum cls H Q W
  map_zero' := classNum_zero_poly cls Q W
  map_add' H₁ H₂ := classNum_add_poly cls H₁ H₂ Q W
end ClassNum
section PairNum
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def pairNumHom {n : ℕ} (P : Ideal (MRing ι O)) (x x' : Fin n → K → ℤ) (f g : Fin n → MRing ι O)
    (Q : List (K → ℤ)) : (Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) →+ ℤ where
  toFun Gs := pairNum P x x' f g Gs Q
  map_zero' := by
    unfold pairNum
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [cycEval_eq_sum (ratDiv_finite_support P (f i) (g i))]
    simp [classNum_zero_poly]
  map_add' Gs Hs := by
    unfold pairNum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [cycEval_eq_sum (ratDiv_finite_support P (f i) (g i)), Pi.add_apply, classNum_add_poly,
      mul_add, Finset.sum_add_distrib]
def pushExpansion {n n' : ℕ} (σ : Fin n → Fin n') (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) :
    Fin n' → MvPolynomial (Fin n' ⊕ Fin n') ℤ :=
  fun j => ∑ i ∈ Finset.univ.filter (fun i => σ i = j), rename (Sum.map σ σ) (Gs i)
end PairNum
section Expansions
end Expansions
end
end GroundTheory.Heights₂.Heights.NumbersDVR


