-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairCocycle
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairCocycle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:42.882943+00:00
-- url     : https://prove2.me/theorems/344080f0-70f2-4288-918c-b4f4bdab992f
-- title:
--   PPair Cocycle
-- statement:
--   Definitions and structural lemmas for PPair Cocycle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorsCommute
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
section PolyValues
variable {K : Type*} {σ τ : Type*}
def polyVal (A : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) : ℤ :=
  ∑ μ ∈ H.support, H.coeff μ * A (classList cls μ)
theorem polyVal_eq_sum_of_subset (A : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ}
    {S : Finset (σ →₀ ℕ)} (h : H.support ⊆ S) :
    polyVal A cls H = ∑ μ ∈ S, H.coeff μ * A (classList cls μ) :=
  Finset.sum_subset h fun μ _ hμ => by rw [notMem_support_iff.mp hμ, zero_mul]
theorem polyVal_add (A : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) (H₁ H₂ : MvPolynomial σ ℤ) :
    polyVal A cls (H₁ + H₂) = polyVal A cls H₁ + polyVal A cls H₂ := by
  classical
  rw [polyVal_eq_sum_of_subset A cls (S := H₁.support ∪ H₂.support) support_add,
    polyVal_eq_sum_of_subset A cls (S := H₁.support ∪ H₂.support) Finset.subset_union_left,
    polyVal_eq_sum_of_subset A cls (S := H₁.support ∪ H₂.support) Finset.subset_union_right]
  simp only [coeff_add, add_mul, Finset.sum_add_distrib]
def polyValHom (A : List (K → ℤ) → ℤ) (cls : σ → K → ℤ) : MvPolynomial σ ℤ →+ ℤ where
  toFun := polyVal A cls
  map_zero' := by simp [polyVal]
  map_add' := polyVal_add A cls
def PermInv (A : List (K → ℤ) → ℤ) : Prop := ∀ l l' : List (K → ℤ), l.Perm l' → A l = A l'
def HeadAdd (A : List (K → ℤ) → ℤ) : Prop :=
  ∀ (u v : K → ℤ) (l : List (K → ℤ)), A ((u + v) :: l) = A (u :: l) + A (v :: l)
end PolyValues
section Geometric
variable {R : Type*} [CommRing R]
def geoSum (k : ℕ) (p q : R) : R := ∑ j ∈ Finset.range k, p ^ j * q ^ (k - 1 - j)
def geoSum3 : ℕ → R → R → R → R
  | 0, _, _, _ => 0
  | k + 1, a, b, c => c * geoSum3 k a b c + geoSum k a b
end Geometric
section Triangle
variable {K : Type*}
def geoVal (A : List (K → ℤ) → ℤ) (k : ℕ) (u v : K → ℤ) : ℤ :=
  polyVal A ![u, v] (geoSum k (X 0) (X 1) : MvPolynomial (Fin 2) ℤ)
end Triangle
section CycleSums
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
end CycleSums
section Models
universe u
variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def listNum (W : Ideal (MRing ι O)) (Q : List (K → ℤ)) (d : ℕ) (l : List (K → ℤ)) : ℤ :=
  if l.length + Q.length = d then vNumL W (l ++ Q) else 0
variable [Fintype K] [∀ k, Fintype (ι k)]
end Models
section Flags
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
  {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
end Flags
end
end GroundTheory.Heights₂.Heights.NumbersDVR


