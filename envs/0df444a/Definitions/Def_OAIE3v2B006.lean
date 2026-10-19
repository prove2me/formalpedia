-- Prove2me | Definitions.Def_OAIE3v2B006
-- name    : OAIE3v2B006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:57:25.79099+00:00
-- url     : https://prove2.me/theorems/b39f13df-d302-4e25-8cfd-b8e63e4f33f1
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 7 of 311
-- statement:
--   Definitions bundle 7 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Estimates/AbsorbedSiteTests.lean`, `Estimates/ArrayFunctionalSection.lean`, `Estimates/BooleanCubeModeWitness.lean`, `Estimates/CoefficientModeLowerTerms.lean`, `Estimates/GowersWeightedDerivative.lean`, `Estimates/LinearCoefficientMap.lean`, `Estimates/LowerTriangularMinor.lean`, `Estimates/OrderedLayerSplit.lean`, `Estimates/PhysicalBaseInjection.lean`, `Estimates/PhysicalRowsSiteReconstruction.lean`, `Estimates/PrimitiveExtension.lean`, `Estimates/PrincipalCoefficientMarginal.lean`, `Estimates/QuantitativeNoninjectivity.lean`, `Estimates/RowShiftTopSymbol.lean`, `Estimates/ScalarExtensionSubstitution.lean`, `Fourier/AffineFrequencyLift.lean`, `Fourier/IntegerPeriodicTorusLift.lean`, `Fourier/QuarticBohrProgression.lean`, `Fourier/RationalBohrWidth.lean`, `Fourier/RealQuarterTorusExtension.lean`, `Fourier/RectangularGridCharacter.lean`, `Geometry/MinkowskiSecondBox.lean`, `Geometry/MinkowskiSecondBoxGlue.lean`, `Geometry/SmallBoxCutoff.lean`, `Lattices/AffineCoefficientSubspace.lean`, `Lattices/AffineOneSiteNormalizedLaw.lean`, `Lattices/AnchoredCubeResidueWidths.lean`, `Lattices/IndependentIntegerSiteDirections.lean`, `Lattices/IntegerAffineResidues.lean`, `Lattices/IntegerBoxObservedMean.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/IntegralAffineModeRemoval.lean`, `Lattices/MaskedIntegerPeriodization.lean`, `Lattices/NormalizedIntegerDual.lean`, `Lattices/SelectedResidueApproximation.lean`, `Linear/BooleanCubeCoordinateFrame.lean`, `Linear/MatrixModuleAction.lean`, `Linear/PhysicalCubeMatrix.lean`, `Linear/ProjectedBasisSpan.lean`, `Linear/RealKernelJetInverse.lean`, `Polynomial/AdaptedPolynomialSubstitution.lean`, `Polynomial/HomogenizingMonomial.lean`, `Polynomial/PolynomialKernelValues.lean`, `Polynomial/RealPolynomialEvaluationMass.lean`, `Probability/UniformSelectedCoefficientProductLaw.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem linear_site_sum {S W : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (M : (S → W) →ₗ[ℝ] ℝ) (v : S → W) :
    M v = ∑ s, M (Pi.single s (v s)) := by
  have hv : v = ∑ s, Pi.single s (v s) := by
    funext s
    simp [Pi.single_apply]
  exact (congrArg M hv).trans (map_sum M _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AbsorbedSiteTests
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def absorbedSiteTests {A S X : Type*} [Fintype A]
    (χ : A → S → X → ℂ) (test : S → X → ℂ) : S → X → ℂ :=
  fun s x => (∏ a, χ a s x) * test s x

theorem absorbedSiteTests_norm {A S X : Type*} [Fintype A]
    (χ : A → S → X → ℂ) (hχ : ∀ a s x, ‖χ a s x‖ = 1)
    (test : S → X → ℂ) (s : S) (x : X) :
    ‖absorbedSiteTests χ test s x‖ = ‖test s x‖ := by
  simp only [absorbedSiteTests, norm_mul, norm_prod, hχ, Finset.prod_const_one, one_mul]

theorem absorbedSiteTests_product {A S X : Type*} [Fintype A] [Fintype S]
    (χ : A → S → X → ℂ) (test : S → X → ℂ) (value : S → X) :
    (∏ a, ∏ s, χ a s (value s)) * (∏ s, test s (value s)) =
      ∏ s, absorbedSiteTests χ test s (value s) := by
  rw [Finset.prod_comm]
  exact (Finset.prod_mul_distrib).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixModuleAction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def matrixModuleAction {I J W : Type*} [Fintype J]
    [AddCommGroup W] [Module ℝ W] (A : Matrix I J ℝ) : (J → W) →ₗ[ℝ] (I → W) where
  toFun x i := ∑ j, A i j • x j
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm (A i j) r (x j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ArrayFunctionalSection
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def subspaceArrayFunctional {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℝ) : (I → U) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, ∑ a, frequency i a * (x i).val a
  map_add' x y := by
    simp only [Pi.add_apply, Submodule.coe_add, mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_left_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def booleanCoefficient {α R : Type*} [DecidableEq α] [CommRing R]
    (f : Finset α → R) (s : Finset α) : R :=
  ∑ t ∈ s.powerset, (-1 : R) ^ (s \ t).card * f t

theorem sum_powerset_neg_one_pow_card_ring {α R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) : (∑ t ∈ s.powerset, (-1 : R) ^ t.card) = if s = ∅ then 1 else 0 := by
  have h := congrArg (Int.castRingHom R) (Finset.sum_powerset_neg_one_pow_card (x := s))
  simpa only [map_sum, map_pow, map_neg, map_one, map_zero, apply_ite] using h

theorem boolean_interval_alternating_sum {α R : Type*} [DecidableEq α] [CommRing R]
    (s r : Finset α) (hrs : r ⊆ s) :
    (∑ t ∈ s.powerset with r ⊆ t, (-1 : R) ^ (s \ t).card) = if s = r then 1 else 0 := by
  classical
  have hsum : (∑ t ∈ s.powerset with r ⊆ t, (-1 : R) ^ (s \ t).card) =
      ∑ u ∈ (s \ r).powerset, (-1 : R) ^ u.card := by
    refine Finset.sum_bij (fun t _ => s \ t) ?_ ?_ ?_ ?_
    · intro t ht
      rcases Finset.mem_filter.mp ht with ⟨hts, hrt⟩
      rw [Finset.mem_powerset]
      intro a ha
      rcases Finset.mem_sdiff.mp ha with ⟨has, hat⟩
      exact Finset.mem_sdiff.mpr ⟨has, fun har => hat (hrt har)⟩
    · intro t ht u hu heq
      have ht' := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
      have hu' := Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
      have h := congrArg (fun v => s \ v) heq
      simpa only [Finset.sdiff_sdiff_eq_self ht', Finset.sdiff_sdiff_eq_self hu'] using h
    · intro u hu
      have hu' := Finset.mem_powerset.mp hu
      refine ⟨s \ u, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
        intro a har
        apply Finset.mem_sdiff.mpr
        refine ⟨hrs har, ?_⟩
        intro hau
        exact (Finset.mem_sdiff.mp (hu' hau)).2 har
      · exact Finset.sdiff_sdiff_eq_self (hu'.trans Finset.sdiff_subset)
    · intro t _
      rfl
  rw [hsum, sum_powerset_neg_one_pow_card_ring]
  by_cases h : s = r
  · subst s
    simp
  · have hne : s \ r ≠ ∅ := by
      intro hempty
      exact h ((Finset.sdiff_eq_empty_iff_subset.mp hempty).antisymm hrs)
    simp only [hne, h, ite_false]

theorem booleanCoefficient_monomial {α R : Type*} [DecidableEq α] [CommRing R]
    (r s : Finset α) :
    booleanCoefficient (fun t => if r ⊆ t then (1 : R) else 0) s = if s = r then 1 else 0 := by
  classical
  unfold booleanCoefficient
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  by_cases hrs : r ⊆ s
  · exact boolean_interval_alternating_sum (R := R) s r hrs
  · have hfilter : {t ∈ s.powerset | r ⊆ t} = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨hts, hrt⟩
      exact hrs (hrt.trans (Finset.mem_powerset.mp hts))
    have hne : s ≠ r := fun h => hrs (h.symm ▸ Finset.Subset.refl r)
    simp only [hfilter, Finset.sum_empty, hne, ite_false]

theorem booleanCoefficient_const_mul {α R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) (c : R) (f : Finset α → R) :
    booleanCoefficient (fun t => c * f t) s = c * booleanCoefficient f s := by
  simp only [booleanCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_add {α R : Type*} [DecidableEq α] [CommRing R]
    (f g : Finset α → R) (s : Finset α) :
    booleanCoefficient (fun t => f t + g t) s = booleanCoefficient f s + booleanCoefficient g s := by
  simp only [booleanCoefficient, mul_add, Finset.sum_add_distrib]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def polynomialLinearRow {σ R : Type*} [CommRing R]
    (P : MvPolynomial σ R) (i : σ) : R := P.coeff (Finsupp.single i 1)

noncomputable def rowPolynomial {σ R : Type*} [Fintype σ] [CommRing R]
    (a : σ → R) : MvPolynomial σ R := ∑ i, C (a i) * X i

theorem homogeneous_eq_rowPolynomial {σ R : Type*} [Fintype σ] [CommRing R]
    (P : MvPolynomial σ R) (hP : P.IsHomogeneous 1) :
    P = rowPolynomial (polynomialLinearRow P) := by
  have hp : P ∈ Submodule.span R (Set.range (X : σ → MvPolynomial σ R)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hP
  clear hP
  induction hp using Submodule.span_induction with
  | mem P hp =>
    obtain ⟨v, rfl⟩ := hp
    have hs (i : σ) : (Finsupp.single v 1 : σ →₀ ℕ) = Finsupp.single i 1 ↔ v = i :=
      (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)).eq_iff
    simp only [rowPolynomial, polynomialLinearRow, coeff_X, hs, apply_ite, map_one,
      map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  | zero => simp [rowPolynomial, polynomialLinearRow]
  | add P Q _ _ hP hQ =>
    simpa only [rowPolynomial, polynomialLinearRow, MvPolynomial.coeff_add,
      Finsupp.add_apply, map_add, add_mul,
      Finset.sum_add_distrib] using congrArg₂ (fun a b => a + b) hP hQ
  | smul a P _ hP =>
    simpa only [rowPolynomial, polynomialLinearRow, coeff_smul, coeff_C_mul, smul_eq_mul, map_mul,
      smul_eq_C_mul, Finset.mul_sum, mul_assoc] using congrArg (fun Q => a • Q) hP

theorem rowPolynomial_eval {σ R : Type*} [Fintype σ] [CommRing R] (a x : σ → R) :
    eval x (rowPolynomial a) = ∑ i, a i * x i := by
  simp only [rowPolynomial, map_sum, map_mul, eval_C, eval_X]

theorem homogeneous_eval_eq_row {σ R : Type*} [Fintype σ] [CommRing R]
    (P : MvPolynomial σ R) (hP : P.IsHomogeneous 1) (x : σ → R) :
    eval x P = ∑ i, polynomialLinearRow P i * x i := by
  conv_lhs => rw [homogeneous_eq_rowPolynomial P hP]
  rw [rowPolynomial_eval]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

noncomputable def coefficientLinear (s : Finset α) : (Finset α → R) →ₗ[R] R where
  toFun f := booleanCoefficient f s
  map_add' f g := booleanCoefficient_add f g s
  map_smul' a f := booleanCoefficient_const_mul s a f

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerTriangularMinor
namespace OAI

section

namespace Erdos3

theorem exists_nonzero_row_minor {K ι : Type*} [Field K] [Fintype ι] {k : ℕ}
    (A : Matrix ι (Fin k) K) (hA : LinearIndependent K A.col) :
    ∃ p : Fin k → ι, (A.submatrix p id).det ≠ 0 := by
  classical
  have ht : LinearIndependent K A.transpose.row := hA
  have hr : Module.finrank K (Submodule.span K (Set.range A.row)) = k := by
    rw [← A.rank_eq_finrank_span_row, ← Matrix.rank_transpose]
    simpa only [Fintype.card_fin] using ht.rank_matrix
  have hex := Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.row)
  rw [hr] at hex
  obtain ⟨v, hv, _, hli⟩ := hex
  choose p hp using hv
  have he : (A.submatrix p id).row = v := by
    funext i
    exact hp i
  have hind : LinearIndependent K (A.submatrix p id).row := he.symm ▸ hli
  exact ⟨p, ((A.submatrix p id).isUnit_iff_isUnit_det.mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hind)).ne_zero⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BooleanCubeCoordinateFrame
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α K R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

noncomputable def affineSite (root : K → R) (difference : α → K → R)
    (s : Finset α) : Option K → R
  | none => 1
  | some k => root k + ∑ i ∈ s, difference i k

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem polynomialFunctional_expansion {σ R : Type*} [CommRing R]
    (L : MvPolynomial σ R →ₗ[R] R) (P : MvPolynomial σ R) :
    L P = ∑ d ∈ P.support, P.coeff d * L (monomial d 1) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  have he : monomial d (P.coeff d) = P.coeff d • monomial d (1 : R) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [he, map_smul, smul_eq_mul]

theorem polynomialFunctional_map_expansion {σ R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (L : MvPolynomial σ S →ₗ[S] S) (P : MvPolynomial σ R) :
    L (map ρ P) = ∑ d ∈ P.support, ρ (P.coeff d) * L (monomial d 1) := by
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, map_monomial]
  apply Finset.sum_congr rfl
  intro d _
  have he : monomial d (ρ (P.coeff d)) = ρ (P.coeff d) • monomial d (1 : S) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [he, map_smul, smul_eq_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_substitution_totalDegree_le {I J : Type*}
    (p : MvPolynomial I ℝ) (f : I → MvPolynomial J ℝ) {e d : ℕ}
    (hf : ∀ i, (f i).totalDegree ≤ e) (hd : p.totalDegree ≤ d) :
    (MvPolynomial.eval₂Hom MvPolynomial.C f p).totalDegree ≤ d * e := by
  classical
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  calc
    _ ≤ ∑ i ∈ m.support, (f i ^ m i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ m.support, m i * e := Finset.sum_le_sum (fun i _ =>
      (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i)))
    _ = (m.sum fun _ n => n) * e := by rw [← Finset.sum_mul]; rfl
    _ ≤ d * e := Nat.mul_le_mul_right _ ((MvPolynomial.le_totalDegree hm).trans hd)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineResidues
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerAffineCube {α K : Type*} (root : K → ℤ) (difference : α → K → ℤ)
    (t : Finset α) : K → ℤ := fun k => root k + ∑ r ∈ t, difference r k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealKernelJetInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def realDifferencePivot {α K : Type*} (difference : α → K → ℝ)
    (selection : α → K) : Matrix α α ℝ := fun i j => difference i (selection j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedIntegerDual
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

noncomputable def homogeneousDual {I K R : Type*} [Fintype I] [CommRing R]
    (root : K → R) (selection : I → K) (n : I → R) : MvPolynomial (Option K) R :=
  ∑ j, C (n j) * (X (some (selection j)) - C (root (selection j)) * X none)

theorem homogeneousDual_homogeneous {I K R : Type*} [Fintype I] [CommRing R]
    (root : K → R) (selection : I → K) (n : I → R) :
    (homogeneousDual root selection n).IsHomogeneous 1 := by
  exact IsHomogeneous.sum _ _ _ (fun j _ =>
    ((isHomogeneous_X R _).sub ((isHomogeneous_X R _).C_mul (root (selection j)))).C_mul (n j))

theorem homogeneousDual_eval {α I K R : Type*} [Fintype I] [CommRing R]
    (root : K → R) (difference : α → K → R) (selection : I → K) (n : I → R)
    (s : Finset α) :
    eval (affineSite root difference s) (homogeneousDual root selection n) =
      ∑ i ∈ s, ∑ j, n j * difference i (selection j) := by
  simp only [homogeneousDual, map_sum, map_mul, map_sub, eval_C, eval_X,
    affineSite, mul_one, add_sub_cancel_left, Finset.mul_sum]
  exact Finset.sum_comm

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem affineSite_map {α K R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (difference : α → K → R) (s : Finset α) :
    affineSite (fun k => ρ (root k)) (fun i k => ρ (difference i k)) s = ρ ∘ affineSite root difference s := by
  funext v
  cases v <;> simp [affineSite]

theorem affineSite_eval_map {α K R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (difference : α → K → R) (s : Finset α)
    (P : MvPolynomial (Option K) R) :
    eval (affineSite (fun k => ρ (root k)) (fun i k => ρ (difference i k)) s) (map ρ P) =
      ρ (eval (affineSite root difference s) P) := by
  rw [affineSite_map]
  exact (map_eval ρ _ P).symm

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

def integerDifferencePivot {α K : Type*} (difference : α → K → ℤ) (selection : α → K) :
    Matrix α α ℤ := fun i j => difference i (selection j)

theorem integerDifferencePivot_adjugate_dual {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) (i s : α) :
    (∑ j, (integerDifferencePivot difference selection).adjugate j i * difference s (selection j)) =
      if i = s then (integerDifferencePivot difference selection).det else 0 := by
  have he := congrFun (congrFun (Matrix.mul_adjugate (integerDifferencePivot difference selection)) s) i
  simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, integerDifferencePivot, mul_comm, eq_comm] using he

noncomputable def integerPivotNumerator {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K) (i : α) :
    MvPolynomial (Option K) ℤ :=
  homogeneousDual root selection (fun j => (integerDifferencePivot difference selection).adjugate j i)

theorem integerPivotNumerator_homogeneous {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K) (i : α) :
    (integerPivotNumerator root difference selection i).IsHomogeneous 1 :=
  homogeneousDual_homogeneous root selection _

theorem integerPivotNumerator_eval {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K) (i : α) (s : Finset α) :
    eval (affineSite root difference s) (integerPivotNumerator root difference selection i) =
      if i ∈ s then (integerDifferencePivot difference selection).det else 0 := by
  rw [integerPivotNumerator, homogeneousDual_eval]
  simp only [integerDifferencePivot_adjugate_dual, Finset.sum_ite_eq]

theorem integerDifferencePivot_det_cast {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) :
    ((integerDifferencePivot difference selection).det : ℝ) =
      (realDifferencePivot (fun i k => (difference i k : ℝ)) selection).det :=
  (Int.castRingHom ℝ).map_det _

theorem integerDifferencePivot_adjugate_cast {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) (i j : α) :
    ((integerDifferencePivot difference selection).adjugate i j : ℝ) =
      (realDifferencePivot (fun i k => (difference i k : ℝ)) selection).adjugate i j := by
  exact congrFun (congrFun ((Int.castRingHom ℝ).map_adjugate (integerDifferencePivot difference selection)) i) j

theorem homogeneousDual_map {I K R S : Type*} [Fintype I] [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (selection : I → K) (n : I → R) :
    map ρ (homogeneousDual root selection n) =
      homogeneousDual (fun k => ρ (root k)) selection (fun i => ρ (n i)) := by
  simp only [homogeneousDual, map_sum, map_mul, map_sub, map_C, map_X]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

noncomputable def normalizedIntegerDual {α K : Type*} (a : ℤ)
    (numerator : α → MvPolynomial (Option K) ℤ) (i : α) : MvPolynomial (Option K) ℝ :=
  (a : ℝ)⁻¹ • map (Int.castRingHom ℝ) (numerator i)

theorem normalizedIntegerDual_clear {α K : Type*} (a : ℤ) (ha : a ≠ 0)
    (numerator : α → MvPolynomial (Option K) ℤ) (i : α) :
    map (Int.castRingHom ℝ) (numerator i) = C (a : ℝ) * normalizedIntegerDual a numerator i := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  rw [← smul_eq_C_mul, normalizedIntegerDual, smul_smul, mul_inv_cancel₀ ha', one_smul]

theorem normalizedIntegerDual_boolean {α K : Type*} [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (a : ℤ) (ha : a ≠ 0)
    (numerator : α → MvPolynomial (Option K) ℤ)
    (hn : ∀ i s, eval (affineSite root difference s) (numerator i) = if i ∈ s then a else 0)
    (i : α) (s : Finset α) :
    eval (affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s)
      (normalizedIntegerDual a numerator i) = if i ∈ s then 1 else 0 := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have he := affineSite_eval_map (Int.castRingHom ℝ) root difference s (numerator i)
  simp only [Int.coe_castRingHom] at he
  rw [normalizedIntegerDual, smul_eval, he, hn]
  by_cases hi : i ∈ s <;> simp [hi, ha']

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegralAffineModeRemoval
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

def integerFormMassBound (n : ℕ) (H D A B : ℝ) : ℝ := A * (2 + H) + ((n : ℝ) * D + 1) * B

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GowersWeightedDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def derivativeSupport (Q : Finset H) (h : H) : Finset H :=
  Q.filter (fun x ↦ x + h ∈ Q)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

variable {σ R W Z : Type*} [CommRing R] [AddCommGroup W] [Module R W]
  [AddCommGroup Z] [Module R Z]

noncomputable def siteFunctional {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → R) →ₗ[R] (W →ₗ[R] R)) : (ι → W) →ₗ[R] R :=
  ∑ i, (L (Pi.single i 1)).comp (LinearMap.proj i)

theorem siteFunctional_tmul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → R) →ₗ[R] (W →ₗ[R] R)) (z : ι → R) (w : W) :
    siteFunctional L (fun i => z i • w) = L z w := by
  have hz : z = ∑ i, z i • Pi.single i (1 : R) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [hz]
  simp only [siteFunctional, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

theorem linearFunctional_eq_coordinate_sum {J R : Type*} [Fintype J] [CommRing R]
    (L : (J → R) →ₗ[R] R) (w : J → R) :
    L w = ∑ j, L (Pi.single j 1) * w j := by
  have hw : w = ∑ j, w j • Pi.single j (1 : R) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hw]
  simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped TensorProduct Classical

def integerCubeWitnessBound (q : ℕ) (H D : ℝ) : ℝ :=
  integerFormMassBound q H D ((q.factorial : ℝ) * D ^ q)
    ((q : ℝ) * (((q.factorial : ℝ) * D ^ (q - 1)) * (1 + H)))

theorem integerCubeWitnessBound_nonneg (q : ℕ) {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) :
    0 ≤ integerCubeWitnessBound q H D := by
  unfold integerCubeWitnessBound integerFormMassBound
  positivity

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IndependentIntegerSiteDirections
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem integer_difference_exists_pivot {K : Type*} [Fintype K] {q : ℕ}
    (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ))) :
    ∃ selection : Fin q → K, (integerDifferencePivot difference selection).det ≠ 0 := by
  let A : Matrix K (Fin q) ℝ := fun k i => difference i k
  obtain ⟨selection, hdet⟩ := exists_nonzero_row_minor A hlin
  have he : A.submatrix selection id = (realDifferencePivot
      (fun i k => (difference i k : ℝ)) selection).transpose := rfl
  rw [he, Matrix.det_transpose, ← integerDifferencePivot_det_cast] at hdet
  exact ⟨selection, fun hz => hdet (by rw [hz, Int.cast_zero])⟩

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OrderedLayerSplit
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_subtype_gt {A M : Type*} [Fintype A] [LinearOrder A] [AddCommMonoid M]
    (i : A) (f : A → M) :
    (∑ j : {j : A // i < j}, f j.val) = ∑ j, if i < j then f j else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

theorem sum_split_at_layer {A M : Type*} [Fintype A] [LinearOrder A] [AddCommMonoid M]
    (i : A) (f : A → M) :
    (∑ j, f j) = f i + (∑ j, if j < i then f j else 0) +
      ∑ j : {j : A // i < j}, f j.val := by
  classical
  rw [sum_subtype_gt]
  have he (j : A) : f j =
      (if j = i then f j else 0) + (if j < i then f j else 0) +
        (if i < j then f j else 0) := by
    rcases lt_trichotomy j i with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  conv_lhs => arg 2; ext j; rw [he j]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem exists_highest_exceptional_layer {A : Type*} [Fintype A] [LinearOrder A]
    (good : A → Prop) (hbad : ∃ i, ¬good i) :
    ∃ i, ¬good i ∧ ∀ j, i < j → good j := by
  classical
  let bad := Finset.univ.filter (fun i => ¬good i)
  have hne : bad.Nonempty := by
    obtain ⟨i, hi⟩ := hbad
    exact ⟨i, by simp [bad, hi]⟩
  refine ⟨bad.max' hne, (Finset.mem_filter.mp (Finset.max'_mem bad hne)).2, ?_⟩
  intro j hj
  by_contra hn
  have hm : j ∈ bad := by simp [bad, hn]
  exact (not_le_of_gt hj) (Finset.le_max' bad j hm)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearCoefficientMap
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def mapPolynomialCoefficients {I R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (L : S →ₗ[R] R) (P : MvPolynomial I S) : MvPolynomial I R :=
  ∑ d ∈ P.support, monomial d (L (P.coeff d))

theorem mapPolynomialCoefficients_degree {I R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (L : S →ₗ[R] R) (P : MvPolynomial I S) :
    (mapPolynomialCoefficients L P).totalDegree ≤ P.totalDegree := by
  unfold mapPolynomialCoefficients
  apply totalDegree_finsetSum_le
  intro d hd
  exact (totalDegree_monomial_le d _).trans (le_totalDegree hd)

theorem mapPolynomialCoefficients_eval {I R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (L : S →ₗ[R] R) (P : MvPolynomial I S) (x : I → R) :
    eval x (mapPolynomialCoefficients L P) = L (eval (fun i => algebraMap R S (x i)) P) := by
  unfold mapPolynomialCoefficients
  rw [map_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro d _
  have he : P.coeff d * d.prod (fun i n => (algebraMap R S) (x i) ^ n) =
      (d.prod (fun i n => x i ^ n)) • P.coeff d := by
    simp only [Finsupp.prod, Algebra.smul_def, map_prod, map_pow]
    exact mul_comm _ _
  rw [he, map_smul, smul_eq_mul, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarExtensionSubstitution
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem aeval_polynomial_totalDegree_le {I J R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (P : MvPolynomial I R) (f : I → MvPolynomial J S) {d e : ℕ}
    (hP : P.totalDegree ≤ d) (hf : ∀ i, (f i).totalDegree ≤ e) :
    (aeval f P).totalDegree ≤ d * e := by
  rw [aeval_def, eval₂_eq]
  apply totalDegree_finsetSum_le
  intro a ha
  apply (totalDegree_mul _ _).trans
  simp only [MvPolynomial.algebraMap_apply, totalDegree_C, zero_add]
  calc
    _ ≤ ∑ i ∈ a.support, (f i ^ a i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ a.support, a i * e := Finset.sum_le_sum (fun i _ =>
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i)))
    _ = (a.sum fun _ n => n) * e := by rw [← Finset.sum_mul]; rfl
    _ ≤ d * e := Nat.mul_le_mul_right _ ((le_totalDegree ha).trans hP)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialKernelValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def integerRowLinear {J : Type*} [Fintype J] (a : J → ℤ) :
    (J → ℝ) →ₗ[ℝ] ℝ := ∑ j, (a j : ℝ) • LinearMap.proj j

theorem integerRowLinear_apply {J : Type*} [Fintype J] (a : J → ℤ) (w : J → ℝ) :
    integerRowLinear a w = ∑ j, (a j : ℝ) * w j := by
  simp [integerRowLinear]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def parameterLinearCoordinate {I K : Type*} [Fintype K] (j : I) :
    MvPolynomial (K × I) (MvPolynomial K ℝ) := ∑ k, C (X k) * X (k, j)

noncomputable def parameterPolynomialPullback {I K : Type*} [Fintype K] :
    MvPolynomial I ℝ →ₐ[ℝ] MvPolynomial (K × I) (MvPolynomial K ℝ) :=
  aeval parameterLinearCoordinate

theorem parameterPolynomialPullback_degree {I K : Type*} [Fintype K]
    (P : MvPolynomial I ℝ) {d : ℕ} (hP : P.totalDegree ≤ d) :
    (parameterPolynomialPullback (K := K) P).totalDegree ≤ d := by
  have hc (j : I) : (parameterLinearCoordinate (K := K) j).totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro k _
    exact (totalDegree_mul _ _).trans (by simp)
  simpa only [parameterPolynomialPullback, Nat.mul_one] using
    aeval_polynomial_totalDegree_le P parameterLinearCoordinate hP hc

theorem parameterPolynomialPullback_eval {I K : Type*} [Fintype K]
    (P : MvPolynomial I ℝ) (v : K → I → ℝ) :
    eval (fun z => C (v z.1 z.2)) (parameterPolynomialPullback P) =
      aeval (fun j => rowPolynomial (fun k => v k j)) P := by
  let E : MvPolynomial (K × I) (MvPolynomial K ℝ) →ₐ[ℝ] MvPolynomial K ℝ :=
    (aeval (fun z : K × I => C (v z.1 z.2))).restrictScalars ℝ
  have he : E.comp parameterPolynomialPullback =
      aeval (fun j => rowPolynomial (fun k => v k j)) := by
    apply algHom_ext
    intro j
    simp [E, parameterPolynomialPullback, parameterLinearCoordinate, rowPolynomial, mul_comm]
  exact AlgHom.congr_fun he P

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.HomogenizingMonomial
namespace OAI

section

namespace Erdos3

noncomputable def homogenizingMonomial {I R : Type*} [CommRing R]
    (h : ℕ) (d : I →₀ ℕ) : MvPolynomial (Option I) R :=
  MvPolynomial.X none ^ (h - d.degree) *
    MvPolynomial.rename some (MvPolynomial.monomial d 1)

noncomputable def dehomogenizingSubstitution {I R : Type*} [CommRing R] : Option I → MvPolynomial I R
  | none => 1
  | some i => MvPolynomial.X i

theorem homogenizingMonomial_homogeneous {I R : Type*} [CommRing R]
    (h : ℕ) (d : I →₀ ℕ) (hd : d.degree ≤ h) :
    (homogenizingMonomial (R := R) h d).IsHomogeneous h := by
  have hh := (MvPolynomial.isHomogeneous_X_pow (R := R) (none : Option I) (h - d.degree)).mul
    ((MvPolynomial.isHomogeneous_monomial (1 : R) (rfl : d.degree = d.degree)).rename_isHomogeneous
      (f := some))
  simpa only [homogenizingMonomial, Nat.sub_add_cancel hd] using hh

theorem homogenizingMonomial_dehomogenize {I R : Type*} [CommRing R]
    (h : ℕ) (d : I →₀ ℕ) :
    MvPolynomial.aeval (dehomogenizingSubstitution (R := R)) (homogenizingMonomial (R := R) h d) =
      MvPolynomial.monomial d (1 : R) := by
  simp only [homogenizingMonomial, map_mul, map_pow, MvPolynomial.aeval_X,
    dehomogenizingSubstitution, one_pow, one_mul, MvPolynomial.aeval_rename]
  exact MvPolynomial.aeval_X_left_apply _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowShiftTopSymbol
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def integerSiteValue {K V : Type*} [Fintype K] [AddCommGroup V]
    (site : K → ℤ) (tuple : K → V) : V := ∑ k, site k • tuple k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def baseArrayJoin {K I X : Type*} (tail : K × I → X) (base : I → X) : Option K × I → X :=
  fun z => match z.1 with | none => base z.2 | some k => tail (k,z.2)

theorem baseArrayJoin_eta {K I X : Type*} (z : Option K × I → X) :
    baseArrayJoin (fun k => z (some k.1,k.2)) (fun i => z (none,i)) = z := by
  funext k
  rcases k with ⟨k,i⟩
  cases k <;> rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrimitiveExtension
namespace OAI


namespace Erdos3.BohrLattice.Primitive

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def content (z : ι → ℤ) : ℤ := Finset.univ.gcd z

theorem content_dvd (z : ι → ℤ) (i : ι) : content z ∣ z i := by
  exact Finset.gcd_dvd (Finset.mem_univ i)

theorem content_ne_zero {z : ι → ℤ} (hz : z ≠ 0) : content z ≠ 0 := by
  rw [content, Finset.gcd_ne_zero_iff]
  simpa [funext_iff] using hz

def divideContent (z : ι → ℤ) : ι → ℤ := fun i => z i / content z

theorem content_mul_divideContent (z : ι → ℤ) (i : ι) :
    content z * divideContent z i = z i := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel (content_dvd z i)

omit [Fintype ι] in
theorem exists_bezout_finset (s : Finset ι) (z : ι → ℤ) :
    ∃ u : ι → ℤ, ∑ i ∈ s, u i * z i = s.gcd z := by
  classical
  induction s using Finset.induction with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨u, hu⟩ := ih
      let A : ℤ := Int.gcdA (z a) (s.gcd z)
      let B : ℤ := Int.gcdB (z a) (s.gcd z)
      refine ⟨fun i => if i = a then A else B * u i, ?_⟩
      rw [Finset.sum_insert ha, Finset.gcd_insert]
      simp only [if_pos]
      have hsum :
          (∑ i ∈ s, (if i = a then A else B * u i) * z i) =
            B * s.gcd z := by
        calc
          (∑ i ∈ s, (if i = a then A else B * u i) * z i) =
              ∑ i ∈ s, B * (u i * z i) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [if_neg (by intro hia; subst i; exact ha hi)]
                ring
          _ = B * ∑ i ∈ s, u i * z i := by
                rw [Finset.mul_sum]
          _ = B * s.gcd z := by rw [hu]
      rw [hsum]
      dsimp [A, B]
      rw [mul_comm B, mul_comm (Int.gcdA (z a) (s.gcd z))]
      exact (Int.gcd_eq_gcd_ab (z a) (s.gcd z)).symm

end Erdos3.BohrLattice.Primitive


namespace Erdos3.BohrLattice.PrimitiveExtension

open scoped BigOperators
open Module

noncomputable section

def dotLinear {n : ℕ} (u : Fin n → ℤ) : (Fin n → ℤ) →ₗ[ℤ] ℤ where
  toFun z := ∑ i, u i * z i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_left_comm]

@[simp] theorem dotLinear_apply {n : ℕ} (u z : Fin n → ℤ) :
    dotLinear u z = ∑ i, u i * z i := rfl

def zspanCoordEquiv {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (b : Basis (Fin n) ℝ E) :
    Submodule.span ℤ (Set.range b) ≃ₗ[ℤ] (Fin n → ℤ) :=
  (b.restrictScalars ℤ).repr.trans (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n))

@[simp] theorem zspanCoordEquiv_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (x : Submodule.span ℤ (Set.range b)) (i : Fin n) :
    zspanCoordEquiv b x i = (b.restrictScalars ℤ).repr x i := by
  rfl

end

end Erdos3.BohrLattice.PrimitiveExtension

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem integer_cube_root_bound {K : Type*} {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) {L : ℝ}
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L) :
    ∀ k, |(root k : ℝ)| ≤ L := by
  intro k
  simpa only [affineSite, Finset.sum_empty, add_zero] using hsite ∅ k

theorem integer_cube_difference_bound {K : Type*} {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) {L : ℝ}
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L) :
    ∀ i k, |(difference i k : ℝ)| ≤ 2 * L := by
  intro i k
  have he : (difference i k : ℝ) =
      ((affineSite root difference {i} (some k) : ℤ) : ℝ) - (root k : ℝ) := by
    simp [affineSite]
  rw [he]
  have ht := hsite {i} k
  have hr := integer_cube_root_bound root difference hsite k
  exact (abs_sub _ _).trans (by linarith)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

theorem integerCubeWitnessBound_le_polynomial (q : ℕ) {H D : ℝ}
    (hH : 0 ≤ H) (hD : 0 ≤ D) :
    integerCubeWitnessBound q H D ≤
      (q.factorial : ℝ) * (2 + (q : ℝ) * (q + 1)) * (1 + H + D) ^ (q + 2) := by
  let M := 1 + H + D
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hDq : D ^ q ≤ M ^ q := pow_le_pow_left₀ hD (by dsimp [M]; linarith) q
  have hDm : D ^ (q - 1) ≤ M ^ q :=
    (pow_le_pow_left₀ hD (by dsimp [M]; linarith) (q - 1)).trans
      (pow_le_pow_right₀ hM (Nat.sub_le _ _))
  have hHM : 1 + H ≤ M := by dsimp [M]; linarith
  have hA : (q.factorial : ℝ) * D ^ q ≤ (q.factorial : ℝ) * M ^ q :=
    mul_le_mul_of_nonneg_left hDq (Nat.cast_nonneg _)
  have hB : (q : ℝ) * ((q.factorial : ℝ) * D ^ (q - 1) * (1 + H)) ≤
      (q : ℝ) * (q.factorial : ℝ) * M ^ (q + 1) := by
    calc
      _ ≤ (q : ℝ) * ((q.factorial : ℝ) * M ^ q * M) := by gcongr
      _ = _ := by rw [pow_succ]; ring
  have hfactor : (q : ℝ) * D + 1 ≤ ((q : ℝ) + 1) * M := by
    have hd : D ≤ M := by dsimp [M]; linarith
    nlinarith [show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q]
  have hbase : 2 + H ≤ 2 * M := by dsimp [M]; linarith
  have hpow : M ^ (q + 1) ≤ M ^ (q + 2) := pow_le_pow_right₀ hM (by omega)
  unfold integerCubeWitnessBound integerFormMassBound
  calc
    _ ≤ (q.factorial : ℝ) * M ^ q * (2 * M) +
        (((q : ℝ) + 1) * M) * ((q : ℝ) * (q.factorial : ℝ) * M ^ (q + 1)) := by
      exact add_le_add (mul_le_mul hA hbase (by positivity) (by positivity))
        (mul_le_mul hfactor hB (by positivity) (by positivity))
    _ = 2 * (q.factorial : ℝ) * M ^ (q + 1) +
        ((q : ℝ) * (q + 1) * (q.factorial : ℝ)) * M ^ (q + 2) := by
      simp only [pow_succ]
      ring
    _ ≤ 2 * (q.factorial : ℝ) * M ^ (q + 2) +
        ((q : ℝ) * (q + 1) * (q.factorial : ℝ)) * M ^ (q + 2) := by gcongr
    _ = _ := by dsimp [M]; ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators TensorProduct Classical

def cubeModePolynomialBudget (q : ℕ) (L : ℝ) : ℝ :=
  (q.factorial : ℝ) * (2 + (q : ℝ) * (q + 1)) * (1 + 3 * L) ^ (q + 2)

theorem integerCubeWitnessBound_le_vertex_budget (q : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    integerCubeWitnessBound q L (2 * L) ≤ cubeModePolynomialBudget q L := by
  have he : 1 + L + 2 * L = 1 + 3 * L := by ring
  simpa only [cubeModePolynomialBudget, he] using
    integerCubeWitnessBound_le_polynomial q hL (show 0 ≤ 2 * L by positivity)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientModeLowerTerms
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem linear_pow_totalDegree_le {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R) :
    ((∑ i, a i • X i : MvPolynomial (Fin n) R) ^ n).totalDegree ≤ n := by
  have hsum : (∑ i, a i • X i : MvPolynomial (Fin n) R).totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro i _
    rw [smul_eq_C_mul]
    have hX : (X i : MvPolynomial (Fin n) R).totalDegree ≤ 1 := by
      simpa only [X, Finsupp.sum_single_index, id_eq] using
        (totalDegree_monomial_le (Finsupp.single i 1) (1 : R))
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hX)
  exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left n hsum).trans_eq (Nat.mul_one n))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AffineFrequencyLift
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def affineLiftFrequency {K J A : Type*}
    (frequency : (K →₀ ℕ) → J → A) (d : Option K →₀ ℕ) : J → A := frequency d.some

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def residueLatticeArray {K I : Type*} (residue : K × I → ℤ) (modulus : I → ℕ)
    (x : K × I → ℤ) : K × I → ℤ :=
  fun z => residue z + (modulus z.2 : ℤ) * x z

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MinkowskiSecondBox
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open _root_.Set Module Submodule

noncomputable def minkowskiSecondConstant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (n * (n - 1) / 2)

@[simp] theorem minkowskiSecondConstant_zero : minkowskiSecondConstant 0 = 1 := by
  simp [minkowskiSecondConstant]

@[simp] theorem minkowskiSecondConstant_one : minkowskiSecondConstant 1 = 1 := by
  simp [minkowskiSecondConstant]

theorem minkowskiSecondConstant_nonneg (n : ℕ) :
    0 ≤ minkowskiSecondConstant n := by
  exact pow_nonneg (by norm_num) _

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MinkowskiSecondBoxGlue
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open _root_.Set Module Submodule

noncomputable def matrixBasis {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.det ≠ 0) : Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).map
    (D.toLinearEquiv' (D.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hD)))

@[simp] theorem matrixBasis_apply {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.det ≠ 0) (j : Fin n) :
    matrixBasis D hD j = fun i ↦ D i j := by
  ext i
  rw [matrixBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change Matrix.mulVec D (Pi.single j 1) i = D i j
  simp [Matrix.mulVec]

theorem minkowskiSecondConstant_succ (n : ℕ) :
    minkowskiSecondConstant (n + 1) =
      (2 : ℝ) ^ n * minkowskiSecondConstant n := by
  unfold minkowskiSecondConstant
  have he : (n + 1) * ((n + 1) - 1) / 2 = n + n * (n - 1) / 2 := by
    rw [← Nat.choose_two_right, ← Nat.choose_two_right]
    simp [Nat.choose_succ_succ]
  rw [he, pow_add]

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProjectedBasisSpan
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open Module Submodule
open scoped BigOperators

theorem mem_first_span_of_projection_zero {n : ℕ}
    (b : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ))
    (q : Basis (Fin n) ℝ (Fin n → ℝ))
    (π : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hzero : π (b 0) = 0) (htail : ∀ j, π (b j.succ) = q j)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ span ℤ (Set.range b)) (hπx : π x = 0) :
    x ∈ span ℤ ({b 0} : Set (Fin (n + 1) → ℝ)) := by
  classical
  rw [mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  have hp : ∑ j : Fin n, c j.succ • q j = 0 := by
    rw [map_sum, Fin.sum_univ_succ] at hπx
    simpa only [map_zsmul, hzero, htail, smul_zero, zero_add] using hπx
  have hc : ∀ j : Fin n, c j.succ = 0 :=
    Fintype.linearIndependent_iff.mp (q.linearIndependent.restrict_scalars' ℤ) _ hp
  rw [Fin.sum_univ_succ]
  simp only [hc, zero_smul, Finset.sum_const_zero, add_zero]
  exact smul_mem _ _ (subset_span (Set.mem_singleton _))

theorem span_fin_cons_of_projected_span {n : ℕ}
    (b : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ))
    (q : Basis (Fin n) ℝ (Fin n → ℝ))
    (π : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hzero : π (b 0) = 0) (htail : ∀ j, π (b j.succ) = q j)
    (w : Fin n → Fin (n + 1) → ℝ)
    (hw : ∀ j, w j ∈ span ℤ (Set.range b))
    (hspan : span ℤ (Set.range (fun j => π (w j))) = span ℤ (Set.range q)) :
    span ℤ (Set.range (Fin.cons (b 0) w)) = span ℤ (Set.range b) := by
  classical
  let L := span ℤ (Set.range b)
  let S := span ℤ (Set.range (Fin.cons (b 0) w))
  have hfirst : b 0 ∈ S := subset_span ⟨0, rfl⟩
  have hwm : ∀ j, w j ∈ S := fun j => subset_span ⟨j.succ, rfl⟩
  have hsmall : span ℤ ({b 0} : Set (Fin (n + 1) → ℝ)) ≤ S := by
    exact span_le.mpr (fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hfirst)
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Fin.cases (subset_span (Set.mem_range_self 0)) hw i
  · apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.cases hfirst (fun k => ?_) i
    change b k.succ ∈ S
    have hk : q k ∈ span ℤ (Set.range (fun j => π (w j))) := by
      rw [hspan]
      exact subset_span (Set.mem_range_self k)
    rw [mem_span_range_iff_exists_fun] at hk
    obtain ⟨c, hc⟩ := hk
    let y := ∑ j, c j • w j
    have hyL : y ∈ L := sum_mem (fun j _ => smul_mem _ _ (hw j))
    have hyS : y ∈ S := sum_mem (fun j _ => smul_mem _ _ (hwm j))
    have hdiff : b k.succ - y ∈ L :=
      sub_mem (subset_span (Set.mem_range_self k.succ)) hyL
    have hπdiff : π (b k.succ - y) = 0 := by
      rw [map_sub, htail]
      change q k - π (∑ j, c j • w j) = 0
      rw [map_sum]
      simp only [map_zsmul, hc, sub_self]
    have hm := mem_first_span_of_projection_zero b q π hzero htail hdiff hπdiff
    have hadd := S.add_mem (hsmall hm) hyS
    simpa only [sub_add_cancel] using hadd

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

noncomputable def integerMassTent (K : ℝ) (a : ℤ) (x : ℝ) : ℝ :=
  K * max 0 (1 - 2 * |K * x - a|)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuarticBohrProgression
namespace OAI

section

open scoped BigOperators Matrix Pointwise

namespace Erdos3.BohrProgression

open Erdos3.BohrLattice.MinkowskiSecondBox

noncomputable section

noncomputable def indexedCyclicCharacter {N : ℕ}
    (Gamma : Finset (ZMod N)) : Fin (Gamma.card + 1) → ZMod N :=
  Fin.cases 1 fun i => (Gamma.equivFin.symm i : Gamma)

@[simp] lemma indexedCyclicCharacter_zero {N : ℕ}
    (Gamma : Finset (ZMod N)) : indexedCyclicCharacter Gamma 0 = 1 := rfl

def bohrLatticeMatrixInt {N : ℕ} (Gamma : Finset (ZMod N)) :
    Matrix (Fin (Gamma.card + 1)) (Fin (Gamma.card + 1)) ℤ :=
  fun i j => if j = 0 then ((indexedCyclicCharacter Gamma i).val : ℤ)
    else if i = j then (N : ℤ) else 0

def bohrLatticeMatrix {N : ℕ} (Gamma : Finset (ZMod N)) :
    Matrix (Fin (Gamma.card + 1)) (Fin (Gamma.card + 1)) ℝ :=
  (bohrLatticeMatrixInt Gamma).map (Int.castRingHom ℝ)

@[simp] lemma bohrLatticeMatrixInt_zero_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (j : Fin Gamma.card) :
    bohrLatticeMatrixInt Gamma 0 j.succ = 0 := by
  simp [bohrLatticeMatrixInt, (Fin.succ_ne_zero j).symm]

@[simp] lemma bohrLatticeMatrix_zero_zero {N : ℕ}
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    bohrLatticeMatrix Gamma 0 0 = 1 := by
  simp [bohrLatticeMatrix, bohrLatticeMatrixInt, ZMod.val_one'' (by omega : N ≠ 1)]

@[simp] lemma bohrLatticeMatrix_zero_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (j : Fin Gamma.card) :
    bohrLatticeMatrix Gamma 0 j.succ = 0 := by
  simp [bohrLatticeMatrix]

@[simp] lemma bohrLatticeMatrix_succ_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (i j : Fin Gamma.card) :
    bohrLatticeMatrix Gamma i.succ j.succ =
      if i = j then (N : ℝ) else 0 := by
  simp [bohrLatticeMatrix, bohrLatticeMatrixInt, Fin.succ_inj]

lemma det_bohrLatticeMatrix {N : ℕ} (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    (bohrLatticeMatrix Gamma).det = (N : ℝ) ^ Gamma.card := by
  have hminor :
      (bohrLatticeMatrix Gamma).submatrix Fin.succ (Fin.succAbove 0) =
        Matrix.diagonal (fun _ : Fin Gamma.card => (N : ℝ)) := by
    ext i j
    rw [Matrix.diagonal_apply]
    simp [Matrix.submatrix]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [bohrLatticeMatrix_zero_zero Gamma hN, bohrLatticeMatrix_zero_succ]
  rw [hminor]
  rw [Matrix.det_diagonal]
  simp

lemma det_bohrLatticeMatrix_ne_zero {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    (bohrLatticeMatrix Gamma).det ≠ 0 := by
  rw [det_bohrLatticeMatrix Gamma hN]
  positivity

noncomputable def bohrLatticeBasis {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    Module.Basis (Fin (Gamma.card + 1)) ℝ
      (Fin (Gamma.card + 1) → ℝ) :=
  matrixBasis (bohrLatticeMatrix Gamma)
    (det_bohrLatticeMatrix_ne_zero Gamma hN)

@[simp] lemma bohrLatticeBasis_apply {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N)
    (j i : Fin (Gamma.card + 1)) :
    bohrLatticeBasis Gamma hN j i = bohrLatticeMatrix Gamma i j := by
  exact congrFun (matrixBasis_apply (bohrLatticeMatrix Gamma)
    (det_bohrLatticeMatrix_ne_zero Gamma hN) j) i

def bohrLatticePoint {N : ℕ} (Gamma : Finset (ZMod N))
    (z : Fin (Gamma.card + 1) → ℤ) : Fin (Gamma.card + 1) → ℤ :=
  Matrix.mulVec (bohrLatticeMatrixInt Gamma) z

lemma bohrLatticePoint_zero {N : ℕ} (Gamma : Finset (ZMod N)) (hN : 1 < N)
    (z : Fin (Gamma.card + 1) → ℤ) :
    bohrLatticePoint Gamma z 0 = z 0 := by
  simp [bohrLatticePoint, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    bohrLatticeMatrixInt, ZMod.val_one'' (by omega : N ≠ 1),
    (fun x : Fin Gamma.card => (Fin.succ_ne_zero x).symm)]

lemma bohrLatticePoint_cast_coordinate {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (z : Fin (Gamma.card + 1) → ℤ)
    (hN : 1 < N)
    (i : Fin (Gamma.card + 1)) :
    (bohrLatticePoint Gamma z i : ZMod N) =
      (bohrLatticePoint Gamma z 0 : ZMod N) *
        indexedCyclicCharacter Gamma i := by
  rw [bohrLatticePoint_zero Gamma hN]
  simp only [bohrLatticePoint, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_succ]
  simp only [bohrLatticeMatrixInt]
  by_cases hi : i = 0
  · subst i
    simp
  · simp [mul_comm]

structure CyclicCenteredGAP (N : ℕ) where
  rank : ℕ
  step : Fin rank → ZMod N
  radius : Fin rank → ℕ

lemma int_eq_zero_of_cast_zmod_eq_zero_of_abs_lt {N : ℕ} [NeZero N]
    {t : ℤ} (ht0 : (t : ZMod N) = 0) (htN : |(t : ℝ)| < N) : t = 0 := by
  have hdvd : (N : ℤ) ∣ t :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd t N).mp ht0
  have habs : (t.natAbs : ℝ) = |(t : ℝ)| := by
    calc
      (t.natAbs : ℝ) = (((t.natAbs : ℕ) : ℤ) : ℝ) := by norm_num
      _ = ((|t| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
      _ = |(t : ℝ)| := Int.cast_abs
  have hnat : t.natAbs < N := by
    exact_mod_cast (habs.trans_lt htN)
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
  simpa using hnat

lemma matrixOf_bohrLatticeBasis {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    Matrix.of (bohrLatticeBasis Gamma hN) =
      (bohrLatticeMatrix Gamma)ᵀ := by
  ext i j
  rw [Matrix.of_apply, Matrix.transpose_apply]
  exact bohrLatticeBasis_apply Gamma hN i j

lemma abs_det_matrixOf_bohrLatticeBasis {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    |(Matrix.of (bohrLatticeBasis Gamma hN)).det| =
      (N : ℝ) ^ Gamma.card := by
  rw [matrixOf_bohrLatticeBasis Gamma hN,
    Matrix.det_transpose, det_bohrLatticeMatrix Gamma hN, abs_of_nonneg]
  positivity

end

end Erdos3.BohrProgression

end

section

namespace Erdos3.BohrProgression

open BohrLattice.MinkowskiSecondBox

lemma minkowskiSecondConstant_le_exp (m : ℕ) :
    minkowskiSecondConstant m ≤ Real.exp (2 * (m : ℝ) ^ 2) := by
  have hidx : m * (m - 1) / 2 ≤ m * m :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left m (Nat.sub_le m 1))
  have hcast : ((m * (m - 1) / 2 : ℕ) : ℝ) ≤ (m : ℝ) ^ 2 := by
    rw [pow_two]
    exact_mod_cast hidx
  calc
    minkowskiSecondConstant m = (2 : ℝ) ^ (m * (m - 1) / 2) := rfl
    _ ≤ Real.exp 2 ^ (m * (m - 1) / 2) := by
      apply pow_le_pow_left₀ (by norm_num)
      linarith [Real.add_one_le_exp (2 : ℝ)]
    _ = Real.exp (((m * (m - 1) / 2 : ℕ) : ℝ) * 2) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (2 * (m : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      linarith

lemma progression_size_factor_lower_bound (m : ℕ) (hm : 0 < m)
    {w δ : ℝ} (hδ : Real.exp (-w) ≤ δ) :
    Real.exp (-((m : ℝ) * w + 10 * (m : ℝ) ^ 2)) ≤
      (δ / (8 * m)) ^ m / minkowskiSecondConstant m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : (0 : ℝ) < 8 * m := by positivity
  have hrecip : Real.exp (-(8 * m : ℝ)) ≤ (8 * m : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    apply (inv_le_inv₀ (Real.exp_pos _) hden).2
    linarith [Real.add_one_le_exp (8 * m : ℝ)]
  have hbase : Real.exp (-(w + 8 * m)) ≤ δ / (8 * m) := by
    calc
      Real.exp (-(w + 8 * m)) = Real.exp (-w) * Real.exp (-(8 * m : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ δ * (8 * m : ℝ)⁻¹ :=
        mul_le_mul hδ hrecip (Real.exp_pos _).le ((Real.exp_pos _).le.trans hδ)
      _ = δ / (8 * m) := by rw [div_eq_mul_inv]
  have hpower : Real.exp (-((m : ℝ) * w + 8 * (m : ℝ) ^ 2)) ≤
      (δ / (8 * m)) ^ m := by
    calc
      _ = Real.exp (-(w + 8 * m)) ^ m := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hbase _
  have hc : 0 < minkowskiSecondConstant m := by
    unfold minkowskiSecondConstant
    positivity
  have hinv : Real.exp (-(2 * (m : ℝ) ^ 2)) ≤ (minkowskiSecondConstant m)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hc).2 (minkowskiSecondConstant_le_exp m)
  calc
    _ = Real.exp (-((m : ℝ) * w + 8 * (m : ℝ) ^ 2)) *
        Real.exp (-(2 * (m : ℝ) ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (δ / (8 * m)) ^ m * (minkowskiSecondConstant m)⁻¹ :=
      mul_le_mul hpower hinv (Real.exp_pos _).le ((Real.exp_pos _).le.trans hpower)
    _ = _ := by simp only [div_eq_mul_inv]

end Erdos3.BohrProgression

end

section

namespace Erdos3.BohrProgression

namespace CyclicCenteredGAP

def zero (N : ℕ) : CyclicCenteredGAP N where
  rank := 0
  step := Fin.elim0
  radius := Fin.elim0

end CyclicCenteredGAP

end Erdos3.BohrProgression

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmallBoxCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D]

noncomputable def smallBoxCutoff (x : D → ℝ) : ℝ :=
  max 0 (min 1 (3 - 8 * ‖x‖))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerPeriodicTorusLift
namespace OAI

section

namespace Erdos3

variable {ι : Type*}

noncomputable def integerPeriodicTorusLift (F : (ι → ℝ) → ℂ) (x : UnitAddTorus ι) : ℂ :=
  F (fun i => (AddCircle.equivIoc 1 0 (x i)).val)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RealQuarterTorusExtension
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D]

noncomputable def realPeriodicTorusLift (F : (D → ℝ) → ℝ) (x : D → UnitAddCircle) : ℝ :=
  (integerPeriodicTorusLift (fun y => (F y : ℂ)) x).re

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AnchoredCubeResidueWidths
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators
open VectorPolynomial

theorem cubeModePolynomialBudget_pos (q : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    0 < cubeModePolynomialBudget q L := by
  unfold cubeModePolynomialBudget
  positivity

theorem affineSite_intCast {K : Type*} {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) (s : Finset (Fin q)) :
    (fun k => ((affineSite root difference s k : ℤ) : ℝ)) =
      affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s := by
  exact (affineSite_map (Int.castRingHom ℝ) root difference s).symm

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MaskedIntegerPeriodization
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

variable {D : Type*} [Fintype D]

noncomputable def maskedIntegerPeriodization (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (x : D → ℝ) : ℝ :=
  ∑' n : D → ℤ, mask (fun i => (n i : ZMod q)) * H (fun i => x i + (n i : ℝ))

noncomputable def maskedIntegerTorusKernel (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) : (D → UnitAddCircle) → ℝ :=
  realPeriodicTorusLift (fun x => maskedIntegerPeriodization q mask H (fun i => q * x i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineOneSiteNormalizedLaw
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

noncomputable def physicalAffineSite {I K : Type*} [Fintype K]
    (root : K → ℤ) (z : Option K × I → ℤ) : I → ℝ :=
  integerSiteValue (fun k => match k with | none => 1 | some k => root k)
    (fun k j => (z (k,j) : ℝ))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalBaseInjection
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalAffineSite_baseArrayJoin_apply {K I : Type*} [Fintype K]
    (root : K → ℤ) (tail : K × I → ℤ) (base : I → ℤ) (i : I) :
    physicalAffineSite root (baseArrayJoin tail base) i =
      (base i : ℝ) + ∑ k, (root k : ℝ) * (tail (k,i) : ℝ) := by
  simp only [physicalAffineSite, integerSiteValue, Fintype.sum_option, Finset.sum_apply,
    baseArrayJoin, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, Int.cast_one, one_mul]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxObservedMean
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def integerPhysicalSite {K I : Type*} [Fintype K] (root : K → ℤ)
    (z : Option K × I → ℤ) : I → ℤ :=
  fun i => z (none,i) + ∑ k, root k * z (some k,i)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuantitativeNoninjectivity
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

def jointIntegerPhysicalSite {K I : Type*} [Fintype K] (root : K → ℤ)
    (z : (I → ℤ) × (Option K × I → ℤ)) : I → ℤ :=
  z.1 + integerPhysicalSite root z.2

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PhysicalCubeMatrix
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

def physicalCubeCoefficient {K α : Type*} (root : K → ℤ) (D : Matrix α K ℤ) :
    Matrix (Unit ⊕ α) (Option K) ℤ
  | .inl _, none => 1
  | .inl _, some k => root k
  | .inr _, none => 0
  | .inr i, some k => D i k

def physicalCubeOffset {X α : Type*} (base : X → ℤ) (x : X) : (Unit ⊕ α) → ℤ
  | .inl _ => base x
  | .inr _ => 0

def physicalCubeRootDifferences {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) : X → (Unit ⊕ α) → ℤ :=
  fun x i => physicalCubeOffset base x i + ∑ k, physicalCubeCoefficient root D i k * z (k, x)

theorem physicalCubeRootDifferences_root {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) (x : X) :
    physicalCubeRootDifferences root D base z x (.inl ()) =
      jointIntegerPhysicalSite root (base, z) x := by
  simp [physicalCubeRootDifferences, physicalCubeOffset, physicalCubeCoefficient,
    jointIntegerPhysicalSite, integerPhysicalSite]

theorem physicalCubeRootDifferences_direction {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) (x : X) (i : α) :
    physicalCubeRootDifferences root D base z x (.inr i) = ∑ k, D i k * z (some k, x) := by
  simp [physicalCubeRootDifferences, physicalCubeOffset, physicalCubeCoefficient]

theorem physicalCubeRootDifferences_vertex {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) (x : X) (t : Finset α) :
    physicalCubeRootDifferences root D base z x (.inl ()) +
        ∑ i ∈ t, physicalCubeRootDifferences root D base z x (.inr i) =
      jointIntegerPhysicalSite (integerAffineCube root D t) (base, z) x := by
  rw [physicalCubeRootDifferences_root]
  simp_rw [physicalCubeRootDifferences_direction]
  have hs : (∑ k, ∑ i ∈ t, D i k * z (some k, x)) =
      ∑ i ∈ t, ∑ k, D i k * z (some k, x) := Finset.sum_comm
  simp only [jointIntegerPhysicalSite, integerPhysicalSite, Pi.add_apply,
    integerAffineCube, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [hs]
  ring

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

def physicalCubeVertexValue {I α : Type*} (v : I → (Unit ⊕ α) → ℤ) (s : Finset α) : I → ℤ :=
  fun i => v i (.inl ()) + ∑ a ∈ s, v i (.inr a)

theorem physicalCubeVertexValue_rootDifferences {I K α : Type*} [Fintype K]
    (root : K → ℤ) (difference : Matrix α K ℤ) (base : I → ℤ)
    (z : Option K × I → ℤ) (s : Finset α) :
    physicalCubeVertexValue (physicalCubeRootDifferences root difference base z) s =
      jointIntegerPhysicalSite (integerAffineCube root difference s) (base, z) := by
  funext i
  exact physicalCubeRootDifferences_vertex root difference base z i s

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RationalBohrWidth
namespace OAI

section

namespace Erdos3.BohrWidthBudget

theorem selector_scale_lower_bound {d D : ℝ} (hd : 0 < d) (hD : 0 ≤ D) :
    1 / (1000 * d * (D + 1)) ≤
      (100 * (2 * d) * ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ))⁻¹ := by
  have hceil := (Nat.ceil_lt_add_one hD).le
  have hsmall : (((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ)) ≤ 5 * (D + 1) := by
    push_cast
    linarith
  rw [← one_div]
  apply one_div_le_one_div_of_le (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 100 * (2 * d) by positivity)
  nlinarith

theorem polynomial_denominator_le_exp {W p d : ℝ}
    (hW : 0 < W) (hp : 0 ≤ p) (hd : 1 ≤ d) :
    Real.exp p * W * d ^ 3 * (p + 1) ^ 4 ≤
      Real.exp ((W + 8) * (1 + p + Real.log (2 + d))) := by
  have hWexp : W ≤ Real.exp W := by linarith [Real.add_one_le_exp W]
  have hd0 : 0 ≤ d := by linarith
  have hdlog : d ^ 3 ≤ Real.exp (3 * Real.log (2 + d)) := by
    calc
      d ^ 3 ≤ (2 + d) ^ 3 := pow_le_pow_left₀ hd0 (by linarith) 3
      _ = Real.exp (3 * Real.log (2 + d)) := by
        simpa only [Nat.cast_ofNat, Real.exp_log (by positivity : 0 < 2 + d)] using
          (Real.exp_nat_mul (Real.log (2 + d)) 3).symm
  have hppow : (p + 1) ^ 4 ≤ Real.exp (4 * p) := by
    calc
      (p + 1) ^ 4 ≤ Real.exp p ^ 4 :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp p) 4
      _ = Real.exp (4 * p) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul p 4).symm
  have hlog : 0 ≤ Real.log (2 + d) := Real.log_nonneg (by linarith)
  calc
    Real.exp p * W * d ^ 3 * (p + 1) ^ 4 ≤
        Real.exp p * Real.exp W * Real.exp (3 * Real.log (2 + d)) * Real.exp (4 * p) := by
      gcongr
    _ = Real.exp (p + W + 3 * Real.log (2 + d) + 4 * p) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp ((W + 8) * (1 + p + Real.log (2 + d))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hW.le hp, mul_nonneg hW.le hlog]

theorem exp_neg_budget_le_reciprocal {W p d : ℝ}
    (hW : 0 < W) (hp : 0 ≤ p) (hd : 1 ≤ d) :
    Real.exp (-((W + 8) * (1 + p + Real.log (2 + d)))) ≤
      1 / (Real.exp p * W * d ^ 3 * (p + 1) ^ 4) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity)
    (polynomial_denominator_le_exp hW hp hd)

end Erdos3.BohrWidthBudget

end

section

namespace Erdos3.BohrWidthBudget

theorem rational_width_lower_bound {u d D w v a : ℝ}
    (hu : 0 < u) (hd : 1 ≤ d) (hD : 0 ≤ D) (hw : 0 < w) (hw1 : w ≤ 1)
    (hv : w / (400 * d) ≤ v) (ha : 1 / (1000 * d * (D + 1)) ≤ a) :
    u * w / (10240000000 * d ^ 3 * (D + 1)) ≤
      min ((u / (6400 * d)) * (a * v / 2)) (u / (8 * (D + 1))) / 2 := by
  have hd0 : 0 < d := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hprod : (1 / (1000 * d * (D + 1))) * (w / (400 * d)) ≤ a * v :=
    mul_le_mul ha hv (by positivity) ha0.le
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply le_min
  · calc
      u * w / (10240000000 * d ^ 3 * (D + 1)) * 2 =
          (u / (6400 * d)) * ((1 / (1000 * d * (D + 1))) * (w / (400 * d)) / 2) := by
        field_simp
        ring
      _ ≤ (u / (6400 * d)) * (a * v / 2) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hprod (by norm_num)) (by positivity)
  · have hd3 : 1 ≤ d ^ 3 := one_le_pow₀ hd
    have hfrac : w / (5120000000 * d ^ 3) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc
      u * w / (10240000000 * d ^ 3 * (D + 1)) * 2 =
          (u / (D + 1)) * (w / (5120000000 * d ^ 3)) := by
        field_simp
        ring
      _ ≤ (u / (D + 1)) * (1 / 8) := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = u / (8 * (D + 1)) := by field_simp

theorem rational_width_ge_exponential {epsilon C p d w : ℝ}
    (hepsilon : 0 < epsilon) (hC : 0 ≤ C) (hp : 0 ≤ p) (hd : 1 ≤ d) (hw : 0 ≤ w) :
    let W := 10240000000 * (C + 1) / epsilon
    w * Real.exp (-((W + 8) * (1 + p + Real.log (2 + d)))) ≤
      epsilon * Real.exp (-p) * w / (10240000000 * d ^ 3 * (C * (p + 1) ^ 4 + 1)) := by
  intro W
  have hW : 0 < W := by dsimp [W]; positivity
  have hd0 : 0 < d := by linarith
  have hbound := mul_le_mul_of_nonneg_left (exp_neg_budget_le_reciprocal hW hp hd) hw
  have hp4 : 1 ≤ (p + 1) ^ 4 := one_le_pow₀ (show 1 ≤ p + 1 by linarith)
  have hden : 10240000000 * d ^ 3 * (C * (p + 1) ^ 4 + 1) ≤
      10240000000 * d ^ 3 * ((C + 1) * (p + 1) ^ 4) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  calc
    w * Real.exp (-((W + 8) * (1 + p + Real.log (2 + d)))) ≤
        w * (1 / (Real.exp p * W * d ^ 3 * (p + 1) ^ 4)) := hbound
    _ = epsilon * Real.exp (-p) * w /
        (10240000000 * d ^ 3 * ((C + 1) * (p + 1) ^ 4)) := by
      rw [Real.exp_neg]
      dsimp [W]
      field_simp
    _ ≤ epsilon * Real.exp (-p) * w /
        (10240000000 * d ^ 3 * (C * (p + 1) ^ 4 + 1)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden

end Erdos3.BohrWidthBudget

end

end OAI
end


