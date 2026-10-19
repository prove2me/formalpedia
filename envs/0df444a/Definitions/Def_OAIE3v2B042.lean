-- Prove2me | Definitions.Def_OAIE3v2B042
-- name    : OAIE3v2B042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:13:21.006601+00:00
-- url     : https://prove2.me/theorems/951f1b36-0686-411b-847d-608b2ae3416f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 43 of 311
-- statement:
--   Definitions bundle 43 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B004`, `OAIE3v2B005`, `OAIE3v2B006`, `OAIE3v2B007`, `OAIE3v2B008` of this split.
--
--   Modules: `Estimates/AbsorbedSiteTests.lean`, `Estimates/AllocatedScalarLogBounds.lean`, `Estimates/AllocatedShortAxis.lean`, `Estimates/BooleanCubeModeWitness.lean`, `Estimates/CoefficientRowEvaluation.lean`, `Estimates/DehomogenizedExponent.lean`, `Estimates/DenseProductApproximation.lean`, `Estimates/EmptyLayerDetectionGeometry.lean`, `Estimates/LinearQuotientCoverAverage.lean`, `Estimates/OneSiteCoefficientFactorization.lean`, `Estimates/PairedDiagonalApproximation.lean`, `Estimates/PhysicalRowsSiteReconstruction.lean`, `Estimates/PrincipalAxisInterpolation.lean`, `Estimates/PrincipalCoefficientMarginal.lean`, `Estimates/QuantitativeNoninjectivity.lean`, `Estimates/RationalRowReduction.lean`, `Fourier/AffineFrequencyLift.lean`, `Fourier/CoefficientEvaluationTorus.lean`, `Fourier/EuclideanJetTorus.lean`, `Fourier/ExponentialBohrVolume.lean`, `Fourier/QuarticBohrProgression.lean`, `Fourier/RectangularGridCharacter.lean`, `Fourier/SiteFourierHaarMean.lean`, `Geometry/BoxDifferenceHom.lean`, `Geometry/BoxDifferenceSubstitution.lean`, `Geometry/IntervalBoxDifference.lean`, `Geometry/MultilinearBoxInverse.lean`, `Geometry/SupportedCubeEquivTransport.lean`, `Lattices/AffineCoefficientSubspace.lean`, `Lattices/IntegerAffineResidues.lean`, `Lattices/IntegerBoxObservedMean.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/IntegralAffineModeRemoval.lean`, `Lattices/NormalizedIntegerDual.lean`, `Lattices/PrincipalIntegerInterpolation.lean`, `Linear/BooleanCubeCoordinateFrame.lean`, `Linear/BooleanJetMatrixFactor.lean`, `Linear/MatrixSupInverse.lean`, `Polynomial/AffinePhaseBias.lean`, `Polynomial/AffineShiftPolynomial.lean`, `Polynomial/IntegerPolynomialInterpolation.lean`, `Polynomial/MultiaffinePhaseDifference.lean`, `Polynomial/PolynomialKernelValues.lean`, `Polynomial/PolynomialRationalApproximationMono.lean`, `Polynomial/RealPolynomialEvaluationMass.lean`, `Polynomial/RowPolynomialCombination.lean`, `Polynomial/VectorPolynomialReconstruction.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B005
import Definitions.Def_OAIE3v2B006
import Definitions.Def_OAIE3v2B007
import Definitions.Def_OAIE3v2B008

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

namespace Erdos3

open CircleFourier

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def quotientLinearCharacter (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x : E ⧸ Γ) : ℂ :=
  character (quotientLinearPhase Γ L hint x)

theorem quotientLinearCharacter_mk (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x : E) :
    quotientLinearCharacter Γ L hint (QuotientAddGroup.mk' Γ x) =
      character (L x : CircleFourier.Circle) := rfl

theorem quotientLinearCharacter_add (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x y : E ⧸ Γ) :
    quotientLinearCharacter Γ L hint (x + y) =
      quotientLinearCharacter Γ L hint x * quotientLinearCharacter Γ L hint y := by
  simp only [quotientLinearCharacter, map_add, character_add]

theorem quotientLinearCharacter_norm (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x : E ⧸ Γ) :
    ‖quotientLinearCharacter Γ L hint x‖ = 1 := norm_character _

theorem quotientLinearCharacter_zero (Γ : AddSubgroup E)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, (0 : E →ₗ[ℝ] ℝ) x = n) (x : E ⧸ Γ) :
    quotientLinearCharacter Γ 0 hint x = 1 := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective Γ x
  simp only [quotientLinearCharacter_mk, LinearMap.zero_apply, AddCircle.coe_zero, character_zero]

theorem quotientLinearCharacter_continuous [TopologicalSpace E]
    (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (hL : Continuous L) :
    Continuous (quotientLinearCharacter Γ L hint) := by
  apply (QuotientAddGroup.isQuotientMap_mk Γ).continuous_iff.mpr
  change Continuous (fun x : E => character (L x : CircleFourier.Circle))
  exact (continuous_subtype_val.comp AddCircle.continuous_toCircle).comp
    ((AddCircle.continuous_mk' (1 : ℝ)).comp hL)

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

theorem character_real_sum {S : Type*} (s : Finset S) (f : S → ℝ) :
    character ((∑ t ∈ s, f t : ℝ) : CircleFourier.Circle) =
      ∏ t ∈ s, character (f t : CircleFourier.Circle) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert t s ht ih =>
    simp only [Finset.sum_insert ht, AddCircle.coe_add, character_add, Finset.prod_insert ht, ih]

noncomputable def siteFunctionalCharacter {S W : Type*} [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (M : (S → W) →ₗ[ℝ] ℝ) (s : S) (w : W) : ℂ :=
  character (M (Pi.single s w) : CircleFourier.Circle)

theorem siteFunctionalCharacter_norm {S W : Type*} [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (M : (S → W) →ₗ[ℝ] ℝ) (s : S) (w : W) :
    ‖siteFunctionalCharacter M s w‖ = 1 := norm_character _

theorem character_linear_site_sum {S W : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (M : (S → W) →ₗ[ℝ] ℝ) (v : S → W) :
    character (M v : CircleFourier.Circle) = ∏ s, siteFunctionalCharacter M s (v s) := by
  rw [linear_site_sum M v]
  exact character_real_sum _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AbsorbedSiteTests
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

theorem absorb_factored_phases {A S X G : Type*} [Fintype A] [Fintype S]
    (χ : A → S → X → ℂ) (test : S → X → ℂ) (value : G → S → X)
    (high : A → G → ℝ)
    (hfactor : ∀ a g, character (high a g : CircleFourier.Circle) = ∏ s, χ a s (value g s))
    (low : G → ℝ) (g : G) :
    character ((low g + ∑ a, high a g : ℝ) : CircleFourier.Circle) * (∏ s, test s (value g s)) =
      character (low g : CircleFourier.Circle) * (∏ s, absorbedSiteTests χ test s (value g s)) := by
  rw [AddCircle.coe_add, character_add, character_real_sum]
  simp_rw [hfactor]
  rw [mul_assoc, absorbedSiteTests_product]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalRowReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem RationalHeightLE.add {q r : ℚ} {H K : ℕ}
    (hq : RationalHeightLE q H) (hr : RationalHeightLE r K) :
    RationalHeightLE (q + r) (2 * H * K) := by
  have hqd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hrd : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hd : (q.den : ℤ) * r.den ≠ 0 := by
    exact_mod_cast mul_ne_zero hqd hrd
  have heq : q + r = ((q.num * r.den + (q.den : ℤ) * r.num : ℤ) : ℚ) /
      ((q.den : ℤ) * r.den : ℤ) := by
    calc
      q + r = (q.num : ℚ) / q.den + (r.num : ℚ) / r.den :=
        congrArg₂ (· + ·) q.num_div_den.symm r.num_div_den.symm
      _ = _ := by push_cast; exact div_add_div _ _ hqd hrd
  rw [heq]
  apply rationalHeightLE_fraction _ _ hd
  · calc
      _ ≤ (q.num * r.den).natAbs + ((q.den : ℤ) * r.num).natAbs :=
        Int.natAbs_add_le _ _
      _ ≤ H * K + H * K := by
        simp only [Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2) (Nat.mul_le_mul hq.2 hr.1)
      _ = _ := by ring
  · calc
      _ = q.den * r.den := by simp only [Int.natAbs_mul, Int.natAbs_natCast]
      _ ≤ H * K := Nat.mul_le_mul hq.2 hr.2
      _ ≤ 2 * H * K := by
        simpa only [mul_assoc] using Nat.le_mul_of_pos_left (H * K) (by decide : 0 < 2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*}

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def clearedMatrix (A : Matrix ι κ ℚ) : Matrix ι κ ℤ :=
  fun i j => clearedArray (fun ij : ι × κ => A ij.1 ij.2) (i, j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixSupInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_det_abs_le_uniform_bound (A : Matrix ι ι ℝ) {H : ℝ}
    (hA : ∀ i j, |A i j| ≤ H) :
    |A.det| ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι := by
  simpa only [Finset.prod_const, Finset.card_univ] using
    matrix_det_abs_le_row_bounds A (fun _ => H) hA

theorem matrix_adjugate_entry_abs_le (A : Matrix ι ι ℝ) {H : ℝ}
    (hA : ∀ i j, |A i j| ≤ H) (i j : ι) :
    |A.adjugate i j| ≤ (Fintype.card ι).factorial * H ^ (Fintype.card ι - 1) := by
  rw [Matrix.adjugate_apply]
  let K : ι → ℝ := fun k => if k = j then 1 else H
  have hentry : ∀ k l, |(A.updateRow j (Pi.single i 1)) k l| ≤ K k := by
    intro k l
    by_cases hk : k = j
    · subst k
      simp only [Matrix.updateRow_self, K, ite_true, Pi.single_apply]
      split_ifs <;> norm_num
    · simpa only [Matrix.updateRow_ne hk, K, hk, ite_false] using hA k l
  have hprod : (∏ k, K k) = H ^ (Fintype.card ι - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ K (Finset.mem_univ j)]
    have hj : K j = 1 := by simp [K]
    rw [hj, one_mul]
    calc
      (∏ k ∈ Finset.univ.erase j, K k) = ∏ _k ∈ Finset.univ.erase j, H := by
        apply Finset.prod_congr rfl
        intro k hk
        simp only [K, Finset.ne_of_mem_erase hk, ite_false]
      _ = _ := by simp
  simpa only [hprod] using matrix_det_abs_le_row_bounds _ K hentry

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

def SupportedCube.tail {j : ℕ} {Q : Finset A} (p : SupportedCube (j + 1) (Q : Set A)) :
    SupportedCube j (derivativeSupport Q (p.val.1 0) : Set A) := by
  refine ⟨(Fin.tail p.val.1, p.val.2), ?_⟩
  intro ω
  apply Finset.mem_filter.mpr
  have hfalse := p.property (Fin.cons false ω)
  have htrue := p.property (Fin.cons true ω)
  rw [← Fin.cons_self_tail p.val.1, cubeShift_cons_false] at hfalse
  rw [← Fin.cons_self_tail p.val.1, cubeShift_cons_true] at htrue
  exact ⟨hfalse, by simpa only [Finset.mem_coe, add_assoc, add_left_comm, add_comm] using htrue⟩

def SupportedCube.cons {j : ℕ} {Q : Finset A} (h : A)
    (p : SupportedCube j (derivativeSupport Q h : Set A)) : SupportedCube (j + 1) (Q : Set A) := by
  refine ⟨(Fin.cons h p.val.1, p.val.2), ?_⟩
  intro ω
  obtain ⟨hfalse, htrue⟩ := Finset.mem_filter.mp (p.property (Fin.tail ω))
  rw [← Fin.cons_self_tail ω]
  cases ω 0 with
  | false => simpa only [Finset.mem_coe, cubeShift_cons_false] using hfalse
  | true => simpa only [Finset.mem_coe, cubeShift_cons_true, add_assoc, add_left_comm, add_comm] using htrue

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace VectorPolynomial

variable {σ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

theorem degreeLE_iff (w : σ → ℕ) (d : ℕ) (p : VectorPolynomial σ R V) :
    DegreeLE w d p ↔ ∀ α ∈ (coefficients p).support, Finsupp.weight w α ≤ d := by
  classical
  simp only [DegreeLE, Finsupp.mem_support_iff]
  exact ⟨fun h α hα => le_of_not_gt (fun hd => hα (h α hd)),
    fun h α hd => Classical.byContradiction (fun hα => (not_le_of_gt hd) (h α hα))⟩

theorem DegreeLE.map {w : σ → ℕ} {d : ℕ} {p : VectorPolynomial σ R V}
    (hp : DegreeLE w d p) (f : V →ₗ[R] W) : DegreeLE w d (map f p) := by
  intro α hα
  rw [coefficients_map, hp α hα, f.map_zero]

theorem degreeLE_map_iff (w : σ → ℕ) (d : ℕ) (f : V →ₗ[R] W)
    (hf : Function.Injective f) (p : VectorPolynomial σ R V) :
    DegreeLE w d (map f p) ↔ DegreeLE w d p := by
  refine ⟨fun h α hα => hf ?_, fun h => h.map f⟩
  simpa only [coefficients_map, f.map_zero] using h α hα

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

theorem eval_restrictCoefficients (P : Submodule R V) (p : VectorPolynomial σ R V)
    (hp : ∀ α, coefficients p α ∈ P) (x : σ → R) :
    (eval (V := P) x (restrictCoefficients P p hp) : V) = eval x p := by
  change P.subtype (eval x (restrictCoefficients P p hp)) = _
  rw [← eval_map, map_restrictCoefficients]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffinePhaseBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace CircleFourier

noncomputable def geometricCharacterMean (N : ℕ) (x : Circle) : ℂ :=
  𝔼 n : Fin N, character ((n : ℕ) • x)

end CircleFourier
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem expect_dependent_fin_cons {n : ℕ} {X : Fin (n+1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (∀ i, X i) → M) :
    (𝔼 x, F x) = 𝔼 a : X 0, 𝔼 y : ∀ i : Fin n, X i.succ, F (Fin.cons a y) := by
  calc
    (𝔼 x, F x) = 𝔼 p : X 0 × (∀ i : Fin n, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.expect_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := by
      simpa using (Finset.expect_product' (Finset.univ : Finset (X 0))
        (Finset.univ : Finset (∀ i : Fin n, X i.succ)) (fun a y => F (Fin.cons a y)))

theorem nearIntegerDensity_product_cons {n : ℕ} {X : Fin (n+1) → Type*}
    [∀ i, Fintype (X i)] (v : ∀ i, X i → ℤ) (θ ε : ℝ) :
    nearIntegerDensity (fun x : ∀ i, X i => θ * ∏ i, (v i (x i) : ℝ)) ε =
      𝔼 y : ∀ i : Fin n, X i.succ,
        nearIntegerDensity (fun a : X 0 =>
          (v 0 a : ℝ) * (θ * ∏ i : Fin n, (v i.succ (y i) : ℝ))) ε := by
  unfold nearIntegerDensity
  rw [expect_dependent_fin_cons, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro a _
  congr 2
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDifferenceHom
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem expect_two_dependent_fin_cons {n : ℕ} {X : Fin (n+1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (∀ i, X i) → (∀ i, X i) → M) :
    (𝔼 x, 𝔼 y, F x y) =
      𝔼 a : X 0, 𝔼 b : X 0, 𝔼 u : ∀ i : Fin n, X i.succ,
        𝔼 v : ∀ i : Fin n, X i.succ, F (Fin.cons a u) (Fin.cons b v) := by
  rw [expect_dependent_fin_cons]
  apply Finset.expect_congr rfl
  intro a _
  simp_rw [expect_dependent_fin_cons]
  exact Finset.expect_comm _ _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def iteratedBoxDifference {Z : Type*} :
    (n : ℕ) → {X : Fin n → Type*} → ((∀ i, X i) → Z → ℂ) →
      (∀ i, X i) → (∀ i, X i) → Z → ℂ
  | 0, _, F, _, _, z => F (fun i => Fin.elim0 i) z
  | n+1, _, F, u, v, z => iteratedBoxDifference n
      (fun x z => F (Fin.cons (u 0) x) z * star (F (Fin.cons (v 0) x) z))
      (Fin.tail u) (Fin.tail v) z

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def additiveBoxDifference {Z R : Type*} [AddGroup R] :
    (n : ℕ) → {X : Fin n → Type*} → ((∀ i, X i) → Z → R) →
      (∀ i, X i) → (∀ i, X i) → Z → R
  | 0, _, F, _, _, z => F (fun i => Fin.elim0 i) z
  | n+1, _, F, u, v, z => additiveBoxDifference n
      (fun x z => F (Fin.cons (u 0) x) z - F (Fin.cons (v 0) x) z)
      (Fin.tail u) (Fin.tail v) z

theorem additiveBoxDifference_sum {Z R J : Type*} [AddCommGroup R]
    (n : ℕ) {X : Fin n → Type*} (S : Finset J)
    (F : J → (∀ i, X i) → Z → R) (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x z => ∑ j ∈ S, F j x z) u v z =
      ∑ j ∈ S, additiveBoxDifference n (F j) u v z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [additiveBoxDifference, ← Finset.sum_sub_distrib]
    exact ih (fun j x z => F j (Fin.cons (u 0) x) z - F j (Fin.cons (v 0) x) z)
      (Fin.tail u) (Fin.tail v)

theorem additiveBoxDifference_product {Z R : Type*} [CommRing R]
    (n : ℕ) {X : Fin n → Type*} (a : Z → R) (f : ∀ i, X i → R)
    (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x z => a z * ∏ i, f i (x i)) u v z =
      a z * ∏ i, (f i (u i)-f i (v i)) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [additiveBoxDifference]
    have he : (fun x z =>
        a z * ∏ i, f i (Fin.cons (u 0) x i) - a z * ∏ i, f i (Fin.cons (v 0) x i)) =
        (fun (x : ∀ i : Fin n, X i.succ) z =>
          (a z*(f 0 (u 0)-f 0 (v 0))) * ∏ i, f i.succ (x i)) := by
      funext x z
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring
    rw [he, ih]
    simp only [Fin.prod_univ_succ, Fin.tail_def]
    ring

end Erdos3

end

section

namespace Erdos3

theorem additiveBoxDifference_hom {Z R S : Type*} [AddGroup R] [AddGroup S]
    (L : R →+ S) (n : ℕ) {X : Fin n → Type*}
    (F : (∀ i, X i) → Z → R) (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x t => L (F x t)) u v z =
      L (additiveBoxDifference n F u v z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [additiveBoxDifference, ← map_sub]
    exact ih (fun x t => F (Fin.cons (u 0) x) t - F (Fin.cons (v 0) x) t)
      (Fin.tail u) (Fin.tail v)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

noncomputable def site {α β R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) : Variable α β → R
  | none => 1
  | some (.inl i) => if i ∈ s then 1 else 0
  | some (.inr _) => 0

noncomputable def formPolynomial {α β R : Type*} [CommRing R] :
    Form α β → MvPolynomial (Variable α β) R
  | .coordinate v => X v
  | .difference i => X (some (.inl i)) - X none

noncomputable def formProduct {α β R : Type*} [CommRing R]
    (l : List (Form α β)) : MvPolynomial (Variable α β) R :=
  (l.map formPolynomial).prod

theorem formProduct_nil {α β R : Type*} [CommRing R] :
    formProduct (R := R) ([] : List (Form α β)) = 1 := rfl

theorem formProduct_cons {α β R : Type*} [CommRing R]
    (f : Form α β) (l : List (Form α β)) :
    formProduct (R := R) (f :: l) = formPolynomial f * formProduct l := rfl

noncomputable def vanishingSpan {α β R : Type*} [DecidableEq α] [CommRing R]
    (h : ℕ) : Submodule R (MvPolynomial (Variable α β) R) :=
  Submodule.span R {P | ∃ l : List (Form α β), l.length = h ∧
    (∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) ∧ P = formProduct l}

theorem formProduct_mem_vanishingSpan {α β R : Type*} [DecidableEq α] [CommRing R]
    (l : List (Form α β)) (hz : ∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) :
    formProduct (R := R) l ∈ vanishingSpan l.length :=
  Submodule.subset_span ⟨l, rfl, hz, rfl⟩

theorem vanishingSpan_eval_zero {α β R : Type*} [DecidableEq α] [CommRing R]
    {h : ℕ} {P : MvPolynomial (Variable α β) R} (hP : P ∈ vanishingSpan h) (s : Finset α) :
    eval (site s) P = 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP => obtain ⟨l, _, hz, rfl⟩ := hP; exact hz s
  | zero => simp
  | add P Q _ _ hP hQ => simp only [map_add, hP, hQ, add_zero]
  | smul a P _ hP => simp only [smul_eq_C_mul, map_mul, eval_C, hP, mul_zero]

theorem vanishingSpan_mul_form {α β R : Type*} [DecidableEq α] [CommRing R]
    {h : ℕ} {P : MvPolynomial (Variable α β) R} (hP : P ∈ vanishingSpan h) (f : Form α β) :
    formPolynomial f * P ∈ vanishingSpan (h + 1) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, hz, rfl⟩ := hP
    have he : (f :: l).length = h + 1 := by simp [hl]
    rw [← formProduct_cons, ← he]
    apply formProduct_mem_vanishingSpan
    intro s
    rw [formProduct_cons, map_mul, hz, mul_zero]
  | zero => simpa only [mul_zero] using (vanishingSpan (h + 1)).zero_mem
  | add P Q _ _ hP hQ =>
    simpa only [mul_add] using (vanishingSpan (h + 1)).add_mem hP hQ
  | smul a P _ hP =>
    simpa only [mul_smul_comm] using (vanishingSpan (h + 1)).smul_mem a hP

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

noncomputable def normalMonomial (h : ℕ) (s : Finset α) : MvPolynomial (Variable α β) R :=
  X none ^ (h - s.card) * ∏ i ∈ s, X (some (.inl i))

noncomputable def normalWord (h : ℕ) (s : Finset α) : List (Form α β) :=
  List.replicate (h - s.card) (.coordinate none) ++ s.toList.map (fun i => .coordinate (some (.inl i)))

omit [DecidableEq α] in
theorem normalWord_length (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    (normalWord (β := β) h s).length = h := by
  simp only [normalWord, List.length_append, List.length_replicate, List.length_map,
    Finset.length_toList, Nat.sub_add_cancel hs]

omit [DecidableEq α] in
theorem normalWord_product (h : ℕ) (s : Finset α) :
    formProduct (R := R) (normalWord (β := β) h s) = normalMonomial h s := by
  simp only [normalWord, formProduct, List.map_append, List.prod_append,
    List.map_replicate, List.prod_replicate, List.map_map]
  rw [Finset.prod_map_toList]
  rfl

theorem normalMonomial_eval (h : ℕ) (s t : Finset α) :
    eval (site (β := β) t) (normalMonomial (R := R) h s) = if s ⊆ t then 1 else 0 := by
  simp only [normalMonomial, map_mul, map_pow, eval_X, site, one_pow, one_mul, map_prod]
  by_cases hst : s ⊆ t
  · rw [if_pos hst]
    exact Finset.prod_eq_one (fun i hi => by simp [hst hi])
  · rw [if_neg hst]
    obtain ⟨i, his, hit⟩ := Finset.not_subset.mp hst
    exact Finset.prod_eq_zero his (by simp [hit])

theorem normalMonomial_jet (h : ℕ) (s t : Finset α) :
    booleanCoefficient (fun u => eval (site (β := β) u) (normalMonomial (R := R) h s)) t =
      if t = s then 1 else 0 := by
  simp_rw [normalMonomial_eval]
  exact booleanCoefficient_monomial s t

noncomputable def normalSpan (h : ℕ) : Submodule R (MvPolynomial (Variable α β) R) :=
  Submodule.span R {P | ∃ s : Finset α, s.card ≤ h ∧ P = normalMonomial h s}

omit [DecidableEq α] in
theorem normalMonomial_mem (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    normalMonomial (β := β) (R := R) h s ∈ normalSpan h :=
  Submodule.subset_span ⟨s, hs, rfl⟩

omit [DecidableEq α] in
theorem normalMonomial_mul_root (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    X none * normalMonomial (β := β) (R := R) h s = normalMonomial (h + 1) s := by
  have he : h + 1 - s.card = (h - s.card) + 1 := by omega
  simp only [normalMonomial, he, pow_succ]
  ring

theorem normalMonomial_mul_new (h : ℕ) (s : Finset α) (i : α) (hi : i ∉ s) :
    X (some (.inl i)) * normalMonomial (β := β) (R := R) h s =
      normalMonomial (h + 1) (insert i s) := by
  simp only [normalMonomial, Finset.card_insert_of_notMem hi, Nat.add_sub_add_right,
    Finset.prod_insert hi]
  ring

theorem normalMonomial_mul_coordinate (h : ℕ) (s : Finset α) (hs : s.card ≤ h)
    (v : Variable α β) :
    X v * normalMonomial (R := R) h s ∈ vanishingSpan (h + 1) ⊔ normalSpan (h + 1) := by
  cases v with
  | none =>
    rw [normalMonomial_mul_root h s hs]
    exact Submodule.mem_sup_right (normalMonomial_mem _ _ (by omega))
  | some v =>
    cases v with
    | inl i =>
      by_cases hi : i ∈ s
      · have hz : (X (some (.inl i)) - X none) * normalMonomial (β := β) (R := R) h s ∈
            vanishingSpan (h + 1) := by
          have he : (Form.difference i :: normalWord (β := β) h s).length = h + 1 := by
            simp only [List.length_cons, normalWord_length h s hs]
          rw [← he, ← normalWord_product h s]
          change formProduct (R := R) (Form.difference i :: normalWord h s) ∈ _
          apply formProduct_mem_vanishingSpan
          intro t
          rw [formProduct_cons, normalWord_product, map_mul, normalMonomial_eval]
          by_cases hst : s ⊆ t
          · simp [formPolynomial, site, hst, hst hi]
          · simp [hst]
        have hn := normalMonomial_mem (β := β) (R := R) (h + 1) s (by omega)
        rw [← normalMonomial_mul_root h s hs] at hn
        have he : X (some (.inl i)) * normalMonomial (β := β) (R := R) h s =
            (X (some (.inl i)) - X none) * normalMonomial h s +
              X none * normalMonomial h s := by ring
        rw [he]
        exact Submodule.add_mem_sup hz hn
      · rw [normalMonomial_mul_new h s i hi]
        exact Submodule.mem_sup_right (normalMonomial_mem _ _ (by
          rw [Finset.card_insert_of_notMem hi]; omega))
    | inr j =>
      apply Submodule.mem_sup_left
      have he : (Form.coordinate (some (.inr j)) :: normalWord (β := β) h s).length = h + 1 := by
        simp only [List.length_cons, normalWord_length h s hs]
      rw [← he, ← normalWord_product h s]
      change formProduct (R := R) (Form.coordinate (some (.inr j)) :: normalWord h s) ∈ _
      apply formProduct_mem_vanishingSpan
      intro t
      simp only [formProduct_cons, map_mul, formPolynomial, eval_X, site, zero_mul]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

theorem normalSpan_mul_coordinate {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P ∈ normalSpan h) (v : Variable α β) :
    X v * P ∈ vanishingSpan (h + 1) ⊔ normalSpan (h + 1) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨s, hs, rfl⟩ := hP
    exact normalMonomial_mul_coordinate h s hs v
  | zero => simp only [mul_zero]; exact Submodule.zero_mem _
  | add P Q _ _ hP hQ =>
    rw [mul_add]
    exact Submodule.add_mem _ hP hQ
  | smul a P _ hP =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ a hP

theorem reductionSpace_mul_coordinate {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P ∈ vanishingSpan h ⊔ normalSpan h) (v : Variable α β) :
    X v * P ∈ vanishingSpan (h + 1) ⊔ normalSpan (h + 1) := by
  obtain ⟨A, hA, B, hB, rfl⟩ := Submodule.mem_sup.mp hP
  rw [mul_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (vanishingSpan_mul_form hA (.coordinate v)))
    (normalSpan_mul_coordinate hB v)

theorem reductionSpace_mul_linear {h : ℕ} {P L : MvPolynomial (Variable α β) R}
    (hP : P ∈ vanishingSpan h ⊔ normalSpan h) (hL : L.IsHomogeneous 1) :
    L * P ∈ vanishingSpan (h + 1) ⊔ normalSpan (h + 1) := by
  have hL' : L ∈ Submodule.span R (Set.range (X : Variable α β → MvPolynomial _ R)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hL
  clear hL
  induction hL' using Submodule.span_induction with
  | mem L hL =>
    obtain ⟨v, rfl⟩ := hL
    exact reductionSpace_mul_coordinate hP v
  | zero => simp only [zero_mul]; exact Submodule.zero_mem _
  | add A B _ _ hA hB =>
    rw [add_mul]
    exact Submodule.add_mem _ hA hB
  | smul a L _ hL =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ a hL

theorem homogeneous_mem_reductionSpace {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P.IsHomogeneous h) : P ∈ vanishingSpan h ⊔ normalSpan h := by
  induction h generalizing P with
  | zero =>
    have hp : P ∈ (1 : Submodule R (MvPolynomial (Variable α β) R)) := by
      rw [← homogeneousSubmodule_zero]
      exact hP
    obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hp
    apply Submodule.mem_sup_right
    have hone := normalMonomial_mem (β := β) (R := R) 0 (∅ : Finset α) (by simp)
    have hc := (normalSpan (α := α) (β := β) (R := R) 0).smul_mem a hone
    simpa only [normalMonomial, Finset.card_empty, Nat.sub_self, pow_zero, Finset.prod_empty,
      mul_one, smul_eq_C_mul, algebraMap_eq] using hc
  | succ h ih =>
    have hp : P ∈ homogeneousSubmodule (Variable α β) R 1 *
        homogeneousSubmodule (Variable α β) R h := by
      rw [← homogeneousSubmodule_one_pow (σ := Variable α β) R h, ← pow_succ',
        homogeneousSubmodule_one_pow (σ := Variable α β) R (h + 1)]
      exact hP
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro L hL Q hQ
      exact reductionSpace_mul_linear (ih hQ) hL
    · intro A B hA hB
      exact Submodule.add_mem _ hA hB

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

noncomputable def siteEvaluation :
    MvPolynomial (Variable α β) R →ₗ[R] (Finset α → R) where
  toFun P s := eval (site s) P
  map_add' P Q := by ext s; exact map_add _ _ _
  map_smul' a P := by ext s; exact smul_eval _ _ _

noncomputable def interpolation (h : ℕ) : (Finset α → R) →ₗ[R] MvPolynomial (Variable α β) R :=
  ∑ s : Finset α, if s.card ≤ h then (coefficientLinear s).smulRight (normalMonomial h s) else 0

theorem interpolation_apply (h : ℕ) (f : Finset α → R) :
    interpolation (β := β) h f =
      ∑ s : Finset α, if s.card ≤ h then booleanCoefficient f s • normalMonomial h s else 0 := by
  simp only [interpolation, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s.card ≤ h
  · simp only [hs, ite_true, LinearMap.smulRight_apply]
    rfl
  · simp only [hs, ite_false, LinearMap.zero_apply]

theorem interpolation_normalMonomial (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    interpolation (β := β) h (siteEvaluation (normalMonomial (β := β) (R := R) h s)) =
      normalMonomial h s := by
  rw [interpolation_apply]
  change (∑ t : Finset α, if t.card ≤ h then
    booleanCoefficient (fun u => eval (site u) (normalMonomial (β := β) (R := R) h s)) t •
      normalMonomial h t else 0) = _
  simp_rw [normalMonomial_jet]
  rw [Finset.sum_eq_single s]
  · simp only [hs, ite_true, one_smul]
  · intro t _ ht
    simp only [ht, ite_false, zero_smul, ite_self]
  · simp

theorem interpolation_eq_of_mem_normalSpan {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P ∈ normalSpan h) : interpolation h (siteEvaluation P) = P := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨s, hs, rfl⟩ := hP
    exact interpolation_normalMonomial h s hs
  | zero => simp only [map_zero]
  | add P Q _ _ hP hQ => simp only [map_add, hP, hQ]
  | smul a P _ hP => simp only [map_smul, hP]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

theorem remainder_mem_vanishingSpan {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P.IsHomogeneous h) : P - interpolation h (siteEvaluation P) ∈ vanishingSpan h := by
  obtain ⟨A, hA, B, hB, he⟩ := Submodule.mem_sup.mp (homogeneous_mem_reductionSpace hP)
  have hEA : siteEvaluation A = 0 := by ext s; exact vanishingSpan_eval_zero hA s
  rw [← he, map_add, hEA, zero_add, interpolation_eq_of_mem_normalSpan hB, add_sub_cancel_right]
  exact hA

omit [Fintype α] in
theorem map_vanishingSpan_eq_zero (Λ : MvPolynomial (Variable α β) R →ₗ[R] V) {h : ℕ}
    (hkill : ∀ l : List (Form α β), l.length = h →
      (∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) → Λ (formProduct l) = 0)
    {P : MvPolynomial (Variable α β) R} (hP : P ∈ vanishingSpan h) : Λ P = 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, hz, rfl⟩ := hP
    exact hkill l hl hz
  | zero => exact map_zero Λ
  | add P Q _ _ hP hQ => simp only [map_add, hP, hQ, add_zero]
  | smul a P _ hP => simp only [map_smul, hP, smul_zero]

theorem factor_through_sites_of_kills_products
    (Λ : MvPolynomial (Variable α β) R →ₗ[R] V) (h : ℕ)
    (hkill : ∀ l : List (Form α β), l.length = h →
      (∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) → Λ (formProduct l) = 0)
    {P : MvPolynomial (Variable α β) R} (hP : P.IsHomogeneous h) :
    Λ P = (Λ.comp (interpolation h)) (siteEvaluation P) := by
  have hz := map_vanishingSpan_eq_zero Λ hkill (remainder_mem_vanishingSpan hP)
  rw [map_sub, sub_eq_zero] at hz
  exact hz

theorem exists_vanishing_product_of_nonfactor
    (Λ : MvPolynomial (Variable α β) R →ₗ[R] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → R) →ₗ[R] V,
      ∀ P, P.IsHomogeneous h → Λ P = L (siteEvaluation P)) :
    ∃ l : List (Form α β), l.length = h ∧
      (∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) ∧ Λ (formProduct l) ≠ 0 := by
  by_contra hnone
  apply hnonfactor
  refine ⟨Λ.comp (interpolation h), fun P hP => factor_through_sites_of_kills_products Λ h ?_ hP⟩
  intro l hl hz
  by_contra hne
  exact hnone ⟨l, hl, hz, hne⟩

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem realPolynomialMass_C {I : Type*} (c : ℝ) :
    realPolynomialMass (MvPolynomial.C c : MvPolynomial I ℝ) = |c| :=
  realPolynomialMass_monomial 0 c

theorem realPolynomialMass_one {I : Type*} : realPolynomialMass (1 : MvPolynomial I ℝ) = 1 := by
  simpa only [map_one, abs_one] using (realPolynomialMass_C (I := I) 1)

theorem realPolynomialMass_coeff_le {I : Type*} (p : MvPolynomial I ℝ) (m : I →₀ ℕ) :
    |p.coeff m| ≤ realPolynomialMass p := by
  classical
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (fun n _ => abs_nonneg (p.coeff n)) hm
  · rw [MvPolynomial.notMem_support_iff.mp hm, abs_zero]
    exact realPolynomialMass_nonneg p

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realPolynomialMass_prod_le {I J : Type*} (s : Finset J) (p : J → MvPolynomial I ℝ) :
    realPolynomialMass (∏ j ∈ s, p j) ≤ ∏ j ∈ s, realPolynomialMass (p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, realPolynomialMass_one, le_refl]
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact (realPolynomialMass_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (realPolynomialMass_nonneg _))

theorem realPolynomialMass_C_mul_le {I : Type*} (c : ℝ) (p : MvPolynomial I ℝ) :
    realPolynomialMass (MvPolynomial.C c * p) ≤ |c| * realPolynomialMass p := by
  simpa only [realPolynomialMass_C] using realPolynomialMass_mul_le (MvPolynomial.C c) p

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem polynomialFunctional_le_mass {σ : Type*}
    (L : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (P : MvPolynomial σ ℝ) {C : ℝ}
    (hL : ∀ d ∈ P.support, |L (monomial d 1)| ≤ C) :
    |L P| ≤ C * realPolynomialMass P := by
  rw [polynomialFunctional_expansion]
  calc
    _ ≤ ∑ d ∈ P.support, |P.coeff d * L (monomial d 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.support, C * |P.coeff d| := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hL d hd) (abs_nonneg _)
    _ = C * realPolynomialMass P := by rw [realPolynomialMass, Finset.mul_sum]

theorem polynomialFunctional_homogeneous_le_mass {σ : Type*}
    (L : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) {P : MvPolynomial σ ℝ} {h : ℕ}
    (hP : P.IsHomogeneous h) {C : ℝ}
    (hL : ∀ d : σ →₀ ℕ, d.degree = h → |L (monomial d 1)| ≤ C) :
    |L P| ≤ C * realPolynomialMass P :=
  polynomialFunctional_le_mass L P (fun d hd => hL d
    (by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hP (mem_support_iff.mp hd)))

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

theorem realPolynomialMass_neg {K : Type*} (p : MvPolynomial K ℝ) :
    realPolynomialMass (-p) = realPolynomialMass p := by
  classical
  simp [realPolynomialMass]

theorem realPolynomialMass_sub_le {K : Type*} (p q : MvPolynomial K ℝ) :
    realPolynomialMass (p - q) ≤ realPolynomialMass p + realPolynomialMass q := by
  simpa only [sub_eq_add_neg, realPolynomialMass_neg] using realPolynomialMass_add_le p (-q)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IntervalBoxDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem symmetricIntegerInterval_card (N : ℕ) :
    Fintype.card (SymmetricIntegerInterval N) = 2*N+1 := by
  simpa only [Fintype.card_coe] using symmetricInterval_card N

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MultiaffinePhaseDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

noncomputable def multiaffineIntervalPhase {n : ℕ} {N : Fin n → ℕ} {M : ℕ}
    (a b : Finset (Fin n) → ℝ) (u : Fin n → ℝ) (w : ℝ)
    (x : ∀ i, Fin (N i)) (t : Fin M) : ℂ :=
  character ((multiaffineExpansion (fun S => a S*(w+(t.val : ℝ))+b S)
    (fun i => u i+((x i).val : ℝ)) : ℝ) : CircleFourier.Circle)

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

noncomputable def frameCoordinate (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R) : Variable α K → MvPolynomial (Option K) R
  | none => X none
  | some (.inl i) => q i
  | some (.inr k) => X (some k) - C (root k) * X none - ∑ i, C (difference i k) * q i

noncomputable def liftCoordinate (root : K → R) (difference : α → K → R) :
    Option K → MvPolynomial (Variable α K) R
  | none => X none
  | some k => C (root k) * X none + ∑ i, C (difference i k) * X (some (.inl i)) + X (some (.inr k))

noncomputable def frameProjection (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R) :
    MvPolynomial (Variable α K) R →ₐ[R] MvPolynomial (Option K) R :=
  aeval (frameCoordinate root difference q)

noncomputable def frameLift (root : K → R) (difference : α → K → R) :
    MvPolynomial (Option K) R →ₐ[R] MvPolynomial (Variable α K) R :=
  aeval (liftCoordinate root difference)

omit [DecidableEq α] in
theorem frameProjection_lift (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R) (P : MvPolynomial (Option K) R) :
    frameProjection root difference q (frameLift root difference P) = P := by
  have he : (frameProjection root difference q).comp (frameLift root difference) = AlgHom.id R _ := by
    apply algHom_ext
    intro v
    cases v with
    | none => simp [frameProjection, frameLift, liftCoordinate, frameCoordinate]
    | some k =>
      simp only [AlgHom.comp_apply, frameLift, aeval_X, liftCoordinate, frameProjection,
        map_add, map_sum, map_mul, aeval_C, algebraMap_eq, aeval_X, frameCoordinate, AlgHom.id_apply]
      ring
  exact AlgHom.congr_fun he P

omit [DecidableEq α] in
theorem liftCoordinate_homogeneous (root : K → R) (difference : α → K → R) (v : Option K) :
    (liftCoordinate root difference v).IsHomogeneous 1 := by
  cases v with
  | none => exact isHomogeneous_X R _
  | some k =>
    have hs : (∑ i, C (difference i k) * X (some (.inl i)) :
        MvPolynomial (Variable α K) R).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ (fun i _ => (isHomogeneous_X R _).C_mul (difference i k))
    exact (((isHomogeneous_X R _).C_mul (root k)).add hs).add (isHomogeneous_X R _)

omit [DecidableEq α] in
theorem frameLift_homogeneous (root : K → R) (difference : α → K → R)
    {P : MvPolynomial (Option K) R} {h : ℕ} (hP : P.IsHomogeneous h) :
    (frameLift root difference P).IsHomogeneous h := by
  simpa only [frameLift, Nat.one_mul] using
    hP.aeval (liftCoordinate root difference) (liftCoordinate_homogeneous root difference)

theorem frameCoordinate_eval (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R)
    (hq : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    (s : Finset α) (v : Variable α K) :
    eval (affineSite root difference s) (frameCoordinate root difference q v) = site s v := by
  cases v with
  | none => simp [frameCoordinate, affineSite, site]
  | some v =>
    cases v with
    | inl i => exact hq i s
    | inr k =>
      simp only [frameCoordinate, map_sub, map_mul, map_sum, eval_X, eval_C, affineSite,
        hq, mul_one, mul_ite, mul_zero, site]
      simp

theorem frameProjection_eval (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R)
    (hq : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    (s : Finset α) (P : MvPolynomial (Variable α K) R) :
    eval (affineSite root difference s) (frameProjection root difference q P) = eval (site s) P := by
  have he : (aeval (affineSite root difference s)).comp (frameProjection root difference q) =
      aeval (site (β := K) s) := by
    apply algHom_ext
    intro v
    simpa only [AlgHom.comp_apply, frameProjection, aeval_X, aeval_eq_eval] using
      frameCoordinate_eval root difference q hq s v
  exact AlgHom.congr_fun he P

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedIntegerDual
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α K R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

theorem frameLift_siteEvaluation (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R)
    (hq : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    (P : MvPolynomial (Option K) R) :
    siteEvaluation (frameLift root difference P) = fun s => eval (affineSite root difference s) P := by
  funext s
  change eval (site s) (frameLift root difference P) = _
  rw [← frameProjection_eval root difference q hq, frameProjection_lift]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem homogeneousDual_mass {I K : Type*} [Fintype I]
    (root : K → ℝ) (selection : I → K) (n : I → ℝ) {H N : ℝ}
    (hN : 0 ≤ N) (hroot : ∀ j, |root (selection j)| ≤ H) (hn : ∀ j, |n j| ≤ N) :
    realPolynomialMass (homogeneousDual root selection n) ≤ (Fintype.card I : ℝ) * (N * (1 + H)) := by
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : I, N * (1 + H) := by
      apply Finset.sum_le_sum
      intro j _
      have hr : realPolynomialMass (C (root (selection j)) * X (none : Option K)) ≤ H := by
        exact (realPolynomialMass_C_mul_le (root (selection j)) (X (none : Option K))).trans
            (by simpa only [realPolynomialMass_X, mul_one] using hroot j)
      have hs : realPolynomialMass (X (some (selection j)) - C (root (selection j)) * X none) ≤ 1 + H := by
        exact (realPolynomialMass_sub_le _ _).trans (by rw [realPolynomialMass_X]; linarith)
      exact (realPolynomialMass_C_mul_le _ _).trans
        (mul_le_mul (hn j) hs (realPolynomialMass_nonneg _) hN)
    _ = _ := by simp

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def scaledFrameForm {α K R : Type*} [Fintype α] [CommRing R]
    (root : K → R) (difference : α → K → R) (a : R)
    (numerator : α → MvPolynomial (Option K) R) : Form α K → MvPolynomial (Option K) R
  | .coordinate none => C a * X none
  | .coordinate (some (.inl i)) => numerator i
  | .coordinate (some (.inr k)) =>
      C a * (X (some k) - C (root k) * X none) - ∑ i, C (difference i k) * numerator i
  | .difference i => numerator i - C a * X none

theorem scaledFrameForm_homogeneous {α K R : Type*} [Fintype α] [CommRing R]
    (root : K → R) (difference : α → K → R) (a : R)
    (numerator : α → MvPolynomial (Option K) R)
    (hn : ∀ i, (numerator i).IsHomogeneous 1) (f : Form α K) :
    (scaledFrameForm root difference a numerator f).IsHomogeneous 1 := by
  cases f with
  | coordinate v =>
    cases v with
    | none => exact (isHomogeneous_X R _).C_mul a
    | some v =>
      cases v with
      | inl i => exact hn i
      | inr k =>
        apply (((isHomogeneous_X R _).sub ((isHomogeneous_X R _).C_mul (root k))).C_mul a).sub
        exact IsHomogeneous.sum _ _ _ (fun i _ => (hn i).C_mul (difference i k))
  | difference i => exact (hn i).sub ((isHomogeneous_X R _).C_mul a)

theorem scaledFrameForm_map {α K R S : Type*} [Fintype α] [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (difference : α → K → R) (a : R)
    (numerator : α → MvPolynomial (Option K) R) (q : α → MvPolynomial (Option K) S)
    (hn : ∀ i, map ρ (numerator i) = C (ρ a) * q i) (f : Form α K) :
    map ρ (scaledFrameForm root difference a numerator f) =
      C (ρ a) * frameProjection (fun k => ρ (root k)) (fun i k => ρ (difference i k)) q (formPolynomial f) := by
  cases f with
  | coordinate v =>
    cases v with
    | none => simp [scaledFrameForm, frameProjection, formPolynomial, frameCoordinate]
    | some v =>
      cases v with
      | inl i => simpa only [scaledFrameForm, frameProjection, formPolynomial, aeval_X, frameCoordinate] using hn i
      | inr k =>
        have hs : (∑ i, C (ρ (difference i k)) * (C (ρ a) * q i)) =
            C (ρ a) * ∑ i, C (ρ (difference i k)) * q i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        simp only [scaledFrameForm, map_sub, map_mul, map_sum, map_C, map_X, hn,
          frameProjection, formPolynomial, aeval_X, frameCoordinate]
        rw [hs]
        ring
  | difference i =>
    simp only [scaledFrameForm, map_sub, map_mul, map_C, map_X, hn,
      frameProjection, formPolynomial, aeval_X, frameCoordinate]
    ring

theorem scaledFrameProduct_map {α K R S : Type*} [Fintype α] [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (difference : α → K → R) (a : R)
    (numerator : α → MvPolynomial (Option K) R) (q : α → MvPolynomial (Option K) S)
    (hn : ∀ i, map ρ (numerator i) = C (ρ a) * q i) (l : List (Form α K)) :
    map ρ ((l.map (scaledFrameForm root difference a numerator)).prod) =
      C ((ρ a) ^ l.length) *
        frameProjection (fun k => ρ (root k)) (fun i k => ρ (difference i k)) q (formProduct l) := by
  induction l with
  | nil => simp [formProduct_nil]
  | cons f l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, scaledFrameForm_map ρ root difference a numerator q hn,
      ih, List.length_cons, pow_succ, map_mul, formProduct_cons]
    ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

theorem integerDifferencePivot_det_bound {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) {D : ℝ}
    (hdiff : ∀ i j, |(difference i (selection j) : ℝ)| ≤ D) :
    |((integerDifferencePivot difference selection).det : ℝ)| ≤
      (Fintype.card α).factorial * D ^ Fintype.card α := by
  rw [integerDifferencePivot_det_cast]
  exact matrix_det_abs_le_uniform_bound _ hdiff

theorem integerDifferencePivot_adjugate_bound {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) {D : ℝ}
    (hdiff : ∀ i j, |(difference i (selection j) : ℝ)| ≤ D) (i j : α) :
    |((integerDifferencePivot difference selection).adjugate i j : ℝ)| ≤
      (Fintype.card α).factorial * D ^ (Fintype.card α - 1) := by
  rw [integerDifferencePivot_adjugate_cast]
  exact matrix_adjugate_entry_abs_le _ hdiff i j

theorem integerPivotNumerator_mass {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K) {H D : ℝ} (hD : 0 ≤ D)
    (hroot : ∀ j, |(root (selection j) : ℝ)| ≤ H)
    (hdiff : ∀ i j, |(difference i (selection j) : ℝ)| ≤ D) (i : α) :
    realPolynomialMass (map (Int.castRingHom ℝ) (integerPivotNumerator root difference selection i)) ≤
      (Fintype.card α : ℝ) *
        (((Fintype.card α).factorial * D ^ (Fintype.card α - 1)) * (1 + H)) := by
  rw [integerPivotNumerator, homogeneousDual_map]
  apply homogeneousDual_mass _ selection _ (by positivity) hroot
  intro j
  exact integerDifferencePivot_adjugate_bound difference selection hdiff j i

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

theorem scaledFrameForm_mass {α K : Type*} [Fintype α]
    (root : K → ℤ) (difference : α → K → ℤ) (a : ℤ)
    (numerator : α → MvPolynomial (Option K) ℤ) {H D A B : ℝ}
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (ha : |(a : ℝ)| ≤ A) (hn : ∀ i, realPolynomialMass (map (Int.castRingHom ℝ) (numerator i)) ≤ B)
    (f : Form α K) :
    realPolynomialMass (map (Int.castRingHom ℝ) (scaledFrameForm root difference a numerator f)) ≤
      integerFormMassBound (Fintype.card α) H D A B := by
  have hcross : 0 ≤ (Fintype.card α : ℝ) * D * B := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hD) hB
  have hax : realPolynomialMass (C (a : ℝ) * X (none : Option K)) ≤ A := by
    exact (realPolynomialMass_C_mul_le _ _).trans (by simpa only [realPolynomialMass_X, mul_one] using ha)
  have hbase (k : K) : realPolynomialMass (X (some k) - C (root k : ℝ) * X (none : Option K)) ≤ 1 + H := by
    have hr : realPolynomialMass (C (root k : ℝ) * X (none : Option K)) ≤ H := by
      exact (realPolynomialMass_C_mul_le _ _).trans (by simpa only [realPolynomialMass_X, mul_one] using hroot k)
    exact (realPolynomialMass_sub_le _ _).trans (by rw [realPolynomialMass_X]; linarith)
  cases f with
  | coordinate v =>
    cases v with
    | none =>
      simp only [scaledFrameForm, map_mul, map_C, map_X, Int.coe_castRingHom]
      exact hax.trans (by unfold integerFormMassBound; nlinarith)
    | some v =>
      cases v with
      | inl i =>
        exact (hn i).trans (by unfold integerFormMassBound; nlinarith)
      | inr k =>
        have hp : realPolynomialMass (C (a : ℝ) * (X (some k) - C (root k : ℝ) * X none)) ≤ A * (1 + H) :=
          (realPolynomialMass_C_mul_le _ _).trans
            (mul_le_mul ha (hbase k) (realPolynomialMass_nonneg _) hA)
        have hs : realPolynomialMass (∑ i, C (difference i k : ℝ) * map (Int.castRingHom ℝ) (numerator i)) ≤
            (Fintype.card α : ℝ) * (D * B) := by
          apply (realPolynomialMass_sum_le _ _).trans
          calc
            _ ≤ ∑ _i : α, D * B := by
              apply Finset.sum_le_sum
              intro i _
              exact (realPolynomialMass_C_mul_le _ _).trans
                (mul_le_mul (hdiff i k) (hn i) (realPolynomialMass_nonneg _) hD)
            _ = _ := by simp
        simp only [scaledFrameForm, map_sub, map_mul, map_sum, map_C, map_X, Int.coe_castRingHom]
        apply (realPolynomialMass_sub_le _ _).trans
        unfold integerFormMassBound
        nlinarith
  | difference i =>
    simp only [scaledFrameForm, map_sub, map_mul, map_C, map_X, Int.coe_castRingHom]
    apply (realPolynomialMass_sub_le _ _).trans
    have hi := hn i
    unfold integerFormMassBound
    nlinarith

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

theorem exists_affine_vanishing_labels {α K R V : Type*} [Fintype α] [DecidableEq α]
    [CommRing R] [AddCommGroup V] [Module R V]
    (root : K → R) (difference : α → K → R) (q : α → MvPolynomial (Option K) R)
    (hdual : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    (Λ : MvPolynomial (Option K) R →ₗ[R] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → R) →ₗ[R] V,
      ∀ P, P.IsHomogeneous h → Λ P = L (fun s => eval (affineSite root difference s) P)) :
    ∃ l : List (Form α K), l.length = h ∧
      (∀ s, eval (affineSite root difference s) (frameProjection root difference q (formProduct l)) = 0) ∧
      Λ (frameProjection root difference q (formProduct l)) ≠ 0 := by
  let E := frameProjection root difference q
  let Λ' := Λ.comp E.toLinearMap
  have hn : ¬ ∃ L : (Finset α → R) →ₗ[R] V,
      ∀ P, P.IsHomogeneous h → Λ' P = L (siteEvaluation P) := by
    rintro ⟨L, hL⟩
    apply hnonfactor
    refine ⟨L, ?_⟩
    intro P hP
    have he := hL (frameLift root difference P) (frameLift_homogeneous root difference hP)
    change Λ (frameProjection root difference q (frameLift root difference P)) = _ at he
    rw [frameProjection_lift, frameLift_siteEvaluation root difference q hdual] at he
    exact he
  obtain ⟨l, hl, hz, hΛ⟩ := exists_vanishing_product_of_nonfactor Λ' h hn
  refine ⟨l, hl, ?_, hΛ⟩
  intro s
  exact (frameProjection_eval root difference q hdual s (formProduct l)).trans (hz s)

theorem exists_integer_vanishing_product {α K V : Type*} [Fintype α] [DecidableEq α]
    [AddCommGroup V] [Module ℝ V]
    (root : K → ℤ) (difference : α → K → ℤ) (a : ℤ) (ha : a ≠ 0)
    (numerator : α → MvPolynomial (Option K) ℤ)
    (hlinear : ∀ i, (numerator i).IsHomogeneous 1)
    (hdual : ∀ i s, eval (affineSite root difference s) (numerator i) = if i ∈ s then a else 0)
    (Λ : MvPolynomial (Option K) ℝ →ₗ[ℝ] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → ℝ) →ₗ[ℝ] V,
      ∀ P, P.IsHomogeneous h → Λ P =
        L (fun s => eval (affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) P)) :
    ∃ forms : List (MvPolynomial (Option K) ℤ), forms.length = h ∧
      (∀ P ∈ forms, P.IsHomogeneous 1 ∧ ∃ f : Form α K, P = scaledFrameForm root difference a numerator f) ∧
      (∀ s : Finset α, ∃ P ∈ forms, eval (affineSite root difference s) P = 0) ∧
      Λ (map (Int.castRingHom ℝ) forms.prod) ≠ 0 := by
  let q := normalizedIntegerDual a numerator
  obtain ⟨l, hl, hz, hΛ⟩ := exists_affine_vanishing_labels
    (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) q
    (normalizedIntegerDual_boolean root difference a ha numerator hdual) Λ h hnonfactor
  have hm := scaledFrameProduct_map (Int.castRingHom ℝ) root difference a numerator q
    (normalizedIntegerDual_clear a ha numerator) l
  simp only [Int.coe_castRingHom] at hm
  let forms := l.map (scaledFrameForm root difference a numerator)
  have hzero (s : Finset α) : eval (affineSite root difference s) forms.prod = 0 := by
    have he := affineSite_eval_map (Int.castRingHom ℝ) root difference s forms.prod
    simp only [Int.coe_castRingHom] at he
    have hc : ((eval (affineSite root difference s) forms.prod : ℤ) : ℝ) = 0 := by
      rw [← he]
      change eval _ (map (Int.castRingHom ℝ) ((l.map (scaledFrameForm root difference a numerator)).prod)) = 0
      rw [hm, map_mul, eval_C, hz, mul_zero]
    exact_mod_cast hc
  refine ⟨forms, ?_, ?_, ?_, ?_⟩
  · simpa only [forms, List.length_map] using hl
  · intro P hP
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hP
    exact ⟨scaledFrameForm_homogeneous root difference a numerator hlinear f, f, rfl⟩
  · intro s
    have hp : (forms.map (fun P => eval (affineSite root difference s) P)).prod = 0 := by
      simpa only [map_list_prod] using hzero s
    exact List.mem_map.mp (List.prod_eq_zero_iff.mp hp)
  · change Λ (map (Int.castRingHom ℝ) ((l.map (scaledFrameForm root difference a numerator)).prod)) ≠ 0
    rw [hm, ← smul_eq_C_mul, map_smul]
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    exact smul_ne_zero (pow_ne_zero _ ha') hΛ

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

theorem exists_bounded_integer_vanishing_product {α K V : Type*} [Fintype α] [DecidableEq α]
    [AddCommGroup V] [Module ℝ V]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K)
    (hdet : (integerDifferencePivot difference selection).det ≠ 0)
    {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (Λ : MvPolynomial (Option K) ℝ →ₗ[ℝ] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → ℝ) →ₗ[ℝ] V,
      ∀ P, P.IsHomogeneous h → Λ P =
        L (fun s => eval (affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) P)) :
    let A := ((Fintype.card α).factorial : ℝ) * D ^ Fintype.card α
    let B := (Fintype.card α : ℝ) *
      ((((Fintype.card α).factorial : ℝ) * D ^ (Fintype.card α - 1)) * (1 + H))
    ∃ forms : List (MvPolynomial (Option K) ℤ), forms.length = h ∧
      (∀ P ∈ forms, P.IsHomogeneous 1 ∧
        realPolynomialMass (map (Int.castRingHom ℝ) P) ≤ integerFormMassBound (Fintype.card α) H D A B) ∧
      (∀ s : Finset α, ∃ P ∈ forms, eval (affineSite root difference s) P = 0) ∧
      Λ (map (Int.castRingHom ℝ) forms.prod) ≠ 0 := by
  intro A B
  let a := (integerDifferencePivot difference selection).det
  let numerator := integerPivotNumerator root difference selection
  obtain ⟨forms, hlen, hforms, hz, hΛ⟩ := exists_integer_vanishing_product root difference a hdet numerator
    (integerPivotNumerator_homogeneous root difference selection)
    (integerPivotNumerator_eval root difference selection) Λ h hnonfactor
  refine ⟨forms, hlen, ?_, hz, hΛ⟩
  intro P hP
  obtain ⟨hhom, f, rfl⟩ := hforms P hP
  refine ⟨hhom, scaledFrameForm_mass root difference a numerator hH hD
    (show 0 ≤ A by dsimp [A]; positivity) (show 0 ≤ B by dsimp [B]; positivity) hroot hdiff ?_ ?_ f⟩
  · exact integerDifferencePivot_det_bound difference selection (fun i j => hdiff i (selection j))
  · intro i
    exact integerPivotNumerator_mass root difference selection hD
      (fun j => hroot (selection j)) (fun i j => hdiff i (selection j)) i

end Erdos3.BooleanCubeKernel

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

def Homogeneous (h : ℕ) (p : VectorPolynomial σ R W) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree ≠ h → coefficients p d = 0

theorem homogeneous_tmul {P : MvPolynomial σ R} {h : ℕ} (hP : P.IsHomogeneous h) (w : W) :
    Homogeneous h (P ⊗ₜ[R] w) := by
  intro d hd
  rw [coefficients_tmul, hP.coeff_eq_zero hd, zero_smul]

theorem homogeneous_support_degree {p : VectorPolynomial σ R W} {h : ℕ}
    (hp : Homogeneous h p) {d : σ →₀ ℕ} (hd : d ∈ (coefficients p).support) : d.degree = h := by
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hd) (hp d hn)

theorem eq_of_homogeneous_tmul (f g : VectorPolynomial σ R W →ₗ[R] Z) (h : ℕ)
    (he : ∀ (P : MvPolynomial σ R), P.IsHomogeneous h → ∀ w, f (P ⊗ₜ[R] w) = g (P ⊗ₜ[R] w))
    {p : VectorPolynomial σ R W} (hp : Homogeneous h p) : f p = g p := by
  have hexp := sum_monomial_coefficients p
  conv_lhs => rw [← hexp]
  conv_rhs => rw [← hexp]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact he (MvPolynomial.monomial d 1)
    (MvPolynomial.isHomogeneous_monomial 1 (homogeneous_support_degree hp hd)) (coefficients p d)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {I R S W : Type*} [CommRing R] [CommRing S] [AddCommGroup W] [Module R W]

noncomputable def homogeneousPart (h : ℕ) :
    VectorPolynomial I R W →ₗ[R] VectorPolynomial I R W :=
  (MvPolynomial.homogeneousComponent h).rTensor W

theorem homogeneousPart_tmul (h : ℕ) (P : MvPolynomial I R) (w : W) :
    homogeneousPart h (P ⊗ₜ[R] w) = MvPolynomial.homogeneousComponent h P ⊗ₜ[R] w := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

theorem realPolynomialMass_fin_prod_le {σ : Type*} {h : ℕ}
    (P : Fin h → MvPolynomial σ ℝ) {B : ℝ}
    (hP : ∀ i, realPolynomialMass (P i) ≤ B) :
    realPolynomialMass (∏ i, P i) ≤ B ^ h := by
  apply (realPolynomialMass_prod_le Finset.univ P).trans
  calc
    _ ≤ ∏ _i : Fin h, B := Finset.prod_le_prod
      (fun i _ => realPolynomialMass_nonneg (P i)) (fun i _ => hP i)
    _ = B ^ h := by simp

namespace VectorPolynomial

noncomputable def contractedRow {σ J R : Type*} [CommRing R]
    (Λ : VectorPolynomial σ R (J → R) →ₗ[R] R) (P : MvPolynomial σ R) : J → R :=
  fun j => Λ (P ⊗ₜ[R] Pi.single j 1)

theorem contractedRow_apply {σ J R : Type*} [Fintype J] [CommRing R]
    (Λ : VectorPolynomial σ R (J → R) →ₗ[R] R) (P : MvPolynomial σ R) (w : J → R) :
    ∑ j, contractedRow Λ P j * w j = Λ (P ⊗ₜ[R] w) :=
  (linearFunctional_eq_coordinate_sum (TensorProduct.curry Λ P) w).symm

def MonomialRowBound {σ J : Type*}
    (Λ : VectorPolynomial σ ℝ (J → ℝ) →ₗ[ℝ] ℝ) (h : ℕ) (C : ℝ) : Prop :=
  ∀ (d : σ →₀ ℕ), d.degree = h → ∀ j, |Λ (MvPolynomial.monomial d 1 ⊗ₜ[ℝ] Pi.single j 1)| ≤ C

theorem contractedRow_le_mass {σ J : Type*}
    (Λ : VectorPolynomial σ ℝ (J → ℝ) →ₗ[ℝ] ℝ) {P : MvPolynomial σ ℝ} {h : ℕ}
    (hP : P.IsHomogeneous h) {C : ℝ} (hΛ : MonomialRowBound Λ h C) (j : J) :
    |contractedRow Λ P j| ≤ C * realPolynomialMass P :=
  polynomialFunctional_homogeneous_le_mass ((TensorProduct.curry Λ).flip (Pi.single j 1))
    hP (fun d hd => hΛ d hd j)

theorem contractedRow_prod_bound {σ J : Type*}
    (Λ : VectorPolynomial σ ℝ (J → ℝ) →ₗ[ℝ] ℝ) {h : ℕ}
    (P : Fin h → MvPolynomial σ ℝ) (hP : ∀ i, (P i).IsHomogeneous 1)
    {B C : ℝ} (hmass : ∀ i, realPolynomialMass (P i) ≤ B)
    (hC : 0 ≤ C) (hΛ : MonomialRowBound Λ h C) (j : J) :
    |contractedRow Λ (∏ i, P i) j| ≤ C * B ^ h := by
  have hp : (∏ i, P i).IsHomogeneous h := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ P (fun _ => 1) (fun i _ => hP i)
  exact (contractedRow_le_mass Λ hp hΛ j).trans
    (mul_le_mul_of_nonneg_left (realPolynomialMass_fin_prod_le P hmass) hC)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

noncomputable def coefficientFunctional {σ J R : Type*} [Fintype J] [CommRing R]
    (frequency : (σ →₀ ℕ) → J → R) : VectorPolynomial σ R (J → R) →ₗ[R] R :=
  (Finsupp.lsum R (fun d => ∑ j, frequency d j • LinearMap.proj j)).comp coefficients.toLinearMap

theorem coefficientFunctional_monomial {σ J R : Type*} [Fintype J] [CommRing R]
    (frequency : (σ →₀ ℕ) → J → R) (d : σ →₀ ℕ) (w : J → R) :
    coefficientFunctional frequency (monomial d w) = ∑ j, frequency d j * w j := by
  simp only [coefficientFunctional, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coefficients_monomial, Finsupp.lsum_single, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

theorem coefficientFunctional_unit {σ J R : Type*} [Fintype J] [CommRing R]
    (frequency : (σ →₀ ℕ) → J → R) (d : σ →₀ ℕ) (j : J) :
    coefficientFunctional frequency (MvPolynomial.monomial d 1 ⊗ₜ[R] Pi.single j 1) = frequency d j := by
  change coefficientFunctional frequency (monomial d (Pi.single j 1)) = _
  rw [coefficientFunctional_monomial]
  simp [Pi.single_apply]

theorem coefficientFunctional_rowBound {σ J : Type*} [Fintype J]
    (frequency : (σ →₀ ℕ) → J → ℝ) {h : ℕ} {C : ℝ}
    (hfrequency : ∀ d, d.degree = h → ∀ j, |frequency d j| ≤ C) :
    MonomialRowBound (coefficientFunctional frequency) h C := by
  intro d hd j
  rw [coefficientFunctional_unit]
  exact hfrequency d hd j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def coefficientArrayFunctional {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) : CoefficientArray (K := K) U →ₗ[ℝ] ℝ where
  toFun x := ∑ s, ∑ a, (frequency s.1 s.2.val a : ℝ) * (x s).val a
  map_add' x y := by
    simp only [Pi.add_apply, Submodule.coe_add, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_left_comm]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped TensorProduct Classical

theorem integer_coefficient_le_mass {σ : Type*} (P : MvPolynomial σ ℤ) (d : σ →₀ ℕ) :
    |((P.coeff d : ℤ) : ℝ)| ≤ realPolynomialMass (map (Int.castRingHom ℝ) P) := by
  simpa only [coeff_map, Int.coe_castRingHom] using
    realPolynomialMass_coeff_le (map (Int.castRingHom ℝ) P) d

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialKernelValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def integerRowPolynomial {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) : MvPolynomial I ℝ :=
  coordinate (integerRowLinear a).toAddMonoidHom p

theorem integerRowPolynomial_coeff {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) (α : I →₀ ℕ) :
    (integerRowPolynomial a p).coeff α = ∑ j, (a j : ℝ) * coefficients p α j := by
  simp only [integerRowPolynomial, coeff_coordinate, LinearMap.toAddMonoidHom_coe,
    integerRowLinear_apply]

theorem integerRowPolynomial_eval {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) (w : I → ℝ) :
    MvPolynomial.eval w (integerRowPolynomial a p) = ∑ j, (a j : ℝ) * eval w p j := by
  have he : eval₂ w p = eval w p := by
    simpa using (eval₂_algebraMap (S := ℝ) w p)
  rw [integerRowPolynomial, ← coordinate_eval₂, he, integerRowLinear_apply]

theorem integerRowPolynomial_homogeneous {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) {h : ℕ} (hp : Homogeneous h p) :
    (integerRowPolynomial a p).IsHomogeneous h := by
  intro α hα
  by_contra hn
  have hd : α.degree ≠ h := by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hn
  apply hα
  simp only [integerRowPolynomial_coeff, hp α hd, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultilinearBoxInverse
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem multilinear_box_biased_slice {I : Type*} [Fintype I] [DecidableEq I] {h : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin h => I → ℝ) ℝ)
    (N s : I → ℕ) (hN : ∀ k, 0 < N k) (b : Fin h → I → ℝ)
    (j : Fin h → I) {ζ : ℝ}
    (hbias : ζ ≤ ‖𝔼 x : Fin h → ∀ k, Fin (N k),
      character ((F (stridedMatrixPoint b s x) : ℝ) : CircleFourier.Circle)‖) :
    ∃ c : Fin h → I → ℝ, ζ ≤ ‖𝔼 x : ∀ i, Fin (N (j i)),
      character ((F (fun i => c i + ((s (j i) : ℝ) * ((x i).val : ℝ)) •
        Pi.single (j i) (1 : ℝ)) : ℝ) : CircleFourier.Circle)‖ := by
  let : ∀ k, Nonempty (Fin (N k)) := fun k => ⟨⟨0, hN k⟩⟩
  obtain ⟨y, hy⟩ := exists_biased_matrix_coordinate_slice (H := Fin h) (I := I)
    (fun k => Fin (N k)) j
    (fun x : Fin h → ∀ k, Fin (N k) =>
      character ((F (stridedMatrixPoint b s x) : ℝ) : CircleFourier.Circle))
    (δ := ζ) hbias
  refine ⟨stridedMatrixSliceBase b s y j, ?_⟩
  have he : (𝔼 x : ∀ i, Fin (N (j i)),
      character ((F (stridedMatrixPoint b s (fun i => Function.update (y i) (j i) (x i))) : ℝ) :
        CircleFourier.Circle)) =
      𝔼 x : ∀ i, Fin (N (j i)),
        character ((F (fun i => stridedMatrixSliceBase b s y j i +
          ((s (j i) : ℝ) * ((x i).val : ℝ)) • Pi.single (j i) (1 : ℝ)) : ℝ) :
            CircleFourier.Circle) := by
    apply Finset.expect_congr rfl
    intro x _
    exact congrArg (fun v : Fin h → I → ℝ => character ((F v : ℝ) : CircleFourier.Circle))
      (stridedMatrixPoint_update b s y j x)
  exact hy.trans_eq (congrArg norm he)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDifferenceSubstitution
namespace OAI

section

namespace Erdos3

theorem additiveBoxDifference_map {X Y Z R : Type*} [AddGroup R] (n : ℕ) :
    ∀ (f : Fin n → X → Y) (F : (Fin n → Y) → Z → R)
      (u v : Fin n → X) (z : Z),
      additiveBoxDifference n (fun x t => F (fun i => f i (x i)) t) u v z =
        additiveBoxDifference n F (fun i => f i (u i)) (fun i => f i (v i)) z := by
  induction n with
  | zero =>
    intro f F u v z
    simp only [additiveBoxDifference]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro f F u v z
    have hcons (a : X) (x : Fin n → X) :
        (fun i => f i ((Fin.cons a x : Fin (n + 1) → X) i)) =
          (Fin.cons (f 0 a) (fun i : Fin n => f i.succ (x i)) : Fin (n + 1) → Y) := by
      funext i
      cases i using Fin.cases <;> rfl
    simp only [additiveBoxDifference]
    simp_rw [hcons]
    exact ih (fun i => f i.succ)
      (fun y t => F (Fin.cons (f 0 (u 0)) y) t - F (Fin.cons (f 0 (v 0)) y) t)
      (Fin.tail u) (Fin.tail v) z

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffineShiftPolynomial
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem affineShiftPullback_degree {I : Type*} {n d : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ d) :
    (affineShiftPullback base direction P).totalDegree ≤ d := by
  simpa only [affineShiftPullback, aeval_eq_eval₂Hom, algebraMap_eq, Nat.mul_one] using polynomial_substitution_totalDegree_le P
    (affineShiftCoordinate base direction) (affineShiftCoordinate_degree base direction) hP

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PairedDiagonalApproximation
namespace OAI

section

namespace Erdos3

noncomputable def rowDirectionLinear {K I : Type*} (a : K → ℝ) :
    (I → ℝ) →ₗ[ℝ] ((K × I) → ℝ) :=
  LinearMap.pi (fun z => a z.1 • LinearMap.proj z.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped ContDiff

noncomputable def normalizedIntegerInterpolation (K c δ u : ℝ) : ℝ :=
  K * smoothProbabilityProfile ((u - c) / δ) / shiftedSmoothSampleSum (c * K) (δ * K)

end Erdos3

end

section

namespace Erdos3

noncomputable def constantIntegerInterpolation (K δ : ℝ) : ℝ → ℝ :=
  if 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K then normalizedIntegerInterpolation K 0 δ
  else integerMassTent K 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialRationalApproximationMono
namespace OAI

section

namespace Erdos3

def PolynomialRationalApproximation {I : Type*} (T : I → ℝ) (R : ℝ)
    (P : MvPolynomial I ℝ) : Prop :=
  ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ R ∧ ∃ Q : MvPolynomial I ℤ,
    ∀ α, |P.coeff α - ((Q.coeff α : ℤ) : ℝ) / D| ≤ R / monomialScale T α

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearQuotientCoverAverage
namespace OAI

section

namespace Erdos3

open MeasureTheory CircleFourier
open scoped Classical

theorem character_half : character ((1 / 2 : ℝ) : CircleFourier.Circle) = -1 := by
  have h := fourier_add_half_inv_index (T := (1 : ℝ)) (n := 1)
    (by norm_num) (by norm_num) (0 : CircleFourier.Circle)
  simpa [fourier_apply, character] using h

theorem quotientLinearCharacter_integral {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Γ : AddSubgroup E) [MeasurableSpace (E ⧸ Γ)] [MeasurableAdd₂ (E ⧸ Γ)]
    (L : E →ₗ[ℝ] ℝ) (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n)
    (μ : Measure (E ⧸ Γ)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    (∫ x, quotientLinearCharacter Γ L hint x ∂μ) = if L = 0 then 1 else 0 := by
  classical
  by_cases hL : L = 0
  · subst L
    simp only [quotientLinearCharacter_zero, ite_true, integral_const, probReal_univ, one_smul]
  · rw [if_neg hL]
    have hx : ∃ x, L x ≠ 0 := by
      by_contra hn
      apply hL
      push Not at hn
      ext x
      exact hn x
    obtain ⟨x, hx⟩ := hx
    let v := ((1 / 2) / L x) • x
    have hv : L v = 1 / 2 := by
      change L (((1 / 2) / L x) • x) = _
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
    apply integral_eq_zero_of_add_left_eq_neg (g := QuotientAddGroup.mk' Γ v)
    intro y
    rw [quotientLinearCharacter_add, quotientLinearCharacter_mk, hv, character_half, neg_one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DehomogenizedExponent
namespace OAI

section

namespace Erdos3

theorem some_degree_le {K : Type*} [Fintype K] (d : Option K →₀ ℕ) :
    d.some.degree ≤ d.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_option]
  simp only [Finsupp.some_apply]
  omega

theorem dehomogenize_monomial {K R : Type*} [CommRing R]
    (d : Option K →₀ ℕ) (c : R) :
    MvPolynomial.aeval dehomogenizingSubstitution (MvPolynomial.monomial d c) =
      MvPolynomial.monomial d.some c := by
  rw [MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_option_index d _ (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _)]
  simp only [dehomogenizingSubstitution, one_pow, one_mul, MvPolynomial.algebraMap_eq]
  exact MvPolynomial.monomial_eq.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem rowPolynomial_homogeneous {σ R : Type*} [Fintype σ] [CommRing R] (a : σ → R) :
    (rowPolynomial a).IsHomogeneous 1 :=
  IsHomogeneous.sum Finset.univ _ 1 (fun i _ => isHomogeneous_C_mul_X (a i) i)

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

theorem affineLiftFrequency_bound {K J : Type*} [Fintype K]
    (frequency : (K →₀ ℕ) → J → ℤ) {h : ℕ} {C : ℝ}
    (hbound : ∀ d, d.degree ≤ h → ∀ j, |(frequency d j : ℝ)| ≤ C) :
    ∀ d, d.degree = h → ∀ j, |((affineLiftFrequency frequency d j : ℤ) : ℝ)| ≤ C := by
  intro d hd j
  exact hbound d.some ((some_degree_le d).trans hd.le) j

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RowPolynomialCombination
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem rowPolynomial_map {K R S : Type*} [Fintype K] [CommRing R] [CommRing S]
    (f : R →+* S) (a : K → R) :
    map f (rowPolynomial a) = rowPolynomial (fun k => f (a k)) := by
  simp only [rowPolynomial, map_sum, map_mul, map_C, map_X]

theorem rowPolynomial_diagonal {K H R : Type*} [Fintype K] [Fintype H] [CommRing R]
    (a : H → K → R) (x : H → R) (w : R) :
    rowPolynomial (fun k => ∑ i, a i k * (x i * w)) =
      C w * ∑ i, x i • rowPolynomial (a i) := by
  simp only [rowPolynomial, map_sum, map_mul, smul_eq_C_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BooleanJetMatrixFactor
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

def boundedSiteMatrix {K S : Type*} (h : ℕ) (site : S → K → ℤ) :
    Matrix S (BoundedCoefficientExponent K h) ℤ :=
  fun s d => d.val.prod (fun k n => site s k ^ n)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem coefficientArrayFunctional_integral {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    ∃ n : ℤ, coefficientArrayFunctional U frequency x = n := by
  change ∀ s a, ∃ n : ℤ, (x s).val a = n at hx
  choose z hz using hx
  refine ⟨∑ s : CoefficientSlot K m, ∑ a, frequency s.1 s.2.val a * z s a, ?_⟩
  change (∑ s : CoefficientSlot K m, ∑ a, (frequency s.1 s.2.val a : ℝ) * (x s).val a) = _
  simp only [hz, Int.cast_sum, Int.cast_mul]

noncomputable def coefficientTorusCharacter {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    CoefficientTorus (K := K) U → ℂ :=
  quotientLinearCharacter (coefficientIntegerLattice U) (coefficientArrayFunctional U frequency)
    (coefficientArrayFunctional_integral U frequency)

theorem coefficientTorusCharacter_mk {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (x : CoefficientArray (K := K) U) :
    coefficientTorusCharacter U frequency (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) =
      CircleFourier.character (coefficientArrayFunctional U frequency x : CircleFourier.Circle) := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

def zeroCoefficientExponent (K : Type*) (h : ℕ) : BoundedCoefficientExponent K h :=
  ⟨0, by simp⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.SiteFourierHaarMean
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

noncomputable def coefficientTorusFourierSum {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (x : CoefficientTorus (K := K) U) : ℂ := ∑ a, c a * coefficientTorusCharacter U (frequency a) x

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ExponentialBohrVolume
namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators

variable {N : ℕ} [NeZero N]

@[simp] lemma character_neg_index (r x : ZMod N) :
    character (-r) x = (starRingEnd ℂ) (character r x) := by
  rw [character_comm, AddChar.map_neg_eq_conj, character_comm]

@[simp]
lemma norm_one_sub_character_neg_index (r x : ZMod N) :
    ‖1 - character (-r) x‖ = ‖1 - character r x‖ := by
  rw [character_neg_index]
  simpa using (RCLike.norm_conj (1 - character r x))

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr

lemma character_eq_one_mul {N : ℕ} [NeZero N] (r x : ZMod N) :
    character r x = character 1 (r * x) := by
  change (↑(AddChar.zmod N r x) : ℂ) = ↑(AddChar.zmod N 1 (r * x))
  simp [AddChar.zmod]

lemma norm_one_sub_character_intCast {N : ℕ} [NeZero N] (t : ℤ) :
    ‖1 - character 1 (t : ZMod N)‖ ≤ 8 * |(t : ℝ)| / N := by
  change ‖1 - (↑(AddChar.zmod N 1 (t : ZMod N)) : ℂ)‖ ≤ _
  rw [show (1 : ZMod N) = ((1 : ℤ) : ZMod N) by simp]
  rw [AddChar.zmod_intCast, Circle.coe_exp, norm_sub_rev]
  simp only [Int.cast_one, one_mul]
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hnorm : ‖Complex.exp ((2 * Real.pi * ((t : ℝ) / N) : ℝ) *
      Complex.I) - 1‖ ≤ |2 * Real.pi * ((t : ℝ) / N)| := by
    simpa only [mul_comm, Real.norm_eq_abs]
      using (Real.norm_exp_I_mul_ofReal_sub_one_le
        (x := 2 * Real.pi * ((t : ℝ) / N)))
  refine hnorm.trans ?_
  rw [← mul_div_assoc, abs_div, abs_mul, abs_mul, abs_of_pos hN,
    abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  gcongr
  linarith [Real.pi_le_four]

lemma norm_one_sub_character_le_of_mul_eq_intCast {N : ℕ} [NeZero N]
    (r x : ZMod N) (t : ℤ) (h : r * x = (t : ZMod N)) :
    ‖1 - character r x‖ ≤ 8 * |(t : ℝ)| / N := by
  rw [character_eq_one_mul, h]
  exact norm_one_sub_character_intCast t

end Erdos3.CyclicBohr

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuarticBohrProgression
namespace OAI

section

open scoped BigOperators Matrix Pointwise

namespace Erdos3.BohrProgression

open Erdos3.BohrLattice.BoxCertificate
open Erdos3.BohrLattice.MinkowskiSecondBox

noncomputable section

lemma intCastVec_bohrLatticePoint {N : ℕ} (Gamma : Finset (ZMod N))
    (z : Fin (Gamma.card + 1) → ℤ) :
    intCastVec (bohrLatticePoint Gamma z) =
      Matrix.mulVec (bohrLatticeMatrix Gamma) (intCastVec z) := by
  funext i
  simp [bohrLatticePoint, bohrLatticeMatrix, Matrix.mulVec, dotProduct,
    intCastVec]

end

end Erdos3.BohrProgression

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

noncomputable def tailAxisInterpolation {V : Type*} (T : V → ℝ) (K L s : ℕ) (ε : ℝ)
    (e : V →₀ ℕ) : ℝ → ℝ :=
  if L^(s+1) < K then normalizedIntegerInterpolation K 0 (ε / monomialScale T e)
  else integerMassTent K 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalIntegerInterpolation
namespace OAI

section

namespace Erdos3

noncomputable def principalIntegerInterpolation (K T γ x : ℝ) : ℝ :=
  T * normalizedIntegerInterpolation (K / T) (3 * γ / 2) (γ / 2) (T*x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalAxisInterpolation
namespace OAI

section

namespace Erdos3

noncomputable def principalAxisInterpolation (h K L : ℕ) (γ : ℝ) : ℝ → ℝ :=
  if L^h < K then principalIntegerInterpolation K ((L : ℝ)^h) γ
  else integerMassTent K (inactivePrincipalCoefficient K (inactiveDenominator γ))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialInterpolation
namespace OAI

section

namespace Erdos3

variable {J V : Type*} [Fintype J]

noncomputable def integerPolynomialInterpolation (P : Finset J) (j₀ : J) (h K L s : ℕ)
    (T : V → ℝ) (e : J → V →₀ ℕ) (ρ γ ε : ℝ) (j : J) : ℝ → ℝ := by
  classical
  exact if j = j₀ then constantIntegerInterpolation K ρ
    else if j ∈ P then principalAxisInterpolation h K L γ
    else tailAxisInterpolation T K L s ε (e j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedLayerIntegerInterpolation (j : Fin m) (i : Fin (n j))
    (d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ → ℝ :=
  integerPolynomialInterpolation (layerIntegerPrincipalSlots (G := G) B j i) (constantCoefficientSlot _ _)
    (j.val+1) (basisAxisScale (b j) i) S.value (layerTailDegree m) (layerSamplerBox B U b S) Subtype.val
    (R j / 4) (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))) d

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowEvaluation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

theorem emptyCoefficientExponent_eq (h : ℕ) (d : BoundedCoefficientExponent Empty h) :
    d = zeroCoefficientExponent Empty h := by
  apply Subtype.ext
  ext i
  exact isEmptyElim i

noncomputable def constantCoefficientArray {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) : CoefficientArray (K := Empty) U →ₗ[ℝ] CoefficientArray (K := K) U where
  toFun x s := if s.2.val = 0 then x ⟨s.1, zeroCoefficientExponent Empty (s.1.val + 1)⟩ else 0
  map_add' x y := by
    funext s
    by_cases hs : s.2.val = 0 <;> simp [hs]
  map_smul' c x := by
    funext s
    by_cases hs : s.2.val = 0 <;> simp [hs]

theorem constantCoefficientArray_preserves_lattice {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientArray (K := Empty) U)
    (hx : x ∈ coefficientIntegerLattice U) :
    constantCoefficientArray (K := K) U x ∈ coefficientIntegerLattice U := by
  intro s a
  by_cases hs : s.2.val = 0
  · simpa only [constantCoefficientArray, LinearMap.coe_mk, AddHom.coe_mk, if_pos hs] using
      hx ⟨s.1, zeroCoefficientExponent Empty (s.1.val + 1)⟩ a
  · exact ⟨0, by simp [constantCoefficientArray, hs]⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def coefficientEvaluationArray {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) :
    CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := Empty) U where
  toFun x s := ∑ d : BoundedCoefficientExponent K (s.1.val + 1),
    (boundedSiteMatrix (s.1.val + 1) (fun _ : Unit => t) () d : ℝ) • x ⟨s.1, d⟩
  map_add' x y := by
    funext s
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext s
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro d _
    rw [mul_comm]

theorem coefficientEvaluationArray_preserves_lattice {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientEvaluationArray U t x ∈ coefficientIntegerLattice U := by
  choose z hz using hx
  intro s a
  refine ⟨∑ d : BoundedCoefficientExponent K (s.1.val + 1),
    boundedSiteMatrix (s.1.val + 1) (fun _ : Unit => t) () d * z ⟨s.1, d⟩ a, ?_⟩
  change ((∑ d : BoundedCoefficientExponent K (s.1.val + 1),
    (boundedSiteMatrix (s.1.val + 1) (fun _ : Unit => t) () d : ℝ) •
      (x ⟨s.1, d⟩ : U s.1)) : U s.1).val a = _
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, hz, Int.cast_sum, Int.cast_mul]

theorem coefficientEvaluationArray_constant {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientArray (K := Empty) U) :
    coefficientEvaluationArray U t (constantCoefficientArray U x) = x := by
  funext s
  rcases s with ⟨j, d⟩
  have hd := emptyCoefficientExponent_eq (j.val + 1) d
  subst d
  change (∑ d : BoundedCoefficientExponent K (j.val + 1),
    (boundedSiteMatrix (j.val + 1) (fun _ : Unit => t) () d : ℝ) •
      (if d.val = 0 then x ⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩ else 0)) =
    x ⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩
  rw [Finset.sum_eq_single (zeroCoefficientExponent K (j.val + 1))]
  · simp only [zeroCoefficientExponent, boundedSiteMatrix, Finsupp.prod_zero_index,
      Int.cast_one, ite_true, one_smul]
  · intro d _ hd
    have hd0 : d.val ≠ 0 := fun he => hd (Subtype.ext he)
    simp [hd0]
  · simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def coefficientLayerInsertion {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m) :
    (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ] CoefficientArray (K := K) U where
  toFun v s := (LinearMap.single ℝ (fun k : Fin m => BoundedCoefficientExponent K (k.val + 1) → U k) j v) s.1 s.2
  map_add' v w := by
    funext s
    simp only [map_add, Pi.add_apply]
  map_smul' c v := by
    funext s
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply]

theorem coefficientLayerInsertion_same {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j)
    (d : BoundedCoefficientExponent K (j.val + 1)) :
    coefficientLayerInsertion U j v ⟨j, d⟩ = v d := by
  simp [coefficientLayerInsertion]

theorem coefficientLayerInsertion_ne {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j k : Fin m) (h : k ≠ j)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j)
    (d : BoundedCoefficientExponent K (k.val + 1)) :
    coefficientLayerInsertion U j v ⟨k, d⟩ = 0 := by
  simp [coefficientLayerInsertion, h]

theorem coefficientArrayFunctional_layerInsertion {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) (j : Fin m)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j) :
    coefficientArrayFunctional U frequency (coefficientLayerInsertion U j v) =
      subspaceArrayFunctional (U j) (fun d a => (frequency j d.val a : ℝ)) v := by
  change (∑ s : CoefficientSlot K m, ∑ a, (frequency s.1 s.2.val a : ℝ) *
    (coefficientLayerInsertion U j v s).val a) = _
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · simp only [coefficientLayerInsertion_same]
    rfl
  · intro k _ hkj
    simp only [coefficientLayerInsertion_ne U j k hkj, ZeroMemClass.coe_zero,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · simp

theorem coefficientEvaluationArray_layerInsertion {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) (j : Fin m)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j) :
    coefficientEvaluationArray U t (coefficientLayerInsertion U j v) =
      coefficientLayerInsertion (K := Empty) U j
        (fun _ => ∑ d, (boundedSiteMatrix (j.val + 1) (fun _ : Unit => t) () d : ℝ) • v d) := by
  funext s
  rcases s with ⟨k, d⟩
  by_cases hk : k = j
  · subst k
    simp only [coefficientEvaluationArray, LinearMap.coe_mk, AddHom.coe_mk,
      coefficientLayerInsertion_same]
  · simp only [coefficientEvaluationArray, LinearMap.coe_mk, AddHom.coe_mk,
      coefficientLayerInsertion_ne U j k hk, smul_zero, Finset.sum_const_zero]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmptyLayerDetectionGeometry
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

noncomputable def mixedDensityCovolumeRatio : ℝ :=
  ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) /
    ∏ i, (basisAxisScale b i : ℝ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoefficientEvaluationTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def constantCoefficientTorusMap {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    CoefficientTorus (K := Empty) U →+ CoefficientTorus (K := K) U :=
  QuotientAddGroup.map (coefficientIntegerLattice U) (coefficientIntegerLattice U)
    (constantCoefficientArray U).toAddMonoidHom
    (constantCoefficientArray_preserves_lattice U)

noncomputable def coefficientEvaluationTorus {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) :
    CoefficientTorus (K := K) U →+ CoefficientTorus (K := Empty) U :=
  QuotientAddGroup.map (coefficientIntegerLattice U) (coefficientIntegerLattice U)
    (coefficientEvaluationArray U t).toAddMonoidHom
    (coefficientEvaluationArray_preserves_lattice U t)

theorem constantCoefficientTorusMap_mk {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientArray (K := Empty) U) :
    constantCoefficientTorusMap (K := K) U (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) (constantCoefficientArray U x) := rfl

theorem coefficientEvaluationTorus_mk {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) (x : CoefficientArray (K := K) U) :
    coefficientEvaluationTorus U t (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) (coefficientEvaluationArray U t x) := rfl

theorem constantCoefficientTorusMap_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    Continuous (constantCoefficientTorusMap (K := K) U) := by
  apply (QuotientAddGroup.isQuotientMap_mk (coefficientIntegerLattice U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (constantCoefficientArray U).continuous_of_finiteDimensional

theorem coefficientEvaluationTorus_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) :
    Continuous (coefficientEvaluationTorus U t) := by
  apply (QuotientAddGroup.isQuotientMap_mk (coefficientIntegerLattice U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (coefficientEvaluationArray U t).continuous_of_finiteDimensional

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OneSiteCoefficientFactorization
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def coefficientResidualArray {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) :
    CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U :=
  LinearMap.id - (constantCoefficientArray U).comp (coefficientEvaluationArray U t)

theorem coefficientResidualArray_preserves_lattice {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientResidualArray U t x ∈ coefficientIntegerLattice U :=
  (coefficientIntegerLattice U).sub_mem hx (constantCoefficientArray_preserves_lattice U _
    (coefficientEvaluationArray_preserves_lattice U t x hx))

theorem coefficientResidualArray_evaluation {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientArray (K := K) U) :
    coefficientEvaluationArray U t (coefficientResidualArray U t x) = 0 := by
  simp only [coefficientResidualArray, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.comp_apply, map_sub, coefficientEvaluationArray_constant, sub_self]

theorem coefficientResidualArray_factor_iff {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (L : CoefficientArray (K := K) U →ₗ[ℝ] ℝ) :
    L.comp (coefficientResidualArray U t) = 0 ↔
      ∃ M : CoefficientArray (K := Empty) U →ₗ[ℝ] ℝ, L = M.comp (coefficientEvaluationArray U t) := by
  constructor
  · intro h
    refine ⟨L.comp (constantCoefficientArray U), ?_⟩
    apply LinearMap.ext
    intro x
    have hx := DFunLike.congr_fun h x
    simpa only [LinearMap.comp_apply, coefficientResidualArray, LinearMap.sub_apply,
      LinearMap.id_apply, map_sub, LinearMap.zero_apply, sub_eq_zero] using hx
  · rintro ⟨M, rfl⟩
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, coefficientResidualArray_evaluation, map_zero,
      LinearMap.zero_apply]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxObservedMean
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem integerPhysicalSite_cast_apply {K I : Type*} [Fintype K]
    (root : K → ℤ) (z : Option K × I → ℤ) (i : I) :
    (integerPhysicalSite root z i : ℝ) = physicalAffineSite root z i := by
  have h := physicalAffineSite_baseArrayJoin_apply root
    (fun k => z (some k.1,k.2)) (fun i => z (none,i)) i
  rw [baseArrayJoin_eta] at h
  simpa only [integerPhysicalSite, Int.cast_add, Int.cast_sum, Int.cast_mul] using h.symm

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuantitativeNoninjectivity
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

theorem jointIntegerPhysicalSite_cast {K I : Type*} [Fintype K]
    (root : K → ℤ) (z : (I → ℤ) × (Option K × I → ℤ)) :
    (fun i => (jointIntegerPhysicalSite root z i : ℝ)) =
      (fun i => (z.1 i : ℝ)) + physicalAffineSite root z.2 := by
  funext i
  simp only [jointIntegerPhysicalSite, Pi.add_apply, Int.cast_add,
    integerPhysicalSite_cast_apply]

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

theorem integerSiteValue_affine_physical {I K : Type*} [Fintype K] {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) (base : I → ℤ)
    (z : Option K × I → ℤ) (s : Finset (Fin q)) :
    (fun i => (base i : ℝ)) + integerSiteValue (affineSite root difference s)
        (fun k i => (z (k, i) : ℝ)) =
      fun i => (physicalCubeVertexValue (physicalCubeRootDifferences root (Matrix.of difference) base z) s i : ℝ) := by
  rw [physicalCubeVertexValue_rootDifferences]
  change (fun i => (base i : ℝ)) + physicalAffineSite (integerAffineCube root (Matrix.of difference) s) z = _
  exact (jointIntegerPhysicalSite_cast (integerAffineCube root (Matrix.of difference) s) (base, z)).symm

end Erdos3.BooleanCubeKernel

end

end OAI
end


