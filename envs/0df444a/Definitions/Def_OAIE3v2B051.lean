-- Prove2me | Definitions.Def_OAIE3v2B051
-- name    : OAIE3v2B051
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:13:56.756699+00:00
-- url     : https://prove2.me/theorems/980cafdc-7944-4a90-b862-41b2602ba0e8
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 52 of 311
-- statement:
--   Definitions bundle 52 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B004`, `OAIE3v2B005`, `OAIE3v2B006`, `OAIE3v2B007`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B013`, `OAIE3v2B015`, `OAIE3v2B016`, `OAIE3v2B017`, `OAIE3v2B018`, `OAIE3v2B019`, `OAIE3v2B020` of this split.
--
--   Modules: `Dynamics/CompatibleReducedFastReset.lean`, `Dynamics/FastRemovalBudget.lean`, `Dynamics/InitialRemovalBudget.lean`, `Dynamics/PointwiseSymbolBudget.lean`, `Estimates/CocycleHorizontalNormalization.lean`, `Estimates/DerivativeIndexBounds.lean`, `Estimates/EuclideanGraphResidual.lean`, `Estimates/LowerTriangularMinor.lean`, `Estimates/OriginalMixedRootEquivalence.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/SplitGroupRelative.lean`, `Estimates/WeightedOverlapCorrelation.lean`, `Geometry/BoxDetectionExponents.lean`, `Geometry/CoordinateMinorCovolume.lean`, `Geometry/SupportedQuotientSection.lean`, `Lattices/EuclideanDerivativeLattice.lean`, `Lattices/LatticeSheetHaar.lean`, `Lattices/ScaledLatticeCovolume.lean`, `Linear/AugmentedMatrixSection.lean`, `Linear/BasisGradedCoordinateBasis.lean`, `Linear/CommonKernelRangeEquiv.lean`, `Linear/ImageDefiningMatrix.lean`, `Linear/QuotientProjectionCoordinates.lean`, `Linear/SortedBasisTriangular.lean`, `Nilpotent/BCHSubmoduleRemainder.lean`, `Polynomial/MixedWeightedPolynomialRename.lean`, `Sampling/DerivativeGridPoints.lean`, `Sampling/GridNormalizationDenominator.lean`, `Sampling/RationalSpanGrid.lean`.
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
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B013
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B016
import Definitions.Def_OAIE3v2B017
import Definitions.Def_OAIE3v2B018
import Definitions.Def_OAIE3v2B019
import Definitions.Def_OAIE3v2B020

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

theorem grid_det_integer_multiple {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (l : ℕ)
    (hA : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l) :
    ∃ z : ℤ, (l : ℝ) ^ Fintype.card ι * A.det = (z : ℝ) := by
  choose z hz using hA
  let B : Matrix ι ι ℤ := fun i j => z j i
  have he : B.map (Int.castRingHom ℝ) = (l : ℝ) • A := by
    ext i j
    exact congrFun (hz j) i
  refine ⟨B.det, ?_⟩
  rw [← Matrix.det_smul, ← he]
  exact ((Int.castRingHom ℝ).map_det B).symm

theorem one_div_pow_le_abs_grid_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (l : ℕ) (hl : 0 < l)
    (hA : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l) (hne : A.det ≠ 0) :
    1 / (l : ℝ) ^ Fintype.card ι ≤ |A.det| := by
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  obtain ⟨z, hz⟩ := grid_det_integer_multiple A l hA
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, Int.cast_zero] at hz
    exact (mul_ne_zero (pow_ne_zero _ hlpos.ne') hne) hz
  have habs : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
  rw [← hz, abs_mul, abs_of_pos (pow_pos hlpos _)] at habs
  exact (div_le_iff₀ (pow_pos hlpos _)).mpr (by simpa only [mul_comm] using habs)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Pointwise

variable {σ : Type*}

theorem polynomialDegreeGap_directionalDerivative [Fintype σ] (h : σ → ℚ)
    {k d : ℕ} {p : MvPolynomial σ ℚ} (hp : p ∈ polynomialDegreeGap k d) :
    scalarDirectionalDerivative h p ∈ polynomialDegreeGap (k + 1) d := by
  rw [scalarDirectionalDerivative_apply]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (polynomialDegreeGap_pderiv hp i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DerivativeGridPoints
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {σ κ : Type*} [Fintype κ]

def derivativeGridPoints (T : σ → ℝ) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ) (l : ℕ) :
    Set ((σ → ℝ) × (κ → ℝ)) :=
  {v | ∃ h : σ → ℤ, ∃ r : κ → ℝ, r ∈ realDenominatorGrid l ∧
    v = derivativeGridPoint T scale Y M h r}

theorem derivativeGridPoint_mem (T : σ → ℝ) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ) (l : ℕ)
    (h : σ → ℤ) (r : κ → ℝ) (hr : r ∈ realDenominatorGrid l) :
    derivativeGridPoint T scale Y M h r ∈ derivativeGridPoints T scale Y M l :=
  ⟨h, r, hr, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EuclideanDerivativeLattice
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

theorem standardProductBasis_mem_iff (x : (σ → ℝ) × (κ → ℝ)) :
    x ∈ Submodule.span ℤ (Set.range (standardProductBasis (σ := σ) (κ := κ))) ↔
      x.1 ∈ realIntegerGrid ∧ x.2 ∈ realIntegerGrid := by
  rw [(standardProductBasis (σ := σ) (κ := κ)).mem_span_iff_repr_mem ℤ x]
  constructor
  · intro h
    have h₁ : ∀ i : σ, ∃ n : ℤ, (n : ℝ) = x.1 i := by
      intro i
      simpa [standardProductBasis] using h (Sum.inl i)
    have h₂ : ∀ i : κ, ∃ n : ℤ, (n : ℝ) = x.2 i := by
      intro i
      simpa [standardProductBasis] using h (Sum.inr i)
    choose a ha using h₁
    choose b hb using h₂
    exact ⟨⟨a, funext ha⟩, ⟨b, funext hb⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ i
    cases i with
    | inl i => exact ⟨a i, by simpa [standardProductBasis] using congrFun ha i⟩
    | inr i => exact ⟨b i, by simpa [standardProductBasis] using congrFun hb i⟩

variable (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

theorem derivativeLattice_mem_iff (v : (σ → ℝ) × (κ → ℝ)) :
    v ∈ derivativeLattice T hT scale hscale Y A l hl ↔
      ∃ h : σ → ℤ, ∃ z : κ → ℤ,
        v = derivativeLatticeEquiv T hT scale hscale Y A l hl
          (fun i => (h i : ℝ), fun j => (z j : ℝ)) := by
  change v ∈ Submodule.span ℤ (Set.range
    (standardProductBasis.map (derivativeLatticeEquiv T hT scale hscale Y A l hl))) ↔ _
  rw [← ZSpan.map]
  constructor
  · rintro ⟨x, hx, hxv⟩
    obtain ⟨⟨h, hh⟩, ⟨z, hz⟩⟩ := (standardProductBasis_mem_iff x).mp hx
    have he : x = ((fun i => (h i : ℝ)), (fun j => (z j : ℝ))) := Prod.ext hh.symm hz.symm
    exact ⟨h, z, hxv.symm.trans (congrArg (derivativeLatticeEquiv T hT scale hscale Y A l hl) he)⟩
  · rintro ⟨h, z, rfl⟩
    refine ⟨((fun i => (h i : ℝ)), (fun j => (z j : ℝ))), ?_, rfl⟩
    exact (standardProductBasis_mem_iff _).mpr ⟨⟨h, rfl⟩, ⟨z, rfl⟩⟩

theorem derivativeLattice_carrier [DecidableEq κ] :
    (derivativeLattice T hT scale hscale Y A l hl : Set ((σ → ℝ) × (κ → ℝ))) =
      derivativeGridPoints T scale Y (LinearMap.toMatrix' A.toLinearMap) l := by
  ext v
  change (v ∈ derivativeLattice T hT scale hscale Y A l hl) ↔ _
  rw [derivativeLattice_mem_iff]
  have hlr : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  constructor
  · rintro ⟨h, z, rfl⟩
    refine ⟨h, (fun j => (z j : ℝ) / l), ⟨z, ?_⟩, ?_⟩
    · funext j
      change (z j : ℝ) = (l : ℝ) * ((z j : ℝ) / l)
      field_simp
    · simp only [derivativeLatticeEquiv_apply, derivativeGridPoint, LinearMap.toMatrix'_mulVec,
        LinearEquiv.coe_coe]
  · rintro ⟨h, r, ⟨z, hz⟩, hv⟩
    have hdiv : (fun j => (z j : ℝ) / l) = r := by
      funext j
      have hj : (z j : ℝ) = (l : ℝ) * r j := congrFun hz j
      rw [hj]
      field_simp
    refine ⟨h, z, hv.trans ?_⟩
    simp only [derivativeLatticeEquiv_apply, derivativeGridPoint, LinearMap.toMatrix'_mulVec, hdiv,
      LinearEquiv.coe_coe]

end Erdos3

end

section

namespace Erdos3

open Module

variable {σ κ : Type*} [Fintype σ] [Fintype κ]
  (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

theorem productEuclideanEquiv_mem_derivativeLattice (v : (σ → ℝ) × (κ → ℝ)) :
    productEuclideanEquiv v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl ↔
      v ∈ derivativeLattice T hT scale hscale Y A l hl := by
  rw [euclideanDerivativeLattice_mem_iff, LinearEquiv.symm_apply_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDetectionExponents
namespace OAI

section

namespace Erdos3

theorem retained_exponential_weight (d : ℕ) {p r : ℝ} (hd : (d : ℝ) ≤ p) :
    let L := 2 * r + 2 * p + 6
    Real.exp (-L) ≤ Real.exp (-r) ^ 2 / (2 * Real.exp (p + 1) ^ 2) -
      (2 : ℝ) ^ d * Real.exp (-(L + p)) := by
  let L := 2 * r + 2 * p + 6
  have hloss : (2 : ℝ) ^ d * Real.exp (-(L + p)) ≤ Real.exp (-L) := by
    calc
      _ ≤ Real.exp p * Real.exp (-(L + p)) :=
        mul_le_mul_of_nonneg_right (two_pow_le_exp_of_le d hd) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he : Real.exp (-r) ^ 2 / (2 * Real.exp (p + 1) ^ 2) =
      Real.exp 4 / 2 * Real.exp (-L) := by
    calc
      _ = (Real.exp (-r) ^ 2 / Real.exp (p + 1) ^ 2) / 2 := by ring
      _ = Real.exp (2 * (-r) - 2 * (p + 1)) / 2 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub]
        norm_num
      _ = (Real.exp 4 * Real.exp (-L)) / 2 := by
        rw [← Real.exp_add]
        congr 2
        dsimp [L]
        ring
      _ = _ := by ring
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  change Real.exp (-L) ≤ _
  rw [he]
  nlinarith [Real.exp_pos (-L)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedOverlapCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem sum_overlaps {M : Type*} [AddCommMonoid M]
    (Q : Finset A) (F : A → A → M) :
    (∑ h ∈ cubeDifferenceSupport Q, ∑ x ∈ derivativeSupport Q h, F x (x + h)) =
      ∑ x ∈ Q, ∑ y ∈ Q, F x y := by
  calc
    _ = ∑ p ∈ (cubeDifferenceSupport Q ×ˢ Q).filter (fun p => p.2 + p.1 ∈ Q),
        F p.2 (p.2 + p.1) := by
      rw [Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro h _
      simp only [derivativeSupport, Finset.sum_filter]
    _ = ∑ p ∈ Q ×ˢ Q, F p.1 p.2 := by
      apply Finset.sum_bij (fun p _ => (p.2, p.2 + p.1))
      · intro p hp
        obtain ⟨hp, hsum⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).2, hsum⟩
      · intro p hp q hq he
        have hx := congrArg Prod.fst he
        have hh := congrArg Prod.snd he
        simp only at hx hh
        apply Prod.ext
        · apply add_left_cancel (a := p.2)
          exact hh.trans (congrArg (fun x => x + q.1) hx).symm
        · exact hx
      · intro p hp
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
        refine ⟨(p.2 - p.1, p.1), ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨?_, hx⟩, ?_⟩
          · exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
          · simpa only [add_sub_cancel] using hy
        · simp only [add_sub_cancel, Prod.eta]
      · intro p hp
        rfl
    _ = _ := Finset.sum_product Q Q (fun p => F p.1 p.2)

theorem sum_overlap_card (Q : Finset A) :
    (∑ h ∈ cubeDifferenceSupport Q, (derivativeSupport Q h).card) = Q.card ^ 2 := by
  simpa only [Finset.sum_const, smul_eq_mul, mul_one, pow_two] using
    sum_overlaps Q (fun _ _ => (1 : ℕ))

theorem sum_overlap_weights {Q : Finset A} (hQ : Q.Nonempty) :
    (∑ h ∈ cubeDifferenceSupport Q, ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) = 1 := by
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_overlap_card, Nat.cast_pow]
  exact div_self (pow_ne_zero _ (by exact_mod_cast hQ.card_pos.ne'))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem correlation_sq_mul_card (Q : Finset A) (f u : A → ℂ) :
    (Q.card : ℝ) ^ 2 * ‖finiteCorrelation Q f u‖ ^ 2 =
      ∑ h ∈ cubeDifferenceSupport Q, ((derivativeSupport Q h).card : ℝ) *
        (finiteCorrelation (derivativeSupport Q h)
          (multiplicativeDerivative f h) (multiplicativeDerivative u h)).re := by
  let g := fun x => f x * star (u x)
  have hp : (∑ h ∈ cubeDifferenceSupport Q, ∑ x ∈ derivativeSupport Q h, g x * star (g (x + h))) =
      (∑ x ∈ Q, g x) * star (∑ x ∈ Q, g x) := by
    rw [sum_overlaps Q (fun x y => g x * star (g y))]
    simp only [Finset.sum_mul, Finset.mul_sum, star_sum]
    rw [Finset.sum_comm]
  have hinner (h : A) : (∑ x ∈ derivativeSupport Q h, g x * star (g (x + h))) =
      ((derivativeSupport Q h).card : ℂ) * finiteCorrelation (derivativeSupport Q h)
        (multiplicativeDerivative f h) (multiplicativeDerivative u h) := by
    rw [finiteCorrelation, Finset.card_mul_expect]
    apply Finset.sum_congr rfl
    intro x _
    simp only [g, multiplicativeDerivative, star_mul, star_star]
    ring
  have hnorm : ‖∑ x ∈ Q, g x‖ ^ 2 = (Q.card : ℝ) ^ 2 * ‖finiteCorrelation Q f u‖ ^ 2 := by
    rw [← Finset.card_mul_expect Q g, norm_mul, Complex.norm_natCast, mul_pow]
    rfl
  have hreal := congrArg Complex.re hp
  simp_rw [hinner] at hreal
  rw [mul_star_re_eq_norm_sq, hnorm] at hreal
  simpa only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] using hreal.symm

theorem correlation_sq_eq_sum_overlap {Q : Finset A} (hQ : Q.Nonempty) (f u : A → ℂ) :
    ‖finiteCorrelation Q f u‖ ^ 2 =
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (finiteCorrelation (derivativeSupport Q h)
          (multiplicativeDerivative f h) (multiplicativeDerivative u h)).re := by
  have hcard : (Q.card : ℝ) ≠ 0 := by exact_mod_cast hQ.card_pos.ne'
  calc
    _ = ((Q.card : ℝ) ^ 2 * ‖finiteCorrelation Q f u‖ ^ 2) / (Q.card : ℝ) ^ 2 := by
      field_simp
    _ = _ := by
      rw [correlation_sq_mul_card, Finset.sum_div]
      simp only [div_mul_eq_mul_div]

theorem correlation_sq_le_sum_overlap_norm {Q : Finset A} (hQ : Q.Nonempty) (f u : A → ℂ) :
    ‖finiteCorrelation Q f u‖ ^ 2 ≤
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        ‖finiteCorrelation (derivativeSupport Q h)
          (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ := by
  rw [correlation_sq_eq_sum_overlap hQ]
  apply Finset.sum_le_sum
  intro h _
  exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by positivity)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem weight_small_overlaps {Q : Finset A} (hQ : Q.Nonempty) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ h ∈ (cubeDifferenceSupport Q).filter
      (fun h => ((derivativeSupport Q h).card : ℝ) ≤ δ * Q.card),
      ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) ≤
        δ * (cubeDifferenceSupport Q).card / Q.card := by
  classical
  have hq : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  let I := (cubeDifferenceSupport Q).filter
    (fun h => ((derivativeSupport Q h).card : ℝ) ≤ δ * Q.card)
  have hp (h : A) (hh : h ∈ I) :
      ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2 ≤ δ / Q.card := by
    have hsmall := (Finset.mem_filter.mp hh).2
    apply (div_le_div_iff₀ (sq_pos_of_pos hq) hq).mpr
    nlinarith
  calc
    _ ≤ ∑ _h ∈ I, δ / (Q.card : ℝ) := Finset.sum_le_sum hp
    _ = (I.card : ℝ) * (δ / Q.card) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((cubeDifferenceSupport Q).card : ℝ) * (δ / Q.card) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) (div_nonneg hδ hq.le)
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basisCoordinateProjection_eq_zero_iff (b : Basis ι K V) (S : Set ι) (x : V) :
    basisCoordinateProjection b S x = 0 ↔ x ∈ Submodule.span K (b '' Sᶜ) := by
  classical
  rw [basis_mem_span_image_iff]
  constructor
  · intro hx i hi
    have hiS : i ∈ S := by simpa only [Set.mem_compl_iff, not_not] using hi
    have h := congrArg (fun v => b.repr v i) hx
    simpa only [basisCoordinateProjection_repr, hiS, ↓reduceIte, map_zero, Finsupp.zero_apply] using h
  · intro hx
    apply b.repr.injective
    ext i
    simp only [basisCoordinateProjection_repr, map_zero, Finsupp.zero_apply]
    split_ifs with hi
    · exact hx i (by simpa only [Set.mem_compl_iff, not_not] using hi)
    · rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ImageDefiningMatrix
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem baseChange_matrix_apply [DecidableEq ι] [DecidableEq κ]
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (P : L →ₗ[ℚ] M) (x : ℝ ⊗[ℚ] L) :
    (fun i j => (LinearMap.toMatrix e f P i j : ℝ)) *ᵥ (e.baseChange ℝ).equivFun x =
      (f.baseChange ℝ).equivFun (P.baseChange ℝ x) := by
  have heq : (fun i j => (LinearMap.toMatrix e f P i j : ℝ)) =
      LinearMap.toMatrix (e.baseChange ℝ) (f.baseChange ℝ) (P.baseChange ℝ) := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, linearMap_baseChange_basis]
  rw [heq]
  simpa only [Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (e.baseChange ℝ) (f.baseChange ℝ) (P.baseChange ℝ) x

open NilpotentLieBCHGroup

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι κ δ : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def blockSpanningFamily (b : Basis ι K V) (c : ι → δ) (v : κ → V) : ι × κ → V :=
  fun z => basisCoordinateProjection b {i | c i = c z.1} (v z.2)

theorem blockSpanningFamily_repr [DecidableEq δ] (b : Basis ι K V) (c : ι → δ) (v : κ → V)
    (z : ι × κ) (i : ι) :
    b.repr (blockSpanningFamily b c v z) i = if c i = c z.1 then b.repr (v z.2) i else 0 := by
  exact basisCoordinateProjection_repr b {i | c i = c z.1} (v z.2) i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization
namespace OAI

section

namespace Erdos3

section Algebra

variable {R E H : Type*} [Field R] [AddCommGroup E] [Module R E]
  [AddCommGroup H] [Module R H]

theorem horizontal_remove_zero (P : E →ₗ[R] H) (a b : E ≃ₗ[R] E)
    (ha : ∀ x, P (a x) = P x) (hb : ∀ x, P (b x) = P x)
    (s r ya yb : E) (hya : P ya = P s) (hyb : P yb = P r) :
    P (a.symm (s - ya)) = 0 ∧ P (b r - yb) = 0 := by
  constructor
  · have he := ha (a.symm (s - ya))
    rw [LinearEquiv.apply_symm_apply] at he
    rw [← he, map_sub, hya, sub_self]
  · rw [map_sub, hb, hyb, sub_self]

theorem horizontal_derivative_of_zero_parts (U K : Submodule R H) (P : E →ₗ[R] H)
    (f : E →ₗ[R] E) (hf : P.comp f = P) (S : K →ₗ[R] E)
    (hS : P.comp S = K.subtype) (y s r : E) (k : K)
    (hsystem : y = s + f r + S k) (hs : P s = 0) (hr : P r = 0) (hk : k.val ∈ U) :
    P y = k.val ∧ P y ∈ U ⊓ K := by
  have he : P y = k.val := by
    rw [hsystem, map_add, map_add, hs,
      show P (f r) = P r from DFunLike.congr_fun hf r, hr,
      show P (S k) = k.val from DFunLike.congr_fun hS k, zero_add, zero_add]
  exact ⟨he, he.symm ▸ ⟨hk, k.property⟩⟩

end Algebra

end Erdos3

end

section

namespace Erdos3

variable {σ G E H R : Type*} [Group G] [Field R]
  [AddCommGroup E] [Module R E] [AddCommGroup H] [Module R H]

theorem cocycle_horizontal_normalization
    (ρ : G →* (E ≃ₗ[R] E)) (Y : G → σ → E)
    (hY : ∀ g h i, Y (g * h) i = Y g i + ρ g (Y h i))
    (P : E →ₗ[R] H) (hρ : ∀ g x, P (ρ g x) = P x)
    (U K : Submodule R H) (B a c : G) (S T : K →ₗ[R] E)
    (hST : S = (ρ B).toLinearMap.comp T)
    (hS : P.comp S = K.subtype) (hT : P.comp T = K.subtype)
    (small rational : σ → E) (k : σ → K)
    (hsystem : ∀ i, Y B i = small i + ρ B (rational i) + S (k i))
    (ha : ∀ i, P (Y a i) = P (small i)) (hc : ∀ i, P (Y c i) = P (rational i))
    (hk : ∀ i, (k i).val ∈ U) :
    let B' := a⁻¹ * B * c⁻¹
    let S' := (ρ a).symm.toLinearMap.comp S
    let T' := (ρ c).toLinearMap.comp T
    let small' := fun i => (ρ a).symm (small i - Y a i)
    let rational' := fun i => ρ c (rational i) - Y c i
    a * B' * c = B ∧ S' = (ρ B').toLinearMap.comp T' ∧
      P.comp S' = K.subtype ∧ P.comp T' = K.subtype ∧
      ∀ i, Y B' i = small' i + ρ B' (rational' i) + S' (k i) ∧
        P (small' i) = 0 ∧ P (rational' i) = 0 ∧ P (Y B' i) = (k i).val ∧
        P (Y B' i) ∈ U ⊓ K := by
  let B' := a⁻¹ * B * c⁻¹
  let S' := (ρ a).symm.toLinearMap.comp S
  let T' := (ρ c).toLinearMap.comp T
  let small' := fun i => (ρ a).symm (small i - Y a i)
  let rational' := fun i => ρ c (rational i) - Y c i
  have hprod : a * B' * c = B := by dsimp [B']; group
  have haction (x : E) : ρ B x = ρ a (ρ B' (ρ c x)) := by
    rw [← hprod]
    exact linear_action_triple ρ a B' c x
  have hfac : S' = (ρ B').toLinearMap.comp T' :=
    linear_lift_remove (ρ a) (ρ c) (ρ B) (ρ B') haction S T hST
  have hhor := horizontal_lift_remove P (ρ a) (ρ c) (hρ a) (hρ c) S T K.subtype hS hT
  refine ⟨hprod, hfac, hhor.1, hhor.2, fun i => ?_⟩
  have htriple := linear_cocycle_triple ρ (fun g => Y g i)
    (fun g h => hY g h i) a B' c
  rw [hprod] at htriple
  have hnew : Y B' i = small' i + ρ B' (rational' i) + S' (k i) :=
    linear_derivative_remove (ρ a) (ρ c) (ρ B) (ρ B') haction
      (Y B i) (Y a i) (Y B' i) (Y c i) (small i) (rational i) (S (k i)) htriple (hsystem i)
  have hzero := horizontal_remove_zero P (ρ a) (ρ c) (hρ a) (hρ c)
    (small i) (rational i) (Y a i) (Y c i) (ha i) (hc i)
  have hPB : P.comp (ρ B').toLinearMap = P := by
    ext x
    exact hρ B' x
  have hfinal := horizontal_derivative_of_zero_parts U K P (ρ B').toLinearMap hPB S'
    hhor.1 (Y B' i) (small' i) (rational' i) (k i) hnew hzero.1 hzero.2 (hk i)
  exact ⟨hnew, hzero.1, hzero.2, hfinal.1, hfinal.2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem toLin_baseChange_coordinates {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (T : Matrix ι κ ℚ) (y : ℝ ⊗[ℚ] M) :
    (e.baseChange ℝ).equivFun ((Matrix.toLin f e T).baseChange ℝ y) =
      (fun i j => (T i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun y := by
  classical
  simpa only [LinearMap.toMatrix_toLin] using
    (baseChange_matrix_apply f e (Matrix.toLin f e T) y).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AugmentedMatrixSection
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {ι κ μ R : Type*} [CommRing R]

theorem constraintProjectionInput_grid [Fintype ι] [Fintype μ]
    (l : ℕ) (y : μ → ℝ) (hy : y ∈ realDenominatorGrid l) :
    constraintProjectionInput (ι := ι) y ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hy
  refine ⟨Sum.elim (fun _ => (0 : ℤ)) z, ?_⟩
  funext i
  cases i with
  | inl i => simp [constraintProjectionInput]
  | inr i => exact congrFun hz i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonKernelRangeEquiv
namespace OAI

section

namespace Erdos3

variable {K A B C : Type*} [Field K] [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]

theorem commonKernelRangeEquiv_apply (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (h : LinearMap.ker f = LinearMap.ker g) (x : A) :
    (commonKernelRangeEquiv f g h ⟨f x, ⟨x, rfl⟩⟩ : C) = g x := by
  dsimp only [commonKernelRangeEquiv, LinearEquiv.trans_apply]
  rw [f.quotKerEquivRange_symm_apply_image x ⟨x, rfl⟩]
  rfl

theorem commonKernelSubmoduleEquiv_apply (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (U : Submodule K B) (V : Submodule K C)
    (h : LinearMap.ker f = LinearMap.ker g)
    (hf : LinearMap.range f = U) (hg : LinearMap.range g = V)
    (x : A) (hx : f x ∈ U) :
    (commonKernelSubmoduleEquiv f g U V h hf hg ⟨f x, hx⟩ : C) = g x :=
  commonKernelRangeEquiv_apply f g h x

theorem commonKernelSubmoduleEquiv_symm_apply (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (U : Submodule K B) (V : Submodule K C)
    (h : LinearMap.ker f = LinearMap.ker g)
    (hf : LinearMap.range f = U) (hg : LinearMap.range g = V)
    (x : A) (y : V) (hy : g x = y.val) :
    f x = ((commonKernelSubmoduleEquiv f g U V h hf hg).symm y : B) := by
  have hx : f x ∈ U := hf.le ⟨x, rfl⟩
  have he : commonKernelSubmoduleEquiv f g U V h hf hg ⟨f x, hx⟩ = y :=
    Subtype.ext ((commonKernelSubmoduleEquiv_apply f g U V h hf hg x hx).trans hy)
  have hi := congrArg (commonKernelSubmoduleEquiv f g U V h hf hg).symm he
  rw [LinearEquiv.symm_apply_apply] at hi
  exact congrArg Subtype.val hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitGroupRelative
namespace OAI

section

namespace Erdos3

variable {G H : Type*} [Group G] [Group H] (q : G →* H) (d : H →* G)

theorem splitRelativePart_same_projection {g h : G} (hproj : q g = q h) :
    splitRelativePart q d g * (splitRelativePart q d h)⁻¹ = g * h⁻¹ := by
  simp only [splitRelativePart, hproj]
  group

theorem splitRelativePart_pair_mem (hd : ∀ h, q (d h) = h) (U : Subgroup G)
    {g h : G} (hg : g ∈ U) (hh : h ∈ U) (hproj : q g = q h) :
    splitRelativePart q d g * (splitRelativePart q d h)⁻¹ ∈ U ⊓ q.ker := by
  constructor
  · rw [splitRelativePart_same_projection q d hproj]
    exact U.mul_mem hg (U.inv_mem hh)
  · change q (splitRelativePart q d g * (splitRelativePart q d h)⁻¹) = 1
    rw [map_mul, map_inv, splitRelativePart_projection q d hd,
      splitRelativePart_projection q d hd, inv_one, mul_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubmoduleRemainder
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rightBracketList_mem_submodule (K W : Submodule ℚ L)
    (hbracket : ∀ x ∈ W, ∀ y ∈ K, ⁅x, y⁆ ∈ W)
    (f : X → L) (hf : ∀ x, f x ∈ K) (xs : List X) (a : L) (ha : a ∈ W) :
    rightBracketList f xs a ∈ W := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    exact ih ⁅a, f x⁆ (hbracket a ha (f x) (hf x))

theorem dynkinWord_mem_submodule_of_nonlinear (K W : Submodule ℚ L) (hWK : W ≤ K)
    (hbracket : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ W)
    (f : X → L) (hf : ∀ x, f x ∈ K) (w : FreeSemigroup X) (hw : w.tail ≠ []) :
    dynkinWord f w ∈ W := by
  unfold dynkinWord
  cases ht : w.tail with
  | nil => exact False.elim (hw ht)
  | cons x xs =>
    exact rightBracketList_mem_submodule K W
      (fun a ha b hb => hbracket a (hWK ha) b hb) f hf xs ⁅f w.head, f x⁆
        (hbracket _ (hf _) _ (hf _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CompatibleReducedFastReset
namespace OAI

section

namespace Erdos3

theorem reducedResetParameter_nonneg (a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reducedResetParameter a p := by
  unfold reducedResetParameter
  positivity

theorem le_reducedResetParameter (a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ reducedResetParameter a p := by
  have h₁ : 0 ≤ ((p + 2) ^ 10 + 2) ^ 36 := by positivity
  have h₂ : 0 ≤ (p + 2) ^ a := by positivity
  exact (le_add_of_nonneg_left (add_nonneg h₁ h₂)).trans
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))

theorem reducedResetParameter_controls (a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + 2) ^ a ≤ reducedResetParameter a p + 2 ∧
      ((p + 2) ^ 10 + 2) ^ 36 ≤ reducedResetParameter a p ∧
      ((p + 2) ^ 10 + 2) ^ 18 + (p + 2) ^ a ≤ reducedResetParameter a p + 2 := by
  have h₁ : 0 ≤ ((p + 2) ^ 10 + 2) ^ 36 := by positivity
  have h₂ : 0 ≤ (p + 2) ^ a := by positivity
  have hbase : 1 ≤ (p + 2) ^ 10 + 2 := by
    exact (by norm_num : (1 : ℝ) ≤ 2).trans
      (le_add_of_nonneg_left (by positivity : 0 ≤ (p + 2) ^ 10))
  have hpow := pow_le_pow_right₀ hbase (by decide : 18 ≤ 36)
  have hsum : ((p + 2) ^ 10 + 2) ^ 36 + (p + 2) ^ a ≤ reducedResetParameter a p :=
    (le_add_of_nonneg_right hp).trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  have hplus : reducedResetParameter a p ≤ reducedResetParameter a p + 2 :=
    le_add_of_nonneg_right (by norm_num)
  exact ⟨(le_add_of_nonneg_left h₁).trans (hsum.trans hplus),
    (le_add_of_nonneg_right h₂).trans hsum,
    (add_le_add hpow (le_refl ((p + 2) ^ a))).trans (hsum.trans hplus)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FastRemovalBudget
namespace OAI

section

namespace Erdos3

theorem exists_fast_removal_factor_budget (s a cA cD : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (p : ℝ), 0 ≤ p → ∀ (K : ℝ), 0 ≤ K → K ≤ Real.exp p →
      K * Real.exp ((p + cA) ^ cA) * K ≤ Real.exp ((p + C) ^ C) ∧
      K * (Real.exp ((p + cD) ^ cD) * ((s + 1 : ℕ) * Real.exp ((p + 2) ^ a))) ≤
        Real.exp ((p + C) ^ C) := by
  let P : Polynomial ℕ := 2 * Polynomial.X + (Polynomial.X + Polynomial.C cA) ^ cA +
    (Polynomial.X + Polynomial.C cD) ^ cD + Polynomial.C (s + 1) + (Polynomial.X + 2) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp K hK hKp
  have hpoly : 2 * p + (p + cA) ^ cA + (p + cD) ^ cD + (s + 1 : ℕ) + (p + 2) ^ a ≤
      (p + C) ^ C := by simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have hAexp : 2 * p + (p + cA) ^ cA ≤ (p + C) ^ C := by
    have h1 : 0 ≤ (p + cD) ^ cD := by positivity
    have h2 : 0 ≤ (p + 2) ^ a := by positivity
    have h3 : (0 : ℝ) ≤ (s + 1 : ℕ) := Nat.cast_nonneg _
    linarith
  have hDexp : p + (p + cD) ^ cD + (s + 1 : ℕ) + (p + 2) ^ a ≤ (p + C) ^ C := by
    have h1 : 0 ≤ (p + cA) ^ cA := by positivity
    linarith
  have hAfactor : K * Real.exp ((p + cA) ^ cA) * K ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp p * Real.exp ((p + cA) ^ cA) * Real.exp p := by gcongr
      _ = Real.exp (2 * p + (p + cA) ^ cA) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hAexp
  have hstep : ((s + 1 : ℕ) : ℝ) ≤ Real.exp (s + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (s + 1 : ℝ))
  have hDfactor : K * (Real.exp ((p + cD) ^ cD) * ((s + 1 : ℕ) * Real.exp ((p + 2) ^ a))) ≤
      Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp p * (Real.exp ((p + cD) ^ cD) * (Real.exp (s + 1) * Real.exp ((p + 2) ^ a))) := by
        gcongr
      _ = Real.exp (p + (p + cD) ^ cD + (s + 1 : ℕ) + (p + 2) ^ a) := by
        simp only [← Real.exp_add, Nat.cast_add, Nat.cast_one]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hDexp
  exact ⟨hAfactor, hDfactor⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InitialRemovalBudget
namespace OAI

section

namespace Erdos3

theorem exists_initial_removal_budget (cS cR : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let A := (p + cS) ^ cS
      let B := (p + cR) ^ cR
      let r := p + 1 + 2 * A
      Real.exp A * Real.exp p ≤ Real.exp r ∧
      Real.exp A * (Real.exp p + Real.exp A) ≤ Real.exp r ∧
      Real.exp p * Real.exp r ≤ Real.exp ((p + C) ^ C) ∧
      Real.exp p * Real.exp B ≤ Real.exp ((p + C) ^ C) := by
  let P : Polynomial ℕ := 2 * Polynomial.X + 1 +
    2 * (Polynomial.X + Polynomial.C cS) ^ cS +
    (Polynomial.X + Polynomial.C cR) ^ cR
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp A B r
  have hA : 0 ≤ A := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have hB : 0 ≤ B := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have hpoly : 2 * p + 1 + 2 * A + B ≤ (p + C) ^ C := by
    simpa [P, A, B, Polynomial.eval₂_pow] using hbudget p hp
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hsmall : Real.exp A * (Real.exp p + Real.exp A) ≤ Real.exp r := by
    calc
      _ ≤ Real.exp A * (Real.exp (p + A) + Real.exp (p + A)) := by
        gcongr <;> linarith
      _ = 2 * Real.exp (p + 2 * A) := by
        rw [← two_mul, mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp 1 * Real.exp (p + 2 * A) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp r := by rw [← Real.exp_add]; congr 1; dsimp [r]; ring
  refine ⟨?_, hsmall, ?_, ?_⟩
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [r]
    linarith
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [r]
    linarith
  · rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PointwiseSymbolBudget
namespace OAI

section

namespace Erdos3

theorem symbol_spanning_count_bound (s d m k : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hk : (k : ℝ) ≤ p) :
    ((d * (s + 1) * (m + 1) ^ s * k : ℕ) : ℝ) ≤ (p + (s + 3)) ^ (s + 3) := by
  have hdim := NilpotentLieFiltration.symbol_dimension_bound_le_power s d m hp hd hm
  have hbase : p + (s + 2 : ℝ) ≤ p + (s + 3 : ℝ) := by linarith
  have hdim' : ((d * (s + 1) * (m + 1) ^ s : ℕ) : ℝ) ≤
      (p + (s + 3)) ^ (s + 2) :=
    hdim.trans (pow_le_pow_left₀ (by positivity) hbase _)
  rw [Nat.cast_mul]
  calc
    _ ≤ (p + (s + 3)) ^ (s + 2) * (p + (s + 3)) :=
      mul_le_mul hdim' (hk.trans (le_add_of_nonneg_right (by positivity))) (by positivity) (by positivity)
    _ = (p + (s + 3)) ^ (s + 3) := (pow_succ (p + (s + 3)) (s + 2)).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerTriangularMinor
namespace OAI

section

namespace Erdos3

theorem exists_minimal_row_minor {K : Type*} [Field K] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) K) (hA : LinearIndependent K A.col) :
    ∃ p : Fin k → Fin m, (A.submatrix p id).det ≠ 0 ∧
      ∀ q : Fin k → Fin m, (A.submatrix q id).det ≠ 0 →
        (∑ j, (p j).val) ≤ ∑ j, (q j).val := by
  classical
  let S := Finset.univ.filter (fun p : Fin k → Fin m => (A.submatrix p id).det ≠ 0)
  obtain ⟨p, hp⟩ := exists_nonzero_row_minor A hA
  have hS : S.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  obtain ⟨q, hq, hmin⟩ := S.exists_min_image (fun p => ∑ j, (p j).val) hS
  exact ⟨q, (Finset.mem_filter.mp hq).2,
    fun p hp => hmin p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_preserved_nonzero_row_minor
    {K : Type*} [Field K] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) K) (hA : LinearIndependent K A.col) :
    ∃ p : Fin k → Fin m, Function.Injective p ∧ (A.submatrix p id).det ≠ 0 ∧
      ∀ M : Matrix (Fin m) (Fin m) K,
        (∀ i j, i < j → M i j = 0) → (∀ i, M i i = 1) →
        ((M * A).submatrix p id).det = (A.submatrix p id).det := by
  obtain ⟨p, hp, hmin⟩ := exists_minimal_row_minor A hA
  exact ⟨p, nonzero_row_minor_injective A p hp, hp,
    fun M hM hdiag => lower_unitriangular_preserves_minimal_minor A p hp hmin M hM hdiag⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeSheetHaar
namespace OAI

section

namespace Erdos3

open Module

theorem zspan_covolume_sq_eq_det_gram_fintype
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (b : Basis ι ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ^ 2 = (Matrix.gram ℝ b).det := by
  classical
  let e := Fintype.equivFin ι
  let b' := b.reindex e
  have hspan : Submodule.span ℤ (Set.range b') = Submodule.span ℤ (Set.range b) := by
    congr 1
    simp [b', Basis.coe_reindex]
  have hgram : Matrix.gram ℝ b' = (Matrix.gram ℝ b).submatrix e.symm e.symm := by
    ext i j
    simp [b', Matrix.gram_apply]
  have h := zspan_covolume_sq_eq_det_gram b'
  rw [hspan, hgram, Matrix.det_submatrix_equiv_self] at h
  exact h

theorem lattice_covolume_sq_eq_gram
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis ι ℤ Λ) :
    ZLattice.covolume Λ ^ 2 = (Matrix.gram ℝ (b.ofZLatticeBasis ℝ Λ)).det := by
  have h := zspan_covolume_sq_eq_det_gram_fintype (b.ofZLatticeBasis ℝ Λ)
  simpa only [b.ofZLatticeBasis_span ℝ] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateMinorCovolume
namespace OAI

section

namespace Erdos3

open RealInnerProductSpace

theorem abs_isometric_lattice_basis_det_le_covolume {r : ℕ} {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin r) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (p : Fin r → ι) (hp : Function.Injective p) :
    |(Matrix.of (fun i j => f (b i).val (p j))).det| ≤ ZLattice.covolume Λ := by
  have hs : ZLattice.covolume Λ ^ 2 =
      (Matrix.gram ℝ (fun i : Fin r => f (b i).val)).det := by
    rw [lattice_covolume_sq_eq_gram Λ b]
    congr 1
    ext i j
    simp only [Matrix.gram_apply, Module.Basis.ofZLatticeBasis_apply, LinearIsometry.inner_map_map]
  have h := abs_coordinate_det_le_sqrt_gram (fun i : Fin r => f (b i).val) p hp
  rw [← hs, Real.sqrt_sq (ZLattice.covolume_pos Λ MeasureTheory.volume).le] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScaledLatticeCovolume
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem rational_vector_mem_span_integer_points {κ : Type*} [Fintype κ]
    (U : Submodule ℝ (κ → ℝ)) (q : κ → ℚ) (hq : (fun i => (q i : ℝ)) ∈ U) :
    (fun i => (q i : ℝ)) ∈ Submodule.span ℝ
      {x : κ → ℝ | x ∈ realIntegerGrid ∧ x ∈ U} := by
  classical
  let D := arrayDenominator q
  let z := clearedArray q
  have hD : (D : ℝ) ≠ 0 := by exact_mod_cast (arrayDenominator_pos q).ne'
  have he : (fun i => (z i : ℝ)) = (D : ℝ) • (fun i => (q i : ℝ)) := by
    funext i
    change (clearedArray q i : ℝ) = (arrayDenominator q : ℝ) * (q i : ℝ)
    exact_mod_cast clearedArray_cast q i
  have hz : (fun i => (z i : ℝ)) ∈ U := by rw [he]; exact U.smul_mem _ hq
  have hs : (fun i => (z i : ℝ)) ∈ Submodule.span ℝ
      {x : κ → ℝ | x ∈ realIntegerGrid ∧ x ∈ U} := Submodule.subset_span ⟨⟨z, rfl⟩, hz⟩
  have hinv := (Submodule.span ℝ {x : κ → ℝ | x ∈ realIntegerGrid ∧ x ∈ U}).smul_mem
    (D : ℝ)⁻¹ hs
  simpa only [he, smul_smul, inv_mul_cancel₀ hD, one_smul] using hinv

theorem exists_rational_matrix_height {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) : ∃ H : ℕ, 1 ≤ H ∧ ∀ i j, RationalHeightLE (A i j) H := by
  classical
  let H := max 1 (Finset.univ.sup fun ij : ι × κ => max (A ij.1 ij.2).num.natAbs (A ij.1 ij.2).den)
  refine ⟨H, le_max_left _ _, ?_⟩
  intro i j
  have hmax : max (A i j).num.natAbs (A i j).den ≤ H :=
    (Finset.le_sup (f := fun ij : ι × κ => max (A ij.1 ij.2).num.natAbs (A ij.1 ij.2).den)
      (Finset.mem_univ (i, j))).trans (le_max_right _ _)
  exact ⟨(le_max_left _ _).trans hmax, (le_max_right _ _).trans hmax⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanGraphResidual
namespace OAI

section

namespace Erdos3

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

variable (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

theorem euclideanDerivativeShiftMap_integer (v : EuclideanSpace ℝ (σ ⊕ κ))
    (hv : v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl) :
    euclideanDerivativeShiftMap T hT v ∈ realIntegerGrid := by
  have hv' := (euclideanDerivativeLattice_mem_iff T hT scale hscale Y A l hl v).mp hv
  obtain ⟨h, z, hz⟩ := (derivativeLattice_mem_iff T hT scale hscale Y A l hl _).mp hv'
  refine ⟨h, ?_⟩
  funext i
  change (h i : ℝ) = T i * (productEuclideanEquiv.symm v).1 i
  rw [hz, derivativeLatticeEquiv_apply]
  exact (mul_div_cancel₀ (h i : ℝ) (hT i)).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeIndexBounds
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem euclideanVerticalMap_horizontal {σ : Type*} {m a : ℕ}
    (scale : Fin m → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (x : Fin m → ℝ) (i : Fin m) (hi : i.val < a) :
    euclideanVerticalMap (σ := σ) scale hscale A x (Sum.inr i) = x i := by
  rw [euclideanVerticalMap_apply_inr, hscalehor i hi, one_mul]
  calc
    A x i = ((LinearMap.toMatrix' A.toLinearMap) *ᵥ x) i :=
      (congrFun (LinearMap.toMatrix'_mulVec A.toLinearMap x) i).symm
    _ = x i := lower_triangular_horizontal_mulVec _ hA hblock x i hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SortedBasisTriangular
namespace OAI

section

namespace Erdos3

open Module

theorem realDenominatorGrid_comp {ι κ : Type*} (l : ℕ) (x : ι → ℝ)
    (hx : x ∈ realDenominatorGrid l) (e : κ → ι) :
    (x ∘ e) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨z ∘ e, ?_⟩
  funext i
  exact congrFun hz (e i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedQuotientSection
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

section Algebra

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
  (hP : P = Submodule.span K (b '' S))

noncomputable def supportedQuotientSection : (V ⧸ P) →ₗ[K] V :=
  (supportedQuotientBasis b P S hP).constr K (fun i => b i.val)

@[simp] theorem supportedQuotientSection_basis (i : {i // i ∉ S}) :
    supportedQuotientSection b P S hP (supportedQuotientBasis b P S hP i) = b i.val :=
  Basis.constr_basis _ _ _ i

theorem supportedQuotientSection_rightInverse (x : V ⧸ P) :
    P.mkQ (supportedQuotientSection b P S hP x) = x := by
  have he : P.mkQ.comp (supportedQuotientSection b P S hP) = LinearMap.id := by
    apply (supportedQuotientBasis b P S hP).ext
    intro i
    change P.mkQ (supportedQuotientSection b P S hP
      (supportedQuotientBasis b P S hP i)) = supportedQuotientBasis b P S hP i
    rw [supportedQuotientSection_basis, supportedQuotientBasis_apply]
  exact DFunLike.congr_fun he x

theorem supportedQuotientSection_coordinate (x : V ⧸ P) (i : {i // i ∉ S}) :
    b.repr (supportedQuotientSection b P S hP x) i =
      (supportedQuotientBasis b P S hP).repr x i := by
  rw [← supportedQuotientBasis_repr_mk b P S hP, supportedQuotientSection_rightInverse]

theorem supportedQuotientSection_coordinate_zero (x : V ⧸ P) (i : ι) (hi : i ∈ S) :
    b.repr (supportedQuotientSection b P S hP x) i = 0 := by
  have he : (b.coord i).comp (supportedQuotientSection b P S hP) = 0 := by
    apply (supportedQuotientBasis b P S hP).ext
    intro j
    change b.repr (supportedQuotientSection b P S hP
      (supportedQuotientBasis b P S hP j)) i = 0
    rw [supportedQuotientSection_basis, b.repr_self]
    apply Finsupp.single_eq_of_ne
    exact fun hij => j.property (hij ▸ hi)
  exact DFunLike.congr_fun he x

end Algebra

variable {V ι : Type*} [AddCommGroup V] [Module ℚ V]
  (b : Basis ι ℚ V) (P : Submodule ℚ V) (S : Set ι)
  (hP : P = Submodule.span ℚ (b '' S))

theorem realSupportedQuotientSection_rightInverse (x : ℝ ⊗[ℚ] (V ⧸ P)) :
    P.mkQ.baseChange ℝ ((supportedQuotientSection b P S hP).baseChange ℝ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      supportedQuotientSection_rightInverse]

theorem realSupportedQuotientSection_coordinate
    (x : ℝ ⊗[ℚ] (V ⧸ P)) (i : {i // i ∉ S}) :
    (b.baseChange ℝ).repr ((supportedQuotientSection b P S hP).baseChange ℝ x) i =
      ((supportedQuotientBasis b P S hP).baseChange ℝ).repr x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, supportedQuotientSection_coordinate]

theorem realSupportedQuotientSection_coordinate_zero
    (x : ℝ ⊗[ℚ] (V ⧸ P)) (i : ι) (hi : i ∈ S) :
    (b.baseChange ℝ).repr ((supportedQuotientSection b P S hP).baseChange ℝ x) i = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      supportedQuotientSection_coordinate_zero b P S hP x i hi]
    exact zero_smul ℚ r

theorem realSupportedQuotientSection_norm [Fintype ι] [DecidablePred (· ∈ S)]
    (x : ℝ ⊗[ℚ] (V ⧸ P)) :
    ‖(b.baseChange ℝ).equivFun ((supportedQuotientSection b P S hP).baseChange ℝ x)‖ =
      ‖((supportedQuotientBasis b P S hP).baseChange ℝ).equivFun x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    by_cases hi : i ∈ S
    · rw [Basis.equivFun_apply, realSupportedQuotientSection_coordinate_zero b P S hP x i hi,
        norm_zero]
      exact norm_nonneg _
    · rw [Basis.equivFun_apply,
        realSupportedQuotientSection_coordinate b P S hP x ⟨i, hi⟩]
      exact norm_le_pi_norm (((supportedQuotientBasis b P S hP).baseChange ℝ).equivFun x) ⟨i, hi⟩
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [Basis.equivFun_apply, ← realSupportedQuotientSection_coordinate b P S hP x i]
    exact norm_le_pi_norm ((b.baseChange ℝ).equivFun
      ((supportedQuotientSection b P S hP).baseChange ℝ x)) i.val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.GridNormalizationDenominator
namespace OAI

section

namespace Erdos3

theorem exists_integer_scaled_grid_matrix {ι κ : Type*}
    (H : Matrix ι κ ℝ) (l : ℕ) (hgrid : ∀ j, H.col j ∈ realDenominatorGrid l) :
    ∃ Z : Matrix ι κ ℤ, Z.map (Int.castRingHom ℝ) = (l : ℝ) • H := by
  choose z hz using hgrid
  refine ⟨fun i j => z j i, ?_⟩
  ext i j
  exact congrFun (hz j) i

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem exists_bounded_rational_grid_matrix {ι κ : Type*}
    (A : Matrix ι κ ℝ) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, A.col j ∈ realDenominatorGrid l)
    (C : ℝ) (hbound : ∀ i j, |A i j| ≤ C) :
    ∃ Q : Matrix ι κ ℚ, Q.map (Rat.castHom ℝ) = A ∧
      ∀ i j, RationalHeightLE (Q i j) (max l (Nat.ceil ((l : ℝ) * C))) := by
  obtain ⟨Z, hZ⟩ := exists_integer_scaled_grid_matrix A l hgrid
  let Q : Matrix ι κ ℚ := fun i j => (Z i j : ℚ) / l
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  refine ⟨Q, ?_, ?_⟩
  · ext i j
    change (((Z i j : ℚ) / l : ℚ) : ℝ) = A i j
    push_cast
    apply (div_eq_iff hlr.ne').mpr
    have h := congrArg (fun B : Matrix ι κ ℝ => B i j) hZ
    change (Z i j : ℝ) = (l : ℝ) * A i j at h
    simpa only [mul_comm] using h
  · intro i j
    have hz : (Z i j).natAbs ≤ Nat.ceil ((l : ℝ) * C) := by
      have he : (Z i j : ℝ) = (l : ℝ) * A i j :=
        congrArg (fun B : Matrix ι κ ℝ => B i j) hZ
      have hb : |(Z i j : ℝ)| ≤ (l : ℝ) * C := by
        rw [he, abs_mul, abs_of_pos hlr]
        exact mul_le_mul_of_nonneg_left (hbound i j) hlr.le
      have hc := hb.trans (Nat.le_ceil ((l : ℝ) * C))
      apply (Nat.cast_le (α := ℝ)).mp
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hc
    change RationalHeightLE ((Z i j : ℚ) / l) _
    have h := rationalHeightLE_fraction (Z i j) (l : ℤ)
      (by exact_mod_cast hl.ne') (hz.trans (le_max_right _ _))
      (by simpa only [Int.natAbs_natCast] using le_max_left l (Nat.ceil ((l : ℝ) * C)))
    simpa only [Int.cast_natCast] using h

theorem exists_bounded_rational_map_matrix {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : (κ → ℝ) →ₗ[ℝ] (ι → ℝ)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, f (Pi.single j 1) ∈ realDenominatorGrid l)
    (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ∃ Q : Matrix ι κ ℚ,
      (∀ i j, RationalHeightLE (Q i j) (max l (Nat.ceil ((l : ℝ) * C)))) ∧
      ∀ x, f x = Q.map (Rat.castHom ℝ) *ᵥ x := by
  have hcol (j : κ) : (LinearMap.toMatrix' f).col j = f (Pi.single j 1) := by
    funext i
    exact LinearMap.toMatrix'_apply f i j
  obtain ⟨Q, hQ, hheight⟩ := exists_bounded_rational_grid_matrix (LinearMap.toMatrix' f) l hl
    (fun j => by rw [hcol]; exact hgrid j) C (by
      intro i j
      rw [LinearMap.toMatrix'_apply]
      have h := (norm_le_pi_norm (f (Pi.single j 1)) i).trans (hbound (Pi.single j 1))
      simpa only [Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] using h)
  refine ⟨Q, hheight, fun x => ?_⟩
  rw [hQ]
  exact (LinearMap.toMatrix'_mulVec f x).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

def mixedPairBudget (p q : ℝ) : ℝ := 4 * (p + q + 1) + raisedNiltestBudget (p + q) + 6

end Erdos3

end

end OAI
end


