-- Prove2me | Definitions.Def_OAIE3v2B103
-- name    : OAIE3v2B103
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:27:47.56445+00:00
-- url     : https://prove2.me/theorems/57f6bbd5-d813-48e2-80cc-b083f09f0926
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 105 of 311
-- statement:
--   Definitions bundle 105 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B087`, `OAIE3v2B088`, `OAIE3v2B089`, `OAIE3v2B090`, `OAIE3v2B091`, `OAIE3v2B092` of this split.
--
--   Modules: `Estimates/AllocatedReferenceJetWindow.lean`, `Estimates/AllocatedRowsAmbientProjectedFamilyMultiple.lean`, `Estimates/CoefficientModeLowerTerms.lean`, `Estimates/LowJetAmbientReconstruction.lean`, `Estimates/MultiaffineOptionExpansion.lean`, `Estimates/PairedDiagonalApproximation.lean`, `Estimates/PhysicalAmbientVolumeRatio.lean`, `Estimates/PhysicalRowsSiteReconstruction.lean`, `Estimates/RealProjectedCoefficientLift.lean`, `Estimates/StrideProductBounds.lean`, `Estimates/SubspaceLayeredModeSmoothRemoval.lean`, `Estimates/UniformCommutingCircleDecomposition.lean`, `Fourier/CanonicalDensityFourier.lean`, `Fourier/StandardJetFourier.lean`, `Geometry/MultilinearBoxInverse.lean`, `Geometry/RepresentativeWindowTransport.lean`, `Geometry/SpatialShiftedWindowError.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Lattices/AffineCoefficientSubspace.lean`, `Lattices/AffineLiftInsertion.lean`, `Lattices/RelativeSliceAffineThreeFactorLaw.lean`, `Lattices/RetainedAffineCommonCover.lean`, `Lattices/SelectedResidueApproximation.lean`, `Lattices/SelectedResidueL1Surrogate.lean`, `Lattices/SmoothResidueWindowMass.lean`, `Linear/MarkedLieSpan.lean`, `Polynomial/CRTPolynomialPatchComposition.lean`, `Polynomial/MonomialCoordinateRows.lean`, `Polynomial/MultiaffinePolynomialBias.lean`, `Polynomial/MultilinearSlicePolynomial.lean`, `Polynomial/RealGradedSymbolPolynomial.lean`, `Polynomial/RealPolynomialChartSubstitution.lean`, `Polynomial/TranslationTopDegree.lean`, `Probability/IntervalDivisorProbability.lean`, `Probability/PositiveDensityNormalization.lean`, `Probability/ShiftedSmoothProductLaw.lean`, `Sampling/AllocatedExternalCandidateSamplerFamily.lean`, `Sampling/SamplingRankProjectedContainment.lean`, `Sampling/SmoothSplitSampling.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B087
import Definitions.Def_OAIE3v2B088
import Definitions.Def_OAIE3v2B089
import Definitions.Def_OAIE3v2B090
import Definitions.Def_OAIE3v2B091
import Definitions.Def_OAIE3v2B092

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MultilinearSlicePolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem squarefree_polynomial_expansion {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (P : MvPolynomial ι R)
    (hP : ∀ d ∈ P.support, SquarefreeExponent d) :
    P = ∑ S : Finset ι, MvPolynomial.monomial (SquarefreeIndex.ofFinset S).val
      (P.coeff (SquarefreeIndex.ofFinset S).val) := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases hd : SquarefreeExponent d
  · have he : (SquarefreeIndex.ofFinset d.support).val = d :=
      congrArg Subtype.val (SquarefreeIndex.ofFinset_support ⟨d,hd⟩)
    rw [Finset.sum_eq_single d.support]
    · simp [he]
    · intro S _ hS
      have hne : (SquarefreeIndex.ofFinset S).val ≠ d := by
        intro h
        apply hS
        have hs := congrArg Finsupp.support h
        rwa [SquarefreeIndex.support_ofFinset] at hs
      simp [hne]
    · simp
  · have hz : P.coeff d = 0 := by
      by_contra h
      exact hd (hP d (MvPolynomial.mem_support_iff.mpr h))
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro S _
    have hne : (SquarefreeIndex.ofFinset S).val ≠ d := by
      intro h
      exact hd (h ▸ (SquarefreeIndex.ofFinset S).property)
    simp [hne]

theorem squarefree_polynomial_eval {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (P : MvPolynomial ι R)
    (hP : ∀ d ∈ P.support, SquarefreeExponent d) (x : ι → R) :
    MvPolynomial.eval x P = ∑ S : Finset ι, P.coeff (SquarefreeIndex.ofFinset S).val *
      ∏ i, if i ∈ S then x i else 1 := by
  conv_lhs => rw [squarefree_polynomial_expansion P hP]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [MvPolynomial.eval_monomial]
  congr 1
  rw [Finsupp.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [SquarefreeIndex.ofFinset_apply]
  split_ifs <;> simp

theorem multiaffinePolynomial_eval {R : Type*} [CommRing R] {n : ℕ}
    (P : MvPolynomial (Fin n) R) (hP : ∀ i, P.degreeOf i ≤ 1) (x : Fin n → R) :
    MvPolynomial.eval x P =
      multiaffineExpansion (fun S => P.coeff (SquarefreeIndex.ofFinset S).val) x := by
  exact squarefree_polynomial_eval P
    (fun d hd i => (MvPolynomial.le_degreeOf_of_mem_support i hd).trans (hP i)) x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def subsetPolynomial {I R : Type*} [Fintype I] [CommRing R]
    (c : Finset I → R) : MvPolynomial I R :=
  ∑ S, MvPolynomial.monomial (SquarefreeIndex.ofFinset S).val (c S)

theorem subsetPolynomial_coefficient {I R : Type*} [Fintype I] [CommRing R]
    (c : Finset I → R) (S : Finset I) :
    (subsetPolynomial c).coeff (SquarefreeIndex.ofFinset S).val = c S := by
  simp only [subsetPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single S]
  · simp
  · intro T _ hT
    have hne : (SquarefreeIndex.ofFinset T).val ≠ (SquarefreeIndex.ofFinset S).val := by
      intro h
      apply hT
      simpa only [SquarefreeIndex.support_ofFinset] using congrArg Finsupp.support h
    simp [hne]
  · simp

theorem subsetPolynomial_degree {I R : Type*} [Fintype I] [CommRing R]
    (c : Finset I → R) (i : I) : (subsetPolynomial c).degreeOf i ≤ 1 := by
  unfold subsetPolynomial
  apply (MvPolynomial.degreeOf_sum_le i Finset.univ _).trans
  apply Finset.sup_le
  intro S _
  by_cases hc : c S = 0
  · simp [hc]
  · rw [MvPolynomial.degreeOf_monomial_eq _ _ hc]
    exact (SquarefreeIndex.ofFinset S).property i

theorem subsetPolynomial_eval {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (c : Finset I → R) (x : I → R) :
    MvPolynomial.eval x (subsetPolynomial c) = ∑ S, c S * ∏ i ∈ S, x i := by
  rw [subsetPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [MvPolynomial.eval_monomial]
  congr 1
  rw [Finsupp.prod_pow]
  have he : (fun i => x i ^ (SquarefreeIndex.ofFinset S).val i) =
      (fun i => if i ∈ S then x i else 1) := by
    funext i
    rw [SquarefreeIndex.ofFinset_apply]
    split_ifs <;> simp
  rw [he, Finset.prod_ite_mem_eq]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def multilinearSlicePolynomial {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) R) (b w : Fin n → M) :
    MvPolynomial (Fin n) R := subsetPolynomial (fun S => F (S.piecewise w b))

theorem multilinearSlicePolynomial_eval {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) R) (b w : Fin n → M) (x : Fin n → R) :
    MvPolynomial.eval x (multilinearSlicePolynomial F b w) =
      F (fun i => b i + x i • w i) := by
  rw [multilinearSlicePolynomial, subsetPolynomial_eval]
  exact (multilinear_affine_expansion F b w x).symm

theorem multilinearSlicePolynomial_degree {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) R) (b w : Fin n → M) (i : Fin n) :
    (multilinearSlicePolynomial F b w).degreeOf i ≤ 1 := subsetPolynomial_degree _ _

theorem multilinearSlicePolynomial_top {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) R) (b w : Fin n → M) :
    (multilinearSlicePolynomial F b w).coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val = F w := by
  rw [multilinearSlicePolynomial, subsetPolynomial_coefficient, Finset.piecewise_univ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultiaffineOptionExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem optionLinearCoefficient_squarefree {n : ℕ}
    (P : MvPolynomial (Option (Fin n)) ℝ) (hP : ∀ i, P.degreeOf i ≤ 1) (j : ℕ) :
    ∀ d ∈ ((MvPolynomial.optionEquivLeft ℝ (Fin n) P).coeff j).support,
      SquarefreeExponent d := by
  intro d hd i
  have hd' : d.optionElim j ∈ P.support :=
    (MvPolynomial.mem_support_coeff_optionEquivLeft ℝ).mp hd
  have h := (MvPolynomial.le_degreeOf_of_mem_support (some i) hd').trans (hP (some i))
  simpa using h

theorem multiaffineOption_eval {n : ℕ} (P : MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (x : Fin n → ℝ) (t : ℝ) :
    MvPolynomial.eval (fun i => Option.elim i t x) P =
      multiaffineExpansion
        (fun S => P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim 1)*t +
          P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim 0)) x := by
  let Q := MvPolynomial.optionEquivLeft ℝ (Fin n) P
  have hQ : Q.natDegree ≤ 1 := by
    rw [MvPolynomial.natDegree_optionEquivLeft]
    exact hP none
  have he (j : ℕ) : MvPolynomial.eval x (Q.coeff j) =
      multiaffineExpansion (fun S => P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim j)) x := by
    rw [squarefree_polynomial_eval (Q.coeff j) (optionLinearCoefficient_squarefree P hP j)]
    simp only [multiaffineExpansion, Q, MvPolynomial.optionEquivLeft_coeff_coeff]
  rw [MvPolynomial.optionEquivLeft_elim_eval, multiaffineExpansion_affine]
  change Polynomial.eval t (Polynomial.map (MvPolynomial.eval x) Q) = _
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hQ]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [he 1, he 0]

theorem optionSquarefree_full_exponent {n : ℕ} :
    (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val.optionElim 1 =
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Option (Fin n)))).val := by
  ext i
  cases i <;> simp [SquarefreeIndex.ofFinset_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MultiaffinePolynomialBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem multiaffine_polynomial_bias {n : ℕ} (P : MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (N : Fin n → ℕ) (M : ℕ)
    (u : Fin n → ℝ) (w : ℝ) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 x : (∀ i, Fin (N i)), 𝔼 t : Fin M,
      character ((MvPolynomial.eval
        (fun i => Option.elim i (w+(t.val : ℝ)) (fun j => u j+((x j).val : ℝ))) P : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ multiaffineBiasBudget n ζ ∧
      ∃ m : ℤ, |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Option (Fin n)))).val-
        (m : ℝ)/q| ≤ multiaffineBiasBudget n ζ / ((M : ℝ)*∏ i, (N i : ℝ)) := by
  have hQ := multiaffineBiasBudget_pos n hζ
  have hNp : ∀ i, 0 < N i := fun i => by exact_mod_cast hQ.trans_le (hN i)
  have hMp : 0 < M := by exact_mod_cast hQ.trans_le hM
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hNp i⟩⟩
  let : Nonempty (Fin M) := ⟨⟨0,hMp⟩⟩
  have hζ1 : ζ ≤ 1 := hbias.trans (norm_real_phase_double_mean_le_one _)
  let a := fun S : Finset (Fin n) => P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim 1)
  let b := fun S : Finset (Fin n) => P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim 0)
  have hphase (x : ∀ i, Fin (N i)) (t : Fin M) :
      character ((MvPolynomial.eval
        (fun i => Option.elim i (w+(t.val : ℝ)) (fun j => u j+((x j).val : ℝ))) P : ℝ) :
        CircleFourier.Circle) = multiaffineIntervalPhase a b u w x t := by
    rw [multiaffineOption_eval P hP]
    rfl
  simp_rw [hphase] at hbias
  have h := multiaffine_bias_approximation N M a b u w hζ hζ1 hN hM hbias
  simpa only [a, optionSquarefree_full_exponent] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrideProductBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def diagonalMultiaffineScaling {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (s : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  subsetPolynomial (fun S => P.coeff (SquarefreeIndex.ofFinset S).val * ∏ i ∈ S, s i)

theorem diagonalMultiaffineScaling_degree {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (s : Fin n → ℝ) (i : Fin n) : (diagonalMultiaffineScaling P s).degreeOf i ≤ 1 :=
  subsetPolynomial_degree _ _

theorem diagonalMultiaffineScaling_top {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (s : Fin n → ℝ) :
    (diagonalMultiaffineScaling P s).coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val =
      P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val * ∏ i, s i := by
  exact subsetPolynomial_coefficient _ _

theorem diagonalMultiaffineScaling_eval {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (s x : Fin n → ℝ) :
    MvPolynomial.eval x (diagonalMultiaffineScaling P s) =
      MvPolynomial.eval (fun i => s i*x i) P := by
  rw [diagonalMultiaffineScaling, subsetPolynomial_eval, multiaffinePolynomial_eval P hP]
  unfold multiaffineExpansion
  simp only [Finset.prod_ite_mem_eq]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem fullSquarefreeExponent_map_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) :
    (SquarefreeIndex.ofFinset (Finset.univ : Finset ι)).val.mapDomain e =
      (SquarefreeIndex.ofFinset (Finset.univ : Finset κ)).val := by
  ext j
  obtain ⟨i,rfl⟩ := e.surjective j
  rw [Finsupp.mapDomain_apply e.injective]
  simp [SquarefreeIndex.ofFinset_apply]

theorem fin_multiaffine_polynomial_bias {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (N : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i),
      character ((MvPolynomial.eval (fun i => u i+((x i).val : ℝ)) P : ℝ) : CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ multiaffineBiasBudget n ζ ∧
      ∃ m : ℤ, |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val-
        (m : ℝ)/q| ≤ multiaffineBiasBudget n ζ / ∏ i, (N i : ℝ) := by
  let e := _root_.finSuccEquiv n
  let Q := MvPolynomial.rename e P
  have hQ : ∀ j, Q.degreeOf j ≤ 1 := by
    intro j
    obtain ⟨i,rfl⟩ := e.surjective j
    rw [MvPolynomial.degreeOf_rename_of_injective e.injective]
    exact hP i
  have heval (x : ∀ i : Fin n, Fin (N i.succ)) (t : Fin (N 0)) :
      MvPolynomial.eval
        (fun j => Option.elim j (u 0+(t.val : ℝ)) (fun i => u i.succ+((x i).val : ℝ))) Q =
      MvPolynomial.eval
        (fun i => u i+(((Fin.cons t x : ∀ j : Fin (n+1), Fin (N j)) i).val : ℝ)) P := by
    rw [MvPolynomial.eval_rename]
    apply congrArg (fun z : Fin (n+1) → ℝ => MvPolynomial.eval z P)
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e]
    · simp [e]
  rw [expect_dependent_fin_cons, Finset.expect_comm] at hbias
  simp_rw [← heval] at hbias
  have h := multiaffine_polynomial_bias Q hQ (fun i => N i.succ) (N 0)
    (fun i => u i.succ) (u 0) hζ (fun i => hN i.succ) (hN 0) hbias
  have hcoeff : Q.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Option (Fin n)))).val =
      P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val := by
    rw [← fullSquarefreeExponent_map_equiv e, MvPolynomial.coeff_rename_mapDomain e e.injective]
  simpa only [hcoeff, Fin.prod_univ_succ] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem fin_multiaffine_strided_bias {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (N s : Fin (n+1) → ℕ) (hs : ∀ i, 0 < s i)
    (u : Fin (n+1) → ℝ) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i),
      character ((MvPolynomial.eval (fun i => u i+(s i : ℝ)*((x i).val : ℝ)) P : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ i, (s i : ℝ) ∧
      ∃ m : ℤ, |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val-
        (m : ℝ)/D| ≤ multiaffineBiasBudget n ζ / ∏ i, ((s i : ℝ)*(N i : ℝ)) := by
  let A := diagonalMultiaffineScaling P (fun i => (s i : ℝ))
  have hsr : ∀ i, (0 : ℝ) < s i := fun i => by exact_mod_cast hs i
  have heval (x : ∀ i, Fin (N i)) :
      MvPolynomial.eval (fun i => u i/(s i : ℝ)+((x i).val : ℝ)) A =
      MvPolynomial.eval (fun i => u i+(s i : ℝ)*((x i).val : ℝ)) P := by
    rw [diagonalMultiaffineScaling_eval P hP]
    apply congrArg (fun z : Fin (n+1) → ℝ => MvPolynomial.eval z P)
    funext i
    rw [mul_add, mul_div_cancel₀ _ (hsr i).ne']
  obtain ⟨q,hq,hqQ,m,hm⟩ := fin_multiaffine_polynomial_bias A
    (diagonalMultiaffineScaling_degree P _) N (fun i => u i/(s i : ℝ)) hζ hN
    (by simpa only [heval] using hbias)
  let S := ∏ i, s i
  have hSp : 0 < S := Finset.prod_pos (fun i _ => hs i)
  have hSr : (0 : ℝ) < S := by exact_mod_cast hSp
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have happrox : |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val*
      (S : ℝ)-(m : ℝ)/q| ≤ multiaffineBiasBudget n ζ / ∏ i, (N i : ℝ) := by
    simpa only [A, diagonalMultiaffineScaling_top, S, Nat.cast_prod] using hm
  refine ⟨q*S,Nat.mul_pos hq hSp,?_,m,?_⟩
  · simpa only [Nat.cast_mul, S, Nat.cast_prod] using mul_le_mul_of_nonneg_right hqQ hSr.le
  · have he : P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val-
        (m : ℝ)/(q*S : ℕ) =
        (P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val*
          (S : ℝ)-(m : ℝ)/q)/S := by
      push_cast
      field_simp
    rw [he, abs_div, abs_of_pos hSr]
    apply (div_le_div_of_nonneg_right happrox hSr.le).trans_eq
    rw [div_div, Finset.prod_mul_distrib]
    simp only [S, Nat.cast_prod]
    congr 1
    ring

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem multilinear_slice_bias_approximation {M : Type*} [AddCommGroup M] [Module ℝ M]
    {n : ℕ} (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => M) ℝ)
    (b w : Fin (n + 1) → M) (N s : Fin (n + 1) → ℕ)
    (hs : ∀ i, 0 < s i) (u : Fin (n + 1) → ℝ) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i),
      character ((F (fun i => b i + (u i + (s i : ℝ) * ((x i).val : ℝ)) • w i) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ i, (s i : ℝ) ∧
      ∃ m : ℤ, |F w - (m : ℝ) / D| ≤
        multiaffineBiasBudget n ζ / ∏ i, ((s i : ℝ) * (N i : ℝ)) := by
  have hb : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i),
      character ((MvPolynomial.eval (fun i => u i + (s i : ℝ) * ((x i).val : ℝ))
        (multilinearSlicePolynomial F b w) : ℝ) : CircleFourier.Circle)‖ := by
    simpa only [multilinearSlicePolynomial_eval] using hbias
  have h := fin_multiaffine_strided_bias (multilinearSlicePolynomial F b w)
    (multilinearSlicePolynomial_degree F b w) N s hs u hζ hN hb
  simpa only [multilinearSlicePolynomial_top] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothSplitSampling
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedSmoothProductSamples_sum {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) :
    (∑' z : I → ℤ, smoothProductProfile I (fun i => ((z i : ℝ) - a i) / S i)) =
      ∏ i, shiftedSmoothSampleSum (a i) (S i) := by
  classical
  have he := rectangularWeightSum_eq_tsum (smoothProductProfile I) a S hS
    (smoothProductProfile_zero_outside I)
  change rectangularWeightSum (smoothProductProfile I) a S 1 =
    ∑' z : I → ℤ, smoothProductProfile I (fun i => ((z i : ℝ) - a i) / S i) at he
  rw [← he]
  simp only [rectangularWeightSum, rectangularWeightIndices, rectangularWeight,
    rectangularLatticePoint, smoothProductProfile]
  rw [← Finset.prod_univ_sum (fun i => sampledWeightIndices (a i) (S i) 1)
    (fun i k => smoothProbabilityProfile (((k : ℝ) - a i) / S i))]
  apply Finset.prod_congr rfl
  intro i _
  have hi := sampledWeightSum_eq_tsum smoothProbabilityProfile (a := a i) (hS i)
    smoothProbabilityProfile_zero_outside
  exact hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedSmoothProductLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem shiftedSmoothProductMass_eq_prod {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) :
    shiftedSmoothProductMass a S = ∏ i, shiftedSmoothSampleSum (a i) (S i) :=
  shiftedSmoothProductSamples_sum a S hS

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ υ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem coefficients_realChartSubstitute (f : σ → MvPolynomial τ ℝ)
    (p : VectorPolynomial σ ℚ V) (α : τ →₀ ℕ) :
    coefficients (realChartSubstitute f p) α =
      ∑ β ∈ (coefficients p).support,
        (MvPolynomial.aeval f (MvPolynomial.monomial β (1 : ℝ))).coeff α •
          coefficients p β := by
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, coefficients_realCoefficientEquiv_symm,
    coefficients_substitute, coefficients_realCoefficientEquiv]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealGradedSymbolPolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realGradedSymbolPolynomial_coordinate (x : F.RealPolynomialSymbol w)
    (z : SymbolBasisIndex w ω) :
    ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) z.val.1) z.val.2 =
      ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [F.realGradedSymbolPolynomial_coefficient_tmul, Basis.baseChange_repr_tmul,
      F.gradedSymbolPolynomial_coefficient, Basis.baseChange_repr_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem realGradedSymbolPolynomial_coordinate_of_ne (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) (i : ι) (h : Finsupp.weight w α ≠ ω i) :
    ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) i = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [F.realGradedSymbolPolynomial_coefficient_tmul, Basis.baseChange_repr_tmul,
      F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w x α i h, zero_smul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]

theorem realGradedSymbolPolynomial_injective :
    Function.Injective (F.realGradedSymbolPolynomial b ω hlayers w) := by
  intro x y h
  apply ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.injective
  ext z
  rw [← F.realGradedSymbolPolynomial_coordinate, ← F.realGradedSymbolPolynomial_coordinate, h]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

theorem residueSmoothPMF_at {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (x : K × I → ℤ) :
    (residueSmoothPMF residue modulus hmodulus V hV hZ
        (residueLatticeArray residue modulus x)).toReal =
      smoothProductProfile (K × I) (fun z => (residueLatticeArray residue modulus x z : ℝ) / V z) /
        ∑' y, smoothProductProfile (K × I)
          (fun z => (residueLatticeArray residue modulus y z : ℝ) / V z) := by
  rw [residueSmoothPMF, pmf_map_injective_at _ _ (residueLatticeArray_injective residue modulus hmodulus)]
  exact residueSmoothIndexPMF_toReal residue modulus hmodulus V hV hZ x

theorem residueSmoothPMF_zero_off {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (y : K × I → ℤ)
    (hy : ¬∀ z, (modulus z.2 : ℤ) ∣ y z - residue z) :
    residueSmoothPMF residue modulus hmodulus V hV hZ y = 0 := by
  exact pmf_map_zero_off_range _ _ y (by rwa [residueLatticeArray_range])

theorem residueSmoothPMF_expectation {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (φ : (K × I → ℤ) → ℂ) :
    (∑' y, ((residueSmoothPMF residue modulus hmodulus V hV hZ y).toReal : ℂ) * φ y) =
      ∑' x, ((residueSmoothIndexPMF residue modulus hmodulus V hV hZ x).toReal : ℂ) *
        φ (residueLatticeArray residue modulus x) :=
  pmf_map_injective_expectation _ _ (residueLatticeArray_injective residue modulus hmodulus) φ

end Erdos3

end

section

namespace Erdos3

theorem residueSmoothPMF_conditional_weight {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (y : K × I → ℤ) :
    (residueSmoothPMF residue modulus hmodulus V hV hZ y).toReal =
      residueSmoothWeight residue modulus V y / ∑' z, residueSmoothWeight residue modulus V z := by
  classical
  by_cases hc : ∀ z, (modulus z.2 : ℤ) ∣ y z - residue z
  · obtain ⟨x, rfl⟩ := (residueLatticeArray_range residue modulus y).mpr hc
    rw [residueSmoothWeight_at, ← residueSmoothWeight_mass residue modulus hmodulus V hV]
    have he := residueSmoothPMF_at residue modulus hmodulus V hV hZ x
    simpa only [shiftedSmoothProductMass, rectangularWeight,
      residueProfile_point residue modulus hmodulus V hV] using he
  · simp only [residueSmoothPMF_zero_off residue modulus hmodulus V hV hZ y hc,
      ENNReal.toReal_zero, residueSmoothWeight, hc, ite_false, zero_div]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedResidueSmoothPMF_bound_of_cells {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (G : Finset (ColumnResiduePattern K I modulus)) (hG : G.Nonempty)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hc : ∀ r : G, 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus) (residueProfileWidth modulus V))
    (φ : (K × I → ℤ) → ℂ) {ε : ℝ}
    (hφ : ∀ r : G,
      ‖∑' x, ((residueSmoothPMF (columnResidueRepresentative modulus r.val) modulus hmodulus V hV (hc r) x).toReal : ℂ) * φ x‖ ≤ ε) :
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x,
      ‖∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * φ x‖ ≤ ε := by
  have hcell (r : G) : 0 < ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
    rw [← residueSmoothWeight_mass _ modulus hmodulus V hV]
    exact hc r
  have hZ := selectedResidueSmoothWeight_mass_pos modulus G hG V hV hcell
  have ht := selectedResidueSmoothWeight_mass modulus G V hV
  have htotal : 0 < ∑ r : G, ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
    rwa [← ht]
  refine ⟨hZ, ?_⟩
  simp_rw [selectedResidueSmoothPMF_toReal, ht, selectedResidueSmoothWeight_eq_sum]
  apply finite_supported_normalized_mixture_bound _ (rectangularWeightIndices 0 V 1)
    (fun r => residueSmoothWeight_zero_off _ modulus V hV) hcell htotal φ
  intro r
  simpa only [residueSmoothPMF_conditional_weight] using hφ r

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueFiniteLaw_complexMean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (f : (K × I → ℤ) → ℂ) :
    (selectedResidueFiniteLaw modulus G V hV hZ).complexMean (fun x => f x.val) =
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * f x := by
  simp only [selectedResidueFiniteLaw, finiteSupportProbability_complexMean, selectedResidueSmoothPMF_toReal]

theorem selectedResidueFiniteLaw_mean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (f : (K × I → ℤ) → ℝ) :
    (selectedResidueFiniteLaw modulus G V hV hZ).mean (fun x => f x.val) =
      ∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * f x := by
  apply Complex.ofReal_injective
  have h := selectedResidueFiniteLaw_complexMean modulus G V hV hZ (fun x => (f x : ℂ))
  rw [FiniteProbabilityWeights.complexMean_ofReal] at h
  simpa only [Complex.ofReal_tsum, Complex.ofReal_mul] using h

theorem selectedResidueFiniteLaw_densityMass {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (D : (K × I → ℤ) → ℝ) :
    (selectedResidueFiniteLaw modulus G V hV hZ).mean (fun x => D x.val) =
      selectedResidueDensityMass modulus G V D := by
  rw [selectedResidueFiniteLaw_mean]
  simp only [selectedResidueSmoothPMF_toReal, selectedResidueDensityMass, finiteDensityMass]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

def columnResidueReduction {K I : Type*} (modulus refined : I → ℕ)
    (hdiv : ∀ i, modulus i ∣ refined i)
    (r : ColumnResiduePattern K I refined) : ColumnResiduePattern K I modulus :=
  fun z => ZMod.castHom (hdiv z.2) (ZMod (modulus z.2)) (r z)

@[simp] theorem columnResidueReduction_pattern {K I : Type*} (modulus refined : I → ℕ)
    (hdiv : ∀ i, modulus i ∣ refined i) (x : K × I → ℤ) :
    columnResidueReduction modulus refined hdiv (columnResiduePattern refined x) =
      columnResiduePattern modulus x := by
  funext z
  exact map_intCast (ZMod.castHom (hdiv z.2) (ZMod (modulus z.2))) (x z)

noncomputable def selectedResidueRefinement {K I : Type*} [Fintype K] [Fintype I]
    (modulus refined : I → ℕ) [∀ i, NeZero (refined i)]
    (hdiv : ∀ i, modulus i ∣ refined i) (G : Finset (ColumnResiduePattern K I modulus)) :
    Finset (ColumnResiduePattern K I refined) :=
  Finset.univ.filter (fun r => columnResidueReduction modulus refined hdiv r ∈ G)

@[simp] theorem mem_selectedResidueRefinement {K I : Type*} [Fintype K] [Fintype I]
    (modulus refined : I → ℕ) [∀ i, NeZero (refined i)]
    (hdiv : ∀ i, modulus i ∣ refined i) (G : Finset (ColumnResiduePattern K I modulus))
    (r : ColumnResiduePattern K I refined) :
    r ∈ selectedResidueRefinement modulus refined hdiv G ↔
      columnResidueReduction modulus refined hdiv r ∈ G := by
  simp only [selectedResidueRefinement, Finset.mem_filter, Finset.mem_univ, true_and]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueSmoothWeight_plateau {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (cells : Finset (ColumnResiduePattern K X q)) (V : K × X → ℝ)
    (z : K × X → ℤ) (hz : columnResiduePattern q z ∈ cells)
    (hsmall : ∀ i, |(z i : ℝ) / V i| ≤ 1 / 2) :
    selectedResidueSmoothWeight q cells V z =
      (smoothProbabilityProfile 0) ^ Fintype.card (K × X) := by
  classical
  simp only [selectedResidueSmoothWeight, hz, ite_true]
  unfold smoothProductProfile
  calc
    _ = ∏ _i : K × X, smoothProbabilityProfile 0 :=
      Finset.prod_congr rfl (fun i _ => smoothProbabilityProfile_plateau _ (hsmall i))
    _ = _ := by simp

theorem selectedResidueDensityMass_window_bound {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (cells : Finset (ColumnResiduePattern K X q))
    (V : K × X → ℝ) (hV : ∀ i, 0 < V i)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells V z)
    (D : (K × X → ℤ) → ℝ) (hD : ∀ z, 0 ≤ D z)
    (window : Finset (K × X → ℤ))
    (hresidue : ∀ z ∈ window, columnResiduePattern q z ∈ cells)
    (hsmall : ∀ z ∈ window, ∀ i, |(z i : ℝ) / V i| ≤ 1 / 2) :
    (∑ z ∈ window, D z) ≤
      ((∑' z, selectedResidueSmoothWeight q cells V z) /
        (smoothProbabilityProfile 0) ^ Fintype.card (K × X)) *
          selectedResidueDensityMass q cells V D := by
  apply finiteDensityMass_sum_le_of_weight_lower (selectedResidueSmoothWeight q cells V) D
    (rectangularWeightIndices 0 V 1) window (selectedResidueSmoothWeight_nonneg q cells V)
    (selectedResidueSmoothWeight_zero_off q cells V hV) hD hZ
    (pow_pos smoothProbabilityProfile_pos_zero _)
  intro z hz
  exact (selectedResidueSmoothWeight_plateau q cells V z (hresidue z hz) (hsmall z hz)).ge

theorem selectedResidueSmoothWeight_singleton_mass_upper {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (r : ColumnResiduePattern K X q)
    (V : K × X → ℝ) (hV : ∀ i, 0 < V i)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V i) :
    (∑' z, selectedResidueSmoothWeight q {r} V z) ≤
      (3 / 2 : ℝ) ^ Fintype.card (K × X) * ∏ i, residueProfileWidth q V i := by
  classical
  have he : selectedResidueSmoothWeight q {r} V =
      residueSmoothWeight (columnResidueRepresentative q r) q V := by
    funext z
    simp only [selectedResidueSmoothWeight, residueSmoothWeight_eq_pattern, Finset.mem_singleton]
  rw [he, ← residueSmoothWeight_mass _ q hq V hV,
    shiftedSmoothProductMass_eq_prod _ _ (residueProfileWidth_pos q V hq hV)]
  calc
    _ ≤ ∏ i : K × X, 3 * residueProfileWidth q V i / 2 := by
      apply Finset.prod_le_prod
      · intro i _
        exact tsum_nonneg (fun _ => (smoothProbabilityProfile_range _).1)
      · intro i _
        exact (shiftedSmoothSampleSum_bounds _ (hscale i)).2
    _ = _ := by
      simp_rw [show ∀ i : K × X, 3 * residueProfileWidth q V i / 2 =
        (3 / 2 : ℝ) * residueProfileWidth q V i by intro i; ring]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IntervalDivisorProbability
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

noncomputable def reweightPositive {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) : FiniteProbabilityWeights X :=
  ofPositiveWeights (fun x => p.weight x * w x) (fun x => mul_nonneg (p.nonneg x) (hw x)) hm

theorem reweightPositive_weight {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) (x : X) :
    (p.reweightPositive w hw hm).weight x = p.weight x * w x / p.mean w := rfl

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory

variable {X C : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

noncomputable def normalizedDensityTest (D : X → ℝ) (f : X → ℂ) : ℂ :=
  p.complexMean (fun x => (D x : ℂ)*f x)/(p.mean D : ℂ)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem mean_prod (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (f : X × Y → ℝ) :
    (p.prod q).mean f = p.mean (fun x => q.mean (fun y => f (x,y))) := by
  simp only [mean, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

noncomputable def uniformFinset {A : Type*} (S : Finset A) (hS : S.Nonempty) :
    FiniteProbabilityWeights S := by
  letI : Nonempty S := hS.to_subtype
  exact uniform S

theorem uniformFinset_mean {A : Type*} (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) :
    (uniformFinset S hS).mean (fun x => f x.val) = 𝔼 x ∈ S, f x := by
  let : Nonempty S := hS.to_subtype
  rw [uniformFinset, uniform_mean]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Finset.sum_coe_sort, Fintype.card_coe]

end Erdos3.FiniteProbabilityWeights

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

theorem multilinear_box_coordinate_approximation {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => I → ℝ) ℝ)
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) (b : Fin (n + 1) → I → ℝ)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      character ((F (stridedMatrixPoint b s x) : ℝ) : CircleFourier.Circle)‖)
    (j : Fin (n + 1) → I) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ) ∧
      ∃ m : ℤ, |F (fun i => Pi.single (j i) (1 : ℝ)) - (m : ℝ) / D| ≤
        multiaffineBiasBudget n ζ / ∏ i, ((s (j i) : ℝ) * (N (j i) : ℝ)) := by
  have hNp (k : I) : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos n hζ).trans_le (hN k)
  obtain ⟨c, hc⟩ := multilinear_box_biased_slice F N s hNp b j hbias
  apply multilinear_slice_bias_approximation F c
    (fun i => Pi.single (j i) (1 : ℝ)) (fun i => N (j i)) (fun i => s (j i))
    (fun i => hs (j i)) (fun _ => 0) hζ (fun i => hN (j i))
  simpa only [zero_add] using hc

theorem paired_multilinear_box_coordinate_approximation {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => I → ℝ) ℝ)
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((F (fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
          (s k : ℝ) * ((y i k).val : ℝ)) : ℝ) : CircleFourier.Circle)‖)
    (j : Fin (n + 1) → I) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ) ∧
      ∃ m : ℤ, |F (fun i => Pi.single (j i) (1 : ℝ)) - (m : ℝ) / D| ≤
        multiaffineBiasBudget n ζ / ∏ i, ((s (j i) : ℝ) * (N (j i) : ℝ)) := by
  have hNp (k : I) : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos n hζ).trans_le (hN k)
  let : ∀ k, Nonempty (Fin (N k)) := fun k => ⟨⟨0, hNp k⟩⟩
  rw [Finset.expect_comm] at hbias
  obtain ⟨y, hy⟩ := exists_biased_finite_slice
    (fun y x : Fin (n + 1) → ∀ k, Fin (N k) =>
      character ((F (fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
        (s k : ℝ) * ((y i k).val : ℝ)) : ℝ) : CircleFourier.Circle)) hbias
  let b : Fin (n + 1) → I → ℝ := fun i k => -((s k : ℝ) * ((y i k).val : ℝ))
  have he (x : Fin (n + 1) → ∀ k, Fin (N k)) :
      stridedMatrixPoint b s x = fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
        (s k : ℝ) * ((y i k).val : ℝ) := by
    funext i k
    dsimp [stridedMatrixPoint, b]
    ring
  apply multilinear_box_coordinate_approximation F N s hs b hζ hN _ j
  simpa only [he] using hy

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PairedDiagonalApproximation
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem paired_multilinear_common_approximation {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => I → ℝ) ℝ)
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((F (fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
          (s k : ℝ) * ((y i k).val : ℝ)) : ℝ) : CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ ∏ j : Fin (n + 1) → I, (multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ)) ∧
      ∃ a : (Fin (n + 1) → I) → ℤ, ∀ j,
        |F (fun i => Pi.single (j i) (1 : ℝ)) - (a j : ℝ) / D| ≤
          multiaffineBiasBudget n ζ / ∏ i, ((s (j i) : ℝ) * (N (j i) : ℝ)) := by
  exact exists_common_rational_approximations_varying (I := Fin (n + 1) → I)
    (fun j : Fin (n + 1) → I => F (fun i => Pi.single (j i) (1 : ℝ)))
    (fun j : Fin (n + 1) → I => multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ))
    (fun j : Fin (n + 1) → I =>
      multiaffineBiasBudget n ζ / ∏ i, ((s (j i) : ℝ) * (N (j i) : ℝ)))
    (fun j : Fin (n + 1) → I =>
      paired_multilinear_box_coordinate_approximation F N s hs hζ hN hbias j)

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem paired_multilinear_polynomial_approximation {I : Type*} [Fintype I] [DecidableEq I]
    {n : ℕ} (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => I → ℝ) ℝ)
    (P : MvPolynomial I ℝ) (hP : ∀ w, MvPolynomial.eval w P = F (fun _ => w))
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((s k : ℝ) * (N k : ℝ)))
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((F (fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
          (s k : ℝ) * ((y i k).val : ℝ)) : ℝ) : CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ ∏ j : Fin (n + 1) → I, (multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ)) ∧
      ∃ E : MvPolynomial I ℝ, ∃ Q : MvPolynomial I ℤ,
        P = E + MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q ∧
        ∀ α, |E.coeff α| ≤ (Fintype.card I : ℝ) ^ (n + 1) *
          (A ^ (n + 1) * multiaffineBiasBudget n ζ) / monomialScale H α := by
  obtain ⟨D, hD, hDb, m, hm⟩ := paired_multilinear_common_approximation F N s hs hζ hN hbias
  have hT (k : I) : 0 < (s k : ℝ) * (N k : ℝ) := by
    exact mul_pos (Nat.cast_pos.mpr (hs k)) ((multiaffineBiasBudget_pos n hζ).trans_le (hN k))
  have hmH := tensor_entry_bound_rescale
    (fun j : Fin (n + 1) → I => F (fun i => Pi.single (j i) (1 : ℝ)) - (m j : ℝ) / D)
    (fun k => (s k : ℝ) * (N k : ℝ)) H hT hH hscale (multiaffineBiasBudget_pos n hζ).le hm
  obtain ⟨E, Q, hE, hcoeff⟩ := tensorDiagonalPolynomial_approximation
    (fun j : Fin (n + 1) → I => F (fun i => Pi.single (j i) (1 : ℝ))) m D
    H hH (mul_nonneg (pow_nonneg hA _) (multiaffineBiasBudget_pos n hζ).le) hmH
  have he : P = tensorDiagonalPolynomial
      (fun j : Fin (n + 1) → I => F (fun i => Pi.single (j i) (1 : ℝ))) := by
    apply MvPolynomial.funext
    intro w
    rw [hP, tensorDiagonalPolynomial_multilinear_eval]
  exact ⟨D, hD, hDb, E, Q, he.trans hE, hcoeff⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealProjectedCoefficientLift
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r) (A : ℕ → Submodule ℚ M)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ A d → ∀ k, φ x k ∈ F.layer d 1)

def layerHorizontalMap (d : ℕ) : A d →ₗ[ℚ] (Fin 4 → F.HigherHorizontal d) :=
  (F.fourHorizontalMap d).comp
    (((φ : M →ₗ[ℚ] (Fin 4 → L)).comp (A d).subtype).codRestrict
      (F.fourHorizontalLayer d)
      (fun x => (F.mem_fourHorizontalLayer d (φ x.val)).mpr (hφ d x.val x.property)))

def layerHorizontalImage (d : ℕ) : Submodule ℚ (Fin 4 → F.HigherHorizontal d) :=
  LinearMap.range (F.layerHorizontalMap A φ hφ d)

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationTopDegree
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {X R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem homogeneousPart_translate (a : X → R) {n : ℕ}
    (p : VectorPolynomial X R V) (hp : DegreeLE (1 : X → ℕ) n p) :
    homogeneousPart n (translate a p) = homogeneousPart n p := by
  classical
  apply coefficients.injective
  ext d
  simp only [coefficients_homogeneousPart]
  split
  · rename_i hd
    have hdw : n ≤ Finsupp.weight (1 : X → ℕ) d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd.ge
    have h := coefficients_translate_sub_eq_zero_of_degreeLE (1 : X → ℕ)
      (fun _ => by norm_num) a p hp d hdw
    simpa only [map_sub, Finsupp.sub_apply, sub_eq_zero] using h
  · rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def HasLayerSamplingRank {I J : Type*} [Fintype J]
    (h : ℕ) (T : I → ℝ) (R : ℝ) (W : Submodule ℝ (J → ℝ))
    (p : VectorPolynomial I ℝ (J → ℝ)) : Prop :=
  ∀ a : J → ℤ, (∀ j, |(a j : ℝ)| ≤ R) →
    (∃ w : W, (∑ j, (a j : ℝ) * w.val j) ≠ 0) →
    ¬ PolynomialRationalApproximation T R
      (MvPolynomial.homogeneousComponent h (VectorPolynomial.integerRowPolynomial a p))

theorem HasLayerSamplingRank.not_approximation {I J : Type*} [Fintype J]
    {h : ℕ} {T : I → ℝ} {R : ℝ} {W : Submodule ℝ (J → ℝ)}
    {p : VectorPolynomial I ℝ (J → ℝ)} (hrank : HasLayerSamplingRank h T R W p)
    (hp : VectorPolynomial.Homogeneous h p) (a : J → ℤ)
    (ha : ∀ j, |(a j : ℝ)| ≤ R) (hw : ∃ w : W, (∑ j, (a j : ℝ) * w.val j) ≠ 0) :
    ¬ PolynomialRationalApproximation T R (VectorPolynomial.integerRowPolynomial a p) := by
  have hn := hrank a ha hw
  rwa [MvPolynomial.homogeneousComponent_eq_self
    (VectorPolynomial.integerRowPolynomial_homogeneous a p hp)] at hn

end Erdos3

end

section

namespace Erdos3

theorem VectorPolynomial.integerRowPolynomial_homogeneousPart {I J : Type*} [Fintype J]
    (a : J → ℤ) (h : ℕ) (p : VectorPolynomial I ℝ (J → ℝ)) :
    VectorPolynomial.integerRowPolynomial a (VectorPolynomial.homogeneousPart h p) =
      MvPolynomial.homogeneousComponent h (VectorPolynomial.integerRowPolynomial a p) :=
  VectorPolynomial.coordinate_homogeneousPart _ h p

theorem hasLayerSamplingRank_homogeneousPart_iff {I J : Type*} [Fintype J]
    (h : ℕ) (T : I → ℝ) (R : ℝ) (W : Submodule ℝ (J → ℝ))
    (p : VectorPolynomial I ℝ (J → ℝ)) :
    HasLayerSamplingRank h T R W (VectorPolynomial.homogeneousPart h p) ↔
      HasLayerSamplingRank h T R W p := by
  unfold HasLayerSamplingRank
  simp only [VectorPolynomial.integerRowPolynomial_homogeneousPart,
    MvPolynomial.homogeneousComponent_eq_self (MvPolynomial.homogeneousComponent_isHomogeneous h _)]

end Erdos3

end

section

namespace Erdos3

theorem HasLayerSamplingRank.inv_nat_smul {I J : Type*} [Fintype J]
    {h : ℕ} {T : I → ℝ} {R : ℝ} (hR : 0 ≤ R)
    {W : Submodule ℝ (J → ℝ)} {p : VectorPolynomial I ℝ (J → ℝ)}
    (q : ℕ) (hq : 0 < q) (hrank : HasLayerSamplingRank h T ((q : ℝ) * R) W p) :
    HasLayerSamplingRank h T R W ((q : ℝ)⁻¹ • p) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  intro a ha hw happ
  have ha' : ∀ j, |(a j : ℝ)| ≤ (q : ℝ) * R := fun j => (ha j).trans (by nlinarith)
  apply hrank a ha' hw
  have hh := happ.nat_smul q hq
  simpa only [VectorPolynomial.integerRowPolynomial_smul, map_smul, smul_smul,
    mul_inv_cancel₀ hq0, one_smul] using hh

theorem HasLayerSamplingRank.div_nat {I J : Type*} [Fintype J]
    {h : ℕ} {T : I → ℝ} {R : ℝ} (hR : 0 ≤ R)
    {W : Submodule ℝ (J → ℝ)} {p : VectorPolynomial I ℝ (J → ℝ)}
    (hrank : HasLayerSamplingRank h T R W p) (q : ℕ) (hq : 0 < q) :
    HasLayerSamplingRank h T (R / q) W ((q : ℝ)⁻¹ • p) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hr : HasLayerSamplingRank h T ((q : ℝ) * (R / q)) W p := by
    simpa only [mul_div_cancel₀ R hq0] using hrank
  exact HasLayerSamplingRank.inv_nat_smul (div_nonneg hR (Nat.cast_nonneg q)) q hq hr

end Erdos3

end

section

namespace Erdos3

theorem hasLayerSamplingRank_translate_iff {X J : Type*} [Fintype J]
    (a : X → ℝ) (n : ℕ) (H : X → ℝ) (R : ℝ) (U : Submodule ℝ (J → ℝ))
    (p : VectorPolynomial X ℝ (J → ℝ)) (hp : VectorPolynomial.DegreeLE (1 : X → ℕ) n p) :
    HasLayerSamplingRank n H R U (VectorPolynomial.translate a p) ↔
      HasLayerSamplingRank n H R U p := by
  rw [← hasLayerSamplingRank_homogeneousPart_iff n H R U (VectorPolynomial.translate a p),
    VectorPolynomial.homogeneousPart_translate a p hp,
    hasLayerSamplingRank_homogeneousPart_iff]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem coefficientModePolynomial_degreeLE {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    {h : ℕ} (hp : DegreeLE (1 : I → ℕ) h p) :
    (coefficientModePolynomial L p).totalDegree ≤ h := by
  unfold coefficientModePolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply (mapPolynomialCoefficients_degree _ _).trans
  apply parameterPolynomialPullback_degree
  have hb : d.sum (fun _ n => n) ≤ h := by
    simpa only [Finsupp.weight_apply, Pi.one_def, smul_eq_mul, mul_one] using
      (degreeLE_iff (1 : I → ℕ) h p).mp hp d hd
  exact (MvPolynomial.totalDegree_monomial_le d 1).trans hb

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientModeLowerTerms
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

theorem homogeneous_substitute_scaled {I J R W : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] {h : ℕ}
    (p : VectorPolynomial I R W) (hp : Homogeneous h p)
    (w : I → R) (Q : MvPolynomial J R) :
    substitute (fun i => MvPolynomial.C (w i) * Q) p = (Q ^ h) ⊗ₜ[R] eval w p := by
  let f := substitute (V := W) (fun i => MvPolynomial.C (w i) * Q)
  let g : VectorPolynomial I R W →ₗ[R] VectorPolynomial J R W :=
    (TensorProduct.mk R (MvPolynomial J R) W (Q ^ h)).comp (eval w)
  change f p = g p
  apply eq_of_homogeneous_tmul f g h _ hp
  intro P hP v
  change MvPolynomial.aeval (fun i => MvPolynomial.C (w i) * Q) P ⊗ₜ[R] v =
    (Q ^ h) ⊗ₜ[R] (MvPolynomial.eval w P • v)
  rw [Erdos3.homogeneous_aeval_scaled P hP w Q]
  simp only [← MvPolynomial.smul_eq_C_mul,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

theorem homogeneous_mode_diagonal_difference {I T R W : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] {h : ℕ}
    (p : VectorPolynomial I R W) (hp : Homogeneous h p) (w : I → R)
    (A : Fin h → MvPolynomial T R) (L : VectorPolynomial T R W →ₗ[R] R) :
    additiveBoxDifference h
      (fun (x : Fin h → R) (_ : Unit) =>
        L (substitute (fun j => MvPolynomial.C (w j) * ∑ i, x i • A i) p))
      (fun _ => 1) (fun _ => 0) () =
        (h.factorial : R) * L ((∏ i, A i) ⊗ₜ[R] eval w p) := by
  let F : MvPolynomial T R →ₗ[R] R := (TensorProduct.curry L).flip (eval w p)
  have he :
      (fun (x : Fin h → R) (_ : Unit) =>
        L (substitute (fun j => MvPolynomial.C (w j) * ∑ i, x i • A i) p)) =
      (fun x (_ : Unit) => F ((∑ i, x i • A i) ^ h)) := by
    funext x _
    rw [homogeneous_substitute_scaled p hp w]
    rfl
  rw [he]
  have hm := additiveBoxDifference_hom F.toAddMonoidHom h
    (fun (x : Fin h → R) (_ : Unit) => (∑ i, x i • A i) ^ h)
    (fun _ => 1) (fun _ => 0) ()
  refine hm.trans ?_
  rw [linear_power_full_difference_algebra]
  change F ((h.factorial : MvPolynomial T R) * ∏ i, A i) = _
  have hc : (h.factorial : MvPolynomial T R) * ∏ i, A i =
      (h.factorial : R) • ∏ i, A i := by
    rw [MvPolynomial.smul_eq_C_mul, map_natCast]
  rw [hc, map_smul]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

theorem coefficientModePolynomial_top_diagonal {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {h : ℕ}
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (p : VectorPolynomial I ℝ W) (hp : Homogeneous h p)
    (a : Fin h → K → ℝ) (w : I → ℝ) :
    polynomialTopSymbol h (coefficientModePolynomial L p) (fun i z => a i z.1 * w z.2) =
      (h.factorial : ℝ) * L ((∏ i, rowPolynomial (a i)) ⊗ₜ[ℝ] eval w p) := by
  have hphase (x : Fin h → ℝ) :
      MvPolynomial.eval (fun z => 0 + ∑ i, (a i z.1 * w z.2) * x i)
        (coefficientModePolynomial L p) =
      L (substitute (fun j => MvPolynomial.C (w j) * ∑ i, x i • rowPolynomial (a i)) p) := by
    have hv : (fun z : K × I => 0 + ∑ i, (a i z.1 * w z.2) * x i) =
        (fun z => ∑ i, a i z.1 * (x i * w z.2)) := by
      funext z
      simp only [zero_add]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hv, coefficientModePolynomial_eval L p (fun k j => ∑ i, a i k * (x i * w j))]
    apply congrArg (fun f : I → MvPolynomial K ℝ => L (substitute f p))
    funext j
    exact rowPolynomial_diagonal a x (w j)
  have hd := affineShift_difference_eq_topSymbol (fun _ : K × I => 0)
    (fun i z => a i z.1 * w z.2) (coefficientModePolynomial L p)
    (coefficientModePolynomial_degree L p hp) (fun _ => 1) (fun _ => 0)
  simp only [hphase, sub_zero, Finset.prod_const_one, mul_one] at hd
  exact hd.symm.trans (homogeneous_mode_diagonal_difference p hp w (fun i => rowPolynomial (a i)) L)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators TensorProduct Classical

theorem coefficient_mode_with_lower_site_cauchySchwarz {h : ℕ} {S K I X W : Type*}
    [Fintype S] [Fintype K] [Fintype X] [Nonempty X]
    [AddCommGroup W] [Module ℝ W] (hh : 0 < h)
    (site : S → K → ℤ) (rows : Fin h → K → ℤ)
    (hzero : ∀ s, ∃ i, (∑ k, rows i k * site s k) = 0)
    (base : K → I → ℝ) (shift : X → I → ℝ)
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (p : VectorPolynomial I ℝ W) (hp : Homogeneous h p)
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < h)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character ((L (substitute (fun j => rowPolynomial
        (fun k => rowShiftedTuple base rows shift x k j)) p) +
          MvPolynomial.eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) Q : ℝ) :
            CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u : Fin h → X, 𝔼 v : Fin h → X,
        character ((polynomialTopSymbol h (coefficientModePolynomial L p)
          (fun i z => (rows i z.1 : ℝ) * (shift (u i) z.2 - shift (v i) z.2)) : ℝ) : CircleFourier.Circle)‖ := by
  have hdegree : (coefficientModePolynomial L p + Q).totalDegree ≤ h :=
    (MvPolynomial.totalDegree_add _ _).trans (max_le (coefficientModePolynomial_degree L p hp) hQ.le)
  simpa only [map_add, coefficientModePolynomial_eval, polynomialTopSymbol_add_lower _ Q hQ] using
    row_polynomial_site_cauchySchwarz hh site rows hzero base shift
      (coefficientModePolynomial L p + Q) hdegree test htest

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SubspaceLayeredModeSmoothRemoval
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators NNReal Classical

noncomputable def coefficientModeTestedPhase {I K W S : Type*} [Fintype K] [Fintype S]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    (Q : MvPolynomial (K × I) ℝ) (site : S → K → ℤ)
    (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) : ℂ :=
  character ((L (substitute (fun j => rowPolynomial (fun k => b k j)) p) +
    MvPolynomial.eval (fun z => b z.1 z.2) Q : ℝ) : CircleFourier.Circle) *
      ∏ t, test t (integerSiteValue (site t) b)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def lowerModePolynomial {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (h : ℕ) (p : VectorPolynomial I ℝ W) (Q : MvPolynomial (K × I) ℝ) :
    MvPolynomial (K × I) ℝ := coefficientModePolynomial L (p - homogeneousPart h p) + Q

theorem lowerModePolynomial_degree {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    {n : ℕ} (p : VectorPolynomial I ℝ W) (hp : DegreeLE (1 : I → ℕ) (n + 1) p)
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < n + 1) :
    (lowerModePolynomial L (n + 1) p Q).totalDegree < n + 1 := by
  apply lt_of_le_of_lt (MvPolynomial.totalDegree_add _ _)
  apply max_lt
  · exact (coefficientModePolynomial_degreeLE L _ (sub_homogeneousPart_degreeLE hp)).trans_lt
      (Nat.lt_succ_self n)
  · exact hQ

theorem lowerModePolynomial_eval {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (h : ℕ) (p : VectorPolynomial I ℝ W) (Q : MvPolynomial (K × I) ℝ) (b : K → I → ℝ) :
    L (substitute (fun j => rowPolynomial (fun k => b k j)) (homogeneousPart h p)) +
      MvPolynomial.eval (fun z => b z.1 z.2) (lowerModePolynomial L h p Q) =
    L (substitute (fun j => rowPolynomial (fun k => b k j)) p) +
      MvPolynomial.eval (fun z => b z.1 z.2) Q := by
  rw [lowerModePolynomial, map_add, coefficientModePolynomial_eval, map_sub, map_sub]
  ring

theorem coefficientModeTestedPhase_top {I K W S : Type*} [Fintype K] [Fintype S]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (h : ℕ)
    (p : VectorPolynomial I ℝ W) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) :
    coefficientModeTestedPhase L p Q site test b =
      coefficientModeTestedPhase L (homogeneousPart h p) (lowerModePolynomial L h p Q) site test b := by
  unfold coefficientModeTestedPhase
  rw [lowerModePolynomial_eval]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

noncomputable def lowerLayerPolynomial {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (i : Fin m) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) : MvPolynomial (K × I) ℝ :=
  ∑ j, if j < i then coefficientModePolynomial (L j) (p j) else 0

theorem lowerLayerPolynomial_degree {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (i : Fin m) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) :
    (lowerLayerPolynomial i L p).totalDegree < i.val + 1 := by
  apply lt_of_le_of_lt (b := i.val) _ (Nat.lt_succ_self _)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  by_cases hji : j < i
  · rw [if_pos hji]
    exact (coefficientModePolynomial_degreeLE (L j) (p j) (hp j)).trans
      (Nat.succ_le_of_lt hji)
  · simp [hji]

theorem lowerLayerPolynomial_eval {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (i : Fin m) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (b : K → I → ℝ) :
    MvPolynomial.eval (fun z => b z.1 z.2) (lowerLayerPolynomial i L p) =
      ∑ j, if j < i then L j (substitute (fun u => rowPolynomial (fun k => b k u)) (p j)) else 0 := by
  rw [lowerLayerPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j < i <;> simp [hji, coefficientModePolynomial_eval]

noncomputable def layeredModeTestedPhase {I K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) : ℂ :=
  character (((∑ j, L j (substitute (fun u => rowPolynomial (fun k => b k u)) (p j))) +
    MvPolynomial.eval (fun z => b z.1 z.2) Q : ℝ) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) b)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem layeredModeTestedPhase_norm_le {I K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ)
    (htest : ∀ s x, ‖test s x‖ ≤ 1) (b : K → I → ℝ) :
    ‖layeredModeTestedPhase L p Q site test b‖ ≤ 1 := by
  rw [layeredModeTestedPhase, norm_mul, norm_character, one_mul, norm_prod]
  exact Finset.prod_le_one (fun s _ => norm_nonneg _) (fun s _ => htest s _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem degreeLE_restrictCoefficients {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (U : Submodule ℝ V) (p : VectorPolynomial I ℝ V) (hm : ∀ d, coefficients p d ∈ U)
    {w : I → ℕ} {h : ℕ} (hp : DegreeLE w h p) : DegreeLE w h (restrictCoefficients U p hm) := by
  apply (degreeLE_map_iff w h U.subtype Subtype.val_injective _).mp
  simpa only [map_restrictCoefficients] using hp

theorem coefficientModeTestedPhase_map {I K S V W : Type*} [Fintype K] [Fintype S]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (p : VectorPolynomial I ℝ V) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) :
    coefficientModeTestedPhase (L.comp (map f)) p Q site test b =
      coefficientModeTestedPhase L (map f p) Q site test b := by
  simp only [coefficientModeTestedPhase, LinearMap.comp_apply, map_substitute]

theorem layeredModeTestedPhase_map {I K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {V W : Fin m → Type*}
    [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)]
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (f : ∀ j, V j →ₗ[ℝ] W j) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (V j)) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) :
    layeredModeTestedPhase (fun j => (L j).comp (map (f j))) p Q site test b =
      layeredModeTestedPhase L (fun j => map (f j) (p j)) Q site test b := by
  simp only [layeredModeTestedPhase, LinearMap.comp_apply, map_substitute]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MonomialCoordinateRows
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_monomial_coordinate_rows {K : Type*} [Fintype K]
    (d : K →₀ ℕ) {h : ℕ} (hd : d.degree = h) :
    ∃ rows : Fin h → K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ 1) ∧
      (∏ i, rowPolynomial (rows i)) = MvPolynomial.monomial d 1 := by
  have hlen : d.toMultiset.toList.length = h := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    exact hd
  rcases hlen with rfl
  let indices : Fin d.toMultiset.toList.length → K := fun i => d.toMultiset.toList[i.val]
  refine ⟨fun i => Pi.single (indices i) 1, ?_, ?_⟩
  · intro i k
    by_cases he : indices i = k <;> simp [he]
  · simp only [rowPolynomial_single]
    change (∏ i : Fin d.toMultiset.toList.length,
      (MvPolynomial.X d.toMultiset.toList[i.val] : MvPolynomial K ℤ)) = _
    rw [Fin.prod_univ_fun_getElem, Multiset.prod_map_toList]
    rw [Finset.prod_multiset_map_count]
    simpa only [Finsupp.toFinset_toMultiset, Finsupp.count_toMultiset] using
      (MvPolynomial.prod_X_pow_eq_monomial (R := ℤ) (s := d))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformCommutingCircleDecomposition
namespace OAI

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X ι : Type*} [PseudoMetricSpace X] [Fintype ι]

theorem exists_controlled_commuting_circle_decomposition
    (A : ι → IsometricCircleAction X) (hcomm : ∀ i j, (A i).Commutes (A j))
    (f : X → ℂ) (L B D : ℝ≥0) (hf : LipschitzWith L f) (hb : ∀ x, ‖f x‖ ≤ B)
    (horbit : ∀ i (t : Circle) x, dist ((A i).act t x) x ≤ D * ‖t‖)
    (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hLp : (L : ℝ) ≤ Real.exp p) (hDp : (D : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (ν : J → ι → ℤ) (v : J → X → ℂ),
      (Fintype.card J : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ j i, (|ν j i| : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      (∀ j, LipschitzWith L (v j) ∧ (∀ x, ‖v j x‖ ≤ B)) ∧
      (∀ j i (t : Circle) x, v j ((A i).act t x) = character (ν j i • t) * v j x) ∧
      (∀ (g : X → X) (z : ℂ),
        (∀ i t x, (A i).act t (g x) = g ((A i).act t x)) →
        (∀ x, f (g x) = z * f x) → ∀ j x, v j (g x) = z * v j x) ∧
      ∀ x, ‖(∑ j, v j x) - f x‖ ≤ δ := by
  classical
  let is := (Finset.univ : Finset ι).toList
  have hd' : (is.length : ℝ) ≤ p := by simpa [is] using hd
  obtain ⟨N, _, _, hcard, hprops, herr⟩ := exists_controlled_finite_circle_decomposition A is
    (fun i _ j _ => hcomm i j) f L B D hf hb (fun i _ => horbit i)
    δ p hδ hp hd' hLp hDp hδp
  have hcover : ∀ i : ι, ∃ r : Fin is.length, is.get r = i := by
    intro i
    apply List.mem_iff_get.mp
    simp [is]
  choose index hindex using hcover
  let J := Fin is.length → FejerChoice N
  let ν : J → ι → ℤ := fun k i => -(k (index i) : ℤ)
  let v : J → X → ℂ := fun k => iteratedCircleComponent N A is (fun r => (k r : ℤ)) f
  refine ⟨J, inferInstance, ν, v, hcard, ?_, ?_, ?_, ?_, herr⟩
  · intro k i
    simpa only [ν, Int.cast_neg, abs_neg] using (hprops k).1 (index i)
  · intro k
    exact ⟨(hprops k).2.1, (hprops k).2.2.1⟩
  · intro k i t x
    have hi := (hprops k).2.2.2 (index i) t x
    rw [hindex i] at hi
    exact hi
  · intro g z hg hf k x
    exact iteratedCircleComponent_equivariant N A is (fun r => (k r : ℤ))
      g z (fun i _ => hg i) hf x

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CanonicalDensityFourier
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_ambient_torus_fourier_approximation {J : Type*} [Fintype J]
    (f : (J → UnitAddCircle) → ℂ) (L B : ℝ≥0) (hf : LipschitzWith L f)
    (hB : ∀ x, ‖f x‖ ≤ B) {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hJ : (Fintype.card J : ℝ) ≤ P) (hL : (L : ℝ) ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → J → ℤ) (c : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ a j, |(frequency a j : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) * B ∧
      ∀ x, ‖f x - ∑ a, c a * ∏ j, CircleFourier.character (frequency a j • x j)‖ ≤ δ := by
  classical
  have hact : ∀ t : J → UnitAddCircle, Isometry (fun x : J → UnitAddCircle => t +ᵥ x) :=
    fun t => isometry_add_left t
  let A := CircleFourier.torusCoordinateAction hact
  have horbit : ∀ i (t : UnitAddCircle) x, dist ((A i).act t x) x ≤ (1 : ℝ≥0) * ‖t‖ := by
    intro i t x
    change dist ((Pi.single i t : J → UnitAddCircle) + x) x ≤ (1 : ℝ) * ‖t‖
    rw [one_mul, dist_eq_norm, add_sub_cancel_right]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg t)).mpr
    intro j
    by_cases h : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]
  obtain ⟨F, inst, frequency, v, hcard, hfrequency, hv, hchar, _, herr⟩ :=
    CircleFourier.exists_controlled_commuting_circle_decomposition A
      (CircleFourier.torusCoordinateAction_commutes hact) f L B 1 hf hB horbit δ P hδ hP hJ hL
      (by simpa using Real.one_le_exp hP) hδP
  let _ := inst
  have he (a : F) (x : J → UnitAddCircle) :
      v a x = (∏ j, CircleFourier.character (frequency a j • x j)) * v a 0 := by
    have hc : ∀ i (t : UnitAddCircle) z,
        v a ((Pi.single i t : J → UnitAddCircle) +ᵥ z) = CircleFourier.character (frequency a i • t) * v a z :=
      fun i t z => hchar a i t z
    have hh := CircleFourier.torus_character_of_coordinate_characters (v a) (frequency a) hc x 0
    change v a (x + 0) = _ at hh
    simpa only [add_zero] using hh
  refine ⟨F, inst, frequency, fun a => v a 0, hcard, hfrequency, ?_, ?_⟩
  · calc
      _ ≤ ∑ _a : F, (B : ℝ) := Finset.sum_le_sum (fun a _ => (hv a).2 0)
      _ = (Fintype.card F : ℝ) * B := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard B.coe_nonneg
  · intro x
    have hs : (∑ a, v a x) = ∑ a, v a 0 * ∏ j, CircleFourier.character (frequency a j • x j) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [he a x, mul_comm]
    simpa only [hs, norm_sub_rev] using herr x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineCommonCover
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueSmoothWeight_pos_of_threshold {K I : Type*} [Fintype K] [Fintype I]
    (m : ℕ) {D S ρ ε : ℝ} (hD : 0 ≤ D) (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j) (hbound : ∀ j, (modulus j : ℝ) ≤ S)
    (H : I → ℝ)
    (hsize : ∀ j, modeResidueSideThreshold m (Fintype.card (K × I)) D S ρ ε ≤ H j)
    (G : Finset (ColumnResiduePattern K I modulus)) (hG : G.Nonempty)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    0 < ∑' x, selectedResidueSmoothWeight modulus G V x := by
  let d := Fintype.card (K × I)
  have hv z : 1 ≤ residueProfileWidth modulus V z ∧
      1 / residueProfileWidth modulus V z ≤ modeRemovalMesh d :=
    modeResidueWidth_mesh m d hD hS hρ hε (hmodulus z.2) (hbound z.2)
      (hsize z.2) (hV z) (hwidth z)
  apply selectedResidueSmoothWeight_mass_pos modulus G hG V hV
  intro r
  rw [← residueSmoothWeight_mass _ modulus hmodulus V hV]
  have hlower := shiftedSmoothProductMass_lower
    (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus)
    (residueProfileWidth modulus V) (residueProfileWidth_pos modulus V hmodulus hV)
    (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d) (fun z => (hv z).2) (modeRemovalMesh_small d)
  exact (div_pos (Finset.prod_pos (fun z _ => residueProfileWidth_pos modulus V hmodulus hV z))
    (by norm_num)).trans_le hlower

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

theorem rectangularWeightIndices_zero_bound {I : Type*} [Fintype I]
    (W : I → ℝ) {z : I → ℤ} (hz : z ∈ rectangularWeightIndices 0 W 1) (i : I) :
    |(z i : ℝ)| ≤ W i := by
  classical
  have hi := Fintype.mem_piFinset.mp hz i
  change z i ∈ sampledWeightIndices 0 (W i) 1 at hi
  simp only [sampledWeightIndices, mul_one, zero_sub, zero_add, Finset.mem_Icc] at hi
  exact abs_le.mpr ⟨Int.ceil_le.mp hi.1, Int.le_floor.mp hi.2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalAmbientVolumeRatio
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

noncomputable def centeredPhysicalCubeWindow {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (Q : Option K × X → ℝ) : Finset (X → (Unit ⊕ α) → ℤ) :=
  (rectangularWeightIndices 0 Q 1).image (centeredPhysicalCubeMap root D)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialShiftedWindowError
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem mem_rectangular_zero_radius_iff {I : Type*} [Fintype I]
    (H : I → ℝ) (R : ℝ) (v : I → ℤ) :
    v ∈ rectangularWeightIndices 0 H R ↔ ∀ i, |(v i : ℝ)| ≤ H i * R := by
  classical
  constructor
  · intro hv i
    have h := sampledWeightIndices_mem_bound (Fintype.mem_piFinset.mp hv i)
    simpa only [Pi.zero_apply, sub_zero] using h
  · intro hv
    apply Fintype.mem_piFinset.mpr
    intro i
    change v i ∈ sampledWeightIndices 0 (H i) R
    simp only [sampledWeightIndices, zero_sub, zero_add, Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr (abs_le.mp (hv i)).1, Int.le_floor.mpr (abs_le.mp (hv i)).2⟩

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

namespace BooleanCubeKernel

open scoped BigOperators

noncomputable def spatialWindow {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (b : ℝ) : Finset (X → (Unit ⊕ α) → ℤ) := by
  classical
  exact (Fintype.piFinset (fun d => rectangularWeightIndices 0 (fun _ : Unit ⊕ α => H d) b)).image
    (fun w d => spatialUnstar (w d))

theorem mem_spatialWindow_iff {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (b : ℝ) (v : X → (Unit ⊕ α) → ℤ) :
    v ∈ spatialWindow H b ↔ ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ)| ≤ H d * b := by
  classical
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    intro d i
    have h := (mem_rectangular_zero_radius_iff (fun _ : Unit ⊕ α => H d) b (w d)).mp
      (Fintype.mem_piFinset.mp hw d) i
    simpa only [spatialStar_unstar] using h
  · intro hv
    apply Finset.mem_image.mpr
    refine ⟨fun d => spatialStar (v d), ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro d
      exact (mem_rectangular_zero_radius_iff (fun _ : Unit ⊕ α => H d) b _).mpr (hv d)
    · funext d
      exact spatialUnstar_star (v d)

end BooleanCubeKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Matrix

noncomputable def standardPhysicalJetMap {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    CoefficientTorus (K := Fin q) U →+
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) :=
  euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ)
    (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B K I : Type*} [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)

noncomputable def selectedJointDensityMass (D : B → (K × I → ℤ) → ℝ) : ℝ :=
  𝔼 a ∈ A, selectedResidueDensityMass modulus T W (D a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedReferenceJetWindow
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

theorem spatialWindow_four_coordinate_bound {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ x, 0 ≤ H x) {v : X → (Unit ⊕ α) → ℤ}
    (hv : v ∈ spatialWindow H 4) (x : X) (i : Unit ⊕ α) :
    |(v x i : ℝ)| ≤ 8 * H x := by
  have h := (mem_spatialWindow_iff H 4 v).mp hv
  have hr : |(v x (.inl ()) : ℝ)| ≤ H x * 4 := h x (.inl ())
  cases i with
  | inl i => cases i; nlinarith [hH x]
  | inr i =>
    have hd : |(v x (.inl ()) : ℝ) + (v x (.inr i) : ℝ)| ≤ H x * 4 := by
      simpa only [spatialStar, Sum.elim_inr, Int.cast_add] using h x (.inr i)
    rcases abs_le.mp hr with ⟨hr₁,hr₂⟩
    rcases abs_le.mp hd with ⟨hd₁,hd₂⟩
    apply abs_le.mpr
    constructor <;> linarith

theorem physicalResidueReconstruction_envelope {K X : Type*} [Fintype K] [Fintype X] {q : ℕ}
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    (r : Option K × X → ℤ) (H : X → ℝ) (hH : ∀ x, 0 < H x)
    (hoffset : ∀ x i, |(physicalCubeRootDifferences root D 0 r x i : ℝ)| ≤ (stride x : ℝ) * H x)
    {v : X → (Unit ⊕ Fin q) → ℤ} (hv : v ∈ spatialWindow H 4)
    (z : Option (Fin q) × X) :
    |(standardPhysicalCubeFrame (physicalResidueReconstruction root D 0 r stride v) z : ℝ) /
      referenceJetEnvelopeWidths stride H z| ≤ 1 / 2 := by
  have hcoord (i : Unit ⊕ Fin q) :
      |(physicalResidueReconstruction root D 0 r stride v z.2 i : ℝ)| ≤
        9 * (stride z.2 : ℝ) * H z.2 := by
    simp only [physicalResidueReconstruction, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (stride z.2) : (0 : ℝ) ≤ stride z.2)]
    have h := mul_le_mul_of_nonneg_left
      (spatialWindow_four_coordinate_bound H (fun x => (hH x).le) hv z.2 i)
      (Nat.cast_nonneg (stride z.2) : (0 : ℝ) ≤ stride z.2)
    linarith [hoffset z.2 i]
  have hf : |(standardPhysicalCubeFrame (physicalResidueReconstruction root D 0 r stride v) z : ℝ)| ≤
      9 * (stride z.2 : ℝ) * H z.2 := by
    rcases z with ⟨k,x⟩
    cases k with
    | none => exact hcoord (.inl ())
    | some k => exact hcoord (.inr k)
  rw [abs_div, abs_of_pos (referenceJetEnvelopeWidths_pos stride hs H hH z),
    div_le_iff₀ (referenceJetEnvelopeWidths_pos stride hs H hH z)]
  dsimp only [referenceJetEnvelopeWidths]
  nlinarith [mul_pos (Nat.cast_pos.mpr (hs z.2) : (0 : ℝ) < stride z.2) (hH z.2)]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.StandardJetFourier
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Classical

namespace VectorPolynomial

variable {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredJetAmbientTorus (d : ℕ) (y : EuclideanJetLayers U O) :
    JetAmbientIndex O J → UnitAddCircle := fun a =>
  subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
    (quotientIntegerCover (latticeSection (standardEuclideanLattice (J a.1))
      (euclideanSubspace (U a.1))).toAddSubgroup d (y a.1 a.2.1))) a.2.2

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_continuous (d : ℕ) :
    Continuous (coveredJetAmbientTorus (O := O) U d) := by
  apply continuous_pi
  intro a
  exact (continuous_apply a.2.2).comp ((subspaceAmbientTorus_continuous (U a.1)).comp
    ((euclideanSubspaceTorusEquiv_continuous (U a.1)).comp
      ((quotientIntegerCover_continuous _ d).comp
        ((continuous_apply a.2.1).comp (continuous_apply a.1)))))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ}
variable {O J : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_coefficient (d : ℕ) (x : CoefficientTorus (K := K) U)
    (j : Fin m) (o : O j) (i : J j) :
    coveredJetAmbientTorus U d (euclideanCoefficientJetMap U root D rows x) ⟨j, o, i⟩ =
      ∑ e : BoundedCoefficientExponent K (j.val + 1),
        ((d : ℤ) * boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e) •
          coefficientAmbientTorus U x ⟨⟨j, e⟩, i⟩ := by
  change subspaceAmbientTorus (U j) (euclideanSubspaceTorusEquiv (U j)
    (d • euclideanCoefficientJetMap U root D rows x j o)) i = _
  rw [euclideanCoefficientJetMap_apply, map_nsmul, map_sum, map_nsmul, map_sum]
  simp only [map_zsmul, euclideanCoefficientEquiv_apply, AddEquiv.apply_symm_apply,
    Pi.smul_apply, Finset.sum_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e _
  change d • (boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e •
    coefficientAmbientTorus U x ⟨⟨j, e⟩, i⟩) = _
  rw [← natCast_zsmul, ← mul_smul]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RepresentativeWindowTransport
namespace OAI

section

namespace Erdos3.RepresentativeWindow

open _root_.MvPolynomial
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

noncomputable def crtPatch (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) :
    PolynomialPatch J s 1 :=
  w.patch s hs (crtRepresentativePolynomial N hN) (crtRepresentativePolynomial_degree N hN)

omit [NeZero (∏ j, N j)] in
@[simp] theorem crtPatch_lip (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) :
    (w.crtPatch N hN s hs).kernel.lip = w.lip := rfl

end Erdos3.RepresentativeWindow

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialPatchComposition
namespace OAI

section

namespace Erdos3.PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

def liftInterleaving (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E) :
    SlotInterleaving D E :=
  SlotInterleaving.sorted A.weight B.weight A.weight_mono B.weight_mono

noncomputable def insertLifts (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E) :
    PolynomialPatch σ s (D + E) :=
  let I := A.liftInterleaving B
  { weight := I.fill A.weight B.weight
    weight_pos := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_pos i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_pos i)
    weight_le := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_le i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_le i)
    weight_mono := SlotInterleaving.sorted_weight_mono _ _ _ _
    form := A.form.insertLifts B.form I
    kernel := A.kernel.product B.kernel I }

@[simp] theorem insertLifts_lip (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E) :
    (A.insertLifts B).kernel.lip = A.kernel.lip + B.kernel.lip := rfl

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

omit [NeZero (∏ j, N j)] in
theorem crtLiftPolynomial_degree :
    crtLiftPolynomial N hN ∈
      weightedSupportLE (Sum.elim (fun _ : J => 1) (fun _ : Fin 1 => 1)) 1 := by
  apply (weightedSupportLE _ _).sub_mem
  · apply Submodule.sum_mem
    intro j _
    apply (weightedSupportLE _ _).smul_mem
    exact weightedSupportLE_X _ (Sum.inl j)
  · exact (weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ (Sum.inr 0))

namespace RepresentativeWindow

variable (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) {d : ℕ}

noncomputable def composeCRTPatch (P : PolynomialPatch Unit s d) : PolynomialPatch J s (1 + d) :=
  (w.crtPatch N hN s hs).insertLifts
    (P.weightedParameters.reparam
      (q := Sum.elim (fun _ : J => 1) (w.crtPatch N hN s hs).weight)
      (fun _ : Unit => crtLiftPolynomial N hN)
      (by
        intro _
        change crtLiftPolynomial N hN ∈
          weightedSupportLE (Sum.elim (fun _ : J => 1) (fun _ : Fin 1 => 1)) 1
        exact crtLiftPolynomial_degree N hN))

omit [NeZero (∏ j, N j)] in
@[simp] theorem composeCRTPatch_lip (P : PolynomialPatch Unit s d) :
    (w.composeCRTPatch N hN s hs P).kernel.lip = w.lip + P.kernel.lip := rfl

end RepresentativeWindow
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineLiftInsertion
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ ρ : Type*} {D E s : ℕ}

noncomputable def affineLiftSubstitution (c : ρ → ℝ) (M : ρ → Fin D → ℝ) :
    σ ⊕ ρ → MvPolynomial (σ ⊕ Fin D) ℝ :=
  Sum.elim (fun a => X (Sum.inl a))
    (fun a => C (c a) + ∑ j, M a j • X (Sum.inr j))

theorem affineLiftSubstitution_degree {p : ρ → ℕ} {w : Fin D → ℕ}
    (c : ρ → ℝ) (M : ρ → Fin D → ℝ)
    (hM : ∀ a j, M a j ≠ 0 → w j ≤ p a) (a : σ ⊕ ρ) :
    affineLiftSubstitution c M a ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w)
      (Sum.elim (fun _ : σ => 1) p a) := by
  classical
  cases a with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr a =>
    apply (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    apply (weightedSupportLE _ _).sum_mem
    intro j _
    by_cases hj : M a j = 0
    · simp only [hj, zero_smul]
      exact (weightedSupportLE _ _).zero_mem
    · exact weightedSupportLE_mono (hM a j hj)
        ((weightedSupportLE _ _).smul_mem (M a j)
          (weightedSupportLE_X (Sum.elim (fun _ : σ => 1) w) (Sum.inr j)))

namespace PolynomialPatch

noncomputable def insertAffineLifts {p : ρ → ℕ} (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ ρ) (Sum.elim (fun _ => 1) p) s E)
    (c : ρ → ℝ) (M : ρ → Fin D → ℝ)
    (hM : ∀ a j, M a j ≠ 0 → A.weight j ≤ p a) : PolynomialPatch σ s (D + E) :=
  A.insertLifts (B.reparam (affineLiftSubstitution c M) (affineLiftSubstitution_degree c M hM))

@[simp] theorem insertAffineLifts_lip {p : ρ → ℕ} (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ ρ) (Sum.elim (fun _ => 1) p) s E)
    (c : ρ → ℝ) (M : ρ → Fin D → ℝ)
    (hM : ∀ a j, M a j ≠ 0 → A.weight j ≤ p a) :
    (A.insertAffineLifts B c M hM).kernel.lip = A.kernel.lip + B.kernel.lip := rfl

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MarkedLieSpan
namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedLieSpan_le_layer {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d k l : ℕ) :
    markedLieSpan v w marked d k l ≤ F.layer d l := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, hd, _, hl, rfl⟩
  exact F.degree_antitone l hd
    (F.rank_antitone (lieTreeWeight w a) hl (F.lieTreeEval_mem_length v w hv a))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)

omit [Fintype D] [DecidableEq D] [∀ index, Fintype (B index)]
  [∀ index, DecidableEq (B index)] in
@[simp] theorem principalAffineIntervalPoint_value (t : ∀ j, Fin (H j))
    (j : PrincipalTupleIndex B h) (a : Option Empty) :
    (principalAffineIntervalPoint B h L H step start hinside t j a : ℤ) =
      start j + (step j : ℤ) * (t j).val := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateSamplerFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedExternalCandidateSides : LayerSamplerVariables G I n B → ℕ :=
  Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

noncomputable def allocatedExternalCandidateRootBudget : ℝ :=
  Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ)

noncomputable def allocatedExternalCandidateWidths (N : X → ℕ) (τ ξ : ℝ) :
    Option (LayerSamplerVariables G I n B) × X → ℝ :=
  narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedExternalCandidateRootBudget B U b S) τ ξ N

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowJetAmbientReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem lowJetAmbientSites_coefficient {K : Type*} [Fintype K]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (x : CoefficientTorus (K := K) U) :
    lowJetAmbientSites (coveredJetAmbientTorus U 1
      (euclideanCoefficientJetMap U root D (fun j =>
        (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) x)) =
      coefficientAmbientSiteEvaluation (integerAffineCube root D) (coefficientAmbientTorus U x) := by
  funext t
  rcases t with ⟨j, s, i⟩
  simp only [lowJetAmbientSites, coveredJetAmbientTorus_coefficient, Nat.cast_one, one_mul,
    coefficientAmbientSiteEvaluation, Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_smul]
  congr 1
  have h := boundedBooleanReconstruction_siteMatrix root D (j.val + 1)
  rw [Matrix.mul_assoc, booleanJetExtractionMatrix_mul_boundedSite] at h
  exact congrFun (congrFun h s) e

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRowsAmbientProjectedFamilyMultiple
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped Classical BigOperators NNReal

attribute [local irreducible] boundedBooleanJetRows

variable {m dim : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
local notation "Row" => (fun j : Fin m =>
  {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)})

attribute [local instance] OAI.Erdos3.BooleanCubeKernel.physicalRowsAmbientFintype
theorem physicalRowsAmbientToStandard_eq (U : ∀ j, Submodule ℝ (J j → ℝ))
    (y : EuclideanJetLayers U Row) :
    physicalRowsAmbientToStandard (coveredJetAmbientTorus U 1 y) =
      coveredJetAmbientTorus U 1 (physicalRowsToStandard U y) := rfl

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueL1Surrogate
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped Classical BigOperators NNReal

theorem selectedResidueDensityMass_l1_surrogate
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {K I : Type*} [Fintype K] [Fintype I]
    (stride : I → ℕ) (cells : Finset (ColumnResiduePattern K I stride))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (s : (K × I → ℤ) → X) (f ideal g : X → ℂ)
    (hf : Measurable f) (hi : Measurable ideal) (hg : Measurable g)
    {Cf Cg : ℝ} (hfb : ∀ x, ‖f x‖ ≤ Cf) (hgb : ∀ x, ‖g x‖ ≤ Cg)
    {E δ ε : ℝ} (happrox : ∀ x, ‖ideal x - g x‖ ≤ δ)
    (hmass : (∫ x, ‖f x - ideal x‖ ∂μ) ≤ E)
    (hsample : selectedResidueDensityMass stride cells V
      (fun z => ‖f (s z) - g (s z)‖) ≤ (∫ x, ‖f x - g x‖ ∂μ) + ε) :
    selectedResidueDensityMass stride cells V
      (fun z => ‖f (s z) - ideal (s z)‖) ≤ E + 2 * δ + ε := by
  let ν := (selectedResidueSmoothPMF stride cells V hV hZ).toMeasure
  have hib (x) : ‖ideal x‖ ≤ δ + Cg := by
    calc
      _ ≤ ‖ideal x - g x‖ + ‖g x‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := add_le_add (happrox x) (hgb x)
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable Cf (Filter.Eventually.of_forall hfb)
  have hii : Integrable ideal μ := Integrable.of_bound hi.aestronglyMeasurable (δ + Cg) (Filter.Eventually.of_forall hib)
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable Cg (Filter.Eventually.of_forall hgb)
  have hfs : Integrable (fun z => f (s z)) ν := Integrable.of_bound
    (measurable_of_countable _).aestronglyMeasurable Cf (Filter.Eventually.of_forall (fun z => hfb _))
  have his : Integrable (fun z => ideal (s z)) ν := Integrable.of_bound
    (measurable_of_countable _).aestronglyMeasurable (δ + Cg) (Filter.Eventually.of_forall (fun z => hib _))
  have hgs : Integrable (fun z => g (s z)) ν := Integrable.of_bound
    (measurable_of_countable _).aestronglyMeasurable Cg (Filter.Eventually.of_forall (fun z => hgb _))
  have hs' : (∫ z, ‖f (s z) - g (s z)‖ ∂ν) ≤ (∫ x, ‖f x - g x‖ ∂μ) + ε := by
    exact (selectedResidueDensityMass_integral stride cells V hV hZ _ (hfs.sub hgs).norm).symm.trans_le hsample
  exact (selectedResidueDensityMass_integral stride cells V hV hZ _ (hfs.sub his).norm).trans_le
    (l1_sampling_via_uniform_surrogate μ ν s f ideal g hfi hii hgi hfs his hgs happrox hmass hs')

end Erdos3

end

end OAI
end


