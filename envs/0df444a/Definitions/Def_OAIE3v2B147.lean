-- Prove2me | Definitions.Def_OAIE3v2B147
-- name    : OAIE3v2B147
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:18:49.854226+00:00
-- url     : https://prove2.me/theorems/d2f4ba93-c7f6-48ea-84dc-096894522d8a
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 149 of 311
-- statement:
--   Definitions bundle 149 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B128`, `OAIE3v2B129`, `OAIE3v2B132`, `OAIE3v2B133`, `OAIE3v2B134`, `OAIE3v2B135`, `OAIE3v2B136` of this split.
--
--   Modules: `Dynamics/InducedMarkedBudget.lean`, `Dynamics/PreparedFiniteStageNativeBudget.lean`, `Estimates/BoundedRealifiedSquareOrbit.lean`, `Estimates/CommonCoefficientFourAnnihilators.lean`, `Estimates/MajorTranslationPureFactorValues.lean`, `Estimates/PreparedFiniteForwardTreeStorage.lean`, `Estimates/RationalTagConstraintSpaces.lean`, `Estimates/RealSymbolGradeEvaluation.lean`, `Estimates/RealSymbolGradeQuotientSplitting.lean`, `Estimates/WeightedTranslationBaseGrading.lean`, `Fourier/HomogeneousGradedProjectionFrequency.lean`, `Fourier/VerticalFrequencyIdentification.lean`, `Geometry/LowTaggedCoordinateRestriction.lean`, `Geometry/TranslationLogCoordinateInputBounds.lean`, `Geometry/TranslationLogCoordinateScaling.lean`, `Lattices/NativeIntegerAffinePullbackHom.lean`, `Lattices/NativeIntegerDivision.lean`, `Lattices/ResidueBoxSliceCoordinateDisintegration.lean`, `Linear/HomogeneousGradedProjectionBounds.lean`, `Linear/LieKernelRealificationMark.lean`, `Linear/LowTaggedCoordinateProjection.lean`, `Linear/RankQuotientHeightBudget.lean`, `Linear/RationalTagConstraintBasis.lean`, `Linear/WeightedTranslationOrderedBasis.lean`, `Nilpotent/CanonicalReducedMajorTwistedNiltest.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Nilpotent/NiltestComplement.lean`, `Polynomial/MajorTranslationDegreeSymbol.lean`, `Polynomial/OrdinaryPhasePairFunctionalBounds.lean`, `Polynomial/RealCoordinatePolynomialSymbol.lean`, `Polynomial/TranslationLogCoordinatePolynomials.lean`, `Polynomial/WeightedLinearPolynomialRestriction.lean`, `Sampling/TranslationLogCoordinateInputGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B128
import Definitions.Def_OAIE3v2B129
import Definitions.Def_OAIE3v2B132
import Definitions.Def_OAIE3v2B133
import Definitions.Def_OAIE3v2B134
import Definitions.Def_OAIE3v2B135
import Definitions.Def_OAIE3v2B136

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedLinearPolynomialRestriction
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

theorem polynomialLinearRestriction_exponentialPath
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    (polynomialExponentialPath (A z) P).map (polynomialLinearRestriction A).toRingHom =
      polynomialExponentialPath z (polynomialLinearRestriction A P) := by
  symm
  apply polynomialExponentialPath_unique
  · rw [Polynomial.derivative_map, polynomialExponentialPath_derivative,
      polynomialLinearRestriction_translationPath]
  · simp

theorem polynomialLinearRestriction_exponentialCoordinate
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    polynomialLinearRestriction A (polynomialExponentialCoordinate (A z) P) =
      polynomialExponentialCoordinate z (polynomialLinearRestriction A P) := by
  unfold polynomialExponentialCoordinate
  rw [← polynomialLinearRestriction_exponentialPath]
  simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (v : σ → ℕ) (P : ι → MvPolynomial σ ℝ)

theorem realSymbolOfPolynomial_ofCoordinates_top :
    F.realSymbolOfPolynomial b ω hlayers v
      (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) =
    F.realSymbolOfPolynomial b ω hlayers v
      (ofCoordinates (R := ℚ) (b.baseChange ℝ)
        (fun i => weightedHomogeneousComponent v (ω i) (P i))) := by
  rw [← F.realSymbolRepresentative_ofCoordinates b ω hlayers v P]
  exact (F.realSymbolOfPolynomial_representative b ω hlayers v _).symm

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.HomogeneousGradedProjectionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module
variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousGradedProjection_basis_repr (i : ι) (j : κ) :
    c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ
      (F.associatedGradedBasis b ω hF i)) j =
      if ω i = ν j then c.repr (φ (b i)) j else 0 := by
  rw [F.homogeneousGradedProjection_repr,
    F.associatedGradedMap_basis_repr G b ω hF c ν hG φ hφ]

theorem homogeneousGradedProjection_gradeProjection (r : ℕ) (x : F.AssociatedGraded) :
    F.homogeneousGradedProjection G c ν hG hc φ hφ
      (basisGradeProjection (F.associatedGradedBasis b ω hF) ω r x) =
      basisGradeProjection c ν r (F.homogeneousGradedProjection G c ν hG hc φ hφ x) := by
  apply basisBlockMap_commutes (F.associatedGradedBasis b ω hF) c ω ν
    (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap
  intro i j hij
  change c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ
    (F.associatedGradedBasis b ω hF i)) j = 0
  rw [F.homogeneousGradedProjection_basis_repr G c ν hG hc φ hφ b ω hF]
  exact if_neg (Ne.symm hij)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.HomogeneousGradedProjectionFrequency
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}

theorem homogeneousAssociatedGradedEquiv_top_piece
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hb : BasisHomogeneousBrackets b ω) (x : F.layer s) :
    F.homogeneousAssociatedGradedEquiv b ω hF hb (F.associatedGradedPieceMap s x) = x.val := by
  rw [F.homogeneousAssociatedGradedEquiv_pieceMap b ω hF hb,
    F.basisGradeProjection_top b ω hF x]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedRealifiedSquareOrbit
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_bounded_normalized_square_orbit (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (h : σ → ℤ) (f : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ q : D.filtration.realification.squareFiltration.PolynomialOrbit w,
          ∀ x : σ → ℤ,
            D.filtration.realification.squareFstHom
              (D.filtration.realification.squareFiltration.polynomialOrbitEval w x q) =
                ε⁻¹ * D.filtration.realification.polynomialOrbitEval w (fun i => x i + h i) f * γ⁻¹ ∧
            D.filtration.realification.squareSndHom
              (D.filtration.realification.squareFiltration.polynomialOrbitEval w x q) =
                D.filtration.realification.polynomialOrbitEval w x f := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_normalized_square s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw h f
  obtain ⟨ε, γ, hγ, hε, r, hr, hfst, hsnd⟩ :=
    hnorm D p hp hD w hw (fun i => (h i : ℚ)) f
  let q := NilpotentLieFiltration.polynomialOrbitOfLog r hr
  refine ⟨ε, γ, hγ, hε, q, ?_⟩
  intro x
  constructor
  · rw [mul_assoc]
    apply NilpotentLieBCHGroup.ext
    have hh := congrArg (eval (fun i => (x i : ℚ))) hfst
    rw [eval_map, eval_normalizedShiftLog] at hh
    change (eval (fun i => (x i : ℚ)) r).val.1 = _ at hh
    change (eval (fun i => (x i : ℚ)) r).val.1 =
      lieBCH s (-ε.coord) (lieBCH s (eval (fun i => ((x i + h i : ℤ) : ℚ)) f.log) (-γ.coord))
    simpa only [Int.cast_add] using hh
  · apply NilpotentLieBCHGroup.ext
    have hh := congrArg (eval (fun i => (x i : ℚ))) hsnd
    rw [eval_map] at hh
    exact hh

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.VerticalFrequencyIdentification
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem vertical_frequency_eq_of_real_line
    (F : NilpotentLieFiltration L s) (Γ : Subgroup F.realification.Group)
    (η : L →ₗ[ℚ] ℚ) (f : F.realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ F.realification.subgroup s, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0) (c : L) (hc : c ∈ F.layer s) (a : ℚ)
    (hline : ∀ t : ℝ, ∀ x,
      f ((⟨t ⊗ₜ[ℚ] c⟩ : F.realification.Group) • x) =
        character ((t * a : ℝ) : CircleFourier.Circle) * f x) :
    η c = a := by
  exact_mod_cast vertical_frequency_on_real_direction F Γ η f hvert hne c hc (a : ℝ) hline

theorem vertical_frequency_eq_one_of_real_line
    (F : NilpotentLieFiltration L s) (Γ : Subgroup F.realification.Group)
    (η : L →ₗ[ℚ] ℚ) (f : F.realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ F.realification.subgroup s, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0) (c : L) (hc : c ∈ F.layer s)
    (hline : ∀ t : ℝ, ∀ x,
      f ((⟨t ⊗ₜ[ℚ] c⟩ : F.realification.Group) • x) =
        character (t : CircleFourier.Circle) * f x) :
    η c = 1 := by
  apply vertical_frequency_eq_of_real_line F Γ η f hvert hne c hc 1
  simpa only [Rat.cast_one, mul_one] using hline

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
namespace OAI

section

namespace Erdos3

open Module

theorem exists_bounded_rank_quotient_data
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n t : ℕ}
    (F : DegreeRankLieFiltration L s r) (e : Basis (Fin n) ℚ L)
    (b : ∀ i : Fin (s + 1), Basis (Fin (finrank ℚ (F.associatedDegree.layer (i.val + 1))))
      ℚ (F.associatedDegree.layer (i.val + 1)))
    (c : ∀ i j : Fin (s + 1), Basis (Fin (finrank ℚ (F.layer i.val j.val)))
      ℚ (F.layer i.val j.val))
    (I : LieIdeal ℚ L) (a : Basis (Fin t) ℚ I)
    (η : L →ₗ[ℚ] ℚ) (hann : F.layer s r ⊓ I.toSubmodule ≤ η.ker)
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i a j, RationalHeightLE (e.repr (b i a).val j) H)
    (hc : ∀ i j a k, RationalHeightLE (e.repr (c i j a).val k) H)
    (ha : ∀ i j, RationalHeightLE (e.repr (a i).val j) H)
    (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hη : ∀ i, RationalHeightLE (η (e i)) H) :
    ∃ m : ℕ, m ≤ t ∧ ∃ q : ℕ, q ≤ n ∧ ∃ u : ℕ, u ≤ q ∧
      ∃ f : Basis (Fin q) ℚ (L ⧸ I),
        (∀ i j, RationalHeightLE (f.repr (lieQuotientMap I (e j)) i)
          (rankQuotientHeight n m q u H)) ∧
        (∀ i j k, RationalHeightLE (lieStructureConstants f i j k)
          (rankQuotientHeight n m q u H)) ∧
        (∀ i : Fin (s + 1), ∃ b' : Basis
            (Fin (finrank ℚ ((F.associatedDegree.layer (i.val + 1)).map (lieQuotientMap I).toLinearMap)))
            ℚ ((F.associatedDegree.layer (i.val + 1)).map (lieQuotientMap I).toLinearMap),
          ∀ a j, RationalHeightLE (f.repr (b' a).val j) (rankQuotientHeight n m q u H)) ∧
        (∀ i j : Fin (s + 1), ∃ c' : Basis
            (Fin (finrank ℚ ((F.layer i.val j.val).map (lieQuotientMap I).toLinearMap)))
            ℚ ((F.layer i.val j.val).map (lieQuotientMap I).toLinearMap),
          ∀ a k, RationalHeightLE (f.repr (c' a).val k) (rankQuotientHeight n m q u H)) ∧
        ∃ ξ : (L ⧸ I) →ₗ[ℚ] ℚ,
          (∀ x ∈ F.layer s r, ξ (lieQuotientMap I x) = η x) ∧
          ∀ i, RationalHeightLE (ξ (f i)) (rankQuotientHeight n m q u H) := by
  classical
  obtain ⟨m, hm, q, hq, f, A, _, hmatrix, _, hA, _, hstructure⟩ :=
    exists_bounded_lie_quotient_with_structure e I (fun i => (a i).val)
      (span_submodule_basis I.toSubmodule a) hH (fun i j => ha j i) hbracket
  have hm' : m ≤ t := by simpa only [Fintype.card_fin] using hm
  have hq' : q ≤ n := by simpa only [Fintype.card_fin] using hq
  let π := (lieQuotientMap I).toLinearMap
  let Q := rationalKernelHeight m H
  let E := rankQuotientLayerHeight n m H
  have hQ : 1 ≤ Q := rationalKernelHeight_pos m hH
  have hE : 1 ≤ E := by
    have : 0 < H := by omega
    have : 0 < Q := by omega
    change 1 ≤ (n + 1) * (H * Q) ^ n
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hproj (i j) : RationalHeightLE (f.repr (π (e j)) i) Q := by
    have h := hA i j
    rw [← hmatrix, LinearMap.toMatrix_apply] at h
    exact h
  have himage (P : Submodule ℚ L)
      (bP : Basis (Fin (finrank ℚ P)) ℚ P)
      (hP : ∀ i j, RationalHeightLE (e.repr (bP i).val j) H) :
      ∃ b' : Basis (Fin (finrank ℚ (P.map π))) ℚ (P.map π),
        ∀ i j, RationalHeightLE (f.repr (b' i).val j) E := by
    have hspan : Submodule.span ℚ (Set.range (fun i => π (bP i).val)) = P.map π := by
      change Submodule.span ℚ (Set.range (π ∘ (fun i => (bP i).val))) = _
      rw [Set.range_comp, ← Submodule.map_span, span_submodule_basis]
    apply exists_bounded_submodule_basis_from_spanning f _ (fun i => π (bP i).val) hspan
    intro i j
    simpa only [Fintype.card_fin, E, Q, rankQuotientLayerHeight] using
      linearMap_coordinate_height e f π (fun i j => hproj j i) (bP i).val (hP i) j
  let u := finrank ℚ ((F.layer s r).map π)
  let _ : FiniteDimensional ℚ (L ⧸ I) := f.finiteDimensional_of_finite
  have hu : u ≤ q := by
    have hfq : finrank ℚ (L ⧸ I) = q := by
      simpa only [Fintype.card_fin] using finrank_eq_card_basis f
    exact (Submodule.finrank_le _).trans_eq hfq
  let cs := c ⟨s, Nat.lt_succ_self s⟩ ⟨r, Nat.lt_succ_of_le F.rank_le_degree⟩
  obtain ⟨ξ, hξ, hξH⟩ := exists_bounded_quotient_functional (F.layer s r) I.toSubmodule f
    (fun i => (cs i).val) (span_submodule_basis _ cs) η hann hE
    (fun i j => by
      change RationalHeightLE (f.repr (π (cs i).val) j) E
      simpa only [Fintype.card_fin, E, Q, rankQuotientLayerHeight] using linearMap_coordinate_height e f π
        (fun i j => hproj j i) (cs i).val (hc _ _ i) j)
    (fun i => by
      simpa only [Fintype.card_fin] using
        linearFunctional_coordinate_height e η hη (cs i).val (hc _ _ i))
  let K := rankQuotientHeight n m q u H
  have hQK : Q ≤ K := by dsimp only [K, rankQuotientHeight, Q]; omega
  have hEK : E ≤ K := by dsimp only [K, rankQuotientHeight, E]; omega
  have hSK : rationalLieStructureHeight n
      (max H (max Q (rationalSolveHeight q Q))) ≤ K := by
    dsimp only [K, rankQuotientHeight, Q]; omega
  have hFK : rankQuotientFrequencyHeight n m u H ≤ K := by
    dsimp only [K, rankQuotientHeight]; omega
  refine ⟨m, hm', q, hq', u, hu, f, fun i j => (hproj i j).mono hQK,
    ?_, ?_, ?_, ξ, hξ, fun i => (hξH i).mono hFK⟩
  · intro i j k
    have h : RationalHeightLE (lieStructureConstants f i j k)
        (rationalLieStructureHeight n (max H (max Q (rationalSolveHeight q Q)))) := by
      simpa only [Fintype.card_fin] using hstructure i j k
    exact h.mono hSK
  · intro i
    obtain ⟨b', hb'⟩ := himage _ (b i) (hb i)
    exact ⟨b', fun a j => (hb' a j).mono hEK⟩
  · intro i j
    obtain ⟨c', hc'⟩ := himage _ (c i j) (hc i j)
    exact ⟨c', fun a k => (hc' a k).mono hEK⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolGradeEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realSymbolGradeEvaluation_eq_projection (d : ℕ) (t : σ → ℝ)
    (x : F.RealPolynomialSymbol w) :
    F.realSymbolGradeEvaluation b ω hlayers w d t x =
      basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) ω d
        (eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) :=
  F.realGradedSymbolPolynomial_eval₂_gradeProjection b ω hlayers w d x t

theorem realSymbolGradeEvaluation_homogeneous (d : ℕ) (t : σ → ℝ)
    (x : F.RealPolynomialSymbol w) :
    basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) ω d
      (F.realSymbolGradeEvaluation b ω hlayers w d t x) =
        F.realSymbolGradeEvaluation b ω hlayers w d t x := by
  simp only [F.realSymbolGradeEvaluation_eq_projection]
  exact basisCoordinateProjection_idempotent
    ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) {i | ω i = d} _

theorem realSymbolGradeEvaluation_current_correction (d : ℕ) (t : σ → ℝ)
    (a g c : F.RealPolynomialSymbolGroup w)
    (ha : a.coord ∈ (F.polynomialSymbolFiltration w).realification.layer d)
    (hc : c.coord ∈ (F.polynomialSymbolFiltration w).realification.layer d) :
    F.realSymbolGradeEvaluation b ω hlayers w d t (a⁻¹ * g * c⁻¹).coord =
      F.realSymbolGradeEvaluation b ω hlayers w d t g.coord -
        F.realSymbolGradeEvaluation b ω hlayers w d t a.coord -
        F.realSymbolGradeEvaluation b ω hlayers w d t c.coord := by
  have h := (F.polynomialSymbolFiltration w).real_correction_current_grade
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) d a g c ha hc
  have he := congrArg (fun x => eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) h
  simpa only [realSymbolGradeEvaluation_apply, map_sub] using he

theorem realSymbolGradeEvaluation_correction_below (d : ℕ) (t : σ → ℝ)
    (a g c : F.RealPolynomialSymbolGroup w)
    (ha : a.coord ∈ (F.polynomialSymbolFiltration w).realification.layer d)
    (hc : c.coord ∈ (F.polynomialSymbolFiltration w).realification.layer d)
    (j : ℕ) (hj : j < d) :
    F.realSymbolGradeEvaluation b ω hlayers w j t (a⁻¹ * g * c⁻¹).coord =
      F.realSymbolGradeEvaluation b ω hlayers w j t g.coord := by
  have h := (F.polynomialSymbolFiltration w).real_correction_preserves_grades_below
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) d a g c ha hc j hj
  exact congrArg (fun x => eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationBaseGrading
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module
open scoped TensorProduct

variable {B : Type*} [Fintype B]

theorem weightedTranslationBase_real_image_graded
    {J : Type*} (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (weightedSubalgebra w d))
    (hU : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) U)
    (g : J → weightedSubalgebra w d) (hg : Submodule.span ℚ (Set.range g) = U) :
    BasisGradedSubmodule (Pi.basisFun ℝ B) w
      ((U.baseChange ℝ).map
        (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) := by
  let ℓ := baseLinear.comp (weightedSubalgebra w d).subtype
  rw [realifyCoordinateMap_image_eq_span U g hg ℓ]
  intro j z hz
  let K := Submodule.span ℝ (Set.range (fun a i => ((g a).val.base i : ℝ)))
  change basisGradeProjection (Pi.basisFun ℝ B) w j z ∈ K
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    have hga : g a ∈ U := by rw [← hg]; exact Submodule.subset_span ⟨a, rfl⟩
    have hproj := hU j (g a) hga
    have ht := Submodule.tmul_mem_baseChange_of_mem (1 : ℝ) hproj
    have hm := realifyCoordinateMap_mem_span U g hg ℓ ht
    change _ ∈ K at hm
    convert hm using 1
    funext i
    have hp := basisGradeProjection_repr (Pi.basisFun ℝ B) w j
      (fun i => ((g a).val.base i : ℝ)) i
    simp only [Pi.basisFun_repr] at hp
    change (basisGradeProjection (Pi.basisFun ℝ B) w j
      (fun i => ((g a).val.base i : ℝ))) i = _
    rw [hp, realifyCoordinateMap_tmul, one_mul]
    change (if w i = j then ((g a).val.base i : ℝ) else 0) =
      ((basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j (g a)).val.base i : ℝ)
    rw [weightedBasis_projection_base]
    split_ifs <;> simp
  | zero => simpa only [map_zero] using K.zero_mem
  | add x y hx hy hxp hyp =>
    rw [map_add]
    exact K.add_mem hxp hyp
  | smul c x hx hxp =>
    rw [map_smul]
    exact K.smul_mem c hxp

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationOrderedBasis
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ)
  (hw : ∀ i, 0 < w i) [Fintype (WeightedBasisIndex w d)]

theorem weightedLayerBasis_height (hwd : ∀ i, w i ≤ d) (r : ℕ)
    (i : {j : Fin (Fintype.card (WeightedBasisIndex w d)) // r ≤ weightedOrderedGrade w d j}) (j) :
    RationalHeightLE ((weightedOrderedBasis w d hw).repr
      (weightedLayerBasis w d hw hwd r i).val j) 1 := by
  rw [weightedLayerBasis, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one (weightedOrderedBasis w d hw) _ _

theorem weightedLayerFinBasis_height (hwd : ∀ i, w i ≤ d) (r : ℕ) (i j) :
    RationalHeightLE ((weightedOrderedBasis w d hw).repr
      (weightedLayerFinBasis w d hw hwd r i).val j) 1 := by
  rw [weightedLayerFinBasis, Basis.reindex_apply]
  exact weightedLayerBasis_height w d hw hwd r _ _

include hw in
theorem weightedBasisIndex_card_le :
    Fintype.card (WeightedBasisIndex w d) ≤ Fintype.card σ + (Fintype.card σ + 1)^d := by
  rw [← finrank_eq_card_basis (weightedBasis w d hw)]
  exact weightedSubalgebra_finrank_le w d hw

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {U : Type*} {N : U → ℕ} {q : ℕ}

variable [Fintype U] [DecidableEq U]

theorem expect_integerPoints (A : ResidueBoxSlice N q) (hq : 0 < q)
    {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V] (f : (U → ℤ) → V) :
    (𝔼 x ∈ A.integerPoints, f x) =
      (𝔼 j : (∀ i, Fin (A.length i)), f (A.integerPoint j)) := by
  exact Finset.expect_image (A.integerPoint_injective hq).injOn

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MajorTranslationPureFactorValues
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped TensorProduct

namespace PolynomialTranslationLie

variable {B : Type*} [Fintype B]

theorem bchRealTranslationHom_pure_base_of_shape
    (w : B → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d)
    (v : ℝ ⊗[ℚ] weightedSubalgebra w d) (b : B → ℝ)
    (hb : ∀ i, (realShearEmbedding w d v).val (X (Sum.inl i)) = C (b i))
    (hP : (realShearEmbedding w d v).val (X (Sum.inr ())) = 0) :
    bchRealTranslationHom w d hwd ⟨v⟩ = ⟨b, 0⟩ := by
  apply PolynomialTranslationGroupOver.actionMonoidHom_injective
  rw [bchRealTranslationHom_action]
  change (polynomialShearExpAut (realShearEmbedding w d v)).val = _
  have h := PolynomialTranslationGroupOver.action_eq_of_shape
    (polynomialShearExpAut (realShearEmbedding w d v)).val b 0
    (fun i => polynomialShearExp_X_of_derivation_eq_C _ _ _ (hb i)) ?_
  · simpa only [PolynomialTranslationGroupOver.actionElement, map_zero] using h.symm
  · change polynomialShearExp (realShearEmbedding w d v) (X (Sum.inr ())) = _
    simpa only [map_zero] using polynomialShearExp_X_of_derivation_eq_C
      (realShearEmbedding w d v) (Sum.inr ()) 0 (by simpa only [map_zero] using hP)

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorTranslationDegreeSymbol
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem majorTranslationJointPolynomial_sub_degree_top_lower (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    majorTranslationJointPolynomial D A -
      majorTranslationJointPolynomial
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) A ∈
      weightedSupportLT (Sum.elim (fun _ : U => 1) w) d := by
  rw [← majorTranslationJointPolynomial_sub]
  exact majorTranslationJointPolynomial_lower w
    (weightedTopPart_remainder_lt (Sum.elim (fun _ : U => 1) w) hD) A hA

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (v : σ → ℕ)

theorem realSymbolRepresentative_of_gradedPolynomial
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v) :
    F.realSymbolRepresentative b ω hlayers v (F.realSymbolOfPolynomial b ω hlayers v P) = P := by
  apply coefficients.injective
  ext α
  apply (b.baseChange ℝ).repr.injective
  ext i
  by_cases h : Finsupp.weight v α = ω i
  · rw [F.realSymbolRepresentative_coefficient b ω hlayers v
      (F.realSymbolOfPolynomial b ω hlayers v P) ⟨(α, i), h⟩]
    exact F.realSymbolOfPolynomial_coordinate b ω hlayers v P ⟨(α, i), h⟩
  · rw [F.realSymbolRepresentative_coefficient_of_ne b ω hlayers v _ α i h]
    have hi := congrArg (fun x => (b.baseChange ℝ).repr x i) (hP α)
    simp only [LinearMap.restrictScalars_apply] at hi
    rw [basisGradeProjection_repr, if_neg (Ne.symm h)] at hi
    exact hi

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

noncomputable def translationCoordinatePolynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  translationBasePolynomialOrbit w d hw hwd A hA *
    translationPurePolynomialOrbit w d hw hwd P hP

theorem translationBasePolynomialOrbit_eval_coordinates
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (u : U → ℝ) (i : WeightedBasisIndex w d) :
    ((weightedBasis w d hw).baseChange ℝ).repr
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationBasePolynomialOrbit w d hw hwd A hA)).coord i =
      eval u (translationBaseCoordinatePolynomial w d A i) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit_eval_coordinates
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationBaseCoordinatePolynomial w d A)
    (translationBaseCoordinatePolynomial_adapted w d A hA) u i

theorem translationPurePolynomialOrbit_eval_coordinates
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (u : U → ℝ) (i : WeightedBasisIndex w d) :
    ((weightedBasis w d hw).baseChange ℝ).repr
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationPurePolynomialOrbit w d hw hwd P hP)).coord i =
      eval u (translationPolynomialCoordinatePolynomial w d P i) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit_eval_coordinates
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationPolynomialCoordinatePolynomial w d P)
    (translationPolynomialCoordinatePolynomial_adapted w d P hP) u i

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

noncomputable def majorTranslationPolynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  translationCoordinatePolynomialOrbit w d hw hwd A hA
    (majorTranslationJointPolynomial D A) (majorTranslationJointPolynomial_degree w hD A hA)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productProjectionHom_mem_layer (i : ι) (k : ℕ) (g : (pi D).RealGroup)
    (hg : g ∈ (pi D).filtration.realification.subgroup k) :
    productProjectionHom D i g ∈ (D i).filtration.realification.subgroup k := by
  apply baseChange_mem_of_mapsTo ((pi D).filtration.layer k) ((D i).filtration.layer k)
    (liePiEval i).toLinearMap _ hg
  intro x hx
  exact (NilpotentLieFiltration.mem_pi_layer (fun i => (D i).filtration) k x).mp hx i

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def scaleNormLeOne {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ}
    {f : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p f)
    (c : ℂ) (hc : ‖c‖ ≤ 1) :
    NativeIntegerExpansion w s p (fun x => c * f x) :=
  { E with
    coefficient := fun i => c * E.coefficient i
    cost := by
      simp only [norm_mul, ← Finset.mul_sum]
      exact (mul_le_of_le_one_left (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hc).trans E.cost
    eval := by
      intro x
      rw [E.eval, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (mul_assoc _ _ _).symm }

end Erdos3.NativeIntegerExpansion

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LieKernelRealificationMark
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem mem_realificationSubgroup_ker_iff (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    g ∈ realificationSubgroup (hnil := hnil) φ.ker.toLieSubalgebra ↔
      realificationMap (hnil := hnil) (hM := hM) φ g = 1 := by
  change g.coord ∈ (LinearMap.ker φ.toLinearMap).baseChange ℝ ↔ _
  exact coord_mem_realificationKernel_iff φ g

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t n : ℕ}

theorem raiseStep_top_subgroup_eq_bot (D : RationalFilteredNilmanifold L s n)
    (hst : s < t) :
    (D.raiseStep hst.le).filtration.realification.subgroup t = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  change z = 1
  apply NilpotentLieBCHGroup.ext
  change z.coord = 0
  change z.coord ∈ D.filtration.realification.layer t at hz
  simpa only [D.filtration.realification.layer_eq_bot_above_step hst,
    Submodule.mem_bot] using hz

theorem raiseStep_observable_top_vertical (D : RationalFilteredNilmanifold L s n)
    (hst : s < t) (f : (D.raiseStep hst.le).Space → ℂ)
    (z : (D.raiseStep hst.le).RealGroup)
    (hz : z ∈ (D.raiseStep hst.le).filtration.realification.subgroup t)
    (x : (D.raiseStep hst.le).Space) :
    f (z • x) =
      CircleFourier.character
        ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) * f x := by
  have hz' : z = 1 := by
    simpa only [raiseStep_top_subgroup_eq_bot D hst, Subgroup.mem_bot] using hz
  subst z
  simp

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTagConstraintSpaces
namespace OAI

section

namespace Erdos3.VectorPolynomial.RationalTagConstraint

open Module

variable {m : ℕ} {J : Fin m → Type*}

theorem exists_function_spanning_logHeight
    {B η : Type*} [Fintype B] (U : Submodule ℚ (B → ℚ)) (v : η → B → ℚ)
    (hspan : Submodule.span ℚ (Set.range v) = U) {p : ℝ} (hp : 0 ≤ p)
    (hv : ∀ a i, rationalLogHeight (v a i) ≤ p) :
    ∃ w : Fin (Fintype.card B) → B → ℚ,
      Submodule.span ℚ (Set.range w) = U ∧ ∀ a i, rationalLogHeight (w a i) ≤ p := by
  let H := ⌊Real.exp p⌋₊
  have hH : 1 ≤ H := (Nat.le_floor_iff (Real.exp_nonneg p)).mpr (by
    simpa using Real.exp_le_exp.mpr hp)
  have hentry (a : η) (i : B) : RationalHeightLE (v a i) H := by
    obtain ⟨hn, hd⟩ := (rationalLogHeight_le_iff (v a i) p).mp (hv a i)
    exact ⟨(Nat.le_floor_iff (Real.exp_nonneg p)).mpr hn,
      (Nat.le_floor_iff (Real.exp_nonneg p)).mpr hd⟩
  obtain ⟨w, hw, hwH⟩ := exists_bounded_submodule_ambient_spanning
    (Pi.basisFun ℚ B) U v hspan hH hentry
  exact ⟨w, hw, fun a i => rationalLogHeight_le_of_height (hwH a i)
    (Nat.floor_le (Real.exp_nonneg p))⟩

theorem exists_rationalSpace_spanning [∀ j, Fintype (J j)]
    (c : RationalTagConstraint J) (j : Fin m) {p : ℝ} (hp : 0 ≤ p) (hc : c.BudgetLE p) :
    ∃ w : Fin (Fintype.card (J j)) → J j → ℚ,
      Submodule.span ℚ (Set.range w) = c.rationalSpace j ∧
      ∀ a i, rationalLogHeight (w a i) ≤ p := by
  classical
  by_cases hj : j = c.tag
  · subst j
    rw [rationalSpace_self]
    exact exists_function_spanning_logHeight _ c.generators rfl hp hc.2
  · rw [c.rationalSpace_of_ne hj]
    apply exists_function_spanning_logHeight ⊤ (Pi.basisFun ℚ (J j))
      (Pi.basisFun ℚ (J j)).span_eq hp
    intro a i
    by_cases hai : i = a
    · subst i
      simpa [Pi.basisFun_apply, rationalLogHeight] using hp
    · simpa [Pi.basisFun_apply, Pi.single_apply, hai, rationalLogHeight] using hp

end Erdos3.VectorPolynomial.RationalTagConstraint

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintBasis
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem exists_rationalTagConstraintList_basis
    (cs : List (RationalTagConstraint J)) (j : Fin m) {p : ℝ}
    (hp : 0 ≤ p) (hdim : (Fintype.card (J j) : ℝ) ≤ p)
    (hlen : (cs.length : ℝ) ≤ p) (hcs : ∀ c ∈ cs, c.BudgetLE p) :
    ∃ n : ℕ, n ≤ Fintype.card (J j) ∧
      ∃ b : Basis (Fin n) ℚ (rationalTagConstraintIntersection cs j),
        ∀ a i, rationalLogHeight ((b a : J j → ℚ) i) ≤ ((p + 2) ^ 2 + 2) ^ 63 := by
  classical
  choose v hv hheight using fun i : Fin cs.length =>
    (cs.get i).exists_rationalSpace_spanning j hp (hcs _ (List.get_mem _ _))
  obtain ⟨n, hn, b, hb⟩ := exists_submodule_intersection_basis_logHeight
    (Pi.basisFun ℚ (J j)) (fun i : Fin cs.length => (cs.get i).rationalSpace j)
    v hv hp hdim (by simpa only [Fintype.card_fin] using hdim)
    (by simpa only [Fintype.card_fin] using hlen) hheight
  exact ⟨n, hn, b, hb⟩

theorem RationalTaggedConstraintCertificate.exists_bounded_tag_bases {X : Type*}
    {Kinitial K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Kinitial K p Cblocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    ∃ (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
      (b : ∀ j, Basis (Fin (n j)) ℚ (W j)),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      (∀ j a i, rationalLogHeight ((b j a : J j → ℚ) i) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      K = Kinitial ∩ {point | ∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈
        Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ)))} := by
  classical
  obtain ⟨cs, hlen, hbudget, hK⟩ := hcert
  have hl : (cs.length : ℝ) ≤ p := (Nat.cast_le.mpr hlen).trans hblocks
  choose n hn b hb using fun j =>
    exists_rationalTagConstraintList_basis cs j hp (hdim j) hl hbudget
  refine ⟨rationalTagConstraintIntersection cs, n, b, hn, hb, ?_⟩
  rw [hK]
  ext point
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
    rationalTagConstraintList_basis_member_iff cs n b point]

theorem RationalTaggedConstraintCertificate.exists_bounded_tag_bases_univ {X : Type*}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p Cblocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    ∃ (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
      (b : ∀ j, Basis (Fin (n j)) ℚ (W j)),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      (∀ j a i, rationalLogHeight ((b j a : J j → ℚ) i) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      K = {point | ∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈
        Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ)))} := by
  obtain ⟨W, n, b, hn, hb, hK⟩ := hcert.exists_bounded_tag_bases hp hdim hblocks
  exact ⟨W, n, b, hn, hb, by simpa only [Set.univ_inter] using hK⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InducedMarkedBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_inducedMarkedLogBudget_bound (C A B : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p → inducedMarkedLogBudget C A B p ≤ (p + N) ^ N := by
  let q : Polynomial ℕ := 6 * Polynomial.X + (Polynomial.X + Polynomial.C C) ^ C + 2
  let a := (q + Polynomial.C A) ^ A
  let t := a + q + 8 * Polynomial.X + 3
  let b := (t + Polynomial.C B) ^ B
  let P : Polynomial ℕ := 2 * (b + 2 * a + 8 * Polynomial.X + (Polynomial.X + 3) ^ 2 + q + 10) + 132
  obtain ⟨N, hN, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨N, hN, ?_⟩
  intro p hp
  have heq : P.eval₂ (Nat.castRingHom ℝ) p = inducedMarkedLogBudget C A B p := by
    simp [P, q, a, t, b, inducedMarkedLogBudget, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  rw [← heq]
  exact hbound p hp

theorem exists_inducedMarkedLipschitzBound_exp_bound (s u C : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (d e : ℕ) (p : ℝ) (R : ℝ≥0),
      0 ≤ p → (d : ℝ) ≤ p → (e : ℝ) ≤ p → (R : ℝ) ≤ Real.exp ((p + C) ^ C) →
      (inducedMarkedLipschitzBound s d u e p R : ℝ) ≤ Real.exp ((p + N) ^ N) := by
  obtain ⟨A, _, hsource⟩ := exists_bchBoxMetricConstant_exp_bound (s + 1) 1
  obtain ⟨B, _, htarget⟩ := exists_bchBoxMetricConstant_exp_bound u 1
  obtain ⟨N, hN, hbudget⟩ := exists_inducedMarkedLogBudget_bound C A B
  refine ⟨N, hN, ?_⟩
  intro d e p R hp hd he hR
  apply le_trans ?_ (Real.exp_le_exp.mpr (hbudget p hp))
  let r := (p + C) ^ C
  let q := 6 * p + r + 2
  let a := (q + A) ^ A
  let t := a + q + 8 * p + 3
  let b := (t + B) ^ B
  let W := b + 2 * a + 8 * p + (p + 3) ^ 2 + q + 10
  let H := ⌈Real.exp p⌉₊
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hpq : p + 1 ≤ q := by dsimp [q]; linarith
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hH : (H : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hpq)
  have hplus (x : ℝ) (hx : 0 ≤ x) : Real.exp x + 1 ≤ Real.exp (x + 1) := by
    calc
      _ ≤ Real.exp x * 2 := by linarith [Real.one_le_exp hx]
      _ ≤ Real.exp x * Real.exp 1 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hRplus : ((R + 1 : ℝ≥0) : ℝ) ≤ Real.exp (r + 1) := by
    change (R : ℝ) + 1 ≤ Real.exp (r + 1)
    exact (add_le_add hR (le_refl (1 : ℝ))).trans (hplus r hr)
  have hRq : (R : ℝ) ≤ Real.exp q := hR.trans (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  have hbox (D : ℝ≥0) (hD : (D : ℝ) ≤ Real.exp q) :
      bchBoxCoordinateBound (s + 1) d H D ≤ Real.exp a := by
    apply (bchBoxCoordinateBound_le_bchBoxMetricConstant (s + 1) d H D).trans
    apply hsource d H D q hq (hd.trans (by linarith)) hH
    simpa only [pow_one] using hD.trans (Real.exp_le_exp.mpr (by linarith : q ≤ q + 2))
  have hlog (D : ℝ≥0) (hD : (D : ℝ) ≤ Real.exp q) :
      (bchLogMetricConstant (s + 1) d H D : ℝ) ≤ Real.exp (a + 1) := by
    change bchBoxCoordinateBound (s + 1) d H D + 1 ≤ _
    exact (add_le_add (hbox D hD) (le_refl (1 : ℝ))).trans (hplus a ha)
  have hC0 : (bchLogMetricConstant (s + 1) d H 1 : ℝ) ≤ Real.exp (a + 1) :=
    hlog 1 (Real.one_le_exp hq)
  have hcoord : (phaseBandCoordinateConstant (s + 1) d H R : ℝ) ≤ Real.exp (2 * (a + 1)) := by
    change (bchLogMetricConstant (s + 1) d H R : ℝ) * (bchLogMetricConstant (s + 1) d H 1 : ℝ) ≤ _
    calc
      _ ≤ Real.exp (a + 1) * Real.exp (a + 1) :=
        mul_le_mul (hlog R hRq) hC0 (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hinput : Real.exp (5 * p) * ((R + 1 : ℝ≥0) : ℝ) ≤ Real.exp q := by
    calc
      _ ≤ Real.exp (5 * p) * Real.exp (r + 1) := mul_le_mul_of_nonneg_left hRplus (Real.exp_nonneg _)
      _ = Real.exp (5 * p + (r + 1)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [q]; linarith)
  have hret : (markedRetractionBoxConstant s d H p (R + 1) : ℝ) ≤ Real.exp (a + 5 * p) := by
    change bchBoxCoordinateBound (s + 1) d H (Real.exp (5 * p) * ((R + 1 : ℝ≥0) : ℝ)) * Real.exp (5 * p) ≤ _
    calc
      _ ≤ Real.exp a * Real.exp (5 * p) := mul_le_mul_of_nonneg_right
        (hbox ⟨Real.exp (5 * p) * ((R + 1 : ℝ≥0) : ℝ),
          mul_nonneg (Real.exp_nonneg _) (R + 1).coe_nonneg⟩ hinput) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hT : (markedEvaluationBoxRadius s d H p (R + 1) : ℝ) ≤ Real.exp t := by
    change Real.exp (2 * p) * (markedRetractionBoxConstant s d H p (R + 1) : ℝ) *
      ((R + 1 : ℝ≥0) : ℝ) + 1 ≤ _
    calc
      _ ≤ Real.exp (2 * p) * Real.exp (a + 5 * p) * Real.exp (r + 1) + 1 := by gcongr
      _ = Real.exp (a + 7 * p + r + 1) + 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (a + 7 * p + r + 1 + 1) := hplus _ (by positivity)
      _ ≤ Real.exp t := Real.exp_le_exp.mpr (by dsimp [t, q]; linarith)
  have htargetMetric : (bchBoxMetricConstant u e H (markedEvaluationBoxRadius s d H p (R + 1)) : ℝ) ≤
      Real.exp b := by
    apply htarget e H _ t ht (he.trans (by linarith)) (hH.trans (Real.exp_le_exp.mpr hqt))
    simpa only [pow_one] using hT.trans (Real.exp_le_exp.mpr (by linarith : t ≤ t + 2))
  have hlocal : (markedLocalBoxConstant s d H u e H p (R + 1) ⟨Real.exp p, Real.exp_nonneg _⟩ : ℝ) ≤
      Real.exp (b + a + 8 * p) := by
    change Real.exp p * (bchBoxMetricConstant u e H (markedEvaluationBoxRadius s d H p (R + 1)) : ℝ) *
      Real.exp (2 * p) * (markedRetractionBoxConstant s d H p (R + 1) : ℝ) ≤ _
    calc
      _ ≤ Real.exp p * Real.exp b * Real.exp (2 * p) * Real.exp (a + 5 * p) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hcoordW := hcoord.trans (Real.exp_le_exp.mpr (show 2 * (a + 1) ≤ W by dsimp [W]; nlinarith [sq_nonneg (p + 3)]))
  have hlocalW := hlocal.trans (Real.exp_le_exp.mpr (show b + a + 8 * p ≤ W by dsimp [W]; nlinarith [sq_nonneg (p + 3)]))
  have hC0W := hC0.trans (Real.exp_le_exp.mpr (show a + 1 ≤ W by dsimp [W]; nlinarith [sq_nonneg (p + 3)]))
  have hphaseW : Real.exp ((p + 3) ^ 2) ≤ Real.exp W := Real.exp_le_exp.mpr (by dsimp [W]; linarith)
  have honeW : 1 ≤ Real.exp W := Real.one_le_exp hW
  change 2 * (2 * (phaseBandCoordinateConstant (s + 1) d H R : ℝ) *
      (markedLocalBoxConstant s d H u e H p (R + 1) ⟨Real.exp p, Real.exp_nonneg _⟩ : ℝ) +
      16 * (Real.exp ((p + 3) ^ 2) + (bchLogMetricConstant (s + 1) d H 1 : ℝ) +
        (phaseBandCoordinateConstant (s + 1) d H R : ℝ) + 1)) ≤ Real.exp (2 * W + 132)
  calc
    _ ≤ 2 * (2 * Real.exp W * Real.exp W +
        16 * (Real.exp W + Real.exp W + Real.exp W + Real.exp W)) := by gcongr
    _ = 4 * Real.exp (2 * W) + 128 * Real.exp W := by
      rw [show 2 * W = W + W by ring, Real.exp_add W W]
      ring
    _ ≤ 132 * Real.exp (2 * W) := by
      have hexp : Real.exp W ≤ Real.exp (2 * W) := Real.exp_le_exp.mpr (by linarith)
      linarith
    _ ≤ Real.exp 132 * Real.exp (2 * W) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (132 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolGradeQuotientSplitting
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem realifyFunctional_eq_sum_basis {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype ι] (b : Basis ι ℚ V) (θ : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional θ x = ∑ i, (b.baseChange ℝ).repr x i * (θ (b i) : ℝ) := by
  classical
  calc
    realifyFunctional θ x = realifyFunctional θ
        (∑ i, (b.baseChange ℝ).repr x i • (b.baseChange ℝ) i) :=
      congrArg (realifyFunctional θ) ((b.baseChange ℝ).sum_repr x).symm
    _ = _ := by
      simp only [map_sum, map_smul, Basis.baseChange_apply, realifyFunctional_tmul,
        one_mul, smul_eq_mul]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_quotient_section_residual
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (U : Submodule ℚ V) (S : (V ⧸ U) →ₗ[ℚ] V)
    (hS : ∀ y, U.mkQ (S y) = y)
    (x : ℝ ⊗[ℚ] V) (a c : ℝ ⊗[ℚ] (V ⧸ U))
    (hquot : U.mkQ.baseChange ℝ x = a + c) :
    x - S.baseChange ℝ a - S.baseChange ℝ c ∈ U.baseChange ℝ := by
  have hcomp : U.mkQ.comp S = LinearMap.id := LinearMap.ext hS
  have hSr (y : ℝ ⊗[ℚ] (V ⧸ U)) :
      U.mkQ.baseChange ℝ (S.baseChange ℝ y) = y := by
    have h := congrArg (fun f => LinearMap.baseChange ℝ f) hcomp
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at h
    exact LinearMap.congr_fun h y
  have hker : U.baseChange ℝ = LinearMap.ker (U.mkQ.baseChange ℝ) := by
    simpa only [Submodule.ker_mkQ] using real_baseChange_ker U.mkQ
  rw [hker]
  change U.mkQ.baseChange ℝ (x - S.baseChange ℝ a - S.baseChange ℝ c) = 0
  rw [map_sub, map_sub, hSr, hSr, hquot]
  abel

theorem real_graded_quotient_section_residual
    {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (ω : ι → ℕ) (U : Submodule ℚ V)
    (hU : BasisGradedSubmodule b ω U)
    (S : (V ⧸ U) →ₗ[ℚ] V) (hS : ∀ y, U.mkQ (S y) = y)
    (k : ℕ) (x : ℝ ⊗[ℚ] V) (a c : ℝ ⊗[ℚ] (V ⧸ U))
    (hx : basisGradeProjection (b.baseChange ℝ) ω k x = x)
    (hquot : U.mkQ.baseChange ℝ x = a + c) :
    x - basisGradeProjection (b.baseChange ℝ) ω k (S.baseChange ℝ a) -
      basisGradeProjection (b.baseChange ℝ) ω k (S.baseChange ℝ c) ∈ U.baseChange ℝ := by
  have h := hU.baseChange b ω U k _ (real_quotient_section_residual U S hS x a c hquot)
  simpa only [map_sub, hx] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators
namespace OAI

section

namespace Erdos3

open Module

variable {R V ι κ : Type*} [Field R] [AddCommGroup V] [Module R V]

theorem fourBasisVectors_apply (D : Submodule R V) (b : Basis κ R D) (a : Σ _ : Fin 4, κ) :
    fourBasisVectors D b a = LinearMap.single R (fun _ : Fin 4 => V) a.1 (b a.2 : V) := by
  classical
  funext k
  simp only [fourBasisVectors, Function.comp_apply, LinearMap.pi_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, Pi.basis_apply, LinearMap.single_apply]
  by_cases h : k = a.1
  · subst k
    simp only [Pi.single_eq_same]
    rfl
  · simp only [Pi.single_eq_of_ne h]
    rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerDivision
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem divisionPolynomial_support {σ : Type*} (d : ℕ) (r : σ → ℤ) (i : σ) :
    divisionPolynomial d r i ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
  have hx : (MvPolynomial.X i : MvPolynomial σ ℚ) ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : σ => 1) (Finsupp.single i 1) (1 : ℚ)
  simpa only [divisionPolynomial, zero_add] using
    weightedSupportLE_mul (weightedSupportLE_C (fun _ : σ => 1) 0 (d : ℚ)⁻¹)
      (Submodule.sub_mem _ hx (weightedSupportLE_C _ 1 (r i : ℚ)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteStageNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteForwardParameter (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardParameterPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

noncomputable def preparedFiniteForwardCap (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardCapPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

noncomputable def preparedFiniteForwardCount (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardCountPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

noncomputable def preparedFiniteForwardBranch (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardBranchPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

@[simp] theorem preparedFiniteForwardParameter_zero (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (x : ℝ) :
    preparedFiniteForwardParameter A stageCountConstant 0 x = x := by
  simp [preparedFiniteForwardParameter]

theorem preparedFiniteForwardCount_eq (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardCount A stageCountConstant n x =
      preparedFiniteForwardParameter A stageCountConstant n x +
        preparedFiniteForwardCap A stageCountConstant n x := by
  simp [preparedFiniteForwardCount, preparedFiniteForwardCountPolynomial,
    preparedFiniteForwardParameter, preparedFiniteForwardCap]

theorem preparedFiniteForwardBranch_eq (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardBranch A stageCountConstant n x =
      x * preparedFiniteForwardCap A stageCountConstant n x +
        (preparedFiniteForwardCount A stageCountConstant n x + 8) ^ 8 +
        (preparedFiniteForwardCount A stageCountConstant n x + stageCountConstant n) ^
          stageCountConstant n := by
  simp [preparedFiniteForwardBranch, preparedFiniteForwardBranchPolynomial,
    preparedFiniteForwardCap, preparedFiniteForwardCount, Polynomial.eval₂_pow]

theorem preparedFiniteForwardParameter_succ (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardParameter A stageCountConstant (n + 1) x =
      preparedFiniteForwardParameter A stageCountConstant n x +
        preparedFiniteForwardCap A stageCountConstant n x +
        preparedFiniteForwardBranch A stageCountConstant n x + 1 := by
  simp [preparedFiniteForwardParameter, preparedFiniteForwardParameterPolynomial_succ,
    preparedFiniteForwardCap, preparedFiniteForwardBranch]

theorem preparedFiniteForwardParameter_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardParameter A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardCap_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardCap A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardCount_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardCount A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardBranch_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardBranch A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardParameter_strictMono (A : ℕ)
    (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x) :
    StrictMono (fun n => preparedFiniteForwardParameter A stageCountConstant n x) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [preparedFiniteForwardParameter_succ]
  have := preparedFiniteForwardCap_nonneg A stageCountConstant n hx
  have := preparedFiniteForwardBranch_nonneg A stageCountConstant n hx
  linarith

theorem preparedFiniteForwardParameter_monotone (A : ℕ)
    (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Monotone (fun n => preparedFiniteForwardParameter A stageCountConstant n x) :=
  (preparedFiniteForwardParameter_strictMono A stageCountConstant hx).monotone

theorem le_preparedFiniteForwardParameter (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ≤ preparedFiniteForwardParameter A stageCountConstant n x := by
  simpa using preparedFiniteForwardParameter_monotone A stageCountConstant hx (Nat.zero_le n)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardTreeStorage
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteForwardPrefixLog
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, preparedFiniteForwardBranch A stageCountConstant j x

noncomputable def preparedFiniteForwardCumulative
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, preparedFiniteForwardCap A stageCountConstant j x

theorem preparedFiniteForwardParameter_prefix
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardParameter A stageCountConstant n x = x +
      preparedFiniteForwardCumulative A stageCountConstant n x +
      preparedFiniteForwardPrefixLog A stageCountConstant n x + n := by
  induction n with
  | zero => simp [preparedFiniteForwardCumulative, preparedFiniteForwardPrefixLog,
      preparedFiniteForwardParameter_zero]
  | succ n ih =>
    rw [preparedFiniteForwardParameter_succ, ih]
    simp only [preparedFiniteForwardCumulative, preparedFiniteForwardPrefixLog,
      Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem preparedFiniteForward_prefix_bounds
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCumulative A stageCountConstant n x ∈
      Set.Icc 0 (preparedFiniteForwardParameter A stageCountConstant n x) ∧
    preparedFiniteForwardPrefixLog A stageCountConstant n x ∈
      Set.Icc 0 (preparedFiniteForwardParameter A stageCountConstant n x) := by
  have hc : 0 ≤ preparedFiniteForwardCumulative A stageCountConstant n x :=
    Finset.sum_nonneg (fun j _ => preparedFiniteForwardCap_nonneg A stageCountConstant j hx)
  have hb : 0 ≤ preparedFiniteForwardPrefixLog A stageCountConstant n x :=
    Finset.sum_nonneg (fun j _ => preparedFiniteForwardBranch_nonneg A stageCountConstant j hx)
  have heq := preparedFiniteForwardParameter_prefix A stageCountConstant n x
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  exact ⟨⟨hc, by linarith only [heq, hb, hx, hn]⟩,
    ⟨hb, by linarith only [heq, hc, hx, hn]⟩⟩

theorem preparedFiniteForward_branch_count_log
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x d : ℝ}
    (hx : 0 ≤ x) (hd : d ≤ x) :
    d * preparedFiniteForwardCap A stageCountConstant n x +
      (preparedFiniteForwardCount A stageCountConstant n x + 8) ^ 8 +
      (preparedFiniteForwardCount A stageCountConstant n x + stageCountConstant n) ^
        stageCountConstant n ≤ preparedFiniteForwardBranch A stageCountConstant n x := by
  rw [preparedFiniteForwardBranch_eq]
  have h := mul_le_mul_of_nonneg_right hd
    (preparedFiniteForwardCap_nonneg A stageCountConstant n hx)
  linarith only [h]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem preparedFiniteForwardCumulative_succ
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ) (x : ℝ) :
    preparedFiniteForwardCumulative A stageCountConstant (r + 1) x =
      preparedFiniteForwardCumulative A stageCountConstant r x +
        preparedFiniteForwardCap A stageCountConstant r x := by
  simp only [preparedFiniteForwardCumulative, Finset.sum_range_succ]

theorem preparedFiniteForwardCumulative_nonneg
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardCumulative A stageCountConstant r x :=
  (preparedFiniteForward_prefix_bounds A stageCountConstant r hx).1.1

theorem preparedFiniteForwardCumulative_le_succ
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCumulative A stageCountConstant r x ≤
      preparedFiniteForwardCumulative A stageCountConstant (r + 1) x := by
  rw [preparedFiniteForwardCumulative_succ]
  exact le_add_of_nonneg_right (preparedFiniteForwardCap_nonneg A stageCountConstant r hx)

theorem preparedFiniteForwardCumulative_monotone
    (A : ℕ) (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Monotone (fun r => preparedFiniteForwardCumulative A stageCountConstant r x) := by
  apply monotone_nat_of_le_succ
  intro r
  exact preparedFiniteForwardCumulative_le_succ A stageCountConstant r hx

theorem preparedFiniteForwardCap_le_cumulative_succ
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCap A stageCountConstant r x ≤
      preparedFiniteForwardCumulative A stageCountConstant (r + 1) x := by
  rw [preparedFiniteForwardCumulative_succ]
  exact le_add_of_nonneg_left (preparedFiniteForwardCumulative_nonneg A stageCountConstant r hx)

theorem preparedFiniteForwardCap_le_cumulative
    (A : ℕ) (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x)
    {j r : ℕ} (hjr : j < r) :
    preparedFiniteForwardCap A stageCountConstant j x ≤
      preparedFiniteForwardCumulative A stageCountConstant r x :=
  (preparedFiniteForwardCap_le_cumulative_succ A stageCountConstant j hx).trans
    (preparedFiniteForwardCumulative_monotone A stageCountConstant hx hjr)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardParameter_le_count
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardParameter A stageCountConstant n x ≤
      preparedFiniteForwardCount A stageCountConstant n x := by
  rw [preparedFiniteForwardCount_eq]
  exact le_add_of_nonneg_right (preparedFiniteForwardCap_nonneg A stageCountConstant n hx)

theorem le_preparedFiniteForwardCount
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ≤ preparedFiniteForwardCount A stageCountConstant n x :=
  (le_preparedFiniteForwardParameter A stageCountConstant n hx).trans
    (preparedFiniteForwardParameter_le_count A stageCountConstant n hx)

theorem preparedFiniteForwardCap_le_count
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCap A stageCountConstant n x ≤
      preparedFiniteForwardCount A stageCountConstant n x := by
  rw [preparedFiniteForwardCount_eq]
  exact le_add_of_nonneg_left (preparedFiniteForwardParameter_nonneg A stageCountConstant n hx)

theorem preparedFiniteForwardCount_le_parameter_succ
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCount A stageCountConstant n x ≤
      preparedFiniteForwardParameter A stageCountConstant (n + 1) x := by
  rw [preparedFiniteForwardCount_eq, preparedFiniteForwardParameter_succ]
  have hbranch := preparedFiniteForwardBranch_nonneg A stageCountConstant n hx
  linarith only [hbranch]

theorem preparedFiniteForwardCount_le_parameter
    (A : ℕ) (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x)
    {n depth : ℕ} (hn : n < depth) :
    preparedFiniteForwardCount A stageCountConstant n x ≤
      preparedFiniteForwardParameter A stageCountConstant depth x :=
  (preparedFiniteForwardCount_le_parameter_succ A stageCountConstant n hx).trans
    (preparedFiniteForwardParameter_monotone A stageCountConstant hx hn)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LowTaggedCoordinateRestriction
namespace OAI

section

namespace Erdos3
open Module
open scoped BigOperators

variable {B R : Type*} [Fintype B] [Field R]

theorem pi_basisGradeProjection_apply (w : B → ℕ) (h : ℕ) (x : B → R) (i : B) :
    basisGradeProjection (Pi.basisFun R B) w h x i = if w i = h then x i else 0 := by
  simpa only [Pi.basisFun_repr] using
    basisGradeProjection_repr (Pi.basisFun R B) w h x i

theorem sum_positive_coordinate_grades
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : B → R) :
    (∑ h : Fin d, basisGradeProjection (Pi.basisFun R B) w (h.val + 1) x) = x := by
  classical
  funext i
  rw [Finset.sum_apply]
  simp_rw [pi_basisGradeProjection_apply]
  let hi : Fin d := ⟨w i - 1, by have := hw i; have := hwd i; omega⟩
  have he (h : Fin d) : w i = h.val + 1 ↔ h = hi := by
    dsimp only [hi]
    have := hw i
    constructor
    · intro hh
      apply Fin.ext
      change h.val = w i - 1
      omega
    · intro hh
      subst h
      change w i = (w i - 1) + 1
      omega
  simp_rw [he]
  simp

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem lowTaggedEmbedding_restriction (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :
    lowTaggedEmbedding J d j hj (lowTaggedRestriction J d j hj z) =
      basisGradeProjection (Pi.basisFun ℝ _) (lowTaggedWeight J d) (j.val + 1) z := by
  classical
  funext i
  rw [pi_basisGradeProjection_apply]
  by_cases hi : (lowTaggedIndex J d i).1 = j
  · obtain ⟨k, rfl⟩ := lowTaggedSlot_eq_of_tag J d j hj i hi
    simp [lowTaggedWeight]
  · have hw : lowTaggedWeight J d i ≠ j.val + 1 := by
      intro hw
      apply hi
      apply Fin.ext
      exact Nat.add_right_cancel hw
    rw [lowTaggedEmbedding_apply_of_ne J d j hj _ i hi, if_neg hw]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationLogCoordinatePolynomials
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {U B κ : Type*} [Fintype B] [Fintype κ]

noncomputable def translationLogPolynomialShear (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    PolynomialShearLieAlgebra (shearWeight w d) (MvPolynomial U ℝ) :=
  ∑ k, f k • polynomialShearMap (MvPolynomial.C.comp (algebraMap ℚ ℝ))
    (weightedShearEmbedding w d (x k))

noncomputable def translationLogBasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) (i : B) :
    MvPolynomial U ℝ := ∑ k, f k * C ((x k).val.base i : ℝ)

noncomputable def translationLogPhasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    MvPolynomial B (MvPolynomial U ℝ) :=
  ∑ k, C (f k) * MvPolynomial.map (MvPolynomial.C.comp (algebraMap ℚ ℝ))
    (x k).val.polynomial

theorem translationLogPolynomialShear_base (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) (i : B) :
    (translationLogPolynomialShear w d x f).val (X (Sum.inl i)) =
      C (translationLogBasePolynomial w d x f i) := by
  classical
  simp only [translationLogPolynomialShear, translationLogBasePolynomial,
    shear_sum_apply, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro k _
  change f k • (polynomialShearMap ((C (σ := U)).comp (algebraMap ℚ ℝ))
    (weightedShearEmbedding w d (x k))).val (X (Sum.inl i)) = _
  rw [polynomialShearMap_X]
  change f k • MvPolynomial.map ((C (σ := U)).comp (algebraMap ℚ ℝ))
    (shearDerivation (x k).val (X (Sum.inl i))) = _
  rw [shearDerivation_X_inl, map_C]
  rw [← MvPolynomial.C_mul']
  rfl

theorem translationLogPolynomialShear_phase (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    (translationLogPolynomialShear w d x f).val (X (Sum.inr ())) =
      rename Sum.inl (translationLogPhasePolynomial w d x f) := by
  classical
  simp only [translationLogPolynomialShear, translationLogPhasePolynomial,
    shear_sum_apply, map_sum, map_mul, rename_C]
  apply Finset.sum_congr rfl
  intro k _
  change f k • (polynomialShearMap ((C (σ := U)).comp (algebraMap ℚ ℝ))
    (weightedShearEmbedding w d (x k))).val (X (Sum.inr ())) = _
  rw [polynomialShearMap_X]
  change f k • MvPolynomial.map ((C (σ := U)).comp (algebraMap ℚ ℝ))
    (shearDerivation (x k).val (X (Sum.inr ()))) = _
  rw [shearDerivation_X_inr, MvPolynomial.map_rename]
  exact MvPolynomial.C_mul'.symm

theorem translationLogPolynomialShear_specialize (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) (u : U → ℝ) :
    polynomialShearMap (MvPolynomial.eval u) (translationLogPolynomialShear w d x f) =
      realShearEmbedding w d (∑ k, (MvPolynomial.eval u (f k)) ⊗ₜ[ℚ] x k) := by
  classical
  have hc : (MvPolynomial.eval u).comp (C.comp (algebraMap ℚ ℝ)) = algebraMap ℚ ℝ := by
    ext r
    simp
  simp only [translationLogPolynomialShear, polynomialShearMap_sum, polynomialShearMap_smul,
    polynomialShearMap_comp, hc, map_sum, realShearEmbedding_tmul]

noncomputable def translationLogGroupPolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    PolynomialTranslationGroupOver (MvPolynomial U ℝ) B :=
  translationShearCoordinates (translationLogPolynomialShear w d x f)
    (translationLogBasePolynomial w d x f) (translationLogPhasePolynomial w d x f)
    (translationLogPolynomialShear_base w d x f) (translationLogPolynomialShear_phase w d x f)

theorem translationLogGroupPolynomial_specialize (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (MvPolynomial.eval u) (translationLogGroupPolynomial w d x f) =
      bchRealTranslationHom w d hwd
        ⟨∑ k, (MvPolynomial.eval u (f k)) ⊗ₜ[ℚ] x k⟩ := by
  apply PolynomialTranslationGroupOver.actionMonoidHom_injective
  rw [translationLogGroupPolynomial, translationShearCoordinates_map_action,
    bchRealTranslationHom_action, weightedShearRealGroupHom_apply]
  rw [translationLogPolynomialShear_specialize]
  rfl

noncomputable def translationLogMixedGroupPolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    MvPolynomial (U ⊕ B) ℝ :=
  packTranslationPolynomial (translationLogGroupPolynomial w d x f).polynomial

theorem translationLogMixedGroupPolynomial_eval (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) (u : U → ℝ) (a : B → ℝ) :
    eval (Sum.elim u a) (translationLogMixedGroupPolynomial w d x f) =
      eval a (bchRealTranslationHom w d hwd
        ⟨∑ k, (MvPolynomial.eval u (f k)) ⊗ₜ[ℚ] x k⟩).polynomial := by
  rw [translationLogMixedGroupPolynomial, packTranslationPolynomial_eval]
  congr 1
  exact congrArg PolynomialTranslationGroupOver.polynomial
    (translationLogGroupPolynomial_specialize w d hwd x f u)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationLogCoordinateInputBounds
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

namespace PolynomialTranslationLie

variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem pack_translationLogPhasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    packTranslationPolynomial (translationLogPhasePolynomial w d x f) =
      ∑ k, rename Sum.inl (f k) *
        rename Sum.inr (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) := by
  classical
  unfold translationLogPhasePolynomial
  simp only [map_sum, map_mul, packTranslationPolynomial_C]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [← MvPolynomial.map_map, packTranslationPolynomial_map_C]

theorem realPolynomialMass_translationLogBasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {M B₀ : ℝ} (hM : 0 ≤ M) (hf : ∀ k, realPolynomialMass (f k) ≤ M)
    (hx : ∀ k i, |((x k).val.base i : ℝ)| ≤ B₀) (i : B) :
    realPolynomialMass (translationLogBasePolynomial w d x f i) ≤
      (Fintype.card κ : ℝ) * M * B₀ := by
  classical
  unfold translationLogBasePolynomial
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : κ, M * B₀ := by
      apply Finset.sum_le_sum
      intro k _
      apply (realPolynomialMass_mul_le _ _).trans
      rw [realPolynomialMass_C]
      exact mul_le_mul (hf k) (hx k i) (abs_nonneg _) hM
    _ = _ := by simp; ring

theorem realPolynomialMass_pack_translationLogPhasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {M B₀ : ℝ} (hM : 0 ≤ M) (hf : ∀ k, realPolynomialMass (f k) ≤ M)
    (hx : ∀ k, realPolynomialMass
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) ≤ B₀) :
    realPolynomialMass (packTranslationPolynomial (translationLogPhasePolynomial w d x f)) ≤
      (Fintype.card κ : ℝ) * M * B₀ := by
  classical
  rw [pack_translationLogPhasePolynomial]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : κ, M * B₀ := by
      apply Finset.sum_le_sum
      intro k _
      exact (realPolynomialMass_mul_le _ _).trans
        (mul_le_mul ((realPolynomialMass_rename_le _ _).trans (hf k))
          ((realPolynomialMass_rename_le _ _).trans (hx k)) (realPolynomialMass_nonneg _) hM)
    _ = _ := by simp; ring

theorem weightedSubalgebra_realPolynomial_degreeOf_le (w : B → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d) (i : B) :
    (MvPolynomial.map (algebraMap ℚ ℝ) x.val.polynomial).degreeOf i ≤ d := by
  classical
  rw [degreeOf_eq_sup]
  apply Finset.sup_le
  intro α hα
  have hs := MvPolynomial.support_map_subset (algebraMap ℚ ℝ) x.val.polynomial hα
  have hx := x.property.2 hs
  change Finsupp.weight w α + 1 ≤ d at hx
  have hαi := Finsupp.le_weight w (hw i).ne' α
  exact hαi.trans (by omega)

theorem degreeOf_pack_translationLogPhasePolynomial (w : B → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) (i : B) :
    (packTranslationPolynomial (translationLogPhasePolynomial w d x f)).degreeOf
      (Sum.inr i) ≤ d := by
  classical
  rw [pack_translationLogPhasePolynomial]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro k _
  apply (degreeOf_mul_le _ _ _).trans
  rw [degreeOf_rename_inl_inr, zero_add,
    degreeOf_rename_of_injective Sum.inr_injective i]
  exact weightedSubalgebra_realPolynomial_degreeOf_le w d hw (x k) i

theorem realPolynomialMass_translationLogDirectionalSeries (w : B → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) {M B₀ : ℝ} (hM : 0 ≤ M) (hB₀ : 0 ≤ B₀)
    (hf : ∀ k, realPolynomialMass (f k) ≤ M)
    (hbase : ∀ k i, |((x k).val.base i : ℝ)| ≤ B₀)
    (hphase : ∀ k, realPolynomialMass
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) ≤ B₀) :
    realPolynomialMass (translationDirectionalSeries d (translationLogBasePolynomial w d x f)
      (packTranslationPolynomial (translationLogPhasePolynomial w d x f))) ≤
      ((d : ℝ) + 1) * ((Fintype.card κ : ℝ) * M * B₀) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card κ : ℝ) * M * B₀)) ^ d := by
  exact realPolynomialMass_translationDirectionalSeries d _ _
    (degreeOf_pack_translationLogPhasePolynomial w d hw x f) (by positivity)
    (realPolynomialMass_translationLogBasePolynomial w d x f hM hf hbase)
    (realPolynomialMass_pack_translationLogPhasePolynomial w d x f hM hf hphase)

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.TranslationLogCoordinateInputGrid
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped BigOperators

variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem translationLogBasePolynomial_coefficientGrid (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {q l : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q (f k))
    (hbase : ∀ k i, ∃ z : ℤ, (z : ℝ) = (l : ℝ) * ((x k).val.base i : ℝ))
    (i : B) :
    realPolynomialCoefficientGrid (q * l) (translationLogBasePolynomial w d x f i) := by
  unfold translationLogBasePolynomial
  exact realPolynomialCoefficientGrid_sum Finset.univ _ fun k _ =>
    realPolynomialCoefficientGrid_mul (hf k) (constant_coefficientGrid (hbase k i))

theorem pack_translationLogPhasePolynomial_coefficientGrid (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {q l : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q (f k))
    (hphase : ∀ k, realPolynomialCoefficientGrid l
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial)) :
    realPolynomialCoefficientGrid (q * l)
      (packTranslationPolynomial (translationLogPhasePolynomial w d x f)) := by
  rw [pack_translationLogPhasePolynomial]
  exact realPolynomialCoefficientGrid_sum Finset.univ _ fun k _ =>
    realPolynomialCoefficientGrid_mul (realPolynomialCoefficientGrid_rename Sum.inl (hf k))
      (realPolynomialCoefficientGrid_rename Sum.inr (hphase k))

theorem translationLogDirectionalSeries_coefficientGrid (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {q l : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q (f k))
    (hbase : ∀ k i, ∃ z : ℤ, (z : ℝ) = (l : ℝ) * ((x k).val.base i : ℝ))
    (hphase : ∀ k, realPolynomialCoefficientGrid l
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial)) :
    realPolynomialCoefficientGrid (d.factorial * (q * l) ^ (d + 1))
      (translationDirectionalSeries d (translationLogBasePolynomial w d x f)
        (packTranslationPolynomial (translationLogPhasePolynomial w d x f))) :=
  translationDirectionalSeries_coefficientGrid d _ _
    (translationLogBasePolynomial_coefficientGrid w d x f hf hbase)
    (pack_translationLogPhasePolynomial_coefficientGrid w d x f hf hphase)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationLogCoordinateScaling
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial
open scoped BigOperators
variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem translationLogMixedGroupPolynomial_eq_series (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) :
    translationLogMixedGroupPolynomial w d x f =
      translationDirectionalSeries d (translationLogBasePolynomial w d x f)
        (packTranslationPolynomial (translationLogPhasePolynomial w d x f)) := by
  have hweights : ∀ i, shearWeight w d i ≤ d := by
    intro i
    cases i with
    | inl i => exact hwd i
    | inr i => exact le_rfl
  unfold translationLogMixedGroupPolynomial translationLogGroupPolynomial
  rw [translationShearCoordinates_polynomial_series (shearWeight w d) d hweights]
  simp only [shearWeight, translationDirectionalSeries, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_rat_smul, packTranslationPolynomial_baseDerivative_pow]
  rw [← algebraMap_smul ℝ ((-1 : ℚ) ^ k / ((k + 1).factorial : ℚ))]
  congr 1
  simp only [map_div₀, map_pow, map_neg, map_one, map_natCast]

theorem realPolynomialMass_translationLogMixedGroupPolynomial (w : B → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {M B₀ : ℝ} (hM : 0 ≤ M) (hB₀ : 0 ≤ B₀)
    (hf : ∀ k, realPolynomialMass (f k) ≤ M)
    (hbase : ∀ k i, |((x k).val.base i : ℝ)| ≤ B₀)
    (hphase : ∀ k, realPolynomialMass
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) ≤ B₀) :
    realPolynomialMass (translationLogMixedGroupPolynomial w d x f) ≤
      ((d : ℝ) + 1) * ((Fintype.card κ : ℝ) * M * B₀) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card κ : ℝ) * M * B₀)) ^ d := by
  rw [translationLogMixedGroupPolynomial_eq_series w d hwd]
  exact realPolynomialMass_translationLogDirectionalSeries w d hw x f hM hB₀ hf hbase hphase

theorem translationLogMixedGroupPolynomial_coefficientGrid_of_inputs
    (w : B → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {q l : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q (f k))
    (hbase : ∀ k i, ∃ z : ℤ, (z : ℝ) = (l : ℝ) * ((x k).val.base i : ℝ))
    (hphase : ∀ k, realPolynomialCoefficientGrid l
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial)) :
    realPolynomialCoefficientGrid (d.factorial * (q * l) ^ (d + 1))
      (translationLogMixedGroupPolynomial w d x f) := by
  rw [translationLogMixedGroupPolynomial_eq_series w d hwd]
  exact translationLogDirectionalSeries_coefficientGrid w d x f hf hbase hphase

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial
open scoped BigOperators
variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem translationLogMixedGroupPolynomial_scale (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) (H : U → ℝ) :
    scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (translationLogMixedGroupPolynomial w d x f) =
    translationLogMixedGroupPolynomial w d x (fun k => scaleMvPolynomialAxes H (f k)) := by
  apply MvPolynomial.funext
  intro z
  let u : U → ℝ := fun i => z (Sum.inl i)
  let a : B → ℝ := fun i => z (Sum.inr i)
  have hz : z = Sum.elim u a := by funext i; cases i <;> rfl
  rw [hz, scaleMvPolynomialAxes_eval]
  have he : (fun i => Sum.elim H (fun _ : B => (1 : ℝ)) i * Sum.elim u a i) =
      Sum.elim (fun i => H i * u i) a := by
    funext i
    cases i <;> simp
  rw [he, translationLogMixedGroupPolynomial_eval w d hwd,
    translationLogMixedGroupPolynomial_eval w d hwd]
  simp only [scaleMvPolynomialAxes_eval]

theorem realPolynomialMass_translationLogMixedGroupPolynomial_scale
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    (H : U → ℝ) {M B₀ : ℝ} (hM : 0 ≤ M) (hB₀ : 0 ≤ B₀)
    (hf : ∀ k, realPolynomialMass (scaleMvPolynomialAxes H (f k)) ≤ M)
    (hbase : ∀ k i, |((x k).val.base i : ℝ)| ≤ B₀)
    (hphase : ∀ k, realPolynomialMass
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) ≤ B₀) :
    realPolynomialMass (scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (translationLogMixedGroupPolynomial w d x f)) ≤
      ((d : ℝ) + 1) * ((Fintype.card κ : ℝ) * M * B₀) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card κ : ℝ) * M * B₀)) ^ d := by
  rw [translationLogMixedGroupPolynomial_scale w d hwd]
  exact realPolynomialMass_translationLogMixedGroupPolynomial w d hw hwd x _
    hM hB₀ hf hbase hphase

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LowTaggedCoordinateProjection
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem lowTaggedCoordinates_projection (d : ℕ) (x : ∀ j, J j → ℝ)
    (j : Fin m) (hj : j.val + 1 ≤ d) :
    basisGradeProjection (Pi.basisFun ℝ _) (lowTaggedWeight J d) (j.val + 1)
        (lowTaggedCoordinates J d x) =
      lowTaggedEmbedding J d j hj (x j) := by
  classical
  funext i
  rw [pi_basisGradeProjection_apply]
  by_cases hi : (lowTaggedIndex J d i).1 = j
  · obtain ⟨k, hk⟩ := lowTaggedSlot_eq_of_tag J d j hj i hi
    subst i
    simp [lowTaggedWeight]
  · have hweight : lowTaggedWeight J d i ≠ j.val + 1 := by
      intro he
      apply hi
      apply Fin.ext
      unfold lowTaggedWeight at he
      omega
    rw [if_neg hweight, lowTaggedEmbedding_apply_of_ne J d j hj _ i hi]

theorem lowTaggedCoordinates_projection_eq_zero (d : ℕ) (x : ∀ j, J j → ℝ)
    (h : ℕ) (hm : m ≤ h) :
    basisGradeProjection (Pi.basisFun ℝ _) (lowTaggedWeight J d) (h + 1)
      (lowTaggedCoordinates J d x) = 0 := by
  classical
  funext i
  rw [pi_basisGradeProjection_apply]
  have hweight : lowTaggedWeight J d i ≠ h + 1 := by
    have hi := (lowTaggedIndex J d i).1.isLt
    unfold lowTaggedWeight
    omega
  simp only [hweight, ite_false, Pi.zero_apply]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CanonicalReducedMajorTwistedNiltest
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

variable {U : Type*} {m : ℕ}

theorem majorZeroParameterSlice_degree (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
    {d : ℕ} {D : MvPolynomial (U ⊕ Fin m) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    (specializeMajorParameters (RingHom.id ℝ) D 0).totalDegree ≤ d := by
  rw [majorZeroParameterSlice_eq]
  apply totalDegree_le_of_positive_weightedSupport w hw
  apply weightedSupportLE_aeval _ _ _ _ hD
  intro i
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr i => exact weightedSupportLE_X w i

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem fractionalCoefficientPolynomial_mem_weightedSupportLE {σ : Type*}
    (D : MvPolynomial σ ℝ) (w : σ → ℕ) (d : ℕ)
    (hD : D ∈ weightedSupportLE w d) :
    fractionalCoefficientPolynomial D ∈ weightedSupportLE w d := by
  intro a ha
  apply hD
  apply mem_support_iff.mpr
  intro hz
  change D.coeff a = 0 at hz
  have hcoeff := mem_support_iff.mp ha
  apply hcoeff
  change (fractionalCoefficientPolynomial D).coeff a = 0
  simp only [fractionalCoefficientPolynomial_coeff, hz, Int.fract_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPhasePairFunctionalBounds
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module _root_.MvPolynomial PolynomialTranslationLie

theorem polynomial_eq_constant (P : MvPolynomial (Fin 0) ℚ) :
    P = C (P.coeff 0) := by
  ext α
  have hα : α = 0 := Subsingleton.elim _ _
  subst α
  simp

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end


