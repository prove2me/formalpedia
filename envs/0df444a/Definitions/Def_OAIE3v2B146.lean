-- Prove2me | Definitions.Def_OAIE3v2B146
-- name    : OAIE3v2B146
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:17:55.020719+00:00
-- url     : https://prove2.me/theorems/4f35894e-d4bb-4946-9b0b-bf8372a8eccd
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 148 of 311
-- statement:
--   Definitions bundle 148 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B123`, `OAIE3v2B128`, `OAIE3v2B129`, `OAIE3v2B130`, `OAIE3v2B131`, `OAIE3v2B132`, `OAIE3v2B133`, `OAIE3v2B134`, `OAIE3v2B135` of this split.
--
--   Modules: `Estimates/AnchoredSparseFamilies.lean`, `Estimates/FixedObservableCorrelation.lean`, `Estimates/FormalCurrentDerivativeAdvance.lean`, `Estimates/NativeEquivalenceTransitivity.lean`, `Estimates/NativePositiveCoefficientBases.lean`, `Estimates/NativeProductCoefficient.lean`, `Estimates/NativeSquarefreeCoefficientBases.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/ReducedNativeFactorization.lean`, `Estimates/SquarefreeRealAction.lean`, `Estimates/StepDropTerminalContainment.lean`, `Estimates/UnconditionalStepDrop.lean`, `Geometry/BoundedDependentCoordinates.lean`, `Geometry/HorizontalCoordinateBounds.lean`, `Geometry/SparseCoordinateCorrections.lean`, `Lattices/NativeIntegerAffinePullbackHom.lean`, `Lattices/RealifiedSubgroupLattice.lean`, `Linear/ComparisonChosenLayerBasis.lean`, `Linear/NativePrescribedProjection.lean`, `Linear/RankQuotientHeightBudget.lean`, `Linear/RealSparseFourProjection.lean`, `Nilpotent/NiltestAffineProjection.lean`, `Polynomial/ControlledPositivePolynomialDownsets.lean`, `Polynomial/MarkedPolynomialGenerators.lean`, `Polynomial/NativeDegreePowerBound.lean`, `Polynomial/NativeTotalDegreeMultifiltration.lean`, `Polynomial/PolynomialDerivativeBounds.lean`, `Sampling/NativeSquarefreeGrids.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B123
import Definitions.Def_OAIE3v2B128
import Definitions.Def_OAIE3v2B129
import Definitions.Def_OAIE3v2B130
import Definitions.Def_OAIE3v2B131
import Definitions.Def_OAIE3v2B132
import Definitions.Def_OAIE3v2B133
import Definitions.Def_OAIE3v2B134
import Definitions.Def_OAIE3v2B135

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realificationMap_incl_mem (K : LieSubalgebra ℚ L)
    (x : NilpotentLieBCHGroup (ℝ ⊗[ℚ] K) s
      (realification_lowerCentralSeries_eq_bot (lie_subalgebra_lowerCentralSeries_eq_bot hnil K))) :
    realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl x ∈
      realificationSubgroup (hnil := hnil) K :=
  ⟨x.coord, rfl⟩

theorem realificationMap_incl_range (K : LieSubalgebra ℚ L) :
    (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl).range =
      realificationSubgroup (hnil := hnil) K := by
  ext g
  change (∃ x, realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
    (hM := hnil) K.incl x = g) ↔ ∃ y, realificationLieHom K.incl y = g.coord
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.coord, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨⟨y⟩, ext hy⟩

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem mem_real_symbolPointwiseSubalgebra_iff_values
    (U : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w) :
    x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hlayers w U) ↔
      ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x) ∈
        realificationLieSubalgebra U := by
  rw [F.mem_real_symbolPointwiseSubalgebra_iff_coefficients]
  exact (eval₂_mem_iff_coefficients (realificationLieSubalgebra U).toSubmodule _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RealifiedSubgroupLattice
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realificationSubgroupHom (K : LieSubalgebra ℚ L) :
    NilpotentLieBCHGroup (ℝ ⊗[ℚ] K) s
      (realification_lowerCentralSeries_eq_bot (lie_subalgebra_lowerCentralSeries_eq_bot hnil K)) →*
      realificationSubgroup (hnil := hnil) K :=
  (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
    (hM := hnil) K.incl).codRestrict _ (realificationMap_incl_mem (hnil := hnil) K)

theorem realificationSubgroupHom_surjective (K : LieSubalgebra ℚ L) :
    Function.Surjective (realificationSubgroupHom (hnil := hnil) K) := by
  intro g
  have hg : g.1 ∈ (realificationMap
      (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl).range := by
    rw [realificationMap_incl_range]
    exact g.2
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, Subtype.ext hx⟩

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ : Type*} [Fintype ι]

theorem realCoordinate_projection (x : ℝ ⊗[ℚ] (Fin 4 → ι → ℚ)) (k : Fin 4) (i : ι) :
    realRationalCoordinateEquiv ((LinearMap.proj k).baseChange ℝ x) i =
      DegreeRankLieFiltration.realFourCoordinateEquiv x ⟨k, i⟩ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, realRationalCoordinateEquiv_tmul, realFourCoordinateEquiv_tmul]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem realFourCoordinateSpan_span (v : κ → Fin 4 → ι → ℚ) :
    realFourCoordinateSpan (Submodule.span ℚ (Set.range v)) =
      Submodule.span ℝ (Set.range (fun a (j : Σ _ : Fin 4, ι) => (v a j.1 j.2 : ℝ))) := by
  unfold realFourCoordinateSpan
  rw [Submodule.baseChange_span, Submodule.map_span, Set.image_image]
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    funext j
    change (v a j.1 j.2 : ℝ) =
      DegreeRankLieFiltration.realFourCoordinateEquiv (1 ⊗ₜ[ℚ] v a) j
    simpa only [one_mul] using (realFourCoordinateEquiv_tmul (1 : ℝ) (v a) j).symm
  · rintro ⟨a, rfl⟩
    refine ⟨v a, ⟨a, rfl⟩, ?_⟩
    funext j
    change DegreeRankLieFiltration.realFourCoordinateEquiv (1 ⊗ₜ[ℚ] v a) j =
      (v a j.1 j.2 : ℝ)
    simpa only [one_mul] using realFourCoordinateEquiv_tmul (1 : ℝ) (v a) j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealSparseFourProjection
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {ι : Type*} [Fintype ι]

theorem real_fourCoordinateKernel_mem_iff (S : Finset (Fin 4))
    (x : ℝ ⊗[ℚ] (Fin 4 → ι → ℚ)) :
    x ∈ (fourCoordinateKernel (V := ι → ℚ) S).baseChange ℝ ↔
      ∀ k ∈ S, ∀ i, DegreeRankLieFiltration.realFourCoordinateEquiv x ⟨k, i⟩ = 0 := by
  have hker : fourCoordinateKernel (V := ι → ℚ) S =
      ⨅ k : S, LinearMap.ker (LinearMap.proj (k : Fin 4) : (Fin 4 → ι → ℚ) →ₗ[ℚ] (ι → ℚ)) := by
    ext v
    constructor
    · intro hv
      apply (Submodule.mem_iInf _).mpr
      intro k
      exact (mem_fourCoordinateKernel S v).mp hv k k.property
    · intro hv
      apply (mem_fourCoordinateKernel S v).mpr
      intro k hk
      exact (Submodule.mem_iInf _).mp hv ⟨k, hk⟩
  rw [hker, real_baseChange_iInf]
  constructor
  · intro hx k hk i
    have hz := (Submodule.mem_iInf _).mp hx ⟨k, hk⟩
    rw [realification_ker] at hz
    have hzero : (LinearMap.proj k : (Fin 4 → ι → ℚ) →ₗ[ℚ] (ι → ℚ)).baseChange ℝ x = 0 := hz
    rw [← realCoordinate_projection]
    simpa only [map_zero, Pi.zero_apply] using
      congrFun (congrArg realRationalCoordinateEquiv hzero) i
  · intro hx
    apply (Submodule.mem_iInf _).mpr
    intro k
    rw [realification_ker]
    change (LinearMap.proj (k : Fin 4) : (Fin 4 → ι → ℚ) →ₗ[ℚ] (ι → ℚ)).baseChange ℝ x = 0
    apply realRationalCoordinateEquiv.injective
    funext i
    simpa only [map_zero, Pi.zero_apply, realCoordinate_projection] using hx k k.property i

theorem mem_realSparseFirstProjection_of_zero
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (S : Finset (Fin 4))
    (y : (Σ _ : Fin 4, ι) → ℝ) (hy : y ∈ realFourCoordinateSpan J)
    (hzero : ∀ k ∈ S, ∀ i, y ⟨k, i⟩ = 0) :
    (fun i => y ⟨0, i⟩) ∈ realRationalCoordinateSpan (fourSparseFirstProjection J S) := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hxK := (real_fourCoordinateKernel_mem_iff S x).mpr hzero
  have hxJK : x ∈ (J ⊓ fourCoordinateKernel S).baseChange ℝ := by
    rw [realification_inf]
    exact ⟨hx, hxK⟩
  have hproj : (LinearMap.proj (0 : Fin 4)).baseChange ℝ x ∈
      (fourSparseFirstProjection J S).baseChange ℝ := by
    change _ ∈ ((J ⊓ fourCoordinateKernel S).map (LinearMap.proj 0)).baseChange ℝ
    rw [realification_map]
    exact ⟨x, hxJK, rfl⟩
  have hmem : realRationalCoordinateEquiv ((LinearMap.proj (0 : Fin 4)).baseChange ℝ x) ∈
      realRationalCoordinateSpan (fourSparseFirstProjection J S) := ⟨_, hproj, rfl⟩
  have heq : realRationalCoordinateEquiv ((LinearMap.proj (0 : Fin 4)).baseChange ℝ x) =
      fun i => DegreeRankLieFiltration.realFourCoordinateEquiv x ⟨0, i⟩ := by
    funext i
    exact realCoordinate_projection x 0 i
  rwa [heq] at hmem

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SparseCoordinateCorrections
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_sparse_coordinate_corrections
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ p)
    (hK : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 →
      ∀ (a b : (Σ _ : K, ι) → ℝ) (x : (Σ _ : Fin 4, ι) → ℝ),
        x ∈ realFourCoordinateSpan J →
        ‖a‖ ≤ Real.exp p / monomialScale T α → b ∈ realDenominatorGrid l →
        (∀ j : Σ _ : K, ι, x ⟨j.1, j.2⟩ = a j + b j) →
        ∃ e q : (Σ _ : Fin 4, ι) → ℝ,
          e ∈ realFourCoordinateSpan J ∧ q ∈ realFourCoordinateSpan J ∧
          (∀ j : Σ _ : K, ι, e ⟨j.1, j.2⟩ = a j) ∧
          (∀ j : Σ _ : K, ι, q ⟨j.1, j.2⟩ = b j) ∧
          ‖e‖ ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
          q ∈ realDenominatorGrid m ∧
          x - e - q ∈ realFourCoordinateSpan J ∧
          (fun i => (x - e - q) ⟨0, i⟩) ∈
            realRationalCoordinateSpan (fourSparseFirstProjection J K) := by
  let A : Matrix (Σ _ : Fin 4, ι) κ ℚ := fun j a => v a j.1 j.2
  let ρ : (Σ _ : K, ι) → (Σ _ : Fin 4, ι) := fun j => ⟨j.1, j.2⟩
  have hspan : realFourCoordinateSpan J =
      LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
    ext x
    rw [← hv, realFourCoordinateSpan_span]
    exact real_column_span_mem_iff A x
  obtain ⟨S, m, hm, hmp, hsolve⟩ := exists_selected_image_corrections A ρ hH hl
    (fun i a => hvH a i.1 i.2) hp hι hK hκ hHp hlp T hT
  refine ⟨m, hm, hmp, ?_⟩
  intro α hα a b x hx ha hb hselect
  obtain ⟨he, hq, heq, hqq, hslow, hgrid, hrem, hzero⟩ :=
    hsolve α hα a b x (hspan ▸ hx) ha hb hselect
  refine ⟨_, _, hspan.symm ▸ he, hspan.symm ▸ hq, heq, hqq, hslow, hgrid,
    hspan.symm ▸ hrem, ?_⟩
  apply mem_realSparseFirstProjection_of_zero J K _ (hspan.symm ▸ hrem)
  intro k hk i
  exact hzero ⟨⟨k, hk⟩, i⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnchoredSparseFamilies
namespace OAI

section

namespace Erdos3

theorem exists_anchored_sparse_corrections
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ p)
    (hK : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 →
      ∀ (u u₀ E E₀ Q Q₀ : (Σ _ : Fin 4, ι) → ℝ),
        u - E - Q ∈ realFourCoordinateSpan J →
        u₀ - E₀ - Q₀ ∈ realFourCoordinateSpan J →
        (∀ j : Σ _ : K, ι, u ⟨j.1, j.2⟩ = u₀ ⟨j.1, j.2⟩) →
        ‖E - E₀‖ ≤ Real.exp p / monomialScale T α →
        Q ∈ realDenominatorGrid l → Q₀ ∈ realDenominatorGrid l →
        ∃ e q : (Σ _ : Fin 4, ι) → ℝ,
          ‖e‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) /
            monomialScale T α ∧
          q ∈ realDenominatorGrid m ∧
          (fun i => (u - u₀ - e - q) ⟨0, i⟩) ∈
            realRationalCoordinateSpan (fourSparseFirstProjection J K) := by
  obtain ⟨m, hm, hmp, hsolve⟩ := exists_sparse_coordinate_corrections J K v hv hH hl hvH
    hp hι hK hκ hHp hlp T hT
  refine ⟨l * m, Nat.mul_pos hl hm, ?_, dvd_mul_right l m, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hlp hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro α hα u u₀ E E₀ Q Q₀ hu hu₀ hanchor hE hQ hQ₀
    let ρ : (Σ _ : K, ι) → (Σ _ : Fin 4, ι) := fun j => ⟨j.1, j.2⟩
    let x := (u - E - Q) - (u₀ - E₀ - Q₀)
    let a := (E₀ - E) ∘ ρ
    let b := (Q₀ - Q) ∘ ρ
    have hx : x ∈ realFourCoordinateSpan J := Submodule.sub_mem _ hu hu₀
    have ha : ‖a‖ ≤ Real.exp p / monomialScale T α := by
      apply (pi_norm_restriction_le (E₀ - E) ρ).trans
      simpa only [norm_sub_rev] using hE
    have hb : b ∈ realDenominatorGrid l :=
      realDenominatorGrid_comp l _ (realDenominatorGrid_sub l Q₀ Q hQ₀ hQ) ρ
    have hselect (j : Σ _ : K, ι) : x ⟨j.1, j.2⟩ = a j + b j := by
      change (u ⟨j.1, j.2⟩ - E ⟨j.1, j.2⟩ - Q ⟨j.1, j.2⟩) -
        (u₀ ⟨j.1, j.2⟩ - E₀ ⟨j.1, j.2⟩ - Q₀ ⟨j.1, j.2⟩) =
        (E₀ ⟨j.1, j.2⟩ - E ⟨j.1, j.2⟩) + (Q₀ ⟨j.1, j.2⟩ - Q ⟨j.1, j.2⟩)
      rw [hanchor j]
      ring
    obtain ⟨e, q, _, _, _, _, he, hq, _, hrem⟩ := hsolve α hα a b x hx ha hb hselect
    refine ⟨E - E₀ + e, Q - Q₀ + q, ?_, ?_, ?_⟩
    · calc
        ‖E - E₀ + e‖ ≤ ‖E - E₀‖ + ‖e‖ := norm_add_le _ _
        _ ≤ Real.exp p / monomialScale T α +
            Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α :=
          add_le_add hE he
        _ = _ := (add_div _ _ _).symm
    · simpa only [sub_neg_eq_add] using realDenominatorGrid_sub_product l m
        (Q - Q₀) (-q) (realDenominatorGrid_sub l Q Q₀ hQ hQ₀) (realDenominatorGrid_neg m hq)
    · have heq : u - u₀ - (E - E₀ + e) - (Q - Q₀ + q) = x - e - q := by
        funext j
        change u j - u₀ j - (E j - E₀ j + e j) - (Q j - Q₀ j + q j) =
          ((u j - E j - Q j) - (u₀ j - E₀ j - Q₀ j)) - e j - q j
        ring
      simpa only [heq] using hrem

end Erdos3

end

section

namespace Erdos3

theorem exists_anchored_sparse_family
    {ι κ σ η : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p) (hfour : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ p)
    (hK : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p) (hcols : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 →
      ∀ (u : η → (Σ _ : Fin 4, ι) → ℝ) (β : η → ι → ℝ) (a₀ : η) (M : ℝ),
        2 * M ≤ Real.exp p →
        (∀ a i, u a ⟨0, i⟩ = β a i) →
        (∀ a (j : Σ _ : K, ι), u a ⟨j.1, j.2⟩ = u a₀ ⟨j.1, j.2⟩) →
        (∀ a, ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
          ‖E‖ ≤ M / monomialScale T α ∧ Q ∈ realDenominatorGrid l ∧
          u a - E - Q ∈ realFourCoordinateSpan J) →
        ∀ a, ∃ e q : ι → ℝ,
          ‖e‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) /
            monomialScale T α ∧ q ∈ realDenominatorGrid m ∧
          β a - β a₀ - e - q ∈ realRationalCoordinateSpan (fourSparseFirstProjection J K) := by
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_anchored_sparse_corrections J K v hv hH hl hvH
    hp hfour hK hcols hHp hlp T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α hα u β a₀ M hM hfirst hanchor hcorrect a
  obtain ⟨E₀, Q₀, hE₀, hQ₀, hu₀⟩ := hcorrect a₀
  obtain ⟨E, Q, hE, hQ, hu⟩ := hcorrect a
  have hscale : 0 < monomialScale T α :=
    monomialScale_pos T (fun i => (Real.exp_pos _).trans_le (hT i)) α
  have hdiff : ‖E - E₀‖ ≤ Real.exp p / monomialScale T α := by
    calc
      ‖E - E₀‖ ≤ ‖E‖ + ‖E₀‖ := norm_sub_le _ _
      _ ≤ M / monomialScale T α + M / monomialScale T α := add_le_add hE hE₀
      _ = (2 * M) / monomialScale T α := by ring
      _ ≤ Real.exp p / monomialScale T α := div_le_div_of_nonneg_right hM hscale.le
  obtain ⟨e, q, he, hq, hrem⟩ :=
    hsolve α hα (u a) (u a₀) E E₀ Q Q₀ hu hu₀ (hanchor a) hdiff hQ hQ₀
  refine ⟨(fun i => e ⟨0, i⟩), (fun i => q ⟨0, i⟩),
    (pi_norm_restriction_le e (fun i => ⟨0, i⟩)).trans he,
    realDenominatorGrid_comp m q hq (fun i => ⟨0, i⟩), ?_⟩
  have heq : (fun i => (u a - u a₀ - e - q) ⟨0, i⟩) =
      β a - β a₀ - (fun i => e ⟨0, i⟩) - (fun i => q ⟨0, i⟩) := by
    funext i
    simp only [Pi.sub_apply, hfirst]
  rwa [heq] at hrem

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_native_factor_partitions (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} [Fintype α] [DecidableEq α]
      {L : α → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : α → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {p rho : ℝ},
      0 ≤ p → (Fintype.card α : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < rho → 1 / rho ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (D i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧
            (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ i j x y, 0 < ψ i j x → 0 < ψ i j y → dist x y ≤ rho := by
  obtain ⟨c, _, hpart⟩ := exists_native_positive_partition s a
  let R : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Polynomial.X * R + R)
  refine ⟨C, hC, ?_⟩
  intro α _ _ L _ _ _ _ _ _ d D p rho hp hα hD hrho hscale
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  choose n hn hnb K hKb ψ hunit hsum hLip hdiam using
    (fun i => hpart (D i) hp (hD i) hrho hscale)
  have hR : 0 ≤ (p + c) ^ c := pow_nonneg (add_nonneg hp (Nat.cast_nonneg c)) _
  have hbudget' : p * (p + c) ^ c + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [R, Polynomial.eval₂_pow] using hbudget p hp
  have hsmall : (p + c) ^ c ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (mul_nonneg hp hR)).trans hbudget'
  have hlarge : p * (p + c) ^ c ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right hR).trans hbudget'
  refine ⟨n, hn, fun i => (hnb i).trans (Real.exp_le_exp.mpr hsmall),
    (pi_fin_card_le_exp n hR hα hnb).trans (Real.exp_le_exp.mpr hlarge),
    K, fun i => (hKb i).trans (Real.exp_le_exp.mpr hsmall), ψ, hunit, hsum, hLip, hdiam⟩

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalCurrentDerivativeAdvance
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_current_derivative_advance
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ)
    (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hvanish : ∀ i α, coefficients
        (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
          (dualAdjoint A⁻¹ (small i - formalLogDerivative i A))) α ∈ V ∧
      coefficients (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
          (dualAdjoint B (rational i) - formalLogDerivative i B)) α ∈ V) :
    ∀ i α,
      coefficients (dualAdjoint A⁻¹ (small i - formalLogDerivative i A)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
      coefficients (dualAdjoint B (rational i) - formalLogDerivative i B) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  let W := V.restrictScalars ℚ ⊔ F.realification.layer j
  have hWiff (x : ℝ ⊗[ℚ] L) : x ∈ W ↔ x ∈ V ⊔ (F.realLayer j).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer j).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have advance (x : ℝ ⊗[ℚ] L) (hx : x ∈ W)
      (hπ : basisGradeProjection (b.baseChange ℝ) w j x ∈ V) :
      x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    have hrem := F.real_sub_grade_mem_sup_next b w hlayers V hV j x ((hWiff x).mp hx)
    have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem hrem (Submodule.mem_sup_left hπ)
    simpa only [sub_add_cancel] using h
  intro i α
  have hpres := polynomial_derivative_removal_preserves_coefficients U W
    (F.realification.invariant_sup_layer U (V.restrictScalars ℚ) hUV j)
    i A B (small i) (rational i) hAU hBU
    (fun β => Submodule.mem_sup_right (hA β)) (fun β => Submodule.mem_sup_right (hB β))
    (fun β => (hWiff _).mpr (hsmall i β)) (fun β => (hWiff _).mpr (hrational i β))
  have hv := hvanish i α
  simp only [coefficients_map, LinearMap.restrictScalars_apply] at hv
  exact ⟨advance _ (hpres.1 α) hv.1, advance _ (hpres.2 α) hv.2⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeEquivalenceTransitivity
namespace OAI

section

namespace Erdos3.NativeVectorEquivalence

variable {J K : Type*} [Fintype J] [Fintype K] {s N : ℕ} [NeZero N] {p q : ℝ}
  {chi : J → ZMod N → ℂ} {chi' : K → ZMod N → ℂ}

theorem mono (E : NativeVectorEquivalence s N p chi chi') (hpq : p ≤ q) :
    NativeVectorEquivalence s N q chi chi' where
  left_dimension := E.left_dimension.trans (Real.exp_le_exp.mpr hpq)
  right_dimension := E.right_dimension.trans (Real.exp_le_exp.mpr hpq)
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    exact ⟨R.mono hpq⟩

end Erdos3.NativeVectorEquivalence

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct BigOperators

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem symbol_translate (T : D.Niltest w) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hw : ∀ i, 0 < w i) (h : σ → ℤ) :
    (T.translate hw h).symbol b ω hF = T.symbol b ω hF := by
  apply D.filtration.realPolynomialSymbolHom_eq_of_quotient_eq b ω hF w
  apply NilpotentLieBCHGroup.ext
  exact D.filtration.realification.polynomialSymbolMap_translate w hw
    (fun i => (h i : ℚ)) ⟨T.orbit.log, T.orbit.property⟩

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDerivativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem directionalDerivative_scaled_coordinate_bound
    (f : L →ₗ[ℚ] ℝ) (p : VectorPolynomial σ ℚ L)
    (d : ℕ) (hdegree : ∀ (β : σ →₀ ℕ) (i : σ), d < β i → f (coefficients p β) = 0)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ β, |f (coefficients p β)| ≤ M / monomialScale T β)
    (h : σ → ℚ) (hh : ∀ i, |(h i : ℝ)| ≤ T i) (α : σ →₀ ℕ) :
    |f (coefficients (directionalDerivative h p) α)| ≤
      (Fintype.card σ : ℝ) * d * M / monomialScale T α := by
  classical
  rw [directionalDerivative_coordinate]
  have hscale := monomialScale_pos T hT α
  have hterm (i : σ) :
      |(h i : ℝ) * (α i + 1 : ℝ) * f (coefficients p (α + Finsupp.single i 1))| ≤
        d * M / monomialScale T α := by
    by_cases hd : d < α i + 1
    · rw [hdegree _ i (by simpa using hd), mul_zero, abs_zero]
      positivity
    · have hdi : α i + 1 ≤ d := Nat.le_of_not_gt hd
      have hdir : (α i + 1 : ℝ) ≤ d := by exact_mod_cast hdi
      have hiScale : monomialScale T (α + Finsupp.single i 1) = monomialScale T α * T i := by
        rw [monomialScale_add]
        congr 1
        simp [monomialScale]
      have hcoef := hp (α + Finsupp.single i 1)
      rw [hiScale] at hcoef
      calc
        _ = |(h i : ℝ)| * (α i + 1 : ℝ) * |f (coefficients p (α + Finsupp.single i 1))| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α i + 1)]
        _ ≤ (T i * d) * (M / (monomialScale T α * T i)) :=
          mul_le_mul (mul_le_mul (hh i) hdir (by positivity) (hT i).le) hcoef
            (abs_nonneg _) (mul_nonneg (hT i).le (Nat.cast_nonneg d))
        _ = d * M / monomialScale T α := by
          field_simp [ne_of_gt hscale, ne_of_gt (hT i)]
  calc
    _ ≤ ∑ i, |(h i : ℝ) * (α i + 1 : ℝ) * f (coefficients p (α + Finsupp.single i 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : σ, (d : ℝ) * M / monomialScale T α := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp [mul_assoc, mul_div_assoc]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepDropTerminalContainment
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {R L μ : Type*} [Field R] [AddCommGroup L] [Module R L]

theorem homogeneousIntersection_baseChange {L μ : Type*} [AddCommGroup L] [Module ℚ L]
    (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ) (U V : Submodule ℚ L) :
    (homogeneousIntersection b w j U V).baseChange ℝ =
      homogeneousIntersection (b.baseChange ℝ) w j (U.baseChange ℝ) (V.baseChange ℝ) := by
  simp only [homogeneousIntersection, realification_inf, realification_ker,
    LinearMap.baseChange_sub, LinearMap.baseChange_id, basisGradeProjection,
    basisCoordinateProjection_baseChange]

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

theorem exists_preimage_basis_logHeight
    {V W μ ν ι κ : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [Fintype μ] [Fintype ν] [Fintype ι] [Fintype κ]
    (e : Basis μ ℚ V) (f : Basis ν ℚ W) (U : Submodule ℚ V) (K : Submodule ℚ W)
    (T : V →ₗ[ℚ] W) (u : ι → V) (v : κ → W)
    (hu : Submodule.span ℚ (Set.range u) = U)
    (hv : Submodule.span ℚ (Set.range v) = K)
    {p : ℝ} (hp : 0 ≤ p) (hν : (Fintype.card ν : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (huH : ∀ a i, rationalLogHeight (e.repr (u a) i) ≤ p)
    (hvH : ∀ a i, rationalLogHeight (f.repr (v a) i) ≤ p)
    (hTu : ∀ a i, rationalLogHeight (f.repr (T (u a)) i) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (U ⊓ K.comap T : Submodule ℚ V))) ℚ
        (U ⊓ K.comap T : Submodule ℚ V),
      ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ preimageBasisBudget p := by
  obtain ⟨H, _, hH, d, hd, g, hg⟩ := exists_submodule_quotient_basis_exp f K v hv
    (one_le_ceil_exp p) (fun a i => rationalHeightLE_ceil_exp (hvH a i))
    (show 0 ≤ p + 1 by linarith) (hκ.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
  have hgH (i : ν) (j : Fin d) :
      rationalLogHeight (g.repr (K.mkQ (f i)) j) ≤ (p + 3) ^ 7 := by
    have h := rationalLogHeight_le_of_height (hg j i) hH
    simpa only [show p + 1 + 2 = p + 3 by ring] using h
  let q := p + (p + 3) ^ 7
  have hpq : p ≤ q := le_add_of_nonneg_right (by positivity)
  have hq : 0 ≤ q := hp.trans hpq
  have hquot (a : ι) (j : Fin d) :
      rationalLogHeight (g.repr (K.mkQ (T (u a))) j) ≤ (q + 2) ^ 4 :=
    linearMap_coordinate_logHeight f g K.mkQ hq (hν.trans hpq)
      (fun i j => (hgH i j).trans (le_add_of_nonneg_left hp))
      (T (u a)) (fun i => (hTu a i).trans hpq) j
  let Q := p + (q + 2) ^ 4
  have hpQ : p ≤ Q := le_add_of_nonneg_right (by positivity)
  have hQ : 0 ≤ Q := hp.trans hpQ
  let B := ⌈Real.exp Q⌉₊
  obtain ⟨t, ht, z, hz, hzH⟩ := exists_bounded_span_kernel_generators e g
    (K.mkQ.comp T) u (one_le_ceil_exp Q)
    (fun a i => rationalHeightLE_ceil_exp ((huH a i).trans hpQ))
    (fun a i => rationalHeightLE_ceil_exp
      ((hquot a i).trans (le_add_of_nonneg_left hp)))
  have hker : LinearMap.ker (K.mkQ.comp T) = K.comap T := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [hu, hker] at hz
  obtain ⟨b, hb⟩ := exists_bounded_submodule_basis_from_spanning e _ z hz hzH
  have ht' : (t : ℝ) ≤ p := by
    exact (Nat.cast_le.mpr ((show t ≤ d by simpa only [Fintype.card_fin] using ht).trans hd)).trans hν
  have hcost : (((Fintype.card ι + 1) * (rationalKernelHeight t B * B) ^
      Fintype.card ι : ℕ) : ℝ) ≤ Real.exp (preimageBasisBudget p) :=
    sparseGeneratorHeight_bound (show 0 ≤ Q + 1 by linarith) t (Fintype.card ι) B
      (ht'.trans (hpQ.trans (by linarith))) (hι.trans (hpQ.trans (by linarith)))
      (ceil_exp_le_exp_add_one hQ)
  exact ⟨b, fun a i => rationalLogHeight_le_of_height (hb a i) hcost⟩

end Erdos3

end

section

namespace Erdos3

open Module

variable {L μ υ ν : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def homogeneousIntersectionSystem (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule ℚ L) (fU : Basis υ ℚ (L ⧸ U)) (fV : Basis ν ℚ (L ⧸ V)) :
    L →ₗ[ℚ] (υ ⊕ ν ⊕ μ → ℚ) :=
  LinearMap.pi fun
    | .inl i => (fU.coord i).comp U.mkQ
    | .inr (.inl i) => (fV.coord i).comp V.mkQ
    | .inr (.inr i) => (b.coord i).comp (basisGradeProjection b w j - LinearMap.id)

theorem homogeneousIntersectionSystem_ker (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule ℚ L) (fU : Basis υ ℚ (L ⧸ U)) (fV : Basis ν ℚ (L ⧸ V)) :
    LinearMap.ker (homogeneousIntersectionSystem b w j U V fU fV) = homogeneousIntersection b w j U V := by
  ext x
  rw [LinearMap.mem_ker, mem_homogeneousIntersection]
  constructor
  · intro hx
    refine ⟨(stepDrop_quotient_mem_iff U fU x).mpr (fun i => congrFun hx (.inl i)),
      (stepDrop_quotient_mem_iff V fV x).mpr (fun i => congrFun hx (.inr (.inl i))), ?_⟩
    apply sub_eq_zero.mp
    apply b.repr.injective
    ext i
    have hi := congrFun hx (.inr (.inr i))
    change b.repr (basisGradeProjection b w j x - x) i = 0 at hi
    simpa only [map_zero, Finsupp.zero_apply] using hi
  · rintro ⟨hU, hV, hj⟩
    funext i
    rcases i with i | i | i
    · exact (stepDrop_quotient_mem_iff U fU x).mp hU i
    · exact (stepDrop_quotient_mem_iff V fV x).mp hV i
    · change b.repr (basisGradeProjection b w j x - x) i = 0
      rw [hj, sub_self, map_zero]
      rfl

theorem homogeneousIntersectionSystem_basis_height (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule ℚ L) (fU : Basis υ ℚ (L ⧸ U)) (fV : Basis ν ℚ (L ⧸ V))
    {H : ℕ} (hH : 1 ≤ H)
    (hU : ∀ i k, RationalHeightLE (fU.repr (U.mkQ (b k)) i) H)
    (hV : ∀ i k, RationalHeightLE (fV.repr (V.mkQ (b k)) i) H)
    (i : υ ⊕ ν ⊕ μ) (k : μ) :
    RationalHeightLE (homogeneousIntersectionSystem b w j U V fU fV (b k) i) H := by
  classical
  rcases i with i | i | i
  · exact hU i k
  · exact hV i k
  · change RationalHeightLE (b.repr (basisGradeProjection b w j (b k) - b k) i) H
    have hp : basisGradeProjection b w j (b k) = if w k = j then b k else 0 :=
      basisCoordinateProjection_basis b {i | w i = j} k
    rw [hp]
    split_ifs
    · simpa only [sub_self, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
    · simpa only [zero_sub, map_neg, Finsupp.neg_apply] using (basis_repr_height_one b k i).neg.mono hH

theorem exists_homogeneousIntersection_basis [Fintype μ] [Fintype υ] [Fintype ν]
    (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ) (U V : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U)) (fV : Basis ν ℚ (L ⧸ V)) {H r : ℕ}
    (hH : 1 ≤ H) (hr : Fintype.card υ + Fintype.card ν + Fintype.card μ ≤ r)
    (hU : ∀ i k, RationalHeightLE (fU.repr (U.mkQ (b k)) i) H)
    (hV : ∀ i k, RationalHeightLE (fV.repr (V.mkQ (b k)) i) H) :
    ∃ e : Basis (Fin (Module.finrank ℚ (homogeneousIntersection b w j U V)))
      ℚ (homogeneousIntersection b w j U V), ∀ i k,
      RationalHeightLE (b.repr (e i : L) k) (homogeneousIntersectionBasisHeight (Fintype.card μ) r H) := by
  classical
  let P := homogeneousIntersectionSystem b w j U V fU fV
  have hP : ∀ i k, RationalHeightLE ((Pi.basisFun ℚ (υ ⊕ ν ⊕ μ)).repr (P (b i)) k) H := by
    intro i k
    change RationalHeightLE (P (b i) k) H
    exact homogeneousIntersectionSystem_basis_height b w j U V fU fV hH hU hV k i
  obtain ⟨t, ht, v, hspan, hv⟩ := exists_bounded_span_kernel_generators b
    (Pi.basisFun ℚ (υ ⊕ ν ⊕ μ)) P b hH (basis_repr_height_one b) hP
  have htr : t ≤ r := by
    simp only [Fintype.card_sum] at ht
    omega
  have hspan' : Submodule.span ℚ (Set.range v) = homogeneousIntersection b w j U V := by
    simpa only [b.span_eq, top_inf_eq, P, homogeneousIntersectionSystem_ker] using hspan
  have hv' : ∀ i k, RationalHeightLE (b.repr (v i) k)
      (homogeneousIntersectionBasisHeight (Fintype.card μ) r H) := by
    intro i k
    apply (hv i k).mono
    simp only [homogeneousIntersectionBasisHeight, mul_one]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (rationalKernelHeight_mono hH htr) _)
  exact exists_bounded_submodule_basis_from_spanning b _ v hspan' hv'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePositiveCoefficientBases
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_positive_coefficient_basis (a : BoxedDegreeIndex bound) {p : ℝ}
    (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.positiveCoefficientLayer a))) ℚ
        (M.filtration.positiveCoefficientLayer a),
      ∀ j k, RationalHeightLE (D.basis.repr (b j).val k) ⌈Real.exp p⌉₊ := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  by_cases ha : boxedDegreeMonomial a = 0
  · have hU : M.filtration.positiveCoefficientLayer a = ⊥ := by
      simp only [MultidegreeLieFiltration.positiveCoefficientLayer, ha, ite_true]
    rw [hU]
    refine ⟨Module.finBasis ℚ (⊥ : Submodule ℚ L), ?_⟩
    intro j k
    have hz : (Module.finBasis ℚ (⊥ : Submodule ℚ L) j).val = 0 :=
      (Module.finBasis ℚ (⊥ : Submodule ℚ L) j).property
    rw [hz, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (one_le_ceil_exp p)
  · have hU : M.filtration.positiveCoefficientLayer a = M.filtration.layer (fun i => (a i).val) := by
      simp only [MultidegreeLieFiltration.positiveCoefficientLayer, ha, ite_false]
    rw [hU]
    obtain ⟨b, hb⟩ := M.exists_layer_basis (fun i => (a i).val)
      (fun i => Nat.le_of_lt_succ (a i).isLt) hM
    exact ⟨b, fun j k => rationalHeightLE_ceil_exp (hb j k)⟩

noncomputable def positiveCoefficientBasis (p : ℝ) (a : BoxedDegreeIndex bound) :
    Basis (Fin (finrank ℚ (M.filtration.positiveCoefficientLayer a))) ℚ
      (M.filtration.positiveCoefficientLayer a) := by
  letI : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊ _

theorem positiveCoefficientBasis_height {p : ℝ} (hM : M.ComplexityLE p)
    (a : BoxedDegreeIndex bound) (j k) :
    RationalHeightLE (D.basis.repr (M.positiveCoefficientBasis p a j).val k) ⌈Real.exp p⌉₊ := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis_height D.basis ⌈Real.exp p⌉₊ _
    (M.exists_positive_coefficient_basis a hM) j k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSquarefreeCoefficientBases
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeCoefficientBasis_height {p : ℝ} (hM : M.ComplexityLE p)
    (a : SquarefreeIndex (ReplicatedIndex bound)) (j k) :
    RationalHeightLE (D.basis.repr (M.squarefreeCoefficientBasis p a j).val k) ⌈Real.exp p⌉₊ := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis_height D.basis ⌈Real.exp p⌉₊ _
    (M.exists_squarefree_coefficient_basis a hM) j k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ComparisonChosenLayerBasis
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeBasisIndex_card_le (p : ℝ) :
    Fintype.card M.SquarefreeBasisIndex ≤ 2 ^ (∑ i, bound i) * d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  rw [← finrank_eq_card_basis (M.squarefreeBasis p)]
  simpa only [replicatedIndex_card, finrank_eq_card_basis D.basis, Fintype.card_fin] using
    M.filtration.squarefreeAlgebra_finrank_le (fun j : ReplicatedIndex bound => j.1)

theorem squarefreeBasis_structure_height {p : ℝ} (hM : M.ComplexityLE p)
    (i j k : M.SquarefreeBasisIndex) :
    RationalHeightLE (lieStructureConstants (M.squarefreeBasis p) i j k)
      (squarefreeStructureHeight d ⌈Real.exp p⌉₊) := by
  have h := M.filtration.squarefreeBasis_structure_height
    (fun j : ReplicatedIndex bound => j.1) (M.squarefreeCoefficientBasis p) D.basis
    (one_le_ceil_exp p) (M.squarefreeCoefficientBasis_height hM)
    (fun i j k => rationalHeightLE_ceil_exp (hM.1.2.2.1 i j k))
    (fun a => by simpa only [Fintype.card_fin] using M.squarefreeCoefficientBasis_card_le a) i j k
  simp only [Fintype.card_fin] at h
  exact h

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NativeSquarefreeGrids
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_squarefree_stable_grid {p : ℝ} (hM : M.ComplexityLE p) (l : ℕ) (hl : 0 < l) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧
      B ≤ bchIntegralDenominatorBound (Fintype.card (ReplicatedIndex bound)) *
        squarefreeStructureHeight d ⌈Real.exp p⌉₊ ^ (Fintype.card M.SquarefreeBasisIndex ^ 3) * l ∧
      ∀ x ∈ coordinateGridModule (M.squarefreeBasis p) B,
        ∀ y ∈ coordinateGridModule (M.squarefreeBasis p) B,
          lieBCH (Fintype.card (ReplicatedIndex bound)) x y ∈ coordinateGridModule (M.squarefreeBasis p) B :=
  exists_bch_stable_integral_grid (M.squarefreeBasis p)
    (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).lowerCentralSeries_eq_bot
    l hl (M.squarefreeBasis_structure_height hM)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeRealAction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeFinBasis_structure_height {p : ℝ} (hM : M.ComplexityLE p) (i j k) :
    RationalHeightLE (lieStructureConstants (M.squarefreeFinBasis p) i j k)
      (squarefreeStructureHeight d ⌈Real.exp p⌉₊) := by
  rw [squarefreeFinBasis, lieStructureConstants_reindex]
  exact M.squarefreeBasis_structure_height hM _ _ _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem blockLayerMap_chosen_height (p : ℝ) (a : σ → ℕ) (ha : a ≠ 0)
    (j : Fin (finrank ℚ (M.filtration.layer a))) (k : M.SquarefreeBasisIndex) :
    RationalHeightLE ((M.squarefreeBasis p).repr
      (M.filtration.blockLayerMap (fun i : ReplicatedIndex bound => i.1) a ha
        (M.comparisonLayerBasis p a j)) k) (multidegreeFactorial a) := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let π := fun i : ReplicatedIndex bound => i.1
  let v := M.filtration.squarefreeAlgebraEquiv π
    (M.filtration.blockLayerMap π a ha (M.comparisonLayerBasis p a j)) k.1
  change RationalHeightLE
    ((chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊
      (M.filtration.squarefreeCoefficientLayer π k.1)).repr v k.2) _
  by_cases hka : blockDegree π k.1.val = a
  · have hk : k.1.val ≠ 0 := by
      intro h
      apply ha
      rw [h, blockDegree_zero] at hka
      exact hka.symm
    have hUV : M.filtration.layer a = M.filtration.squarefreeCoefficientLayer π k.1 := by
      simp only [MultidegreeLieFiltration.squarefreeCoefficientLayer, if_neg hk, hka]
    have hq : RationalHeightLE (multidegreeFactorial a : ℚ) (multidegreeFactorial a) := by
      constructor
      · simp
      · simpa using Nat.succ_le_of_lt (multidegreeFactorial_pos a)
    apply chosenBasis_smul_coordinate_height D.basis ⌈Real.exp p⌉₊
      (M.filtration.layer a) (M.filtration.squarefreeCoefficientLayer π k.1)
      hUV j v (multidegreeFactorial a) hq
    change squarefreePolynomialEquiv
      (M.filtration.blockLayerMap π a ha (M.comparisonLayerBasis p a j)).val k.1 = _
    rw [M.filtration.blockLayerMap_coe, factorialBlockMonomial_coefficient, if_pos hka]
    rfl
  · have hv : v = 0 := by
      apply Subtype.ext
      change squarefreePolynomialEquiv
        (M.filtration.blockLayerMap π a ha (M.comparisonLayerBasis p a j)).val k.1 = 0
      rw [M.filtration.blockLayerMap_coe, factorialBlockMonomial_coefficient, if_neg hka]
    rw [hv, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (multidegreeFactorial_pos a)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (p : ℝ) (B : ℕ) (hB : 0 < B)
  (hstable : M.SquarefreeGridStable p B)

theorem squarefreeRealPermute_top (e : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup)
    (hg : g ∈ (M.squarefreeModel p B hB hstable).filtration.realification.subgroup
      (Fintype.card (ReplicatedIndex bound))) :
    M.squarefreeRealPermute p B hB hstable e g = g := by
  apply NilpotentLieBCHGroup.ext
  exact realificationLieHom_eq_self_on _ _
    (M.filtration.replicatedLiePermute_ordinary_top e) g.coord hg

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem select_sample_correlation {σ X : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ}
    {eta : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p eta)
    (S : Finset X) (sample : X → σ → ℤ) (f : X → ℂ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star (eta (sample u))‖) :
    ∃ i : Fin E.count, Real.exp (-(q + p)) ≤
      ‖𝔼 u ∈ S, f u * star ((E.test i).eval (sample u))‖ := by
  have hpoint (u : X) : f u * star (eta (sample u)) =
      ∑ i, star (E.coefficient i) * (f u * star ((E.test i).eval (sample u))) := by
    rw [E.eval, star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [star_mul]
    ring
  have hmean : (𝔼 u ∈ S, f u * star (eta (sample u))) =
      ∑ i, star (E.coefficient i) * (𝔼 u ∈ S, f u * star ((E.test i).eval (sample u))) := by
    calc
      _ = 𝔼 u ∈ S, ∑ i, star (E.coefficient i) *
          (f u * star ((E.test i).eval (sample u))) := Finset.expect_congr rfl (fun u _ => hpoint u)
      _ = _ := by simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  obtain ⟨i, hi⟩ := exists_large_weighted_term (fun i => star (E.coefficient i))
    (fun i => 𝔼 u ∈ S, f u * star ((E.test i).eval (sample u)))
    (Real.exp_pos (-q)) (Real.exp_pos p) (by simpa only [norm_star] using E.cost)
    (by rwa [← hmean])
  refine ⟨i, ?_⟩
  have heq : Real.exp (-q) / Real.exp p = Real.exp (-(q + p)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rwa [heq] at hi

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def affinePullback {σ τ : Type*} [Fintype τ] {s : ℕ} {p : ℝ}
    {f : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion (fun _ : σ => 1) s p f)
    (A : σ → τ → ℤ) (b : σ → ℤ) :
    NativeIntegerExpansion (fun _ : τ => 1) s p (fun x => f (integerAffineMap A b x)) :=
  { E with
    test := fun i => (E.test i).affinePullback A b
    complexity := E.complexity
    eval := fun x => by
      simpa only [RationalFilteredNilmanifold.Niltest.eval_affinePullback] using
        E.eval (integerAffineMap A b x) }

noncomputable def toCyclic {s : ℕ} {p : ℝ} {f : (Unit → ℤ) → ℂ}
    (E : NativeIntegerExpansion (fun _ : Unit => 1) s p f) (N : ℕ) [NeZero N] :
    NativeNilsequenceExpansion s N p (fun x => f (fun _ => (x.val : ℤ))) where
  count := E.count
  count_bound := E.count_bound
  L := E.L
  dim := E.dim
  model := E.model
  test := E.test
  complexity := E.complexity
  coefficient := E.coefficient
  cost := E.cost
  eval x := E.eval (fun _ => (x.val : ℤ))

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ τ : Type*} {w : σ → ℕ} {v : τ → ℕ} {s : ℕ} {p : ℝ}
  {f : (σ → ℤ) → ℂ}

noncomputable def substitutedValue (E : NativeIntegerExpansion w s p f)
    (P : σ → MvPolynomial τ ℚ) (hP : ∀ i, P i ∈ weightedSupportLE v (w i))
    (x : τ → ℤ) : ℂ :=
  ∑ i, E.coefficient i * ((E.test i).substitute P hP).eval x

noncomputable def substituteExpansion (E : NativeIntegerExpansion w s p f)
    (P : σ → MvPolynomial τ ℚ) (hP : ∀ i, P i ∈ weightedSupportLE v (w i)) :
    NativeIntegerExpansion v s p (E.substitutedValue P hP) :=
  { E with
    test := fun i => (E.test i).substitute P hP
    complexity := E.complexity
    eval := fun _ => rfl }

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3

open scoped TensorProduct

namespace NativeIntegerExpansion

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def linearPullbackHom {σ τ : Type*} [Fintype τ] {s : ℕ} {p : ℝ}
    {f : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion (fun _ : σ => 1) s p f)
    (A : σ → ((τ → ℤ) →+ ℤ)) :
    NativeIntegerExpansion (fun _ : τ => 1) s p (fun x => f (fun i => A i x)) :=
  { E with
    test := fun i => (E.test i).linearPullbackHom A
    complexity := E.complexity
    eval := fun x => by
      simpa only [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom]
        using E.eval (fun i => A i x) }

end NativeIntegerExpansion

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativePrescribedProjection
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open CircleFourier
open scoped NNReal

variable {L ι : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_prescribed_central_projection
    (Γ T : Subgroup (NilpotentLieBCHGroup L s hnil))
    [PseudoMetricSpace (NilpotentLieBCHGroup L s hnil ⧸ Γ)]
    (hT : ∀ z ∈ T, ∀ v : L, ⁅z.coord, v⁆ = 0)
    (u : ι → L) (hline : ∀ i r, realBCHLine (hnil := hnil) (u i) r ∈ T)
    (hspan : ∀ z ∈ T, z.coord ∈ Submodule.span ℝ (Set.range u))
    (A : ι → IsometricCircleAction (NilpotentLieBCHGroup L s hnil ⧸ Γ))
    (hcomm : ∀ i j, (A i).Commutes (A j))
    (hact : ∀ i (r : ℝ) x, (A i).act (r : CircleFourier.Circle) x =
      realBCHLine (hnil := hnil) (u i) r • x)
    (η : L →ₗ[ℝ] ℝ) (f : NilpotentLieBCHGroup L s hnil ⧸ Γ → ℂ)
    (hseed : ∀ z ∈ T, f (QuotientGroup.mk z) = logCharacter η z)
    {K : ℝ≥0} {B : ℝ} (hf : LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ B) :
    ∃ g : NilpotentLieBCHGroup L s hnil ⧸ Γ → ℂ,
      LipschitzWith K g ∧ (∀ x, ‖g x‖ ≤ B) ∧
      (∀ z ∈ T, ∀ x, g (z • x) = logCharacter η z * g x) ∧
      ∀ z ∈ T, g (QuotientGroup.mk z) = logCharacter η z := by
  classical
  have hperiod (i) : (QuotientGroup.mk (realBCHLine (hnil := hnil) (u i) 1) : _ ⧸ Γ) =
      QuotientGroup.mk (1 : NilpotentLieBCHGroup L s hnil) := by
    have h := hact i 1 (QuotientGroup.mk (1 : NilpotentLieBCHGroup L s hnil))
    simpa only [AddCircle.coe_period, (A i).zero_act, MulAction.Quotient.smul_mk,
      smul_eq_mul, mul_one] using h.symm
  have hint (i) : ∃ n : ℤ, η (u i) = n := by
    have he : character (η (u i) : CircleFourier.Circle) = 1 := by
      calc
        _ = f (QuotientGroup.mk (realBCHLine (hnil := hnil) (u i) 1)) := by
          rw [hseed _ (hline i 1)]
          simp only [logCharacter, realBCHLine, one_smul]
        _ = f (QuotientGroup.mk (1 : NilpotentLieBCHGroup L s hnil)) := congrArg f (hperiod i)
        _ = 1 := by rw [hseed _ T.one_mem]; simp only [logCharacter, coord_one, map_zero,
          AddCircle.coe_zero, character_zero]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp ((character_eq_one_iff _).mp he)
    exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn.symm⟩
  choose n hn using hint
  have hlinechar (i r) : logCharacter η (realBCHLine (hnil := hnil) (u i) r) =
      character (n i • (r : CircleFourier.Circle)) := by
    simp only [logCharacter, realBCHLine, map_smul, smul_eq_mul, hn, ← AddCircle.coe_zsmul,
      zsmul_eq_mul, mul_comm]
  let S : Set (NilpotentLieBCHGroup L s hnil ⧸ Γ) := Set.range (fun z : T => QuotientGroup.mk z.val)
  have hstable : ∀ i t x, x ∈ S → (A i).act t x ∈ S := by
    intro i t x hx
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    obtain ⟨z, rfl⟩ := hx
    rw [hact, MulAction.Quotient.smul_mk, smul_eq_mul]
    exact ⟨⟨realBCHLine (u i) r * z.val, T.mul_mem (hline i r) z.property⟩, rfl⟩
  have hchar : ∀ i t x, x ∈ S → f ((A i).act t x) = character (n i • t) * f x := by
    intro i t x hx
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    obtain ⟨z, rfl⟩ := hx
    rw [hact, MulAction.Quotient.smul_mk, smul_eq_mul,
      hseed _ (T.mul_mem (hline i r) z.property), hseed _ z.property,
      logCharacter_mul η _ _ (hT _ (hline i r) z.val.coord), hlinechar]
  obtain ⟨g, hg, hgb, hgchar, hgeq⟩ :=
    exists_prescribed_circle_projection A n hcomm S f hstable hchar hf hb
  refine ⟨g, hg, hgb, ?_, fun z hz => (hgeq _ ⟨⟨z, hz⟩, rfl⟩).trans (hseed z hz)⟩
  intro z hz x
  apply central_span_character u (fun i v => ?_) η g (fun i r y => ?_) (hspan z hz) x
  · simpa only [realBCHLine, one_smul] using hT _ (hline i 1) v
  · have h := hgchar i (r : CircleFourier.Circle) y
    rw [hact, ← hlinechar] at h
    simpa only [logCharacter, realBCHLine, map_smul, smul_eq_mul] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

theorem exists_native_prescribed_projection {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (η : L →ₗ[ℚ] ℚ) (f : D.Space → ℂ) {K : ℝ≥0} {B : ℝ}
    (hf : letI := D.metricSpace; LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ B)
    (hseed : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
      f (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z) :
    ∃ g : D.Space → ℂ, (letI := D.metricSpace; LipschitzWith K g) ∧
      (∀ x, ‖g x‖ ≤ B) ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
        g (z • x) = logCharacter (realifyFunctional η) z * g x) ∧
      g (QuotientGroup.mk (1 : D.RealGroup)) = 1 := by
  let := D.metricSpace
  obtain ⟨b, w, N, hlayers, _, _, hN, _, _, _, A, hcomm, _, hact⟩ :=
    D.exists_controlled_central_actions hp hD
  let S : Set (Fin (finrank ℚ L)) := {j | s ≤ w j}
  let u (j : S) := (N : ℝ) • b.baseChange ℝ j
  have hbReal (j : S) : b.baseChange ℝ j ∈ D.filtration.realLayer s := by
    rw [Basis.baseChange_apply]
    change rationalLieInclusion (b j) ∈ D.filtration.realLayer s
    apply D.filtration.rational_inclusion_mem_realLayer
    rw [hlayers s]
    exact Submodule.subset_span ⟨j, j.property, rfl⟩
  have hline (j : S) (r : ℝ) : realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (u j) r ∈ D.filtration.realification.subgroup s := by
    change r • ((N : ℝ) • b.baseChange ℝ j) ∈ D.filtration.realLayer s
    exact (D.filtration.realLayer s).smul_mem r ((D.filtration.realLayer s).smul_mem _ (hbReal j))
  obtain ⟨g, hg, hgb, hgvert, hgeq⟩ := exists_prescribed_central_projection
    D.realLattice (D.filtration.realification.subgroup s)
    (fun z hz v => D.filtration.realification.top_layer_central hz v) u hline
    (fun z hz => D.filtration.realLayer_le_span_scaled_basis b s S (hlayers s) N hN hz)
    A hcomm hact (realifyFunctional η) f hseed hf hb
  refine ⟨g, hg, hgb, hgvert, ?_⟩
  have h := hgeq 1 (D.filtration.realification.subgroup s).one_mem
  simpa only [logCharacter, coord_one, map_zero, AddCircle.coe_zero, CircleFourier.character_zero] using h

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

abbrev PositivePolynomialBasisIndex := Σ a : BoxedDegreeIndex bound,
  Fin (finrank ℚ (M.filtration.positiveCoefficientLayer a))

omit [DecidableEq σ] in
theorem positiveCoefficientBasis_card_le (a : BoxedDegreeIndex bound) :
    finrank ℚ (M.filtration.positiveCoefficientLayer a) ≤ d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
    (M.filtration.positiveCoefficientLayer a).finrank_le

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)

abbrev PositivePolynomialDownsetIndex :=
  {j : M.PositivePolynomialBasisIndex // j ∉ {k | boxedDegreeMonomial k.1 ∉ J}}

theorem positivePolynomialDownsetIndex_card_le :
    Fintype.card (M.PositivePolynomialDownsetIndex J) ≤
      Fintype.card M.PositivePolynomialBasisIndex := Fintype.card_subtype_le _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem positivePolynomialEvaluation_metric_bound {p q : ℝ} (hM : M.ComplexityLE p)
    (hpq : p ≤ q) (hdim : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤ q) :
    (coordinateLipschitzBound d (Fintype.card M.PositivePolynomialBasisIndex) ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp ((q + 3) ^ 2) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hq : 0 ≤ q := hp.trans hpq
  have hH : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (q + 1) :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr (by linarith))
  have h := coordinateLipschitzBound_le_exp d (Fintype.card M.PositivePolynomialBasisIndex)
    ⌈Real.exp p⌉₊ (p := q + 1) (by linarith) (by linarith [hM.1.1]) (by linarith) hH
  have heq : q + 1 + 2 = q + 3 := by ring
  simpa only [heq] using h

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeTotalDegreeMultifiltration
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem totalDegreeMultidegree_complexity (σ : Type*) [Fintype σ] [Nonempty σ]
    {p : ℝ} (hD : D.GeometryComplexityLE p) :
    (D.totalDegreeMultidegree σ hD).ComplexityLE p :=
  ⟨hD, fun a => Classical.choose_spec (D.exists_totalDegree_layer_basis (∑ i, (a i).val) hD)⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

noncomputable def translate {s : ℕ} {p : ℝ} {f : ℤ → ℂ}
    (E : NativeIntegerExpansion (fun _ : Unit => 1) s p (fun x => f (x ()))) (δ : ℤ) :
    NativeIntegerExpansion (fun _ : Unit => 1) s p (fun x => f (x () + δ)) := by
  simpa [integerAffineMap, add_comm] using E.affinePullback (fun (_ : Unit) (_ : Unit) => (1 : ℤ)) (fun _ => δ)

end Erdos3.NativeIntegerExpansion

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem reducedNativeIndex_injective (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ) :
    Function.Injective (reducedNativeIndex s w ω) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : AdaptedBasisIndex w ω => z.val.1) h
  · apply Subtype.ext
    exact congrArg (fun z : AdaptedBasisIndex w ω => z.val.2) h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionalStepDrop
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_real_module_topology {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) :
    ∃ τ : TopologicalSpace (ℝ ⊗[ℚ] V),
      letI := τ
      IsTopologicalAddGroup (ℝ ⊗[ℚ] V) ∧ ContinuousSMul ℝ (ℝ ⊗[ℚ] V) ∧ T2Space (ℝ ⊗[ℚ] V) := by
  let τ := moduleTopology ℝ (ℝ ⊗[ℚ] V)
  let : TopologicalSpace (ℝ ⊗[ℚ] V) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V) := IsModuleTopology.topologicalAddGroup ℝ _
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] V) := (b.baseChange ℝ).finiteDimensional_of_finite
  have hc : Continuous (b.baseChange ℝ).equivFun :=
    IsModuleTopology.continuous_of_linearMap (b.baseChange ℝ).equivFun.toLinearMap
  let : T2Space (ℝ ⊗[ℚ] V) := T2Space.of_injective_continuous (b.baseChange ℝ).equivFun.injective hc
  exact ⟨τ, inferInstance, inferInstance, inferInstance⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductCoefficient
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_firstProjection_mem {V : Type*} [AddCommGroup V] [Module ℚ V]
    (J : Submodule ℚ (Fin 4 → V)) {x : ℝ ⊗[ℚ] (Fin 4 → V)}
    (hx : x ∈ J.baseChange ℝ) :
    (LinearMap.proj (0 : Fin 4)).baseChange ℝ x ∈ (fourFirstProjection J).baseChange ℝ := by
  rw [fourFirstProjection, realification_map]
  exact ⟨x, hx, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoundedDependentCoordinates
namespace OAI

section

namespace Erdos3

open Module

theorem exists_dependent_coordinate_basis
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (v : κ → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = J)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hvH : ∀ a k i, rationalLogHeight (v a k i) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (fourDependentProjection J))) ℚ (fourDependentProjection J),
      ∀ a i, rationalLogHeight ((b a : ι → ℚ) i) ≤ dependentCoordinateBudget p := by
  classical
  let q := 4 * p + 1
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpq : p + 1 ≤ q := by dsimp only [q]; linarith
  have hrows (S : Finset (Fin 4)) : (Fintype.card (Σ _ : S, ι) : ℝ) ≤ q := by
    have hS : Fintype.card S ≤ 4 := by
      simpa only [Fintype.card_coe, Fintype.card_fin] using S.card_le_univ
    have hc : Fintype.card (Σ _ : S, ι) ≤ 4 * Fintype.card ι := by
      simpa using Nat.mul_le_mul_right (Fintype.card ι) hS
    calc
      _ ≤ (4 : ℝ) * Fintype.card ι := by exact_mod_cast hc
      _ ≤ 4 * p := mul_le_mul_of_nonneg_left hι (by norm_num)
      _ ≤ q := by dsimp only [q]; linarith
  have hκq : (Fintype.card κ : ℝ) ≤ q := hκ.trans ((by linarith : p ≤ p + 1).trans hpq)
  have hHq : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hpq)
  obtain ⟨M, _, hM, u, hu, huH⟩ := exists_sparse_generators_exp_height J {1, 2} v hv
    (one_le_ceil_exp p) (fun a k i => rationalHeightLE_ceil_exp (hvH a k i))
    hq (hrows {1, 2}) hκq hHq
  obtain ⟨M', _, hM', u', hu', huH'⟩ := exists_sparse_generators_exp_height J {1, 3} v hv
    (one_le_ceil_exp p) (fun a k i => rationalHeightLE_ceil_exp (hvH a k i))
    hq (hrows {1, 3}) hκq hHq
  let t := p + sparseGeneratorBudget q
  have hpt : p ≤ t := le_add_of_nonneg_right (sparseGeneratorBudget_nonneg hq)
  have ht : 0 ≤ t := hp.trans hpt
  have huB (a : κ) (i : ι) : rationalLogHeight (u a i) ≤ t :=
    (rationalLogHeight_le_of_height (huH a i) hM).trans (le_add_of_nonneg_left hp)
  have huB' (a : κ) (i : ι) : rationalLogHeight (u' a i) ≤ t :=
    (rationalLogHeight_le_of_height (huH' a i) hM').trans (le_add_of_nonneg_left hp)
  obtain ⟨b, hb⟩ := exists_preimage_basis_logHeight (Pi.basisFun ℚ ι) (Pi.basisFun ℚ ι)
    (fourSparseFirstProjection J {1, 2}) (fourSparseFirstProjection J {1, 3})
    (LinearMap.id : (ι → ℚ) →ₗ[ℚ] (ι → ℚ)) u u' hu hu' ht
    (hι.trans hpt) (hκ.trans hpt) (hκ.trans hpt)
    (by simpa only [Pi.basisFun_repr] using huB)
    (by simpa only [Pi.basisFun_repr] using huB')
    (by simpa only [Pi.basisFun_repr, LinearMap.id_apply] using huB)
  change Basis (Fin (finrank ℚ (fourDependentProjection J))) ℚ (fourDependentProjection J) at b
  refine ⟨b, fun a i => ?_⟩
  exact hb a i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeDegreePowerBound
namespace OAI

section

namespace Erdos3

theorem exists_native_coordinate_polynomial_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      nativeCoordinateSeparationBudget s P ≤ (P + C) ^ C ∧
      ((s : ℝ) + 1) * nativeDependentDenominatorBudget s P ≤ (P + C) ^ C ∧
      nativeDependentSlowBudget s P ≤ (P + C) ^ C ∧ (P + 3) ^ 7 ≤ (P + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := ((X + 1 + (X + 3) ^ 7 + 2) ^ 9 + X + 4) ^ 4
  let G := X + X * (R + 1 + (X + 3) ^ 7)
  let U := 4 * X + (X + 3) ^ 7 + G + Polynomial.C s * X + (X + 3) ^ 2 + 4
  let V := U + (U + 2) ^ 3 + X + 2
  let Z := 2 * V + 2 * (V + ((V + 2) ^ 3 + (V + 2) ^ 36)) +
    ((V + 2) ^ 3 + (V + 2) ^ 18 + V) + 2
  let Q := Z + (Z + Z * ((Z + 2) ^ 7 + Z))
  let cut := ((V + 2) ^ 48 + (V + 2) ^ 24 + V + 1) +
    ((Q + 2) ^ 48 + (Q + 2) ^ 24 + Q + 1)
  let den := Q + (Q + 2) ^ 3 + (Q + 2) ^ 36
  let slow := (Q + 2) ^ 3 + (Q + 2) ^ 18 + Q + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (cut + Polynomial.C (s + 1) * den + slow + (X + 3) ^ 7)
  refine ⟨C, hC, ?_⟩
  intro P hP
  have hU : U.eval₂ (Nat.castRingHom ℝ) P = nativeCoordinateBaseBudget s P := by
    simp [U, G, R, X, nativeCoordinateBaseBudget, horizontalCoordinateBudget,
      refiltrationCoordinateBudget, Polynomial.eval₂_pow]
  have hV : V.eval₂ (Nat.castRingHom ℝ) P = nativeCoordinateInputBudget s P := by
    simp [V, X, Polynomial.eval₂_pow, hU, nativeCoordinateInputBudget]
  have hZ : Z.eval₂ (Nat.castRingHom ℝ) P =
      rankDependentInputBudget (nativeCoordinateInputBudget s P) := by
    simp [Z, Polynomial.eval₂_pow, hV, rankDependentInputBudget]
  have hQ : Q.eval₂ (Nat.castRingHom ℝ) P = nativeDependentBudget s P := by
    simp [Q, Polynomial.eval₂_pow, hZ, nativeDependentBudget, sparseGeneratorBudget]
  have hsum : nativeCoordinateSeparationBudget s P +
      ((s : ℝ) + 1) * nativeDependentDenominatorBudget s P +
      nativeDependentSlowBudget s P + (P + 3) ^ 7 ≤ (P + C) ^ C := by
    simpa [cut, den, slow, X, Polynomial.eval₂_pow, hV, hQ,
      nativeCoordinateSeparationBudget, separationBudget, nativeDependentDenominatorBudget,
      nativeDependentSlowBudget] using hbudget P hP
  have hinput := nativeCoordinateInputBudget_nonneg s hP
  have hdep := nativeDependentBudget_nonneg s hP
  have hcut : 0 ≤ nativeCoordinateSeparationBudget s P :=
    add_nonneg (separationBudget_nonneg hinput) (separationBudget_nonneg hdep)
  have hden : 0 ≤ ((s : ℝ) + 1) * nativeDependentDenominatorBudget s P := by
    unfold nativeDependentDenominatorBudget
    positivity
  have hslow : 0 ≤ nativeDependentSlowBudget s P := by
    unfold nativeDependentSlowBudget
    positivity
  have hf : 0 ≤ (P + 3) ^ 7 := by positivity
  exact ⟨by linarith only [hsum, hden, hslow, hf],
    by linarith only [hsum, hcut, hslow, hf],
    by linarith only [hsum, hcut, hden, hf],
    by linarith only [hsum, hcut, hden, hslow]⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MarkedPolynomialGenerators
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedLieSpan_le_markedDegree {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d k l : ℕ) :
    markedLieSpan v w marked d k l ≤ F.layer k l := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, _, hk, hl, rfl⟩
  have hweight := hk.trans
    ((lieTreeMarkedCount_le_length marked a).trans (lieTree_length_le_weight w hw a))
  exact F.degree_antitone l hweight
    (F.rank_antitone (lieTreeWeight w a) hl (F.lieTreeEval_mem_length v w hv a))

end Erdos3

end

end OAI
end


