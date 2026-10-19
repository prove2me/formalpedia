-- Prove2me | Definitions.Def_OAIE3v2B052
-- name    : OAIE3v2B052
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:12:42.486975+00:00
-- url     : https://prove2.me/theorems/af3a6721-1235-464d-9a70-555f66f9df73
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 53 of 311
-- statement:
--   Definitions bundle 53 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B002`, `OAIE3v2B004`, `OAIE3v2B010`, `OAIE3v2B015`, `OAIE3v2B018`, `OAIE3v2B019`, `OAIE3v2B020`, `OAIE3v2B021` of this split.
--
--   Modules: `Estimates/BoundedFastCoefficientGenerators.lean`, `Estimates/EuclideanDerivativeCovolume.lean`, `Estimates/EuclideanGraphNorm.lean`, `Estimates/EuclideanGraphResidual.lean`, `Estimates/NormalizedMinorBounds.lean`, `Estimates/ScaledSectionGram.lean`, `Geometry/LayerOneTransportBudget.lean`, `Geometry/ProductEuclideanCoordinates.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Lattices/DenseIntegerSpan.lean`, `Lattices/DerivativeLatticeDivision.lean`, `Lattices/EuclideanDerivativeLattice.lean`, `Lattices/EuclideanLatticeGraph.lean`, `Lattices/IntegerAbsInterval.lean`, `Lattices/IntegerMinorNormalization.lean`, `Lattices/LatticeCoordinateLifts.lean`, `Lattices/LatticeVoronoiPacking.lean`, `Lattices/ScaledLatticeCovolume.lean`, `Linear/EuclideanVerticalProjection.lean`, `Linear/ShortVectorProjection.lean`, `Polynomial/VectorPolynomialReconstruction.lean`, `Sampling/DerivativeGridPoints.lean`, `Sampling/GridNormalizationDenominator.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B018
import Definitions.Def_OAIE3v2B019
import Definitions.Def_OAIE3v2B020
import Definitions.Def_OAIE3v2B021

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem one_le_monomialScale {σ : Type*} (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i) (α : σ →₀ ℕ) :
    1 ≤ monomialScale T α := by
  classical
  exact Finset.one_le_prod (fun index _ => one_le_pow₀ (hT index))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductEuclideanCoordinates
namespace OAI

section

namespace Erdos3

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

theorem productEuclideanEquiv_norm_le (x : (σ → ℝ) × (κ → ℝ)) :
    ‖productEuclideanEquiv x‖ ≤ ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * ‖x‖ := by
  calc
    _ ≤ ∑ i : σ ⊕ κ, |productEuclideanEquiv x i| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ _i : σ ⊕ κ, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      cases i with
      | inl i =>
        simpa only [productEuclideanEquiv_apply_inl, ← Real.norm_eq_abs] using
          (norm_le_pi_norm x.1 i).trans (norm_fst_le x)
      | inr j =>
        simpa only [productEuclideanEquiv_apply_inr, ← Real.norm_eq_abs] using
          (norm_le_pi_norm x.2 j).trans (norm_snd_le x)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, nsmul_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAbsInterval
namespace OAI

section

namespace Erdos3

theorem integerAbsInterval_card_le_three (B : ℝ) (hB : 1 ≤ B) :
    ((integerAbsInterval B).card : ℝ) ≤ 3 * B :=
  (integerAbsInterval_card_le B (by linarith)).trans (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DenseIntegerSpan
namespace OAI

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bounded_integer_points_card_le_of_proper_subspace
    (U : Submodule ℝ (ι → ℝ)) (hU : U ≠ ⊤)
    (H : Finset (ι → ℤ)) (T : ι → ℝ) (R : ℝ)
    (hT : ∀ i, 1 ≤ T i) (hR : 1 ≤ R)
    (hmem : ∀ h ∈ H, (fun i => (h i : ℝ)) ∈ U)
    (hbound : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ R * T i) :
    ∃ j : ι, (H.card : ℝ) ≤
      (3 * R) ^ (Fintype.card ι - 1) * ∏ i : {i : ι // i ≠ j}, T i.val := by
  classical
  obtain ⟨j, hj⟩ := integer_points_card_le_of_proper_subspace U hU H
    (fun i => integerAbsInterval (R * T i)) hmem
    (fun h hh i => (mem_integerAbsInterval _ _).mpr (hbound h hh i))
  refine ⟨j, ?_⟩
  have hnum : Fintype.card {i : ι // i ≠ j} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  calc
    (H.card : ℝ) ≤ ∏ i : {i : ι // i ≠ j}, ((integerAbsInterval (R * T i.val)).card : ℝ) := by
      exact_mod_cast hj
    _ ≤ ∏ i : {i : ι // i ≠ j}, (3 * R) * T i.val := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        have hRT : 1 ≤ R * T i.val := by
          simpa only [mul_one] using mul_le_mul hR (hT i.val)
            (show (0 : ℝ) ≤ 1 by norm_num) (show 0 ≤ R by linarith)
        simpa only [mul_assoc] using integerAbsInterval_card_le_three (R * T i.val)
          hRT
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,
        Finset.card_univ, hnum]

theorem integer_points_span_eq_top_of_density
    (H : Finset (ι → ℤ)) (T : ι → ℝ) (R δ : ℝ)
    (hT : ∀ i, 1 ≤ T i) (hR : 1 ≤ R)
    (hbound : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ R * T i)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card ι - 1) < δ * T i) :
    Submodule.span ℝ {x : ι → ℝ | ∃ h ∈ H, x = fun i => (h i : ℝ)} = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨j, hj⟩ := bounded_integer_points_card_le_of_proper_subspace _ hspan H T R hT hR
    (fun h hh => Submodule.subset_span ⟨h, hh, rfl⟩) hbound
  have hp : 0 < ∏ i : {i : ι // i ≠ j}, T i.val :=
    Finset.prod_pos (fun i _ => lt_of_lt_of_le zero_lt_one (hT i.val))
  have hprod : T j * (∏ i : {i : ι // i ≠ j}, T i.val) = ∏ i, T i := by
    have he : (∏ i ∈ Finset.univ.erase j, T i) = ∏ i : {i : ι // i ≠ j}, T i.val :=
      Finset.prod_subtype _ (by simp) T
    rw [← he]
    exact Finset.mul_prod_erase Finset.univ T (Finset.mem_univ j)
  have hstrict := mul_lt_mul_of_pos_right (hlarge j) hp
  have hidentity : δ * T j * (∏ i : {i : ι // i ≠ j}, T i.val) = δ * ∏ i, T i := by
    rw [mul_assoc, hprod]
  rw [hidentity] at hstrict
  exact (hstrict.trans_le hdense).not_ge hj

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeVoronoiPacking
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (Λ : Submodule ℤ E)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeVoronoi_closed : IsClosed (latticeVoronoi Λ) := by
  change IsClosed {x : E | ∀ z : Λ, ‖x‖ ≤ ‖x - z.val‖}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun z => isClosed_le continuous_norm ((continuous_id.sub continuous_const).norm))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeVoronoi_subset_closedBall (B : ℝ)
    (hcover : ∀ x : E, ∃ z : Λ, ‖x - z.val‖ ≤ B) :
    latticeVoronoi Λ ⊆ Metric.closedBall 0 B := by
  intro x hx
  obtain ⟨z, hz⟩ := hcover x
  exact mem_closedBall_zero_iff.mpr ((hx z).trans hz)

theorem latticeVoronoi_isAddFundamentalDomain [DiscreteTopology Λ]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ] :
    IsAddFundamentalDomain Λ (latticeVoronoi Λ) μ where
  nullMeasurableSet := (latticeVoronoi_closed Λ).measurableSet.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall fun x => by
    obtain ⟨z, hz⟩ := exists_sub_mem_latticeVoronoi Λ x
    refine ⟨-z, ?_⟩
    simpa only [Submodule.vadd_def, vadd_eq_add, Submodule.coe_neg, neg_add_eq_sub] using hz
  aedisjoint := by
    intro a b hab
    apply measure_mono_null (t := {x : E | ‖x - a.val‖ = ‖x - b.val‖})
    · intro x hx
      obtain ⟨y, hy, hya⟩ := hx.1
      obtain ⟨z, hz, hzb⟩ := hx.2
      have hay : a.val + y = x := hya
      have hbz : b.val + z = x := hzb
      have hyx : y = x - a.val := by rw [← hay]; abel
      have hzx : z = x - b.val := by rw [← hbz]; abel
      have h₁ := hy (b - a)
      have h₂ := hz (a - b)
      change ‖y‖ ≤ ‖y - (b.val - a.val)‖ at h₁
      change ‖z‖ ≤ ‖z - (a.val - b.val)‖ at h₂
      rw [hyx] at h₁
      rw [hzx] at h₂
      have hsub₁ : x - a.val - (b.val - a.val) = x - b.val := by abel
      have hsub₂ : x - b.val - (a.val - b.val) = x - a.val := by abel
      rw [hsub₁] at h₁
      rw [hsub₂] at h₂
      exact le_antisymm h₁ h₂
    · exact euclidean_bisector_measure_zero μ a.val b.val (fun he => hab (Subtype.ext he))

end Erdos3

end

section

namespace Erdos3

open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) (R : ℝ)

theorem shortVectorLattice_covering (x : shortVectorSpan Λ R) :
    ∃ z : shortVectorLattice Λ R,
      ‖x - z.val‖ ≤ (finrank ℝ (shortVectorSpan Λ R) : ℝ) * R / 2 := by
  obtain ⟨d, b, hd, hb⟩ := exists_shortVectorSpan_basis Λ R
  obtain ⟨z, hz, hnear⟩ := exists_zspan_near_of_basis_bound b R (fun i => (hb i).2) x
  have hsub : Submodule.span ℤ (Set.range b) ≤ shortVectorLattice Λ R := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (hb i).1
  refine ⟨⟨z, hsub hz⟩, ?_⟩
  simpa only [Fintype.card_fin, hd] using hnear

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module
open scoped Pointwise

theorem lattice_points_mul_covolume_le_closedBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (B R : ℝ) (hcover : ∀ x : E, ∃ z : Λ, ‖x - z.val‖ ≤ B)
    (P : Finset Λ) (hP : ∀ p ∈ P, ‖(p : E)‖ ≤ R) :
    (P.card : ℝ) * ZLattice.covolume Λ μ ≤ μ.real (Metric.closedBall 0 (R + B)) := by
  have : MeasurableVAdd Λ E := (inferInstance : MeasurableVAdd Λ.toAddSubgroup E)
  have : VAddInvariantMeasure Λ E μ := (inferInstance : VAddInvariantMeasure Λ.toAddSubgroup E μ)
  let F := latticeVoronoi Λ
  have hfd := latticeVoronoi_isAddFundamentalDomain Λ μ
  have hF : F ⊆ Metric.closedBall 0 B := latticeVoronoi_subset_closedBall Λ B hcover
  have hfinite : μ F ≠ ⊤ := measure_ne_top_of_subset hF measure_closedBall_lt_top.ne
  have hbound : (⋃ p ∈ P, p +ᵥ F) ⊆ Metric.closedBall 0 (R + B) := by
    intro x hx
    obtain ⟨p, hpUnion⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hpmem, hxTranslate⟩ := Set.mem_iUnion.mp hpUnion
    obtain ⟨y, hy, rfl⟩ := hxTranslate
    apply mem_closedBall_zero_iff.mpr
    change ‖(p : E) + y‖ ≤ R + B
    exact (norm_add_le _ _).trans
      (add_le_add (hP p hpmem) (mem_closedBall_zero_iff.mp (hF hy)))
  have hvol : μ.real (⋃ p ∈ P, p +ᵥ F) = (P.card : ℝ) * μ.real F := by
    rw [measureReal_biUnion_finset₀
      (fun p _ q _ hpq => hfd.aedisjoint hpq)
      (fun p _ => hfd.nullMeasurableSet.vadd p)
      (fun p _ => by rw [measure_vadd]; exact hfinite)]
    simp only [F, measureReal_def, measure_vadd, Finset.sum_const, nsmul_eq_mul]
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ μ hfd, ← hvol]
  exact measureReal_mono hbound measure_closedBall_lt_top.ne

theorem shortVectorLattice_covolume_packing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (R : ℝ)
    (P : Finset (shortVectorLattice Λ R))
    (hP : ∀ p ∈ P, ‖(p : shortVectorSpan Λ R)‖ ≤ R) :
    (P.card : ℝ) * ZLattice.covolume (shortVectorLattice Λ R) ≤
      volume.real (Metric.closedBall (0 : shortVectorSpan Λ R)
        (R + (finrank ℝ (shortVectorSpan Λ R) : ℝ) * R / 2)) := by
  exact lattice_points_mul_covolume_le_closedBall (shortVectorLattice Λ R) volume
    ((finrank ℝ (shortVectorSpan Λ R) : ℝ) * R / 2) R
    (shortVectorLattice_covering Λ R) P hP

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ShortVectorProjection
namespace OAI

section

namespace Erdos3

theorem shortVectorSpan_map_eq_top_of_spanning_integer_images
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ)) (H : Finset (ι → ℤ)) (R : ℝ)
    (hspan : Submodule.span ℝ {x : ι → ℝ | ∃ h ∈ H, x = fun i => (h i : ℝ)} = ⊤)
    (hlift : ∀ h ∈ H, ∃ v ∈ Λ, ‖v‖ ≤ R ∧ π v = fun i => (h i : ℝ)) :
    (shortVectorSpan Λ R).map π = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro x ⟨h, hh, rfl⟩
  obtain ⟨v, hv, hnorm, hπ⟩ := hlift h hh
  exact ⟨v, mem_shortVectorSpan Λ R hv hnorm, hπ⟩

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

theorem derivativeGridPoint_eq_imp_shift_eq (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : κ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (h k : σ → ℤ) (r t : κ → ℝ)
    (heq : derivativeGridPoint T scale Y M h r = derivativeGridPoint T scale Y M k t) : h = k := by
  funext i
  have hi := congrArg (fun v : (σ → ℝ) × (κ → ℝ) => v.1 i * T i) heq
  simp only [derivativeGridPoint, div_mul_cancel₀ _ (hT i)] at hi
  exact_mod_cast hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EuclideanDerivativeLattice
namespace OAI

section

namespace Erdos3

variable {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]

omit [DecidableEq σ] [DecidableEq κ] in
theorem derivativeGridPoint_shift_bound
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (h : σ → ℤ) (r : κ → ℝ) (R : ℝ)
    (hR : ‖derivativeGridPoint T scale Y M h r‖ ≤ R) :
    ∀ i, |(h i : ℝ)| ≤ R * T i := by
  intro i
  have hi := (norm_le_pi_norm (derivativeGridPoint T scale Y M h r).1 i).trans
    ((norm_fst_le _).trans hR)
  change ‖(h i : ℝ) / T i‖ ≤ R at hi
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hT i)] at hi
  exact (div_le_iff₀ (hT i)).mp hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedFastCoefficientGenerators
namespace OAI

section

namespace Erdos3

def fastKernelGeneratorHeight (n m r H : ℕ) : ℕ :=
  (m + 1) * (rationalKernelHeight r ((n + 1) * H ^ n) * H) ^ m

def fastCoefficientGeneratorHeight (n m r H : ℕ) : ℕ :=
  (n + 1) * fastKernelGeneratorHeight n m r H ^ n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanDerivativeCovolume
namespace OAI

section

namespace Erdos3

open MeasureTheory Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem shortVectorLattice_covolume_le
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (R N : ℝ) (hR : 0 ≤ R) (hN : 0 < N)
    (P : Finset (shortVectorLattice Λ R))
    (hP : ∀ p ∈ P, ‖(p : shortVectorSpan Λ R)‖ ≤ R) (hcard : N ≤ (P.card : ℝ)) :
    ZLattice.covolume (shortVectorLattice Λ R) ≤
      (((finrank ℝ (shortVectorSpan Λ R) : ℝ) + 2) * R) ^
        finrank ℝ (shortVectorSpan Λ R) / N := by
  let d := finrank ℝ (shortVectorSpan Λ R)
  have hpack := shortVectorLattice_covolume_packing Λ R P hP
  have hvol := euclidean_closedBall_volume_le (E := shortVectorSpan Λ R)
    (R + (d : ℝ) * R / 2) (by positivity)
  have he : 2 * (R + (d : ℝ) * R / 2) = ((d : ℝ) + 2) * R := by ring
  rw [he] at hvol
  have hcov : 0 ≤ ZLattice.covolume (shortVectorLattice Λ R) :=
    (ZLattice.covolume_pos (shortVectorLattice Λ R) volume).le
  apply (le_div_iff₀ hN).mpr
  calc
    ZLattice.covolume (shortVectorLattice Λ R) * N =
        N * ZLattice.covolume (shortVectorLattice Λ R) := mul_comm _ _
    _ ≤ (P.card : ℝ) * ZLattice.covolume (shortVectorLattice Λ R) :=
      mul_le_mul_of_nonneg_right hcard hcov
    _ ≤ _ := hpack.trans hvol

theorem shortVectorLattice_covolume_le_of_points
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (R N : ℝ) (hR : 0 ≤ R) (hN : 0 < N)
    (P : Finset E) (hP : ∀ p ∈ P, p ∈ Λ ∧ ‖p‖ ≤ R) (hcard : N ≤ (P.card : ℝ)) :
    ZLattice.covolume (shortVectorLattice Λ R) ≤
      (((finrank ℝ (shortVectorSpan Λ R) : ℝ) + 2) * R) ^
        finrank ℝ (shortVectorSpan Λ R) / N := by
  classical
  let f : P → shortVectorLattice Λ R := fun p =>
    ⟨⟨p.val, mem_shortVectorSpan Λ R (hP p.val p.property).1 (hP p.val p.property).2⟩,
      (hP p.val p.property).1⟩
  have hf : Function.Injective f := by
    intro p q hpq
    exact Subtype.ext (congrArg (fun z : shortVectorLattice Λ R => z.val.val) hpq)
  let Q : Finset (shortVectorLattice Λ R) := Finset.univ.image f
  have hQcard : Q.card = P.card := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hQ : ∀ q ∈ Q, ‖(q : shortVectorSpan Λ R)‖ ≤ R := by
    intro q hq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hP p.val p.property).2
  exact shortVectorLattice_covolume_le Λ R N hR hN Q hQ (hQcard ▸ hcard)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanGraphNorm
namespace OAI

section

namespace Erdos3

theorem euclidean_graph_gram {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (A : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    Matrix.gram ℝ (fun i => productEuclideanEquiv (Pi.basisFun ℝ σ i, A (Pi.basisFun ℝ σ i))) =
      1 + (LinearMap.toMatrix' A).transpose * LinearMap.toMatrix' A := by
  ext i j
  simp only [Matrix.gram_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fintype.sum_sum_type, Pi.star_apply, star_trivial, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, LinearMap.toMatrix'_apply]
  change (∑ k : σ, (Pi.basisFun ℝ σ j) k * (Pi.basisFun ℝ σ i) k) +
      (∑ k : κ, A (Pi.basisFun ℝ σ j) k * A (Pi.basisFun ℝ σ i) k) = _
  congr 1
  · simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
  · apply Finset.sum_congr rfl
    intro k _
    simpa only [Pi.basisFun_apply] using
      mul_comm (A (Pi.single j 1) k) (A (Pi.single i 1) k)

theorem euclidean_section_gram {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i) :
    let A := ((LinearMap.snd ℝ (σ → ℝ) (κ → ℝ)).comp
      productEuclideanEquiv.symm.toLinearMap).comp (Z.subtype.comp G)
    Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i)) =
      1 + (LinearMap.toMatrix' A).transpose * LinearMap.toMatrix' A := by
  let A := ((LinearMap.snd ℝ (σ → ℝ) (κ → ℝ)).comp
    productEuclideanEquiv.symm.toLinearMap).comp (Z.subtype.comp G)
  have he (y : σ → ℝ) : (G y).val = productEuclideanEquiv (y, A y) := by
    apply PiLp.ext
    intro i
    cases i with
    | inl i => exact hG y i
    | inr j => rfl
  change Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i)) = _
  calc
    _ = Matrix.gram ℝ (fun i => productEuclideanEquiv
        (Pi.basisFun ℝ σ i, A (Pi.basisFun ℝ σ i))) := by
      ext i j
      change inner ℝ (G (Pi.basisFun ℝ σ i)).val (G (Pi.basisFun ℝ σ j)).val = _
      rw [he, he]
      rfl
    _ = _ := euclidean_graph_gram A

end Erdos3

end

section

namespace Erdos3

theorem euclidean_section_gram_sub_one_posSemidef
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i) :
    (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i)) - 1).PosSemidef := by
  let A := ((LinearMap.snd ℝ (σ → ℝ) (κ → ℝ)).comp
    productEuclideanEquiv.symm.toLinearMap).comp (Z.subtype.comp G)
  have he : Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i)) =
      1 + (LinearMap.toMatrix' A).transpose * LinearMap.toMatrix' A :=
    euclidean_section_gram Z G hG
  rw [he, add_sub_cancel_left]
  have hp := Matrix.posSemidef_conjTranspose_mul_self (LinearMap.toMatrix' A)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hp
  exact hp

theorem one_le_euclidean_section_gram_sqrt
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i) :
    1 ≤ Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det := by
  have hd := one_le_det_of_sub_one_posSemidef (Matrix.isHermitian_gram ℝ _)
    (euclidean_section_gram_sub_one_posSemidef Z G hG)
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hd

theorem euclidean_section_norm_le_gram_sqrt
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i)
    (x : σ → ℝ) :
    ‖G x‖ ≤ Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det *
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ σ)‖ :=
  norm_le_sqrt_gram_det_mul G (euclidean_section_gram_sub_one_posSemidef Z G hG) x

theorem euclidean_section_basis_norm_le_gram_sqrt
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i)
    (i : σ) :
    ‖G (Pi.basisFun ℝ σ i)‖ ≤
      Real.sqrt (Matrix.gram ℝ (fun j => G (Pi.basisFun ℝ σ j))).det := by
  simpa only [Pi.basisFun_apply, PiLp.toLp_single, PiLp.norm_single, norm_one, mul_one] using
    euclidean_section_norm_le_gram_sqrt Z G hG (Pi.basisFun ℝ σ i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScaledSectionGram
namespace OAI

section

namespace Erdos3

open Module

theorem coordinateScaleEquiv_basis_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℝ) (hT : ∀ i, T i ≠ 0) :
    (Pi.basisFun ℝ ι).det ((Pi.basisFun ℝ ι).map (coordinateScaleEquiv T hT)) = ∏ i, T i := by
  rw [Pi.basisFun_det_apply]
  have he : Matrix.of ((Pi.basisFun ℝ ι).map (coordinateScaleEquiv T hT)) = Matrix.diagonal T := by
    ext i j
    by_cases hij : i = j <;>
      simp [Basis.map_apply, coordinateScaleEquiv_apply, Pi.basisFun_apply, hij]
  rw [he, Matrix.det_diagonal]

theorem scaled_section_gram_sqrt {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : (ι → ℝ) →ₗ[ℝ] E) (hL : Function.Injective L)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i) :
    Real.sqrt (Matrix.gram ℝ (fun i => L (coordinateScaleEquiv T (fun j => (hT j).ne')
      (Pi.basisFun ℝ ι i)))).det =
      (∏ i, T i) * Real.sqrt (Matrix.gram ℝ (fun i => L (Pi.basisFun ℝ ι i))).det := by
  have h := gram_det_injective_map_basis L hL (Pi.basisFun ℝ ι)
    ((Pi.basisFun ℝ ι).map (coordinateScaleEquiv T (fun j => (hT j).ne')))
  rw [coordinateScaleEquiv_basis_det] at h
  have he := congrArg Real.sqrt h
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Finset.prod_nonneg (fun i _ => (hT i).le))] at he
  simpa only [Basis.map_apply] using he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeCoordinateLifts
namespace OAI

section

namespace Erdos3

open Module MeasureTheory

variable {ι : Type*} [Fintype ι]

theorem mem_integerCoordinateLattice_iff (x : ι → ℝ) :
    x ∈ integerCoordinateLattice ↔ x ∈ realIntegerGrid := by
  change x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔ _
  rw [(Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ x]
  constructor
  · intro hx
    have h : ∀ i, ∃ n : ℤ, (n : ℝ) = x i := by
      intro i
      simpa using hx i
    choose z hz using h
    exact ⟨z, funext hz⟩
  · rintro ⟨z, hz⟩ i
    exact ⟨z i, by simpa using congrFun hz i⟩

theorem integer_lattice_index_nsmul_mem (L : Submodule ℤ (ι → ℝ))
    (x : ι → ℝ) (hx : x ∈ realIntegerGrid) :
    L.toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup • x ∈ L :=
  L.toAddSubgroup.nsmul_relIndex_mem ((mem_integerCoordinateLattice_iff x).mpr hx)

end Erdos3

end

section

namespace Erdos3

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι]
  (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))

theorem latticeImage_le_integer (hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid) :
    latticeImage Λ π ≤ integerCoordinateLattice := by
  rintro y ⟨x, hx, rfl⟩
  exact (mem_integerCoordinateLattice_iff _).mpr (hπ x hx)

theorem latticeImage_discrete (hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid) :
    DiscreteTopology (latticeImage Λ π) := by
  apply isDiscrete_iff_discreteTopology.mp
  apply isDiscrete_realIntegerGrid.mono
  intro y hy
  exact (mem_integerCoordinateLattice_iff y).mp (latticeImage_le_integer Λ π hπ hy)

theorem latticeImage_full [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    [DiscreteTopology (latticeImage Λ π)] (hπ : Function.Surjective π) :
    IsZLattice ℝ (latticeImage Λ π) := by
  constructor
  change Submodule.span ℝ (π '' (Λ : Set E)) = ⊤
  rw [Submodule.span_image, IsZLattice.span_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hπ

theorem latticeImage_index_lift (x : ι → ℝ) (hx : x ∈ realIntegerGrid) :
    ∃ y ∈ Λ, π y = (latticeImage Λ π).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup • x := by
  exact integer_lattice_index_nsmul_mem (latticeImage Λ π) x hx

theorem latticeImage_index_pos [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hinteger : ∀ x ∈ Λ, π x ∈ realIntegerGrid) (hsurj : Function.Surjective π) :
    0 < (latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup := by
  let : DiscreteTopology (latticeImage Λ π) := latticeImage_discrete Λ π hinteger
  let : IsZLattice ℝ (latticeImage Λ π) := latticeImage_full Λ π hsurj
  exact integer_lattice_index_pos (latticeImage Λ π) (latticeImage_le_integer Λ π hinteger)

end Erdos3

end

section

namespace Erdos3

theorem basisFun_mem_realIntegerGrid {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Pi.basisFun ℝ ι i ∈ realIntegerGrid := by
  refine ⟨Pi.single i (1 : ℤ), ?_⟩
  funext j
  simp [Pi.basisFun_apply, Pi.single_apply]

theorem latticeImage_basis_lifts {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ)) :
    let I := (latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup
    ∀ i, ∃ x ∈ Λ, π x = (I : ℝ) • Pi.basisFun ℝ ι i := by
  intro I i
  obtain ⟨x, hx, hπx⟩ := latticeImage_index_lift Λ π (Pi.basisFun ℝ ι i)
    (basisFun_mem_realIntegerGrid i)
  refine ⟨x, hx, ?_⟩
  simpa only [Nat.cast_smul_eq_nsmul] using hπx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScaledLatticeCovolume
namespace OAI

section

namespace Erdos3

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))

def latticeImageProjection : Λ →ₗ[ℤ] latticeImage Λ π :=
  ((π.restrictScalars ℤ).comp Λ.subtype).codRestrict (latticeImage Λ π)
    (fun x => ⟨x.val, x.property, rfl⟩)

theorem latticeImageProjection_surjective : Function.Surjective (latticeImageProjection Λ π) := by
  rintro ⟨y, x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

noncomputable def latticeKernelEquiv :
    latticeKernel Λ π ≃ₗ[ℤ] LinearMap.ker (latticeImageProjection Λ π) where
  toFun x := ⟨⟨x.val.val, x.property⟩, Subtype.ext x.val.property⟩
  invFun x := ⟨⟨x.val.val, congrArg Subtype.val
    (show latticeImageProjection Λ π x.val = 0 from x.property)⟩, x.val.property⟩
  left_inv _x := rfl
  right_inv _x := rfl
  map_add' _x _y := rfl
  map_smul' _a _x := rfl

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_lattice_split_basis
    {E ι α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))
    (bK : Basis α ℤ (latticeKernel Λ π)) (bI : Basis β ℤ (latticeImage Λ π)) :
    ∃ b : Basis (α ⊕ β) ℤ Λ,
      (∀ i, (b (Sum.inl i) : E) = (bK i).val.val) ∧
      (∀ j, π (b (Sum.inr j) : E) = (bI j).val) := by
  let : Free ℤ (latticeImage Λ π) := Free.of_basis bI
  obtain ⟨b, hbK, hbI⟩ := exists_basis_of_surjection (latticeImageProjection Λ π)
    (latticeImageProjection_surjective Λ π) (bK.map (latticeKernelEquiv Λ π)) bI
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [hbK]
    rfl
  · intro j
    exact congrArg Subtype.val (hbI j)

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

omit [Fintype σ] [Fintype κ] in
theorem euclideanDerivativeShiftMap_apply (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (v : EuclideanSpace ℝ (σ ⊕ κ)) (i : σ) :
    euclideanDerivativeShiftMap T hT v i = T i * v (Sum.inl i) := rfl

omit [Fintype σ] [Fintype κ] in
theorem euclideanDerivativeShiftMap_eq_zero_iff (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (v : EuclideanSpace ℝ (σ ⊕ κ)) :
    euclideanDerivativeShiftMap T hT v = 0 ↔ ∀ i : σ, v (Sum.inl i) = 0 := by
  simp only [funext_iff, euclideanDerivativeShiftMap_apply, Pi.zero_apply,
    mul_eq_zero, hT, false_or]

end Erdos3

end

section

namespace Erdos3

theorem euclidean_graph_residual_mem_kernel
    {σ κ : Type*} [Fintype σ] [Fintype κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i) (x : Z) :
    x - G (fun i => x.val (Sum.inl i)) ∈
      LinearMap.ker ((euclideanDerivativeShiftMap T hT).comp Z.subtype) := by
  change euclideanDerivativeShiftMap T hT
    ((x - G (fun i => x.val (Sum.inl i))).val) = 0
  apply (euclideanDerivativeShiftMap_eq_zero_iff T hT _).mpr
  intro i
  change x.val (Sum.inl i) - (G (fun j => x.val (Sum.inl j))).val (Sum.inl i) = 0
  rw [hG, sub_self]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedMinorBounds
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem euclidean_matrix_mulVec_norm_le {ι : Type*} [Fintype ι] {k : ℕ}
    (M : Matrix ι (Fin k) ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hM : ∀ i j, |M i j| ≤ H) (x : Fin k → ℝ) :
    ‖(EuclideanSpace.equiv ι ℝ).symm (M *ᵥ x)‖ ≤
      (Fintype.card ι : ℝ) * k * H * ‖x‖ := by
  have hi (i : ι) : |(M *ᵥ x) i| ≤ (k : ℝ) * H * ‖x‖ := by
    calc
      _ ≤ ∑ j, |M i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin k, H * ‖x‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hM i j)
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j) (abs_nonneg _) hH
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; ring
  calc
    _ ≤ ∑ i, |(M *ᵥ x) i| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ _i : ι, (k : ℝ) * H * ‖x‖ := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LayerOneTransportBudget
namespace OAI

section

namespace Erdos3

theorem layerOne_basis_transport_height_le_exp (a m J : ℕ) (C p : ℝ)
    (hp : 0 ≤ p) (ha : (a : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hC0 : 0 ≤ C) (hC : C ≤ Real.exp p) (hJ : (J : ℝ) ≤ Real.exp p) :
    (((a + 1) * (max m (Nat.ceil ((m : ℝ) * C)) * J) ^ a : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 3) := by
  have hprod : (m : ℝ) * C ≤ Real.exp (2 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hm hC hC0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hheight : ((max m (Nat.ceil ((m : ℝ) * C)) : ℕ) : ℝ) ≤ Real.exp (2 * p + 1) := by
    rw [Nat.cast_max]
    apply max_le
    · exact hm.trans (Real.exp_le_exp.mpr (by linarith))
    · calc
        _ ≤ (Nat.ceil (Real.exp (2 * p)) : ℝ) := Nat.cast_le.mpr (Nat.ceil_mono hprod)
        _ ≤ _ := ceil_exp_le_exp_add_one (by positivity)
  have hHJ : ((max m (Nat.ceil ((m : ℝ) * C)) : ℕ) : ℝ) * J ≤ Real.exp (3 * p + 1) := by
    calc
      _ ≤ Real.exp (2 * p + 1) * Real.exp p :=
        mul_le_mul hheight hJ (Nat.cast_nonneg J) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg J)) hHJ a
  rw [← Real.exp_nat_mul] at hpow
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_mul]
  calc
    _ ≤ Real.exp a * Real.exp ((a : ℝ) * (3 * p + 1)) :=
      mul_le_mul (Real.add_one_le_exp a) hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp ((a : ℝ) * (3 * p + 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (p * (3 * p + 2)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha (by positivity))
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hp (sq_nonneg p)])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℝ W]
  (U : Submodule ℚ V)

theorem realification_mkQ_ker : LinearMap.ker (U.mkQ.baseChange ℝ) = U.baseChange ℝ := by
  rw [← realification_ker, Submodule.ker_mkQ]

noncomputable def realQuotientEquiv :
    (ℝ ⊗[ℚ] (V ⧸ U)) ≃ₗ[ℝ] ((ℝ ⊗[ℚ] V) ⧸ U.baseChange ℝ) :=
  (U.mkQ.baseChange ℝ).quotKerEquivOfSurjective
    (realification_mkQ_surjective U) |>.symm |>.trans
      (Submodule.quotEquivOfEq _ _ (realification_mkQ_ker U))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DerivativeLatticeDivision
namespace OAI

section

namespace Erdos3

theorem realDenominatorGrid_div_nat {ι : Type*} (l I : ℕ) (hI : 0 < I)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) :
    ((I : ℝ)⁻¹ • x) ∈ realDenominatorGrid (l * I) := by
  have hIr : (I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  obtain ⟨z, hz⟩ := hx
  refine ⟨z, ?_⟩
  funext i
  have hi := congrFun hz i
  change (z i : ℝ) = (l : ℝ) * x i at hi
  change (z i : ℝ) = ((l * I : ℕ) : ℝ) * ((I : ℝ)⁻¹ * x i)
  rw [hi, Nat.cast_mul]
  field_simp

theorem divided_derivative_horizontal_coordinates
    {σ κ : Type*} [Fintype σ] [Fintype κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (I : ℕ) (hI : 0 < I)
    (y : σ → ℝ) (v : EuclideanSpace ℝ (σ ⊕ κ))
    (hshift : euclideanDerivativeShiftMap T hT v = (I : ℝ) • y) :
    ∀ i, ((I : ℝ)⁻¹ • v) (Sum.inl i) = y i / T i := by
  have hIr : (I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  intro i
  have hi := congrFun hshift i
  change T i * v (Sum.inl i) = (I : ℝ) * y i at hi
  have hv : v (Sum.inl i) = ((I : ℝ) * y i) / T i :=
    (eq_div_iff (hT i)).mpr (by simpa only [mul_comm] using hi)
  change (I : ℝ)⁻¹ * v (Sum.inl i) = _
  rw [hv]
  field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EuclideanLatticeGraph
namespace OAI

section

namespace Erdos3

theorem euclidean_shift_subspace_surjective
    {σ κ : Type*} [Fintype σ] [Fintype κ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (hproj : Z.map ((LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp
      productEuclideanEquiv.symm.toLinearMap) = ⊤) :
    Function.Surjective ((euclideanDerivativeShiftMap T hT).comp Z.subtype) := by
  have hmap : Z.map (euclideanDerivativeShiftMap T hT) = ⊤ := by
    change Z.map ((coordinateScaleEquiv T hT).toLinearMap.comp
      ((LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap)) = ⊤
    rw [Submodule.map_comp, hproj, Submodule.map_top]
    exact (coordinateScaleEquiv T hT).range
  intro x
  have hx : x ∈ Z.map (euclideanDerivativeShiftMap T hT) := by rw [hmap]; trivial
  obtain ⟨v, hv, he⟩ := hx
  exact ⟨⟨v, hv⟩, he⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerMinorNormalization
namespace OAI

section

namespace Erdos3

theorem integer_row_normalization_height {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (p : Fin k → ι) (hp : (Z.submatrix p id).det ≠ 0)
    (N : ℕ) (hN : ∀ q : Fin k → ι, (Z.submatrix q id).det.natAbs ≤ N)
    (i : ι) (j : Fin k) :
    let H := Z.map (Int.castRingHom ℚ)
    RationalHeightLE ((H * (H.submatrix p id)⁻¹) i j) N := by
  dsimp only
  rw [integer_row_normalization_entry Z p hp i j]
  exact rationalHeightLE_fraction _ _ hp (hN _) (hN _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.EuclideanVerticalProjection
namespace OAI

section

namespace Erdos3

noncomputable def euclideanVerticalProjection {σ κ : Type*} :
    EuclideanSpace ℝ (σ ⊕ κ) →ₗ[ℝ] EuclideanSpace ℝ κ :=
  (EuclideanSpace.equiv κ ℝ).symm.toLinearMap.comp
    ((LinearMap.snd ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap)

@[simp] theorem euclideanVerticalProjection_apply {σ κ : Type*}
    (x : EuclideanSpace ℝ (σ ⊕ κ)) (j : κ) :
    euclideanVerticalProjection x j = x (Sum.inr j) := rfl

theorem euclideanVerticalProjection_norm_le {σ κ : Type*} [Fintype σ] [Fintype κ]
    (x : EuclideanSpace ℝ (σ ⊕ κ)) : ‖euclideanVerticalProjection x‖ ≤ ‖x‖ := by
  have hs : ‖euclideanVerticalProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
    simp only [euclideanVerticalProjection_apply]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => sq_nonneg ‖x (Sum.inl i)‖))
  nlinarith [norm_nonneg (euclideanVerticalProjection x), norm_nonneg x]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.GridNormalizationDenominator
namespace OAI

section

namespace Erdos3

theorem integer_row_normalization_grid {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (p : Fin k → ι) (hp : (Z.submatrix p id).det ≠ 0) :
    let W := Z.map (Int.castRingHom ℚ)
    ∀ j, (W * (W.submatrix p id)⁻¹).col j ∈
      denominatorGrid (Z.submatrix p id).det.natAbs := by
  let d := (Z.submatrix p id).det
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast hp
  have habs : (d.natAbs : ℚ) = (d.sign : ℚ) * (d : ℚ) := by
    calc
      _ = ((d.natAbs : ℤ) : ℚ) := (Int.cast_natCast _).symm
      _ = ((d.sign * d : ℤ) : ℚ) :=
        congrArg (fun z : ℤ => (z : ℚ)) (Int.sign_mul_self_eq_natAbs d).symm
      _ = _ := Int.cast_mul _ _
  dsimp only
  intro j
  refine ⟨fun i => d.sign * (Z.submatrix (Function.update p j i) id).det, fun i => ?_⟩
  change (d.natAbs : ℚ) *
    ((Z.map (Int.castRingHom ℚ) * ((Z.map (Int.castRingHom ℚ)).submatrix p id)⁻¹) i j) = _
  rw [integer_row_normalization_entry Z p hp i j]
  change (d.natAbs : ℚ) * (_ / (d : ℚ)) = _
  rw [habs, Int.cast_mul]
  field_simp

end Erdos3

end

end OAI
end


