-- Prove2me | Definitions.Def_OAIErdos3B039
-- name    : OAIErdos3B039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T04:03:36.627074+00:00
-- url     : https://prove2.me/theorems/6ec3c94c-dfe8-4e91-b877-a4a7bff06c60
-- title:
--   OpenAI Erdős-3 split, definitions bundle 40 of 132
-- statement:
--   Definitions bundle 40 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B038`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 40 available.
--
--   Modules: `OAI.Erdos3.DilationBudget.ambient`, `OAI.Erdos3.DilationBudget.ambient_bounds`, `OAI.Erdos3.DilationBudget.common`, `OAI.Erdos3.DilationBudget.common_bounds`, `OAI.Erdos3.DilationBudget.exists_full_bound`, `OAI.Erdos3.DilationBudget.height`, `OAI.Erdos3.DilationBudget.observable_bound`, `OAI.Erdos3.DilationBudget.quotient`, `OAI.Erdos3.DilationBudget.quotient_bounds`, `OAI.Erdos3.DilationBudget.reconstruction`, `OAI.Erdos3.DilationBudget.reconstruction_bounds`, `OAI.Erdos3.DilationBudget.shift`, `OAI.Erdos3.DilationBudget.shift_bounds`, `OAI.Erdos3.DilationBudget.total`, `OAI.Erdos3.DilationBudget.total_bounds`, `OAI.Erdos3.MultidegreeLieFiltration.exists_weighted_layer_coordinate_basis`, `OAI.Erdos3.MultidegreeLieFiltration.weightedLayerEquiv`, `OAI.Erdos3.MultilinearityBudget.ambient`, `OAI.Erdos3.MultilinearityBudget.ambient_bounds`, `OAI.Erdos3.MultilinearityBudget.coordinates`, `OAI.Erdos3.MultilinearityBudget.exists_total_bound`, `OAI.Erdos3.MultilinearityBudget.observable`, `OAI.Erdos3.MultilinearityBudget.observable_bound`, `OAI.Erdos3.MultilinearityBudget.observable_nonneg`, `OAI.Erdos3.MultilinearityBudget.quotient`, `OAI.Erdos3.MultilinearityBudget.quotient_bounds`, `OAI.Erdos3.MultilinearityBudget.reconstruction`, `OAI.Erdos3.MultilinearityBudget.reconstruction_bounds`, `OAI.Erdos3.MultilinearityBudget.total`, `OAI.Erdos3.MultilinearityBudget.total_bounds`, `OAI.Erdos3.NilpotentLieFiltration.exists_allocatedCandidateCommonFastGeometry`, `OAI.Erdos3.NilpotentLieFiltration.exists_common_refiltered_factorization`, `OAI.Erdos3.NilpotentLieFiltration.pointwiseFastSectionInput_mono`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.additiveTripleGeometryBudget`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.additiveTripleLattice`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.additiveTripleLattice_mem`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_additiveTriple_filtration_basis_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_additiveTriple_layer_basis_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_additiveTriple_model`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_coordinate_active_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_weighted_layer_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_weighted_model`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_weighted_model_of_bases`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.le_triple_basis_budget`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_topInvariant_niltest`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_topInvariant_niltest_budget`, `OAI.Erdos3.allocatedCandidateCommonFastBudget`, `OAI.Erdos3.allocatedCandidateCommonFastBudget_bounds`, `OAI.Erdos3.allocatedCandidateCommonFastBudget_mono`, `OAI.Erdos3.allocatedCandidateCommonFastCoordinateHeight`, `OAI.Erdos3.allocatedCandidateCommonFastCoordinateHeight_bounds`, `OAI.Erdos3.allocatedCandidateCommonFastGeneratorHeight_le`, `OAI.Erdos3.allocatedCandidateCommonFastGeometryLog`, `OAI.Erdos3.allocatedCandidateCommonFastGeometryLog_bounds`, `OAI.Erdos3.allocatedCandidateCommonFastGeometryLog_mono`, `OAI.Erdos3.allocatedCandidateCommonFastSectionInput`, `OAI.Erdos3.allocatedCandidateCommonFastSectionInput_bounds`, `OAI.Erdos3.allocatedCandidateCommonFastSectionInput_mono`, `OAI.Erdos3.basis_generator_matrix_range`, `OAI.Erdos3.continuousOutputBox`, `OAI.Erdos3.continuousOutputBoxMeasure`, `OAI.Erdos3.continuousOutputBoxMeasure_finite`, `OAI.Erdos3.coordinate_spanning_range`, `OAI.Erdos3.exists_binary_intersection_basis_logHeight`, `OAI.Erdos3.exists_bounded_submodule_quotient_section_with_coordinates`, `OAI.Erdos3.exists_intersection_spanning_logHeight`, `OAI.Erdos3.exists_submodule_quotient_presentation_exp_height`, `OAI.Erdos3.latticeGaussianNormalizer`, `OAI.Erdos3.lattice_covolume_sq_eq_gram`, `OAI.Erdos3.lattice_fundamentalDomain_volume`, `OAI.Erdos3.lattice_quotient_haar_countable_sheets`, `OAI.Erdos3.lattice_quotient_haar_image`, `OAI.Erdos3.lattice_quotient_haar_translated_image`, `OAI.Erdos3.lattice_quotient_scaled_haar`, `OAI.Erdos3.normalizedLatticeGaussian`, `OAI.Erdos3.orthogonalLattice_covolume`, `OAI.Erdos3.orthogonalLattice_covolume_sq`, `OAI.Erdos3.quotientInducedMarkHeightBudget_mono`, `OAI.Erdos3.zspan_covolume_sq_eq_det_gram_fintype`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B112

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

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def latticeGaussianNormalizer (Λ : Submodule ℤ E) (t : ℝ) : ℝ :=
  (Real.sqrt t) ^ Module.finrank ℝ E * ZLattice.covolume Λ

noncomputable def normalizedLatticeGaussian (Λ : Submodule ℤ E) (t : ℝ) (x : E) : ℝ :=
  latticeGaussianNormalizer Λ t * latticeGaussianMass Λ t x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem lattice_fundamentalDomain_volume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ) :
    volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) =
      ENNReal.ofReal (ZLattice.covolume Λ) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume
    (ZLattice.isAddFundamentalDomain b volume), measureReal_def,
    ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne]

theorem lattice_quotient_scaled_haar (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] :
    ENNReal.ofReal (ZLattice.covolume Λ) • μ =
      Measure.map (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup)
        (volume.restrict (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ))) := by
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)
  let : Countable Λ.toAddSubgroup := b.repr.injective.countable
  let : Countable Λ.toAddSubgroup.op := Λ.toAddSubgroup.equivOp.symm.injective.countable
  have hF : IsAddFundamentalDomain Λ.toAddSubgroup F volume :=
    ZLattice.isAddFundamentalDomain b volume
  have hop := additiveFundamentalDomain_op Λ.toAddSubgroup hF
  let : HasAddFundamentalDomain Λ.toAddSubgroup.op E volume := ⟨F, hop⟩
  have hclosed : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  let : IsClosed (Λ.toAddSubgroup : Set E) := hclosed
  let c := ENNReal.ofReal (ZLattice.covolume Λ)
  let : IsFiniteMeasure (c • μ) := μ.smul_finite ENNReal.ofReal_ne_top
  have hscale : addCovolume Λ.toAddSubgroup.op E volume = (c • μ) Set.univ := by
    rw [hop.covolume_eq_volume volume, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact lattice_fundamentalDomain_volume Λ b
  let : AddQuotientMeasureEqMeasurePreimage volume (c • μ) :=
    leftInvariantIsAddQuotientMeasureEqMeasurePreimage (ν := volume) hscale
  exact hop.addProjection_respects_measure (c • μ)

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module _root_.Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem lattice_quotient_haar_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {A : Set E} (hAm : MeasurableSet A)
    (hA : InjOn (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) A) :
    μ ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) '' A) =
      volume A / ENNReal.ofReal (ZLattice.covolume Λ) := by
  let : Countable Λ.toAddSubgroup := b.repr.injective.countable
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  have hq : Continuous (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) :=
    continuous_quotient_mk'
  have him := hAm.image_of_continuousOn_injOn hq.continuousOn hA
  have he := congrArg
    (fun ν : Measure (E ⧸ Λ.toAddSubgroup) => ν
      ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) '' A))
    (lattice_quotient_scaled_haar Λ b μ)
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hq.measurable him,
    Measure.restrict_apply (him.preimage hq.measurable)] at he
  rw [quotient_injective_lift_measure Λ.toAddSubgroup volume
    (ZLattice.isAddFundamentalDomain b volume)
    (ZSpan.fundamentalDomain_measurableSet _) hAm hA] at he
  exact (ENNReal.eq_div_iff (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos Λ volume)).ne'
    ENNReal.ofReal_ne_top).mpr he

theorem lattice_quotient_haar_translated_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : E) {A : Set E} (hAm : MeasurableSet A)
    (hA : InjOn (fun x => (QuotientAddGroup.mk (x - v) : E ⧸ Λ.toAddSubgroup)) A) :
    μ ((fun x => (QuotientAddGroup.mk (x - v) : E ⧸ Λ.toAddSubgroup)) '' A) =
      volume A / ENNReal.ofReal (ZLattice.covolume Λ) := by
  have hBm : MeasurableSet ((fun x : E => x - v) '' A) :=
    hAm.image_of_continuousOn_injOn (continuous_id.sub continuous_const).continuousOn
      (fun _ _ _ _ he => sub_left_inj.mp he)
  have hB : InjOn (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup)
      ((fun x : E => x - v) '' A) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    exact congrArg (fun z => z - v) (hA hx hy he)
  have hset : ((fun x : E => x - v) '' A) = (fun x => x + v) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, sub_add_cancel] using hy
    · intro hx
      exact ⟨x + v, hx, add_sub_cancel_right x v⟩
  have he := lattice_quotient_haar_image Λ b μ hBm hB
  rw [image_image] at he
  rw [he, hset, measure_preimage_add_right]

theorem lattice_quotient_haar_countable_sheets {T : Type*} [Countable T]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : T → E) (A : T → Set E) (hAm : ∀ t, MeasurableSet (A t))
    (hA : ∀ t, InjOn (fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) (A t))
    (hdisj : Pairwise (fun s t => Disjoint
      ((fun x => (QuotientAddGroup.mk (x - v s) : E ⧸ Λ.toAddSubgroup)) '' A s)
      ((fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) '' A t))) :
    μ (⋃ t, (fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) '' A t) =
      (∑' t, volume (A t)) / ENNReal.ofReal (ZLattice.covolume Λ) := by
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  rw [measure_iUnion hdisj (fun t => (hAm t).image_of_continuousOn_injOn
    (continuous_quotient_mk'.comp (continuous_id.sub continuous_const)).continuousOn (hA t))]
  simp_rw [lattice_quotient_haar_translated_image Λ b μ _ (hAm _) (hA _)]
  simpa only [div_eq_mul_inv] using ENNReal.tsum_mul_right

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem orthogonalLattice_covolume_sq (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E)
    [IsZLattice ℝ (latticeSection Λ Wᗮ)]
    [DiscreteTopology (orthogonalLatticeImage Λ W)] [IsZLattice ℝ (orthogonalLatticeImage Λ W)] :
    ZLattice.covolume Λ ^ 2 = ZLattice.covolume (latticeSection Λ Wᗮ) ^ 2 *
      ZLattice.covolume (orthogonalLatticeImage Λ W) ^ 2 := by
  classical
  let bK := Free.chooseBasis ℤ (latticeSection Λ Wᗮ)
  let bP := Free.chooseBasis ℤ (orthogonalLatticeImage Λ W)
  obtain ⟨b, hbK, hbP⟩ := exists_orthogonal_lattice_split_basis Λ W bK bP
  let B := b.ofZLatticeBasis ℝ Λ
  let K := bK.ofZLatticeBasis ℝ (latticeSection Λ Wᗮ)
  let P := bP.ofZLatticeBasis ℝ (orthogonalLatticeImage Λ W)
  have hleft (i) : B (Sum.inl i) = (K i : E) := by
    simpa only [B, K, Basis.ofZLatticeBasis_apply] using hbK i
  have hspan : span ℝ (Set.range (fun i => B (Sum.inl i))) = Wᗮ := by
    rw [show (fun i => B (Sum.inl i)) = (fun i => (K i : E)) from funext hleft]
    change span ℝ (Set.range (Wᗮ.subtype ∘ K)) = Wᗮ
    rw [Set.range_comp, ← Submodule.map_span, K.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hright (j) : B (Sum.inr j) - Wᗮ.starProjection (B (Sum.inr j)) = (P j : E) := by
    have hp : W.starProjection (B (Sum.inr j)) = (P j : E) := by
      simpa only [B, P, Basis.ofZLatticeBasis_apply, Submodule.coe_orthogonalProjectionOnto_apply]
        using congrArg Subtype.val (hbP j)
    have hsum := W.starProjection_add_starProjection_orthogonal (B (Sum.inr j))
    rw [hp] at hsum
    exact (eq_sub_iff_add_eq.mpr hsum).symm
  have hKGram : (Matrix.gram ℝ (fun i => B (Sum.inl i))).det =
      ZLattice.covolume (latticeSection Λ Wᗮ) ^ 2 := by
    have hg : Matrix.gram ℝ (fun i => B (Sum.inl i)) = Matrix.gram ℝ K := by
      ext i j
      simp only [Matrix.gram_apply, hleft]
      rfl
    rw [hg]
    exact (lattice_covolume_sq_eq_gram (latticeSection Λ Wᗮ) bK).symm
  have hPGram : (Matrix.gram ℝ (fun j => B (Sum.inr j) -
      Wᗮ.starProjection (B (Sum.inr j)))).det =
      ZLattice.covolume (orthogonalLatticeImage Λ W) ^ 2 := by
    have hg : Matrix.gram ℝ (fun j => B (Sum.inr j) - Wᗮ.starProjection (B (Sum.inr j))) =
        Matrix.gram ℝ P := by
      ext i j
      simp only [Matrix.gram_apply, hright]
      rfl
    rw [hg]
    exact (lattice_covolume_sq_eq_gram (orthogonalLatticeImage Λ W) bP).symm
  have hblock := gram_det_orthogonal_block B
  dsimp only at hblock
  rw [hspan, hKGram, hPGram] at hblock
  rw [lattice_covolume_sq_eq_gram Λ b]
  exact hblock

theorem orthogonalLattice_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E)
    [IsZLattice ℝ (latticeSection Λ Wᗮ)]
    [DiscreteTopology (orthogonalLatticeImage Λ W)] [IsZLattice ℝ (orthogonalLatticeImage Λ W)] :
    ZLattice.covolume Λ = ZLattice.covolume (latticeSection Λ Wᗮ) *
      ZLattice.covolume (orthogonalLatticeImage Λ W) := by
  apply (sq_eq_sq₀ (ZLattice.covolume_pos Λ volume).le
    (mul_nonneg (ZLattice.covolume_pos (latticeSection Λ Wᗮ) volume).le
      (ZLattice.covolume_pos (orthogonalLatticeImage Λ W) volume).le)).mp
  simpa only [mul_pow] using orthogonalLattice_covolume_sq Λ W

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module _root_.Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ContinuousOutputBox
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

def continuousOutputBox (I : Type*) (R : ℝ≥0) : Set (I → ℝ) :=
  Set.Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))

noncomputable def continuousOutputBoxMeasure (I : Type*) [Fintype I] (R : ℝ≥0) : Measure (I → ℝ) :=
  volume.restrict (continuousOutputBox I R)

instance continuousOutputBoxMeasure_finite (I : Type*) [Fintype I] (R : ℝ≥0) :
    IsFiniteMeasure (continuousOutputBoxMeasure I R) := by
  apply isFiniteMeasure_restrict.mpr
  rw [continuousOutputBox, Real.volume_Icc_pi]
  exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateCommonFastGeometry
namespace OAI

section

namespace Erdos3
open Module
open scoped Matrix

variable {ι η V : Type*} [Fintype ι] [Fintype η]
  [AddCommGroup V] [Module ℚ V]

theorem basis_generator_matrix_range (b : Basis ι ℚ V) (v : η → V)
    (U : Submodule ℚ V) (hspan : Submodule.span ℚ (Set.range v) = U) :
    LinearMap.range (Matrix.mulVecLin (show Matrix ι η ℚ from fun i j => b.repr (v j) i)) =
      U.map b.equivFun.toLinearMap := by
  rw [Matrix.range_mulVecLin, ← hspan, Submodule.map_span, ← Set.range_comp]
  rfl

theorem exists_submodule_quotient_presentation_exp_height
    [DecidableEq ι] (b : Basis ι ℚ V) (U : Submodule ℚ V) (v : η → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card η : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ D : Matrix (Fin d) ι ℚ, ∃ T : Matrix ι (Fin d) ℚ,
        LinearMap.ker D.mulVecLin = U.map b.equivFun.toLinearMap ∧ D * T = 1 ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 7)) ∧
        ∀ i j, ((T i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 45) ∧
          ((T i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 45) := by
  obtain ⟨d, hd, D, T, hker, hDT, hD, hT⟩ :=
    exists_quotient_presentation_exp_height (fun i j => b.repr (v j) i)
      hHpos hv hp hrows hcols hH
  exact ⟨d, hd, D, T, hker.trans (basis_generator_matrix_range b v U hspan), hDT, hD, hT⟩

end Erdos3

end

section

namespace Erdos3
open Module
open scoped Matrix TensorProduct Classical

theorem exists_bounded_submodule_quotient_section_with_coordinates
    {ι η V : Type*} [Fintype ι] [Fintype η] [DecidableEq ι]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (U : Submodule ℚ V) (v : η → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card η : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ (eQ : Basis (Fin d) ℚ (V ⧸ U)) (S : (V ⧸ U) →ₗ[ℚ] V) (qS : ℕ),
        Function.RightInverse S U.mkQ ∧
        Function.RightInverse (S.baseChange ℝ) (U.mkQ.baseChange ℝ) ∧
        0 < qS ∧ (qS : ℝ) ≤ Real.exp ((p + 2) ^ 47) ∧
        (∀ i j, |(b.baseChange ℝ).repr
          (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Real.exp ((p + 2) ^ 45)) ∧
        (∀ j, (fun i => (b.baseChange ℝ).repr
          (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS) ∧
        ∀ j i, RationalHeightLE (((eQ.coord j).comp U.mkQ) (b i))
          ⌈Real.exp ((p + 2) ^ 7)⌉₊ := by
  obtain ⟨d, hd, D, T, hker, hDT, hD, hT⟩ :=
    exists_submodule_quotient_presentation_exp_height b U v hspan hHpos hv hp hrows hcols hH
  obtain ⟨eQ, S, hright, hrightR, _hentryQ, hentryR, hcoord⟩ :=
    exists_submoduleQuotientSectionBasis_with_coordinates b U D T hker hDT
  have hdim : (Fintype.card (Fin d) : ℝ) ≤ p := by
    simp only [Fintype.card_fin]
    exact (Nat.cast_le.mpr hd).trans hrows
  obtain ⟨habs, qS, _heq, hqS, hqSbound, hgrid⟩ :=
    rational_section_entry_budget T hp hrows hdim hT
  refine ⟨d, hd, eQ, S, qS, hright, hrightR, hqS, hqSbound, ?_, ?_, ?_⟩
  · intro i j
    rw [hentryR]
    exact habs i j
  · intro j
    choose z hz using fun i => hgrid i j
    refine ⟨z, ?_⟩
    funext i
    change (z i : ℝ) = (qS : ℝ) * (b.baseChange ℝ).repr
      (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i
    rw [hentryR]
    exact (hz i).symm
  · intro j i
    change RationalHeightLE (eQ.repr (U.mkQ (b i)) j) _
    rw [hcoord]
    exact ⟨Nat.cast_le.mp ((hD j i).1.trans (Nat.le_ceil _)),
      Nat.cast_le.mp ((hD j i).2.trans (Nat.le_ceil _))⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Classical TensorProduct

def allocatedCandidateCommonFastSectionInput (p : ℝ) : ℝ := (p + 2) ^ 4 + 1

def allocatedCandidateCommonFastGeometryLog (p : ℝ) : ℝ :=
  (allocatedCandidateCommonFastSectionInput p + 2) ^ 47 + 1

noncomputable def allocatedCandidateCommonFastCoordinateHeight (p : ℝ) : ℕ :=
  ⌈Real.exp ((allocatedCandidateCommonFastSectionInput p + 2) ^ 7)⌉₊

theorem allocatedCandidateCommonFastSectionInput_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedCandidateCommonFastSectionInput p ∧
    p ≤ allocatedCandidateCommonFastSectionInput p := by
  have hbase : 1 ≤ p + 2 := by linarith
  have hp4 : p + 2 ≤ (p + 2) ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ (4 : ℕ) by omega)
  dsimp [allocatedCandidateCommonFastSectionInput]
  constructor <;> linarith

theorem allocatedCandidateCommonFastGeometryLog_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedCandidateCommonFastGeometryLog p ∧
    allocatedCandidateCommonFastSectionInput p ≤ allocatedCandidateCommonFastGeometryLog p := by
  have hq := (allocatedCandidateCommonFastSectionInput_bounds hp).1
  have hbase : 1 ≤ allocatedCandidateCommonFastSectionInput p + 2 := by linarith
  have hpow : allocatedCandidateCommonFastSectionInput p + 2 ≤
      (allocatedCandidateCommonFastSectionInput p + 2) ^ 47 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ (47 : ℕ) by omega)
  dsimp [allocatedCandidateCommonFastGeometryLog]
  constructor <;> linarith

theorem allocatedCandidateCommonFastCoordinateHeight_bounds {p : ℝ} (hp : 0 ≤ p) :
    1 ≤ allocatedCandidateCommonFastCoordinateHeight p ∧
    (allocatedCandidateCommonFastCoordinateHeight p : ℝ) ≤
      Real.exp (allocatedCandidateCommonFastGeometryLog p) := by
  refine ⟨one_le_ceil_exp _, ?_⟩
  have hq := (allocatedCandidateCommonFastSectionInput_bounds hp).1
  apply (ceil_exp_le_exp_add_one (by positivity :
    0 ≤ (allocatedCandidateCommonFastSectionInput p + 2) ^ 7)).trans
  apply Real.exp_le_exp.mpr
  have hpow := pow_le_pow_right₀ (by linarith :
    1 ≤ allocatedCandidateCommonFastSectionInput p + 2) (by omega : 7 ≤ (47 : ℕ))
  dsimp [allocatedCandidateCommonFastGeometryLog]
  linarith only [hpow]

def allocatedCandidateCommonFastBudget (s : ℕ) (p : ℝ) : ℝ :=
  allocatedCandidateCommonFastGeometryLog p +
    NilpotentLieFiltration.pointwiseFastSectionInput s p

theorem allocatedCandidateCommonFastBudget_bounds (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    allocatedCandidateCommonFastGeometryLog p ≤ allocatedCandidateCommonFastBudget s p ∧
    NilpotentLieFiltration.pointwiseFastSectionInput s p ≤ allocatedCandidateCommonFastBudget s p ∧
    p ≤ allocatedCandidateCommonFastBudget s p := by
  have hgeom := allocatedCandidateCommonFastGeometryLog_bounds hp
  have hpoint : 0 ≤ NilpotentLieFiltration.pointwiseFastSectionInput s p := by
    dsimp [NilpotentLieFiltration.pointwiseFastSectionInput]
    positivity
  have hpg := (allocatedCandidateCommonFastSectionInput_bounds hp).2.trans hgeom.2
  dsimp [allocatedCandidateCommonFastBudget]
  constructor
  · linarith only [hpoint]
  constructor
  · linarith only [hgeom.1]
  · linarith only [hpg, hpoint]

theorem allocatedCandidateCommonFastGeneratorHeight_le {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤
      Real.exp (allocatedCandidateCommonFastGeometryLog p) := by
  apply (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4)).trans
  exact Real.exp_le_exp.mpr (allocatedCandidateCommonFastGeometryLog_bounds hp).2

namespace NilpotentLieFiltration

variable {ι κ γ L M : Type*} [Fintype ι] [Fintype κ] [Fintype γ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (v : γ → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)

local notation "fast" => W.map (F.associatedGradedMap G φ hφ)
local notation "bg" => G.associatedGradedBasis c ν hG

include hv hW in

theorem exists_allocatedCandidateCommonFastGeometry
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hγ : (Fintype.card γ : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ p) :
    ∃ d : ℕ, d ≤ Fintype.card κ ∧
      ∃ (eQ : Basis (Fin d) ℚ (G.AssociatedGraded ⧸ (fast).toSubmodule))
        (lift : (G.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] G.AssociatedGraded)
        (qS : ℕ),
        BasisGradedSubmodule bg ν (fast).toSubmodule ∧
        Function.RightInverse lift (fast).toSubmodule.mkQ ∧
        Function.RightInverse (lift.baseChange ℝ) ((fast).toSubmodule.mkQ.baseChange ℝ) ∧
        0 < qS ∧ (qS : ℝ) ≤ Real.exp (allocatedCandidateCommonFastGeometryLog p) ∧
        (∀ i j, |((bg).baseChange ℝ).repr
          (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤
            Real.exp (allocatedCandidateCommonFastGeometryLog p)) ∧
        (∀ j, (fun i => ((bg).baseChange ℝ).repr
          (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS) ∧
        (∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ) (bg i))
          (allocatedCandidateCommonFastCoordinateHeight p)) ∧
        1 ≤ allocatedCandidateCommonFastCoordinateHeight p ∧
        (allocatedCandidateCommonFastCoordinateHeight p : ℝ) ≤
          Real.exp (allocatedCandidateCommonFastGeometryLog p) := by
  classical
  obtain ⟨hspan, hfast, hheight⟩ :=
    F.gradedImage_bounded_spanning G φ hφ b ω hF c ν hG W v hv hW hp hι hvH hφH
  have hq0 := (allocatedCandidateCommonFastSectionInput_bounds hp).1
  have hpq := (allocatedCandidateCommonFastSectionInput_bounds hp).2
  obtain ⟨d, hd, eQ, lift, qS, hsection, hsectionR, hqS, hqSbound, hentry, hgrid, hθ⟩ :=
    exists_bounded_submodule_quotient_section_with_coordinates bg (fast).toSubmodule
      (F.gradedImageSpanningFamily G φ hφ v) hspan
      (one_le_ceil_exp ((p + 2) ^ 4))
      (fun i a => rationalHeightLE_ceil_exp (hheight a i))
      hq0 (hκ.trans hpq) (hγ.trans hpq)
      (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4))
  refine ⟨d, hd, eQ, lift, qS, hfast, hsection, hsectionR, hqS, ?_, ?_, hgrid,
    hθ, allocatedCandidateCommonFastCoordinateHeight_bounds hp⟩
  · exact hqSbound.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right (by norm_num)))
  · intro i j
    apply (hentry i j).trans
    apply Real.exp_le_exp.mpr
    apply (pow_le_pow_right₀ (by linarith :
      1 ≤ allocatedCandidateCommonFastSectionInput p + 2) (by omega : 45 ≤ (47 : ℕ))).trans
    exact le_add_of_nonneg_right (by norm_num)

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateCommonFastBudgetMonotonicity
namespace OAI

section

namespace Erdos3

theorem allocatedCandidateCommonFastSectionInput_mono {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    allocatedCandidateCommonFastSectionInput p ≤ allocatedCandidateCommonFastSectionInput q := by
  unfold allocatedCandidateCommonFastSectionInput
  exact add_le_add
    (pow_le_pow_left₀ (by positivity : 0 ≤ p + 2) (add_le_add hpq (le_refl 2)) 4) (le_refl 1)

theorem allocatedCandidateCommonFastGeometryLog_mono {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    allocatedCandidateCommonFastGeometryLog p ≤ allocatedCandidateCommonFastGeometryLog q := by
  have hinput := allocatedCandidateCommonFastSectionInput_mono hp hpq
  have hnonneg := (allocatedCandidateCommonFastSectionInput_bounds hp).1
  unfold allocatedCandidateCommonFastGeometryLog
  exact add_le_add
    (pow_le_pow_left₀ (by positivity : 0 ≤ allocatedCandidateCommonFastSectionInput p + 2)
      (add_le_add hinput (le_refl 2)) 47) (le_refl 1)

theorem NilpotentLieFiltration.pointwiseFastSectionInput_mono (s : ℕ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    NilpotentLieFiltration.pointwiseFastSectionInput s p ≤
      NilpotentLieFiltration.pointwiseFastSectionInput s q := by
  have hbase : p + ((s : ℝ) + 3) ≤ q + ((s : ℝ) + 3) := add_le_add hpq le_rfl
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ p + ((s : ℝ) + 3)) hbase (s + 3)
  have hsquare := pow_le_pow_left₀
    (by positivity : 0 ≤ (p + ((s : ℝ) + 3)) ^ (s + 3)) hpow 2
  exact add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hpow (by norm_num)) hsquare) hpq

theorem allocatedCandidateCommonFastBudget_mono (s : ℕ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    allocatedCandidateCommonFastBudget s p ≤ allocatedCandidateCommonFastBudget s q := by
  exact add_le_add (allocatedCandidateCommonFastGeometryLog_mono hp hpq)
    (NilpotentLieFiltration.pointwiseFastSectionInput_mono s hp hpq)

theorem quotientInducedMarkHeightBudget_mono {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    quotientInducedMarkHeightBudget p ≤ quotientInducedMarkHeightBudget q := by
  have hseven := pow_le_pow_left₀ (by positivity : 0 ≤ p + 3) (add_le_add hpq (le_refl 3)) 7
  unfold quotientInducedMarkHeightBudget
  exact pow_le_pow_left₀ (by positivity : 0 ≤ p + (p + 3) ^ 7 + 3)
    (add_le_add (add_le_add hpq hseven) (le_refl 3)) 4

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.DilationBudgets
namespace OAI

section

namespace Erdos3.DilationBudget

open RationalFilteredNilmanifold
open scoped NNReal

noncomputable def height (q : ℤ) : ℕ := ⌈rationalLogHeight (q : ℚ)⌉₊

noncomputable def shift (q : ℤ) (p : ℝ) : ℝ := p + height q

noncomputable def ambient (t : ℕ) (q : ℤ) (p : ℝ) : ℝ :=
  shift q p + dilationPairGeometryBudget t (shift q p) + 2 * (shift q p + 1)

noncomputable def quotient (t : ℕ) (q : ℤ) (p : ℝ) : ℝ := (ambient t q p + 3) ^ 11

noncomputable def common (t : ℕ) (q : ℤ) (C : ℕ) (p : ℝ) : ℝ :=
  ambient t q p + quotient t q p + (p + C) ^ C + 4

noncomputable def reconstruction (t : ℕ) (q : ℤ) (p : ℝ) : ℝ :=
  3 * p + (p + 3) ^ 2 + (q ^ t).natAbs + 6

noncomputable def total (t : ℕ) (q : ℤ) (N : ℕ) (p : ℝ) : ℝ :=
  p + (reconstruction t q p + N) ^ N + 4

theorem shift_bounds (q : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ shift q p ∧ p ≤ shift q p ∧ rationalLogHeight (q : ℚ) ≤ shift q p := by
  have hh : rationalLogHeight (q : ℚ) ≤ (height q : ℝ) := Nat.le_ceil _
  exact ⟨add_nonneg hp (Nat.cast_nonneg _), le_add_of_nonneg_right (Nat.cast_nonneg _),
    hh.trans (le_add_of_nonneg_left hp)⟩

theorem ambient_bounds (t : ℕ) (q : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ ambient t q p ∧ shift q p ≤ ambient t q p ∧
      dilationPairGeometryBudget t (shift q p) ≤ ambient t q p ∧
      2 * (shift q p + 1) ≤ ambient t q p := by
  have hr := (shift_bounds q hp).1
  have hG : 0 ≤ dilationPairGeometryBudget t (shift q p) := by
    unfold dilationPairGeometryBudget
    positivity
  have hc : 0 ≤ 2 * (shift q p + 1) := by positivity
  unfold ambient
  exact ⟨by positivity, by linarith, by linarith, by linarith⟩

theorem quotient_bounds (t : ℕ) (q : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ quotient t q p ∧ ambient t q p ≤ quotient t q p ∧
      (ambient t q p + 3) ^ 5 ≤ quotient t q p := by
  have hA := (ambient_bounds t q hp).1
  have hb : 1 ≤ ambient t q p + 3 := by linarith
  have hpow : ambient t q p + 3 ≤ (ambient t q p + 3) ^ 11 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb (by decide : 1 ≤ 11)
  exact ⟨by unfold quotient; positivity, (by linarith : ambient t q p ≤ ambient t q p + 3).trans hpow,
    pow_le_pow_right₀ hb (by decide : 5 ≤ 11)⟩

theorem common_bounds (t : ℕ) (q : ℤ) (C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ common t q C p ∧ p ≤ common t q C p ∧
      ambient t q p ≤ common t q C p ∧ quotient t q p ≤ common t q C p ∧
      (p + C) ^ C ≤ common t q C p := by
  have hA := (ambient_bounds t q hp).1
  have hQ := (quotient_bounds t q hp).1
  have hN : 0 ≤ (p + C) ^ C := by positivity
  have hpA := (shift_bounds q hp).2.1.trans (ambient_bounds t q hp).2.1
  unfold common
  exact ⟨by positivity, by linarith, by linarith, by linarith, by linarith⟩

theorem reconstruction_bounds (t : ℕ) (q : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reconstruction t q p ∧ p + 1 ≤ reconstruction t q p := by
  have hn : 0 ≤ ((q ^ t).natAbs : ℝ) := Nat.cast_nonneg _
  unfold reconstruction
  constructor <;> nlinarith only [hp, hn, sq_nonneg (p + 3)]

theorem observable_bound (t : ℕ) (q : ℤ) {p : ℝ} (hp : 0 ≤ p) (K A : ℝ≥0)
    (hK : (K : ℝ) ≤ Real.exp p) (hA : (A : ℝ) ≤ Real.exp p) :
    (((q ^ t).natAbs : ℝ) + 1) * (K * (A * Real.exp ((p + 3) ^ 2))) ≤
      Real.exp (reconstruction t q p) := by
  have hn : ((q ^ t).natAbs : ℝ) + 1 ≤ Real.exp ((q ^ t).natAbs : ℝ) := Real.add_one_le_exp _
  have hP : 0 ≤ Real.exp ((p + 3) ^ 2) := (Real.exp_pos _).le
  have h := mul_le_mul hn
    (mul_le_mul hK (mul_le_mul_of_nonneg_right hA hP)
      (mul_nonneg A.coe_nonneg hP) (Real.exp_pos p).le)
    (mul_nonneg K.coe_nonneg (mul_nonneg A.coe_nonneg hP)) (Real.exp_pos _).le
  have he : Real.exp ((q ^ t).natAbs : ℝ) *
      (Real.exp p * (Real.exp p * Real.exp ((p + 3) ^ 2))) =
      Real.exp (2 * p + (p + 3) ^ 2 + (q ^ t).natAbs) := by
    rw [show 2 * p = p + p by ring]
    simp only [Real.exp_add]
    ring
  rw [he] at h
  exact h.trans (Real.exp_le_exp.mpr (by unfold reconstruction; linarith))

theorem total_bounds (t : ℕ) (q : ℤ) (N : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ total t q N p ∧ (reconstruction t q p + N) ^ N + 4 ≤ total t q N p := by
  have hr := (reconstruction_bounds t q hp).1
  have hpow : 0 ≤ (reconstruction t q p + N) ^ N := by positivity
  unfold total
  exact ⟨by linarith, by linarith⟩

theorem exists_full_bound (t : ℕ) (q : ℤ) (C N : ℕ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ p : ℝ, 0 ≤ p →
      total t q N (common t q C p) ≤ (p + Z) ^ Z ∧
        ((q ^ t).natAbs + 1 : ℝ) * p ≤ (p + Z) ^ Z := by
  let X : Polynomial ℕ := Polynomial.X
  let r := X + Polynomial.C (height q)
  let G := ((r + 4) ^ 2 + Polynomial.C (t + 2) * (r + 1) + 6) ^ 11
  let A := r + G + 2 * (r + 1)
  let B := A + (A + 3) ^ 11 + (X + Polynomial.C C) ^ C + 4
  let R := 3 * B + (B + 3) ^ 2 + Polynomial.C (q ^ t).natAbs + 6
  let P := B + (R + Polynomial.C N) ^ N + 4
  obtain ⟨Z, hZ, hz⟩ := exists_natPolynomial_eval_budget
    (P + Polynomial.C ((q ^ t).natAbs + 1) * X)
  refine ⟨Z, hZ, fun p hp => ?_⟩
  have h : total t q N (common t q C p) + ((q ^ t).natAbs + 1 : ℝ) * p ≤ (p + Z) ^ Z := by
    simpa [total, reconstruction, common, quotient, ambient, shift, dilationPairGeometryBudget,
      X, r, G, A, B, R, P, Polynomial.eval₂_pow, Nat.cast_add] using hz p hp
  have ht : 0 ≤ total t q N (common t q C p) :=
    (common_bounds t q C hp).1.trans (total_bounds t q N (common_bounds t q C hp).1).1
  have hn : 0 ≤ ((q ^ t).natAbs + 1 : ℝ) * p := by positivity
  exact ⟨by linarith, by linarith⟩

end Erdos3.DilationBudget

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredFactorization
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem coordinate_spanning_range {ι κ V : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) (v : κ → V) (U : Submodule ℚ V)
    (hv : Submodule.span ℚ (Set.range v) = U) :
    LinearMap.range (Matrix.mulVecLin (fun i k => b.equivFun (v k) i)) =
      U.map b.equivFun.toLinearMap := by
  rw [← hv, Submodule.map_span, ← Set.range_comp]
  exact (Matrix.range_mulVecLin _)

theorem exists_intersection_spanning_logHeight {ι κ J V : Type*}
    [Fintype ι] [Fintype κ] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
    (b : Basis ι ℚ V) (U : J → LieSubalgebra ℚ V) (v : J → κ → V)
    (hv : ∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p)
    (hheight : ∀ j a i, rationalLogHeight (b.repr (v j a) i) ≤ p) :
    ∃ w : Fin (Fintype.card ι) → V,
      Submodule.span ℚ (Set.range w) = (⨅ j, U j).toSubmodule ∧
      ∀ a i, rationalLogHeight (b.repr (w a) i) ≤ ((p + 2) ^ 2 + 2) ^ 63 + 1 := by
  classical
  let A : J → Matrix ι κ ℚ := fun j i k => b.equivFun (v j k) i
  let W := ⨅ j, U j
  let Wc : Submodule ℚ (ι → ℚ) := ⨅ j, LinearMap.range (A j).mulVecLin
  have hA (j : J) : LinearMap.range (A j).mulVecLin = (U j).toSubmodule.map b.equivFun.toLinearMap :=
    coordinate_spanning_range b (v j) (U j).toSubmodule (hv j)
  have hmem (x : V) : b.equivFun x ∈ Wc ↔ x ∈ W := by
    constructor
    · intro hx
      simp only [Wc, Submodule.mem_iInf] at hx
      apply (lieSubalgebra_mem_iInf U x).mpr
      intro j
      have hxj := hx j
      rw [hA j] at hxj
      obtain ⟨y, hy, he⟩ := hxj
      have he' : y = x := b.equivFun.injective he
      exact he' ▸ hy
    · intro hx
      simp only [Wc, Submodule.mem_iInf]
      intro j
      rw [hA j]
      exact ⟨x, (lieSubalgebra_mem_iInf U x).mp hx j, rfl⟩
  let e : W ≃ₗ[ℚ] Wc :=
    { toFun := fun x => ⟨b.equivFun x, (hmem x).mpr x.property⟩
      invFun := fun x => ⟨b.equivFun.symm x, (hmem _).mp (by
        simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
      map_add' := fun x y => Subtype.ext (b.equivFun.map_add x y)
      map_smul' := fun c x => Subtype.ext (b.equivFun.map_smul c x)
      left_inv := fun x => Subtype.ext (b.equivFun.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (b.equivFun.apply_symm_apply x) }
  let q := (p + 2) ^ 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hp1q : p + 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hcols : ((∑ _j : J, Fintype.card κ : ℕ) : ℝ) ≤ q := by
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul]
    have hprod := mul_le_mul hJ hκ (Nat.cast_nonneg _) hp
    dsimp [q]
    nlinarith
  obtain ⟨bc, hbc⟩ := exists_image_intersection_basis_exp_height A (one_le_ceil_exp p)
    (fun j i k => rationalHeightLE_ceil_exp (hheight j k i)) hq
    (hJ.trans hpq) (hι.trans hpq) hcols
    ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1q))
  let bw := bc.map e.symm
  let H := ⌈Real.exp ((q + 2) ^ 63)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp _
  have hbheight (a : Fin (finrank ℚ Wc)) (i : ι) : RationalHeightLE (b.repr (bw a : V) i) H := by
    have hb := rationalHeightLE_ceil_exp ((rationalLogHeight_le_iff _ _).mpr (hbc a i))
    change RationalHeightLE (b.repr (b.equivFun.symm (bc a : ι → ℚ)) i) H
    simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hb
  obtain ⟨w, hw, hh⟩ := exists_bounded_ambient_spanning b W bw bw.span_eq hH hbheight
  refine ⟨w, hw, ?_⟩
  intro a i
  exact rationalLogHeight_le_of_height (hh a i) (ceil_exp_le_exp_add_one (by positivity))

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_binary_intersection_basis_logHeight
    {ι α β L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (U V : LieSubalgebra ℚ L)
    (bU : Basis α ℚ U) (bV : Basis β ℚ V)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hU : ∀ a i, rationalLogHeight (e.repr (bU a : L) i) ≤ p)
    (hV : ∀ a i, rationalLogHeight (e.repr (bV a : L) i) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (U ⊓ V : LieSubalgebra ℚ L))) ℚ
        (U ⊓ V : LieSubalgebra ℚ L),
      ∀ a i, rationalLogHeight (e.repr (b a : L) i) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 2 := by
  classical
  obtain ⟨u, hu, hhu⟩ := exists_bounded_ambient_spanning e U bU bU.span_eq
    (one_le_ceil_exp p) (fun a i => rationalHeightLE_ceil_exp (hU a i))
  obtain ⟨v, hv, hhv⟩ := exists_bounded_ambient_spanning e V bV bV.span_eq
    (one_le_ceil_exp p) (fun a i => rationalHeightLE_ceil_exp (hV a i))
  let W : Bool → LieSubalgebra ℚ L := fun j => if j then U else V
  let z : Bool → Fin (Fintype.card ι) → L := fun j => if j then u else v
  have hz (j : Bool) : Submodule.span ℚ (Set.range (z j)) = (W j).toSubmodule := by
    cases j
    · exact hv
    · exact hu
  have hh (j : Bool) (a) (i) : rationalLogHeight (e.repr (z j a) i) ≤ p + 2 := by
    have hceil := ceil_exp_le_exp_add_one hp
    cases j
    · exact (rationalLogHeight_le_of_height (hhv a i) hceil).trans (by linarith)
    · exact (rationalLogHeight_le_of_height (hhu a i) hceil).trans (by linarith)
  obtain ⟨w, hw, hhw⟩ := exists_intersection_spanning_logHeight e W z hz
    (by linarith : 0 ≤ p + 2) (hd.trans (by linarith))
    (by simpa only [Fintype.card_fin] using hd.trans (show p ≤ p + 2 by linarith))
    (by simpa using (show (2 : ℝ) ≤ p + 2 by linarith)) hh
  have hW : (⨅ j, W j) = U ⊓ V := by
    ext x
    simp [lieSubalgebra_mem_iInf, W, Bool.forall_bool, and_comm]
  rw [hW] at hw
  obtain ⟨b, hb⟩ := exists_bounded_submodule_basis_from_spanning e
    (U ⊓ V).toSubmodule w hw (fun a i => rationalHeightLE_ceil_exp (hhw a i))
  refine ⟨b, fun a i => ?_⟩
  have h := rationalLogHeight_le_of_height (hb a i)
    (ceil_exp_le_exp_add_one (by positivity : 0 ≤ ((p + 2 + 2) ^ 2 + 2) ^ 63 + 1))
  simpa only [show p + 2 + 2 = p + 4 by ring, add_assoc, one_add_one_eq_two] using h

end Erdos3

end

section

namespace Erdos3

open Module

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedLayerEquiv (c : σ → ℕ) (n : ℕ) (hn : 1 ≤ n) :
    (F.weightedFiltration c).layer n ≃ₗ[ℚ] F.weightedLayer c n where
  toFun x := ⟨x.val.val, (F.mem_weightedFiltration_layer c n hn x.val).mp x.property⟩
  invFun x := ⟨⟨x.val, F.weightedLayer_antitone c hn x.property⟩,
    (F.mem_weightedFiltration_layer c n hn _).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_weighted_layer_coordinate_basis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : σ → ℕ) (e : Basis ι ℚ L) (b : Basis κ ℚ (F.weightedSubalgebra c))
    (n : ℕ) (hn : 1 ≤ n)
    (a : Basis (Fin (finrank ℚ (F.weightedLayer c n))) ℚ (F.weightedLayer c n))
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i k, RationalHeightLE (e.repr (b i : L) k) H)
    (ha : ∀ i k, RationalHeightLE (e.repr (a i : L) k) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ a' : Basis (Fin (finrank ℚ ((F.weightedFiltration c).layer n))) ℚ
        ((F.weightedFiltration c).layer n),
      ∀ i k, rationalLogHeight (b.repr (a' i : F.weightedSubalgebra c) k) ≤ (p + 2) ^ 8 := by
  let E := F.weightedLayerEquiv c n hn
  let a' := (a.map E.symm).reindex (finCongr E.finrank_eq.symm)
  have hval (i) : ((a' i : F.weightedSubalgebra c) : L) =
      (a ((finCongr E.finrank_eq.symm).symm i) : L) := by
    simp only [a', Basis.reindex_apply, Basis.map_apply, E, weightedLayerEquiv]
    rfl
  refine ⟨a', fun i k => ?_⟩
  apply rationalLogHeight_le_of_height
    (embedding_basis_coordinate_height b e (F.weightedSubalgebra c).incl.toLinearMap
      (fun _ _ h => Subtype.ext h) hH (fun k i => hb i k)
      (a' i : F.weightedSubalgebra c) (K := H) (fun k => by
        change RationalHeightLE (e.repr ((a' i : F.weightedSubalgebra c) : L) k) H
        rw [hval]
        exact ha _ k) k)
  exact embedding_coordinate_height_budget _ _ H H hp hι hκ hHp hHp

end MultidegreeLieFiltration

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_weighted_layer_basis (c : σ → ℕ) (n : ℕ) {H : ℕ}
    (hM : ∀ a i k, RationalHeightLE (D.basis.repr (M.basis a i : L) k) H) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.weightedLayer c n))) ℚ
        (M.filtration.weightedLayer c n),
      ∀ i k, RationalHeightLE (D.basis.repr (b i : L) k) H := by
  apply exists_bounded_submodule_basis_from_spanning D.basis
    (M.filtration.weightedLayer c n).toSubmodule
    (fun a : Σ a : {a : ∀ i, Fin (bound i + 1) //
        n ≤ multidegreeWeight c (fun i => (a i).val)},
        Fin (finrank ℚ (M.filtration.layer (fun i => (a.val i).val))) =>
      (M.basis a.1.val a.2 : L)) (M.weightedLayer_span c n).symm
  exact fun a k => hM a.1.val a.2 k

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_coordinate_active_basis (i : σ) (hi : 1 ≤ bound i)
    (n : Fin (s + 1)) {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.coordinateActiveLayer i (n.val + 1)))) ℚ
        (M.filtration.coordinateActiveLayer i (n.val + 1)),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 2 := by
  have hsingle : Pi.single i 1 ≤ bound := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Pi.single_eq_same] using hi
    · simpa only [Pi.single_eq_of_ne hji] using Nat.zero_le (bound j)
  obtain ⟨a, ha⟩ := M.exists_layer_basis (Pi.single i 1) hsingle hM
  obtain ⟨b, hb⟩ := M.exists_ordinary_layer_basis n hM
  exact exists_binary_intersection_basis_logHeight D.basis
    (M.filtration.layerIdeal (Pi.single i 1)).toLieSubalgebra
    (M.filtration.ordinary.layerIdeal (n.val + 1)).toLieSubalgebra a b
    ((Nat.cast_nonneg d).trans hM.1.1)
    (by simpa only [Fintype.card_fin] using hM.1.1) ha hb

theorem le_triple_basis_budget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ ((p + 4) ^ 2 + 2) ^ 63 := by
  have hb : 1 ≤ (p + 4) ^ 2 + 2 := by nlinarith [sq_nonneg (p + 4)]
  have hpow : (p + 4) ^ 2 + 2 ≤ ((p + 4) ^ 2 + 2) ^ 63 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb (by decide : 1 ≤ 63)
  exact (show p ≤ (p + 4) ^ 2 + 2 by nlinarith [sq_nonneg p]).trans hpow

theorem exists_additiveTriple_layer_basis_logHeight (i : σ) (hi : 1 ≤ bound i)
    (c : σ → ℕ) (n : Fin (s + 1)) {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ q : Basis (Fin (finrank ℚ (M.filtration.additiveTripleLayer i c (n.val + 1)))) ℚ
        (M.filtration.additiveTripleLayer i c (n.val + 1)),
      ∀ j k, rationalLogHeight (D.basis.repr (q j).val.1 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 ∧
        rationalLogHeight (D.basis.repr (q j).val.2.1 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 ∧
        rationalLogHeight (D.basis.repr (q j).val.2.2 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let P := ((p + 4) ^ 2 + 2) ^ 63 + 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpP : p + 1 ≤ P := add_le_add (le_triple_basis_budget hp) (by norm_num)
  obtain ⟨a, ha⟩ := M.exists_weighted_layer_basis c (n.val + 1)
    (fun a j k => rationalHeightLE_ceil_exp (hM.2 a j k))
  obtain ⟨b, hb⟩ := M.exists_coordinate_active_basis i hi n hM
  have ha' (j) (k) : RationalHeightLE (D.basis.repr (a j : L) k) ⌈Real.exp P⌉₊ :=
    rationalHeightLE_ceil_exp
      ((rationalLogHeight_le_of_height (ha j k) (ceil_exp_le_exp_add_one hp)).trans hpP)
  obtain ⟨q, hq⟩ := M.filtration.exists_additiveTriple_layer_basis D.basis i c (n.val + 1)
    a b (one_le_ceil_exp P) ha' (fun j k => rationalHeightLE_ceil_exp (hb j k))
  refine ⟨q, fun j k => ?_⟩
  have hceil : (⌈Real.exp P⌉₊ : ℝ) ≤ Real.exp (((p + 4) ^ 2 + 2) ^ 63 + 3) := by
    simpa only [P, add_assoc, show (2 : ℝ) + 1 = 3 by norm_num] using ceil_exp_le_exp_add_one hP
  exact ⟨rationalLogHeight_le_of_height (hq j k).1 hceil,
    rationalLogHeight_le_of_height (hq j k).2.1 hceil,
    rationalLogHeight_le_of_height (hq j k).2.2 hceil⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_weighted_model_of_bases (c : σ → ℕ)
    (b : Basis (Fin (finrank ℚ (M.filtration.weightedSubalgebra c))) ℚ
      (M.filtration.weightedSubalgebra c))
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i k, RationalHeightLE (D.basis.repr (b i : L) k) H)
    (hlayers : ∀ n, 1 ≤ n →
      ∃ a : Basis (Fin (finrank ℚ (M.filtration.weightedLayer c n))) ℚ
        (M.filtration.weightedLayer c n),
        ∀ i k, RationalHeightLE (D.basis.repr (a i : L) k) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hgrid : (D.grid : ℝ) ≤ Real.exp p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.weightedSubalgebra c)
        (multidegreeWeight c bound) (finrank ℚ (M.filtration.weightedSubalgebra c)),
      E.filtration = M.filtration.weightedFiltration c ∧ E.basis = b ∧
      E.lattice = D.lattice.comap
        (NilpotentLieBCHGroup.mapOfSteps (M.filtration.weightedSubalgebra c).incl) ∧
      E.GeometryComplexityLE ((p + 2) ^ 11) := by
  classical
  let K := M.filtration.weightedSubalgebra c
  let F := M.filtration.weightedFiltration c
  have hr : (finrank ℚ K : ℝ) ≤ p :=
    (Nat.cast_le.mpr (lie_subalgebra_finrank_le D.basis K)).trans
      (by simpa only [Fintype.card_fin] using hd)
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hd
  have hr' : (Fintype.card (Fin (finrank ℚ K)) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin] using hr
  have hmatrix : ∀ i j, RationalHeightLE (LinearMap.toMatrix b D.basis K.incl.toLinearMap i j) H := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    change RationalHeightLE (D.basis.repr (b j : L) i) H
    exact hb j i
  obtain ⟨N, hN, hNb, hin, hout⟩ := exists_bchSubgroup_comap_grid_of_steps
    (hM := F.lowerCentralSeries_eq_bot) b D.basis K.incl
    (fun _ _ h => Subtype.ext h) D.lattice hH D.grid_pos hmatrix D.inner_grid D.outer_grid
    hp hd' hr' hHp hgrid
  obtain ⟨_, _, _, hbracket⟩ := exists_bounded_lie_embedding_retraction b D.basis K.incl
    (fun _ _ h => Subtype.ext h) hH hc hmatrix
  have hbracketBudget := rationalLieStructureHeight_inverse_budget d (finrank ℚ K) H hp hd hr hHp
  have hLayer : ∀ i : Fin (multidegreeWeight c bound + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (i.val + 1)))) ℚ (F.layer (i.val + 1)),
        ∀ j k, rationalLogHeight (b.repr (a j : K) k) ≤ (p + 2) ^ 8 := by
    intro i
    obtain ⟨a, ha⟩ := hlayers (i.val + 1) (Nat.le_add_left 1 _)
    exact M.filtration.exists_weighted_layer_coordinate_basis c D.basis b (i.val + 1)
      (Nat.le_add_left 1 _) a hH hb ha hp hd' hr' hHp
  choose a ha using hLayer
  let E : RationalFilteredNilmanifold K (multidegreeWeight c bound) (finrank ℚ K) :=
    { filtration := F
      basis := b
      layerBasis := a
      lattice := D.lattice.comap (NilpotentLieBCHGroup.mapOfSteps K.incl)
      grid := N
      grid_pos := hN
      inner_grid := hin
      outer_grid := hout }
  have hp1 : 1 ≤ p + 2 := by linarith
  have h9 : (p + 2) ^ 9 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have h8 : (p + 2) ^ 8 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  refine ⟨E, rfl, rfl, rfl, hr.trans (le_power_budget hp (by decide)),
    hNb.trans (Real.exp_le_exp.mpr h9), ?_, ?_⟩
  · intro i j k
    apply rationalLogHeight_le_of_height (hbracket i j k)
    simpa only [Fintype.card_fin] using hbracketBudget
  · intro i j k
    exact (ha i j k).trans h8

theorem exists_weighted_model (c : σ → ℕ) {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.weightedSubalgebra c)
        (multidegreeWeight c bound) (finrank ℚ (M.filtration.weightedSubalgebra c)),
      E.filtration = M.filtration.weightedFiltration c ∧
      E.lattice = D.lattice.comap
        (NilpotentLieBCHGroup.mapOfSteps (M.filtration.weightedSubalgebra c).incl) ∧
      E.GeometryComplexityLE ((p + 3) ^ 11) ∧
      ∀ i k, rationalLogHeight (D.basis.repr (E.basis i : L) k) ≤ p + 1 := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hheight : ∀ a i k, RationalHeightLE (D.basis.repr (M.basis a i : L) k) H :=
    fun a i k => rationalHeightLE_ceil_exp (hM.2 a i k)
  obtain ⟨b, hb⟩ := M.exists_weighted_layer_basis c 1 hheight
  obtain ⟨E, hEF, hEb, hElattice, hEgeom⟩ := M.exists_weighted_model_of_bases c b hH hb
    (fun n _ => M.exists_weighted_layer_basis c n hheight)
    (fun i j k => rationalHeightLE_ceil_exp (hM.1.2.2.1 i j k))
    (by linarith : 0 ≤ p + 1) (hM.1.1.trans (by linarith)) hHp
    (hM.1.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  refine ⟨E, hEF, hElattice, ?_, ?_⟩
  · convert hEgeom using 1
    ring
  · intro i k
    rw [hEb]
    exact rationalLogHeight_le_of_height (hb i k) hHp

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def additiveTripleLattice (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    Subgroup (M.filtration.additiveTripleFiltration i hi c hc).Group :=
  (pi (fun _ : Fin 3 => D)).lattice.comap
    (NilpotentLieBCHGroup.mapOfSteps (M.filtration.additiveTripleToPi i hi c hc))

theorem additiveTripleLattice_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (x : (M.filtration.additiveTripleFiltration i hi c hc).Group) :
    x ∈ M.additiveTripleLattice i hi c hc ↔
      (⟨x.coord.val.1⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨x.coord.val.2.1⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨x.coord.val.2.2⟩ : D.filtration.Group) ∈ D.lattice := by
  change (NilpotentLieBCHGroup.mapOfSteps (M.filtration.additiveTripleToPi i hi c hc) x) ∈
    piBCHSubgroup (fun _ : Fin 3 => D.filtration) (fun _ : Fin 3 => D.lattice) ↔ _
  rw [mem_piBCHSubgroup]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · intro h j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2

theorem exists_additiveTriple_filtration_basis_logHeight (i : σ) (hi : bound i = 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (n : Fin (s + 1))
    {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ a : Basis (Fin (finrank ℚ
        ((M.filtration.additiveTripleFiltration i hi.le c hc).layer (n.val + 1)))) ℚ
        ((M.filtration.additiveTripleFiltration i hi.le c hc).layer (n.val + 1)),
      ∀ j k, rationalLogHeight ((pi (fun _ : Fin 3 => D)).basis.repr
        (M.filtration.additiveTripleToPi i hi.le c hc (a j)) k) ≤
          ((p + 4) ^ 2 + 2) ^ 63 + 3 := by
  obtain ⟨q, hq⟩ := M.exists_additiveTriple_layer_basis_logHeight i hi.ge c n hM
  let e := M.filtration.additiveTripleFiltrationLayerEquiv i hi.le c hc
    (n.val + 1) (Nat.le_add_left 1 _)
  let a := (q.map e.symm).reindex (finCongr e.finrank_eq.symm)
  have hval (j) : ((a j : M.filtration.additiveTripleSubalgebra i hi.le c hc) : L × L × L) =
      (q ((finCongr e.finrank_eq.symm).symm j)).val := by
    simp only [a, Basis.reindex_apply, Basis.map_apply, e,
      MultidegreeLieFiltration.additiveTripleFiltrationLayerEquiv]
    rfl
  refine ⟨a, fun j k => ?_⟩
  change rationalLogHeight ((pi (fun _ : Fin 3 => D)).basis.repr
    (tripleToPi ((a j : M.filtration.additiveTripleSubalgebra i hi.le c hc) : L × L × L)) k) ≤ _
  rw [hval]
  exact D.triple_product_basis_logHeight _ (hq _) k

noncomputable def additiveTripleGeometryBudget (p : ℝ) : ℝ :=
  ((p + 6) ^ 2 + ((p + 4) ^ 2 + 2) ^ 63 + 6) ^ 11

theorem exists_additiveTriple_model (i : σ) (hi : bound i = 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le c hc) s
        (finrank ℚ (M.filtration.additiveTripleSubalgebra i hi.le c hc)),
      E.filtration = M.filtration.additiveTripleFiltration i hi.le c hc ∧
      E.lattice = M.additiveTripleLattice i hi.le c hc ∧
      E.GeometryComplexityLE (additiveTripleGeometryBudget p) ∧
      finrank ℚ (M.filtration.additiveTripleSubalgebra i hi.le c hc) ≤ 3 * d ∧
      ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2.1 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2.2 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 := by
  let P := pi (fun _ : Fin 3 => D)
  let K := M.filtration.additiveTripleSubalgebra i hi.le c hc
  let F := M.filtration.additiveTripleFiltration i hi.le c hc
  let φ := M.filtration.additiveTripleToPi i hi.le c hc
  let C := ((p + 4) ^ 2 + 2) ^ 63
  let q := (p + 6) ^ 2 + C + 3
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCq : C + 3 ≤ q := by
    have h : C + 3 ≤ (p + 6) ^ 2 + (C + 3) := le_add_of_nonneg_left (sq_nonneg (p + 6))
    simpa only [q, add_assoc] using h
  have hP : P.GeometryComplexityLE q := by
    have hh := pi_geometry (fun _ : Fin 3 => D) (by linarith : 0 ≤ p + 3)
      (by simpa using (show (3 : ℝ) ≤ p + 3 by linarith))
      (fun _ => hM.1.mono D (by linarith : p ≤ p + 3))
    apply hh.mono P
    have hsq : (p + 3 + 2) ^ 2 ≤ (p + 6) ^ 2 := by nlinarith only [hp]
    exact hsq.trans ((le_add_of_nonneg_right hC).trans (le_add_of_nonneg_right (by norm_num)))
  obtain ⟨b, hb⟩ := M.exists_additiveTriple_layer_basis_logHeight i hi.ge c
    (⟨0, Nat.succ_pos s⟩ : Fin (s + 1)) hM
  let bK : Basis (Fin (finrank ℚ K)) ℚ K := b
  have hb' (j) (k) : rationalLogHeight (P.basis.repr (φ (bK j)) k) ≤ q :=
    (D.triple_product_basis_logHeight _ (hb j) k).trans hCq
  have hlayers (n : Fin (s + 1)) :
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, rationalLogHeight (P.basis.repr (φ (a j)) k) ≤ q := by
    obtain ⟨a, ha⟩ := M.exists_additiveTriple_filtration_basis_logHeight i hi c hc n hM
    exact ⟨a, fun j k => (ha j k).trans hCq⟩
  have hφ := M.filtration.additiveTripleToPi_injective i hi.le c hc
  obtain ⟨E, hEF, hEb, hEL, hE⟩ := P.exists_model_of_embedding_logHeight F bK φ hφ hP hb' hlayers
  have hdim : finrank ℚ K ≤ 3 * d := by
    have hh := P.embedding_basis_card_le bK φ hφ
    simpa only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] using hh
  refine ⟨E, hEF, hEL, ?_, hdim, ?_⟩
  · simpa only [q, C, additiveTripleGeometryBudget, add_assoc, show (3 : ℝ) + 3 = 6 by norm_num] using hE
  · intro j k
    rw [hEb]
    exact hb j k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_common_refiltered_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J L : Type*} [Fintype σ] [Fintype ι] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (eta : J → L →ₗ[ℚ] ℚ) (p : ℝ), 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, F.ControlledSymbolFactorization b w hF (eta j) T
        (F.realPolynomialSymbolHom b w hF (fun _ => 1) g) p) →
      ∃ (W : LieSubalgebra ℚ F.AssociatedGraded) (v : Fin (Fintype.card ι) → F.AssociatedGraded)
        (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (F.associatedGradedBasis b w hF) w W.toSubmodule ∧
        (∀ i k, rationalLogHeight ((F.associatedGradedBasis b w hF).repr (v i) k) ≤
          ((p + 2) ^ 2 + 2) ^ 63 + 1) ∧
        (∀ j x, x ∈ F.realGradedRefiltrationLayer W s → realifyFunctional (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b w hF (fun _ => 1)
          (F.realPolynomialSymbolHom b w hF (fun _ => 1) p₀).coord) ∈ realificationLieSubalgebra W) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∧
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 →
          ∀ t : σ → ℝ, eval₂ t (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
            realificationLieSubalgebra (F.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨C, hC, hcommon⟩ := exists_common_polynomial_step_drop_factors s
  refine ⟨C, hC, ?_⟩
  intro σ ι J L _ _ _ _ _ F b w hF eta p hp hι hσ hJ hstructure T hT g hfactor
  obtain ⟨U, v, m, e₀, p₀, r₀, hv, hU, hheight, hfreq, hm, hmp, hepr,
      hmid, he, hr, he0, hr0, hp0⟩ :=
    hcommon F b w hF eta p hp hι hσ hJ hstructure T hT g hfactor
  let W := ⨅ j, U j
  obtain ⟨v₀, hv₀, hheight₀⟩ := exists_intersection_spanning_logHeight
    (F.associatedGradedBasis b w hF) U v hv hp hι hι hJ hheight
  have hW : BasisGradedSubmodule (F.associatedGradedBasis b w hF) w W.toSubmodule := by
    intro k x hx
    apply (lieSubalgebra_mem_iInf U _).mpr
    intro j
    exact hU j k x ((lieSubalgebra_mem_iInf U x).mp hx j)
  refine ⟨W, v₀, m, e₀, p₀, r₀, hv₀, hW, hheight₀, ?_, hm, hmp, hepr,
    hmid, he, hr, he0, hr0, hp0, ?_⟩
  · intro j
    exact F.real_frequency_zero_on_refiltered_top b w hF W (eta j) (hfreq j)
  · intro hzero
    exact F.pointwise_refiltered_values_mem b w hF (fun _ => 1) W (fun _ => Nat.zero_lt_one)
      p₀.coord (hp0.trans hzero) hmid

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MultilinearityBudgets
namespace OAI

section

namespace Erdos3.MultilinearityBudget

open RationalFilteredNilmanifold.MultidegreeStructure
open scoped NNReal

noncomputable def coordinates (p : ℝ) : ℝ := ((p + 4) ^ 2 + 2) ^ 63 + 3

noncomputable def ambient (p : ℝ) : ℝ := p + additiveTripleGeometryBudget p + coordinates p

noncomputable def quotient (p : ℝ) : ℝ := (ambient p + 3) ^ 11

noncomputable def observable (C : ℕ) (p : ℝ) : ℝ := p + (p + C) ^ C + (ambient p + 3) ^ 2 + 2

noncomputable def reconstruction (C : ℕ) (p : ℝ) : ℝ := ambient p + quotient p + observable C p + 1

noncomputable def total (C N : ℕ) (p : ℝ) : ℝ := quotient p + (reconstruction C p + N) ^ N + 4

theorem ambient_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ ambient p ∧ p ≤ ambient p ∧ additiveTripleGeometryBudget p ≤ ambient p ∧
      coordinates p ≤ ambient p := by
  have hG : 0 ≤ additiveTripleGeometryBudget p := by unfold additiveTripleGeometryBudget; positivity
  have hC : 0 ≤ coordinates p := by unfold coordinates; positivity
  refine ⟨add_nonneg (add_nonneg hp hG) hC, ?_, ?_, ?_⟩
  · exact (le_add_of_nonneg_right hG).trans (le_add_of_nonneg_right hC)
  · exact (le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right hC)
  · exact le_add_of_nonneg_left (add_nonneg hp hG)

theorem quotient_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ quotient p ∧ ambient p ≤ quotient p ∧ (ambient p + 3) ^ 5 ≤ quotient p := by
  have hR := (ambient_bounds hp).1
  have hbase : 1 ≤ ambient p + 3 :=
    (by norm_num : (1 : ℝ) ≤ 3).trans (le_add_of_nonneg_left hR)
  have hpow : ambient p + 3 ≤ (ambient p + 3) ^ 11 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 11)
  exact ⟨pow_nonneg (add_nonneg hR (by norm_num)) _,
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 3)).trans hpow,
    pow_le_pow_right₀ hbase (by decide : 5 ≤ 11)⟩

theorem observable_nonneg (C : ℕ) {p : ℝ} (hp : 0 ≤ p) : 0 ≤ observable C p := by
  unfold observable
  positivity

theorem reconstruction_bounds (C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reconstruction C p ∧ ambient p ≤ reconstruction C p ∧
      quotient p + 1 ≤ reconstruction C p ∧ observable C p ≤ reconstruction C p := by
  have hR := (ambient_bounds hp).1
  have hQ := (quotient_bounds hp).1
  have hO := observable_nonneg C hp
  refine ⟨add_nonneg (add_nonneg (add_nonneg hR hQ) hO) zero_le_one, ?_, ?_, ?_⟩
  · exact ((le_add_of_nonneg_right hQ).trans (le_add_of_nonneg_right hO)).trans
      (le_add_of_nonneg_right zero_le_one)
  · have h : quotient p ≤ ambient p + quotient p + observable C p :=
      (le_add_of_nonneg_left hR).trans (le_add_of_nonneg_right hO)
    exact add_le_add h (le_refl 1)
  · exact (le_add_of_nonneg_left (add_nonneg hR hQ)).trans (le_add_of_nonneg_right zero_le_one)

theorem total_bounds (C N : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    quotient p ≤ total C N p ∧ (reconstruction C p + N) ^ N + 4 ≤ total C N p := by
  have hQ := (quotient_bounds hp).1
  have hB := (reconstruction_bounds C hp).1
  have hN : 0 ≤ (reconstruction C p + N) ^ N := pow_nonneg (add_nonneg hB (Nat.cast_nonneg N)) _
  refine ⟨(le_add_of_nonneg_right hN).trans (le_add_of_nonneg_right (by norm_num)), ?_⟩
  exact add_le_add (show (reconstruction C p + N) ^ N ≤ quotient p + (reconstruction C p + N) ^ N
    from le_add_of_nonneg_left hQ) (le_refl 4)

theorem observable_bound (C : ℕ) (p : ℝ) (K A : ℝ≥0)
    (hK : (K : ℝ) ≤ Real.exp p) (hA : (A : ℝ) ≤ Real.exp ((p + C) ^ C)) :
    (3 : ℝ) * (K * (A * Real.exp ((ambient p + 3) ^ 2))) ≤ Real.exp (observable C p) := by
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hP : 0 ≤ Real.exp ((ambient p + 3) ^ 2) := (Real.exp_pos _).le
  have h := mul_le_mul h3
    (mul_le_mul hK (mul_le_mul_of_nonneg_right hA hP)
      (mul_nonneg A.coe_nonneg hP) (Real.exp_pos p).le)
    (mul_nonneg K.coe_nonneg (mul_nonneg A.coe_nonneg hP)) (Real.exp_pos 2).le
  simpa only [observable, Real.exp_add, mul_assoc, mul_comm, mul_left_comm] using h

theorem exists_total_bound (C N : ℕ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ p : ℝ, 0 ≤ p → total C N p ≤ (p + Z) ^ Z := by
  let X : Polynomial ℕ := Polynomial.X
  let co : Polynomial ℕ := ((X + 4) ^ 2 + 2) ^ 63 + 3
  let geom : Polynomial ℕ := ((X + 6) ^ 2 + ((X + 4) ^ 2 + 2) ^ 63 + 6) ^ 11
  let R := X + geom + co
  let Q := (R + 3) ^ 11
  let O := X + (X + Polynomial.C C) ^ C + (R + 3) ^ 2 + 2
  let B := R + Q + O + 1
  obtain ⟨Z, hZ, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (B + Polynomial.C N) ^ N + 4)
  refine ⟨Z, hZ, fun p hp => ?_⟩
  simpa [total, reconstruction, observable, quotient, ambient, coordinates,
    additiveTripleGeometryBudget, X, co, geom, R, Q, O, B, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3.MultilinearityBudget

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.TopInvariantNiltestBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]

theorem exists_topInvariant_niltest
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (hQF : Q.filtration = D.filtration.quotientTop)
    (hQL : Q.lattice = D.lattice.map
      (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl))
    {w : σ → ℕ} (T : D.Niltest w)
    (hinv : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = T.observable x)
    (H : ℕ) (hH : 1 ≤ H)
    (he : ∀ i j, RationalHeightLE (Q.basis.repr
      (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants Q.basis i j k) H) :
    ∃ S : Q.Niltest w,
      S.orbit = D.topQuotientOrbit Q hQF T.orbit ∧
      S.normBound = T.normBound ∧
      S.lipBound = rationalReconstructionLipschitzBound s d n H T.lipBound T.normBound ∧
      ∀ x, S.eval x = T.eval x := by
  have hcover : Q.lattice ≤ D.lattice.map
      (mapOfSteps (lieQuotientMap (D.filtration.layerIdeal (s + 1)))) := by
    rw [hQL]
    exact le_rfl
  obtain ⟨f, hf, hfLip, hfBound⟩ := exists_lipschitz_realification_reconstruction
    D.basis Q.basis (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
    (lieQuotientMap_surjective _) D.lattice Q.lattice hcover
    D.grid Q.grid H D.grid_pos Q.grid_pos hH D.outer_grid Q.outer_grid he hc
    T.observable (fun k hk x => hinv k (by
      apply (realification_mkQ_eq_zero_iff
        (D.filtration.layerIdeal (s + 1)).toSubmodule k.coord).mp
      exact congrArg (fun z : Q.RealGroup => z.coord) (MonoidHom.mem_ker.mp hk))
      (QuotientGroup.mk x)) T.lipBound T.normBound T.lipschitz T.norm_le
  let S : Q.Niltest w := {
    orbit := D.topQuotientOrbit Q hQF T.orbit
    observable := f
    normBound := T.normBound
    lipBound := rationalReconstructionLipschitzBound s d n H T.lipBound T.normBound
    norm_le := hfBound
    lipschitz := by
      let : MetricSpace (Q.RealGroup ⧸ Q.lattice.map realificationHom) :=
        realificationQuotientMetricSpace Q.basis Q.lattice Q.grid Q.grid_pos Q.outer_grid
      exact hfLip.weaken (by simp only [Fintype.card_fin]; exact le_rfl)
  }
  refine ⟨S, rfl, rfl, rfl, ?_⟩
  intro x
  exact (congrArg (fun z : Q.RealGroup => f (QuotientGroup.mk z))
    (D.topQuotientOrbit_eval Q hQF T.orbit x)).trans (hf _)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_topInvariant_niltest_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d n : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
      (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
      (hQF : Q.filtration = D.filtration.quotientTop)
      (_hQL : Q.lattice = D.lattice.map
        (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl))
      {w : σ → ℕ} (T : D.Niltest w) (p : ℝ),
      0 ≤ p → T.ComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ p) →
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = T.observable x) →
      ∃ S : Q.Niltest w, S.orbit = D.topQuotientOrbit Q hQF T.orbit ∧
        S.normBound = T.normBound ∧ S.ComplexityLE ((p + C) ^ C) ∧
        ∀ x, S.eval x = T.eval x := by
  obtain ⟨a, _, hcost⟩ := exists_rationalReconstructionLipschitzBound_exp s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 1 + Polynomial.C a) ^ a + X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ d n D _ _ _ _ Q hQF hQL w T p hp hT hQ he hinv
  let H := ⌈Real.exp p⌉₊
  obtain ⟨S, hSo, hSn, hSl, hSe⟩ := D.exists_topInvariant_niltest Q hQF hQL T hinv H
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (he i j))
    (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.lipBound.coe_nonneg]
  have hL : (T.lipBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.normBound.coe_nonneg]
  have hpp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  let r := (p + 1 + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hK : (S.lipBound : ℝ) ≤ Real.exp r := by
    rw [hSl]
    exact hcost d n H T.lipBound T.normBound (p + 1) (by linarith)
      (hT.1.1.trans (by linarith)) (hQ.1.trans (by linarith))
      (ceil_exp_le_exp_add_one hp) (hL.trans hpp) (hB.trans hpp)
  have hnum : 2 + (S.normBound : ℝ) + (S.lipBound : ℝ) ≤ Real.exp (r + p + 4) := by
    have hSn' : (S.normBound : ℝ) ≤ Real.exp (r + p) := by
      rw [hSn]
      exact hB.trans (Real.exp_le_exp.mpr (by linarith))
    have hSl' : (S.lipBound : ℝ) ≤ Real.exp (r + p) :=
      hK.trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ 4 * Real.exp (r + p) := by linarith [Real.one_le_exp (show 0 ≤ r + p by linarith)]
      _ ≤ Real.exp 4 * Real.exp (r + p) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hbound : r + p + 4 ≤ (p + C) ^ C := by
    simpa [r, P, X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨S, hSo, hSn, ⟨hQ.mono Q ((by linarith : p ≤ r + p + 4).trans hbound), ?_⟩, hSe⟩
  exact ((Real.log_le_iff_le_exp (by positivity)).mpr hnum).trans hbound

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end


