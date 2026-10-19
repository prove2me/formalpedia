-- Prove2me | Definitions.Def_OAIE3v2B300
-- name    : OAIE3v2B300
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:23:48.815377+00:00
-- url     : https://prove2.me/theorems/7199f232-468f-428a-99d3-8fa5885eaf4a
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 200 of 311
-- statement:
--   Definitions bundle 200 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B196` of this split.
--
--   Modules: `Estimates/AllocatedCenteredNarrowPrescribedMarginal.lean`, `Estimates/PhysicalSingleSiteCommonCover.lean`, `Estimates/SelectedJointWeightedReferenceComparison.lean`, `Fourier/NormalizedTwistSingleSiteFourierHaar.lean`, `Geometry/CenteredFiniteSpatialModularGoodSet.lean`, `Lattices/AllocatedPhysicalIntegerRankLaw.lean`, `Lattices/SelectedResidueCutoffDomination.lean`, `Linear/SpatialMatrixBlockWideProbability.lean`, `Probability/FixedSpatialDensityBudget.lean`, `Probability/PreparedModularGeneralCenteredLaw.lean`, `Sampling/PreparedActualSlicedForecastSetup.lean`, `Sampling/PreparedCenteredForecastCramer.lean`, `Sampling/PreparedCenteredForecastSpatialBounds.lean`, `Sampling/PreparedConcreteSlicedForecastModelLogs.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

section Joint

variable {C B K I : Type*} [MeasurableSpace C] [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)

include hA hW hZ in

theorem selectedJointDensityMass_measurable
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z)) :
    Measurable (fun c => selectedJointDensityMass A modulus T W (D c)) := by
  have h := (selectedJointReference A hA modulus T W hW hZ).mean_measurable
    (fun c z => D c z.1.val z.2.val) (fun z => hDm z.1.val z.2.val)
  simpa only [selectedJointReference_densityMass] using h

end Joint

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredNarrowPrescribedMarginal
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem centeredFiniteMarginal_siteLaw_excessMass_le_of_uniform
    {C Ω T X : Type*} [MeasurableSpace C] [Fintype Ω]
    [Fintype T] [Nonempty T] [Fintype X]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun c => (law c).weight z))
    (physical : Ω → T → X)
    (reference : FiniteProbabilityWeights X) (cap ε : ℝ)
    (h : ∀ c, reference.excessMass ((law c).siteLaw physical) cap ≤ ε) :
    reference.excessMass ((centeredFiniteMarginal μ law hweight).siteLaw physical) cap ≤ ε := by
  rw [centeredFiniteMarginal_siteLaw]
  exact centeredFiniteMarginal_excessMass_le_of_uniform μ _ _ reference cap ε h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped Classical NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def singleSiteIntegerCover (d : ℕ) :
    EuclideanJetLayers U (fun _ => Unit) →+ EuclideanJetLayers U (fun _ => Unit) where
  toFun y j t := quotientIntegerCover _ d (y j t)
  map_zero' := by ext j t; exact map_zero _
  map_add' x y := by ext j t; exact map_add _ _ _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedJointWeightedReferenceComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedJointFiniteLaw_weighted_reference_comparison
    {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T V D)
    (f : B → (K × I → ℤ) → ℂ) (hf : ∀ a z, ‖f a z‖ ≤ 1)
    {ε η : ℝ}
    (hmass : ∀ a, |selectedResidueDensityMass modulus T V (D a) - 1| ≤ η)
    (htest : ∀ a,
      ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
          (f a z * (D a z : ℂ))) -
        ∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * f a z‖ ≤ ε) :
    ‖(selectedJointFiniteLaw A hA modulus T V hV hZ D hD0 hD).complexMean
        (fun z => f z.1.val z.2.val) -
      (selectedJointReference A hA modulus T V hV hZ).complexMean
        (fun z => f z.1.val z.2.val)‖ ≤ η + ε := by
  let p := FiniteProbabilityWeights.uniformFinset A hA
  let q := selectedResidueFiniteLaw modulus T V hV hZ
  let test (z : A × rectangularWeightIndices 0 V 1) := f z.1.val z.2.val
  let density (z : A × rectangularWeightIndices 0 V 1) := D z.1.val z.2.val
  have hraw := p.norm_complexMean_sub_le
    (fun a => q.complexMean (fun z => (D a.val z.val : ℂ) * f a.val z.val))
    (fun a => q.complexMean (fun z => f a.val z.val)) (fun _ => ε) (by
      intro a _
      change ‖(selectedResidueFiniteLaw modulus T V hV hZ).complexMean
          (fun z => (D a.val z.val : ℂ) * f a.val z.val) -
        (selectedResidueFiniteLaw modulus T V hV hZ).complexMean
          (fun z => f a.val z.val)‖ ≤ ε
      rw [selectedResidueFiniteLaw_complexMean modulus T V hV hZ
          (fun z => (D a.val z : ℂ) * f a.val z),
        selectedResidueFiniteLaw_complexMean modulus T V hV hZ (f a.val)]
      simpa only [mul_comm (D a.val _ : ℂ)] using htest a.val)
  rw [p.mean_const] at hraw
  have hraw' : ‖(p.prod q).complexMean (fun z => (density z : ℂ) * test z) -
      (p.prod q).complexMean test‖ ≤ ε := by
    simpa only [FiniteProbabilityWeights.complexMean_prod, density, test] using hraw
  have hglobal : 0 < (selectedJointReference A hA modulus T V hV hZ).mean density := by
    rw [selectedJointReference_densityMass]
    exact hD
  have hnorm := (selectedJointReference A hA modulus T V hV hZ).normalizedDensityTest_remove_normalization
    density (fun z => hD0 z.1.val z.2.val) hglobal test (fun z => hf z.1.val z.2.val)
  rw [selectedJointReference_densityMass] at hnorm
  have hnorm' := hnorm.trans (selectedJointDensityMass_close A hA modulus T V D hmass)
  rw [selectedJointFiniteLaw_complexMean]
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hnorm' hraw')

theorem selectedJointFiniteLaw_weighted_reference_real_comparison
    {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T V D)
    (f : B → (K × I → ℤ) → ℝ) (hf : ∀ a z, |f a z| ≤ 1)
    {ε η : ℝ}
    (hmass : ∀ a, |selectedResidueDensityMass modulus T V (D a) - 1| ≤ η)
    (htest : ∀ a,
      |(∑' z, (selectedResidueSmoothPMF modulus T V hV hZ z).toReal * (f a z * D a z)) -
        ∑' z, (selectedResidueSmoothPMF modulus T V hV hZ z).toReal * f a z| ≤ ε) :
    |(selectedJointFiniteLaw A hA modulus T V hV hZ D hD0 hD).mean
        (fun z => f z.1.val z.2.val) -
      (selectedJointReference A hA modulus T V hV hZ).mean
        (fun z => f z.1.val z.2.val)| ≤ η + ε := by
  have h := selectedJointFiniteLaw_weighted_reference_comparison A hA modulus T V hV hZ
    D hD0 hD (fun a z => (f a z : ℂ))
    (fun a z => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf a z)
    hmass (fun a => by
      simpa only [← Complex.ofReal_mul, ← Complex.ofReal_tsum, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using htest a)
  simpa only [FiniteProbabilityWeights.complexMean_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NormalizedTwistSingleSiteFourierHaar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def singleSiteEuclideanRow {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ) : euclideanSubspace U →ₗ[ℝ] ℝ :=
  (integerRowLinear a).comp (U.subtype.comp
    ((LinearMap.proj ()).comp (euclideanSubspaceArrayEquiv U).toLinearMap))

theorem singleSiteEuclideanRow_apply {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ) (x : euclideanSubspace U) :
    singleSiteEuclideanRow U a x = ∑ i, (a i : ℝ) * x.val i := by
  change integerRowLinear a (fun i => x.val i) = _
  exact integerRowLinear_apply a _

theorem singleSiteEuclideanRow_integral {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ) (x : euclideanSubspace U)
    (hx : x ∈ (latticeSection (standardEuclideanLattice D)
      (euclideanSubspace U)).toAddSubgroup) :
    ∃ n : ℤ, singleSiteEuclideanRow U a x = n := by
  have h := (euclideanSubspaceArrayEquiv_mem_lattice U x).mpr hx
  choose z hz using fun i => h () i
  refine ⟨∑ i, a i * z i, ?_⟩
  rw [singleSiteEuclideanRow_apply]
  simp only [euclideanSubspaceArrayEquiv_apply] at hz
  simp only [hz, Int.cast_sum, Int.cast_mul]

theorem singleSiteEuclideanRow_eq_zero {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ) :
    singleSiteEuclideanRow U a = 0 ↔ U ≤ LinearMap.ker (integerRowLinear a) := by
  constructor
  · intro h x hx
    have he := LinearMap.congr_fun h
      ((euclideanSubspaceArrayEquiv U).symm (fun _ => ⟨x, hx⟩))
    change integerRowLinear a
      ((euclideanSubspaceArrayEquiv U
        ((euclideanSubspaceArrayEquiv U).symm (fun _ => ⟨x, hx⟩))) ()).val = 0 at he
    rw [ContinuousLinearEquiv.apply_symm_apply] at he
    exact he
  · intro h
    ext x
    exact h ((euclideanSubspaceArrayEquiv U x ()).property)

theorem singleSiteEuclideanRow_character {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ)
    (y : euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) :
    (∏ i, CircleFourier.character
      (a i • subspaceAmbientTorus U (euclideanSubspaceTorusEquiv U y) i)) =
      quotientLinearCharacter _ (singleSiteEuclideanRow U a)
        (singleSiteEuclideanRow_integral U a) y := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
  rw [euclideanSubspaceTorusEquiv_mk, quotientLinearCharacter_mk,
    singleSiteEuclideanRow_apply, character_real_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [subspaceAmbientTorus_mk, euclideanSubspaceArrayEquiv_apply,
    ← AddCircle.coe_zsmul, zsmul_eq_mul]

theorem singleSiteHaar_ambientIntegerCharacter_integral
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (a : (Σ j, J j) → ℤ) :
    (∫ y, ambientIntegerCharacter a
      (fun i => coveredJetAmbientTorus U 1 y ⟨i.1, (), i.2⟩)
      ∂Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) =
      if ∀ j, U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))
      then 1 else 0 := by
  have he (y : EuclideanJetLayers U (fun _ => Unit)) :
      ambientIntegerCharacter a
        (fun i => coveredJetAmbientTorus U 1 y ⟨i.1, (), i.2⟩) =
      ∏ j, ∏ u : Unit, quotientLinearCharacter _
        (singleSiteEuclideanRow (U j) (fun i => a ⟨j, i⟩))
        (singleSiteEuclideanRow_integral (U j) (fun i => a ⟨j, i⟩)) (y j u) := by
    simp only [ambientIntegerCharacter, Fintype.prod_sigma, Fintype.prod_unique,
      coveredJetAmbientTorus, quotientIntegerCover, nsmulAddMonoidHom_apply, one_nsmul]
    apply Finset.prod_congr rfl
    intro j _
    exact singleSiteEuclideanRow_character (U j) (fun i => a ⟨j, i⟩) (y j ())
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun j (v : Unit → _) =>
    ∏ u : Unit, quotientLinearCharacter _
      (singleSiteEuclideanRow (U j) (fun i => a ⟨j, i⟩))
      (singleSiteEuclideanRow_integral (U j) (fun i => a ⟨j, i⟩)) (v u))]
  simp_rw [integral_fintype_prod_eq_prod]
  simp_rw [quotientLinearCharacter_integral, singleSiteEuclideanRow_eq_zero]
  simp only [Fintype.prod_unique]
  split_ifs with h
  · simp only [h, ite_true, Finset.prod_const_one]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem singleSiteHaar_ambientIntegerCharacter_integrable
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, IsProbabilityMeasure (ν j)]
    (a : (Σ j, J j) → ℤ) :
    Integrable (fun y => ambientIntegerCharacter a
      (fun i => coveredJetAmbientTorus U 1 y ⟨i.1, (), i.2⟩))
      (Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) := by
  have : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  have : IsProbabilityMeasure
      (Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) :=
    Measure.pi.instIsProbabilityMeasure _
  apply Integrable.of_bound _ 1
    (ae_of_all _ (fun _ => (ambientIntegerCharacter_norm a _).le))
  apply Continuous.aestronglyMeasurable
  let C : ℝ≥0 := ⟨∑ i, |(a i : ℝ)|, Finset.sum_nonneg (fun i _ => abs_nonneg _)⟩
  have hc : Continuous (ambientIntegerCharacter a) :=
    (ambientIntegerCharacter_lipschitz a C (fun i =>
      Finset.single_le_sum (fun j _ => abs_nonneg (a j : ℝ)) (Finset.mem_univ i))).continuous
  apply hc.comp
  apply continuous_pi
  intro i
  exact (continuous_apply (⟨i.1, (), i.2⟩ : JetAmbientIndex (fun _ : Fin m => Unit) J)).comp
    (coveredJetAmbientTorus_continuous (O := fun _ : Fin m => Unit) U 1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {G P : Type*} [Fintype G] [Fintype P] {n : ℕ}

theorem spatialMatrixBlock_bad_probability (hn : 0 < n) (e : Fin 2 × Fin n ↪ G)
    (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern (Option (G ⊕ P)) (Fin n) q))
    (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hmesh : ∀ i, 1 / spatialMatrixIndexWidth e q V i ≤ δ)
    (hsmall : embeddedMatrixDeterminantLip n (2*n*n) * δ ≤ spatialMatrixBlockThreshold n η) :
    ((selectedResidueSmoothPMF q T V hV hZ).map
      (fun z => decide (spatialMatrixBlockBad e V (spatialMatrixBlockThreshold n η) z)) true).toReal ≤ η / 2 := by
  let hc (r : T) := spatialMatrixBlock_cellMass_pos q hq V hV hscale
    (boundedColumnResidueRepresentative q r.val)
  apply selectedResidueSmoothPMF_bind_le_of_cells q hq T V hV hZ hc
    (fun z => PMF.pure (decide (spatialMatrixBlockBad e V (spatialMatrixBlockThreshold n η) z))) true (η/2)
  intro r
  exact spatialMatrixBlock_residue_bad_probability hn e _ q hq V hV (hc r)
    (fun i => hscale (spatialMatrixBlockSlot e i)) hδ hδ1 hη hmesh hsmall

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem spatialMatrixBlock_bad_probability_of_exp_width
    {G P : Type*} [Fintype G] [Fintype P] {n : ℕ} (hn : 0 < n)
    (e : Fin 2 × Fin n ↪ G)
    (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern (Option (G ⊕ P)) (Fin n) q))
    (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E)
    (hwide : ∀ i, Real.exp (smoothMatrixBlockWidthLogBudget (2 * n * n) n 2 E) ≤
      spatialMatrixIndexWidth e q V i) :
    ((selectedResidueSmoothPMF q T V hV hZ).map
      (fun z => decide (spatialMatrixBlockBad e V (spatialMatrixBlockThreshold n η) z)) true).toReal ≤ η / 2 := by
  have hκ := spatialMatrixBlockThreshold_pos hn hη
  have hδ := smoothMatrixBlockMesh_spec n (2 * n * n) hκ
  have hwide' (i) := smoothMatrixBlockMesh_width_spec n (2 * n * n) hκ
    ((smoothMatrixBlock_actual_width_le_exp (by positivity) hn 2 hη hE hηb).trans (hwide i))
  exact spatialMatrixBlock_bad_probability hn e q hq T V hV hZ hscale
    hδ.1.le hδ.2.1 hη (fun i => (hwide' i).2.2) hδ.2.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CenteredFiniteSpatialModularGoodSet
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem centeredFinite_spatial_modular_good_set
    {C Ω G P : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {n : ℕ}
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (noise : Ω → (Option (G ⊕ P) × Fin n → ℤ))
    (V : Option (G ⊕ P) × Fin n → ℝ)
    (e : Fin 2 × Fin n ↪ G) (κ : ℝ)
    (modularBad : Set (C × Ω)) (hmeas : MeasurableSet modularBad)
    {εmod εsp : ℝ}
    (hmodmass : (centeredFiniteProbabilityMeasure μ law).real modularBad ≤ εmod)
    (hspmass : (centeredFiniteProbabilityMeasure μ law).real
      {z | spatialMatrixBlockBad e V (κ / 2) (noise z.2)} ≤ εsp)
    (charge : C × Ω → ℕ) (cutoff : ℕ)
    (hmodular : ∀ c x, 0 < (law c).weight x →
      ((c, x) ∈ modularBad ↔ cutoff < charge (c, x)))
    (recovered : C × Ω → Prop)
    (hae : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, recovered z) :
    let bad := modularBad ∪ {z | spatialMatrixBlockBad e V (κ / 2) (noise z.2)}
    MeasurableSet bad ∧
      (centeredFiniteProbabilityMeasure μ law).real bad ≤ εmod + εsp ∧
      ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law,
        z ∉ bad → recovered z ∧ charge z ≤ cutoff ∧
          ∀ block : Fin 2, κ / 2 < |Matrix.det (fun i j : Fin n =>
            spatialMatrixNormalizedEntries e V (noise z.2) (block, j, i))| := by
  have hspmeas : MeasurableSet
      {z : C × Ω | spatialMatrixBlockBad e V (κ / 2) (noise z.2)} :=
    (Set.toFinite {x : Ω | spatialMatrixBlockBad e V (κ / 2) (noise x)}).measurableSet.preimage
      measurable_snd
  refine ⟨hmeas.union hspmeas, ?_, ?_⟩
  · exact (measureReal_union_le _ _).trans (add_le_add hmodmass hspmass)
  · filter_upwards [centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight, hae]
      with z hz hrec
    intro hgood
    have hmod : z ∉ modularBad := fun h => hgood (Or.inl h)
    have hsp : ¬spatialMatrixBlockBad e V (κ / 2) (noise z.2) :=
      fun h => hgood (Or.inr h)
    refine ⟨hrec, le_of_not_gt (fun h => hmod ((hmodular z.1 z.2 hz).mpr h)), ?_⟩
    intro block
    exact lt_of_not_ge (fun h => hsp ⟨block, h⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedPhysicalIntegerRankLaw
namespace OAI

section

namespace Erdos3
open scoped Classical

theorem selectedResidueDensityPMF_event_congr_of_density_ne_zero
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (f g : (K × I → ℤ) → Prop) [DecidablePred f] [DecidablePred g]
    (hfg : ∀ x, D x ≠ 0 → (f x ↔ g x)) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if f x then (1 : ℝ) else 0)) =
    ∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if g x then (1 : ℝ) else 0) := by
  apply tsum_congr
  intro x
  by_cases hx : D x = 0
  · rw [selectedResidueDensityPMF_zero_of_density_zero modulus G V hV hZ D hD0 hD x hx]
    simp only [zero_mul]
  · simp only [hfg x hx]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem selectedResidueDensityPMF_badProduct_event_congr
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (S : Finset ℕ) (A : ℕ → ℕ)
    (bad other : ℕ → ℕ → (K × I → ℤ) → Prop) (R : ℕ)
    (heq : ∀ x, D x ≠ 0 → ∀ p ∈ S, ∀ a, 0 < a → a ≤ A p →
      (bad p a x ↔ other p a x)) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if R < ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x then (1 : ℝ) else 0)) =
      ∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if R < ∏ p ∈ S, p ^ largestTestedBadDepth A other p x then (1 : ℝ) else 0) := by
  apply selectedResidueDensityPMF_event_congr_of_density_ne_zero
  intro x hx
  rw [largestBadPrimeProduct_congr_on_tested S A bad other x (heq x hx)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueCutoffDomination
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]
variable (q : I → ℕ) (T : Finset (ColumnResiduePattern K I q))
variable (V : K × I → ℝ) (hV : ∀ t, 0 < V t)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)

theorem selectedResidueFiniteLaw_event_eq_map_true (bad : (K × I → ℤ) → Prop) :
    (selectedResidueFiniteLaw q T V hV hZ).eventProbability (fun z => bad z.val) =
      (((selectedResidueSmoothPMF q T V hV hZ).map (fun z => decide (bad z))) true).toReal := by
  have hoff (z : K × I → ℤ) (hz : z ∉ rectangularWeightIndices 0 V 1) :
      (selectedResidueSmoothPMF q T V hV hZ z).toReal = 0 := by
    rw [selectedResidueSmoothPMF_toReal, selectedResidueSmoothWeight_zero_off q T V hV z hz, zero_div]
  calc
    _ = (FiniteProbabilityWeights.ofSupportedPMF (selectedResidueSmoothPMF q T V hV hZ)
        (rectangularWeightIndices 0 V 1) hoff).eventProbability (fun z => bad z.val) := by
      unfold FiniteProbabilityWeights.eventProbability FiniteProbabilityWeights.mean
      apply Finset.sum_congr rfl
      intro z _
      change selectedResidueSmoothWeight q T V z.val / _ * _ =
        (selectedResidueSmoothPMF q T V hV hZ z.val).toReal * _
      rw [selectedResidueSmoothPMF_toReal]
    _ = _ := supportedPMF_event_eq_map_true _ _ hoff bad

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FixedSpatialDensityBudget
namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem factorial_le_exp_square (n : ℕ) {P : ℝ} (hP : 0 ≤ P) (hn : (n : ℝ) ≤ P) :
    (n.factorial : ℝ) ≤ Real.exp (P ^ 2) := by
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast n.factorial_le_pow
  have hbase : (n : ℝ) ≤ Real.exp P := hn.trans (le_trans (by linarith) (Real.add_one_le_exp P))
  calc
    _ ≤ (n : ℝ) ^ n := hfac
    _ ≤ (Real.exp P) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    _ = Real.exp (P * n) := by simpa only [mul_comm] using (Real.exp_nat_mul P n).symm
    _ ≤ Real.exp (P ^ 2) := Real.exp_le_exp.mpr (by nlinarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredForecastCramer
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {G X T : Type*} [Fintype X] [DecidableEq X]

theorem preparedCenteredForecast_cramer_bounds
    (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
    {P B H κ0 κ1 : ℝ} (hP : 0 ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hH : H ∈ Set.Icc (0 : ℝ) 1) (hκ0 : 0 < κ0) (hκ1 : 0 < κ1)
    (hi0 : κ0⁻¹ ≤ Real.exp B) (hi1 : κ1⁻¹ ≤ Real.exp B)
    (hentry : ∀ i j, |fixedSpatialKernelBlock e W L z false i j| ≤ H)
    (hdet0 : κ0 ≤ |(fixedSpatialKernelBlock e W L z false).det|)
    (hdet1 : κ1 ≤ |(fixedSpatialKernelBlock e W L z true).det|) :
    ∃ h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0,
    ∃ h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0,
      inverseJacobian (fixedSpatialKernelBlockEquiv e W L z true h1) ≤
        Real.exp (B + P ^ 2 + P) ∧
      ‖(fixedSpatialKernelBlockEquiv e W L z false h0).symm.toContinuousLinearMap‖ ≤
        Real.exp (B + P ^ 2 + P) := by
  have h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0 :=
    abs_pos.mp (hκ0.trans_le hdet0)
  have h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0 :=
    abs_pos.mp (hκ1.trans_le hdet1)
  refine ⟨h0, h1, ?_, ?_⟩
  · rw [fixedSpatialKernelBlockEquiv_jacobian]
    exact ((inv_anti₀ hκ1 hdet1).trans hi1).trans
      (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg P]))
  · have hnorm := (matrixSupCLM_inverse_norm_le (fixedSpatialKernelBlock e W L z false)
      hH.1 hentry hκ0 hdet0).2
    rw [← fixedSpatialKernelBlockEquiv_coe e W L z false h0,
      ContinuousLinearMap.inverse_equiv] at hnorm
    have hfac := factorial_le_exp_square (Fintype.card X) hP hX
    have hpow : H ^ (Fintype.card X - 1) ≤ 1 := pow_le_one₀ hH.1 hH.2
    have hXexp : (Fintype.card X : ℝ) ≤ Real.exp P :=
      hX.trans (by linarith [Real.add_one_le_exp P])
    have hinner : ((Fintype.card X).factorial : ℝ) * H ^ (Fintype.card X - 1) / κ0 ≤
        Real.exp (P ^ 2) * Real.exp B := by
      rw [div_eq_mul_inv]
      apply mul_le_mul _ hi0 (inv_nonneg.mpr hκ0.le) (Real.exp_nonneg _)
      exact (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)).trans
        (by simpa only [mul_one] using hfac)
    calc
      _ ≤ Fintype.card X * ((Fintype.card X).factorial * H ^ (Fintype.card X - 1) / κ0) :=
        hnorm
      _ ≤ Real.exp P * (Real.exp (P ^ 2) * Real.exp B) :=
        mul_le_mul hXexp hinner
          (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hH.1 _)) hκ0.le)
          (Real.exp_nonneg _)
      _ = Real.exp (B + P ^ 2 + P) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredForecastSpatialBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {G J X : Type*}

theorem preparedCenteredForecast_spatialBlock_entry_le_one
    [Fintype G] [Fintype J] [Fintype X]
    (e : Fin 2 × X ↪ G) {W L τ ξ : ℝ} (N : X → ℕ)
    (noise : Option (G ⊕ J) × X → ℤ)
    (hnoise : noise ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ x, 0 < N x)
    (hscale : L / (1 + W) ∈ Set.Icc (0 : ℝ) 1) (t : Bool) (i j : X) :
    |fixedSpatialKernelBlock (spatialTwoBlockEquiv e) W L
      (fun k => (noise (Option.map Sum.inl k.1, k.2) : ℝ) / trimmedSpatialWidths W τ N k) t i j| ≤ 1 := by
  rw [preparedCenteredForecast_spatialBlock_eq e W L τ ξ N noise t]
  change |L / (1 + W) * spatialMatrixNormalizedEntries e
    (narrowTrimmedSpatialWidths W τ ξ N) noise ((if t then 1 else 0), j, i)| ≤ 1
  let slot := spatialMatrixBlockSlot (P := J) e ((if t then 1 else 0), j, i)
  have hwidth : 0 < narrowTrimmedSpatialWidths W τ ξ N slot :=
    narrowTrimmedSpatialWidths_pos hW hτ hξ N hN slot
  have hbound := rectangularWeightIndices_zero_bound
    (narrowTrimmedSpatialWidths W τ ξ N) hnoise slot
  have hentry : |spatialMatrixNormalizedEntries e
      (narrowTrimmedSpatialWidths W τ ξ N) noise ((if t then 1 else 0), j, i)| ≤ 1 := by
    change |(noise slot : ℝ) / narrowTrimmedSpatialWidths W τ ξ N slot| ≤ 1
    rw [abs_div, abs_of_pos hwidth]
    exact (div_le_one hwidth).mpr hbound
  rw [abs_mul, abs_of_nonneg hscale.1]
  exact (mul_le_of_le_one_left (abs_nonneg _) hscale.2).trans hentry

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedSlicedForecastCapLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart kernelV p w vchild : ℝ) : ℝ :=
  actualSlicedForecastModelCapLog m (nX + m * M) nX
    (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost)
    (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1)
    (preparedSlicedForecastBadLog m nX Qstride gainLog) (cost + 1)
    (preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart) kernelV p w vchild

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastModelLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedConcreteSlicedForecastCapLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart childLog : ℝ) : ℝ :=
  preparedSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart
    (cost + 1) (preparedSlicedForecastTailLog cost) cost (childLog + 1)

noncomputable def preparedConcreteSlicedForecastPeriodLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart childLog E : ℝ) : ℝ :=
  actualSlicedForecastModelPeriodLog m (nX + m * M) nX
    (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost)
    (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1)
    (preparedSlicedForecastBadLog m nX Qstride gainLog) (cost + 1)
    (preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart)
    (cost + 1) (preparedSlicedForecastTailLog cost) cost (childLog + 1) E

end Erdos3.VectorPolynomial

end

end OAI
end


