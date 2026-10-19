-- Prove2me | Definitions.Def_OAIE3v2B260
-- name    : OAIE3v2B260
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:44:51.984118+00:00
-- url     : https://prove2.me/theorems/f0b17136-dbcd-4f4c-90c2-1af4a5c9e25c
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 267 of 311
-- statement:
--   Definitions bundle 267 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B218`, `OAIE3v2B248`, `OAIE3v2B251`, `OAIE3v2B253`, `OAIE3v2B254` of this split.
--
--   Modules: `Estimates/AllocatedCandidateInnerSourceGain.lean`, `Estimates/AllocatedCenteredNarrowPrescribedMarginal.lean`, `Estimates/AllocatedExternalCandidateTaggedSourceEvaluation.lean`, `Estimates/PreparedCenteredShortJointBadProduct.lean`, `Estimates/PreparedCenteredShortJointGoodData.lean`, `Estimates/PreparedCenteredShortMeasurableBadProduct.lean`, `Estimates/PreparedFiniteNestedSourceRelativeInitializerBounds.lean`, `Estimates/PreparedRelativePositiveNativeRuleCanonical.lean`, `Estimates/SampledNativeDetectionEmptyTags.lean`, `Linear/AllocatedCenteredMeasurableFramedBadTail.lean`, `Linear/PreparedCenteredMarginalProjectionBounds.lean`, `Polynomial/PreparedCenteredShortJointGoodPolynomial.lean`, `Probability/NativeSliceLawVerticalPartners.lean`, `Probability/PreparedCenteredShortProbabilityBadProduct.lean`, `Sampling/PreparedCenteredShortForecastProductiveGoodModel.lean`, `Sampling/PreparedForecastRequiredPowerBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Definitions.Def_OAIE3v2B248
import Definitions.Def_OAIE3v2B251
import Definitions.Def_OAIE3v2B253
import Definitions.Def_OAIE3v2B254

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredNarrowPrescribedMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_centered_narrow_prescribed_marginal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ AllocatedCenteredNarrowPrescribedMarginalStatement m A := by
  obtain ⟨A, hA, hmarginal⟩ := exists_allocated_centered_narrow_prescribed_marginal_pointwise m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density Z
  obtain ⟨hN, hbases, hbox, hmass, hmargin, hnormalizer, hsite⟩ :=
    hmarginal B U basis S hb o μ ν hR hσ hσ1 C V hC hV
      Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ
      hAP hLP hCP hVP p hp hm stride hs hsP hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP
      N hsize hrank hRank T hT
  refine ⟨hN, hbases, hbox, hmass, hmargin, hnormalizer, ?_⟩
  intro law
  have hweight : ∀ z, Measurable (fun center => (law center).weight z) :=
    allocatedCenteredJointFiniteLaw_weight_measurable B U basis hb o hR hσ S p hm
      bases hbases stride T widths (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN)
      hmass (fun center => (hnormalizer center).2.2.1)
  refine ⟨hweight, ?_⟩
  intro Sites _ _ root hroot hrootSum
  exact centeredFiniteMarginal_siteLaw_excessMass_le_of_uniform μ law hweight _ _ _ _
    (hsite root hroot hrootSum)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCenteredMeasurableFramedBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (rankC : ℝ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (c : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ∀ j, U j)
variable (hc : Measurable c)
variable (sample : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
  (Option (LayerSamplerVariables G I n B) × X → ℤ) → CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (read : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
  (Option (LayerSamplerVariables G I n B) × X → ℤ) → AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hread : ∀ center a, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
  inactive spatial kernel block rankC center (c center) a (sample center a) (read center a))
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
variable (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells width
  (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center))
local notation "jointLaw" => (fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hZ
  (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
  (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) (hD center))
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U)) [IsProbabilityMeasure μ]
variable (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (cutoff : ℕ)

include hc hread in

theorem exists_allocatedCentered_measurable_framed_bad_tail
    {ε : ℝ} (hbound : (centeredFiniteProbabilityMeasure μ jointLaw).real
      {z | cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
        (read z.1 z.2.1.val z.2.2.val)} ≤ ε) :
    ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 width 1)),
      MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ jointLaw).real bad ≤ ε ∧
      (∀ center x, 0 < (jointLaw center).weight x →
        ((center,x) ∈ bad ↔ cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
          (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
          (allocatedJointFrameRead x.1.val (read center x.1.val x.2.val)))) ∧
      ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ jointLaw,
        z ∈ bad ↔ cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
          (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
          (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) := by
  have hweight := allocatedCentered_joint_weight_measurable B U b hb o S hR hσ poly hm
    stride cells width hwidth hZ bases hbases hD
  obtain ⟨bad, hbad, hmassbad, heq⟩ := exists_allocatedCentered_measurable_unframed_bad_tail
    B U bW b hb o S hR hσ poly hm inactive spatial kernel block rankC c hc sample read hread
    stride cells width hwidth hZ bases hbases hD μ P A cutoff hbound
  have hpositive : ∀ center x, 0 < (jointLaw center).weight x →
      ((center,x) ∈ bad ↔ cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
        (allocatedJointFrameRead x.1.val (read center x.1.val x.2.val))) := by
    intro center x hx
    rw [allocatedActualPrimeBad_product_jointFrame]
    exact (heq center x hx).symm
  refine ⟨bad, hbad, hmassbad, hpositive, ?_⟩
  exact (centeredFiniteProbabilityMeasure_ae_positive_weight μ jointLaw hweight).mono
    (fun z hz => hpositive z.1 z.2 hz)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceRelativeInitializerBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uα
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformEarlyRadius (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {p g : ℝ}, 0 ≤ p → 0 ≤ g →
      let pRadius := allocatedCommonProductRadiusLog m p g
      let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m p g
      pRadius ∈ Set.Icc 0 ((p + g + A) ^ A) ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      ∀ {G : Type uG} [Fintype G] {I : Fin m → Type uI} [∀ j, Fintype (I j)]
        {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
        {α : Type uα} [Fintype α] (rowSets : Fin m → Finset (Finset α))
        [∀ j, Nonempty (rowSets j)],
        Fintype.card α ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        let T := allocatedIdealCoverSupport (G := G) B rowSets
        let r := allocatedProductIdealSiteRadius (G := G) B rowSets
        1 ≤ r ∧ (∀ j, 0 ≤ T j) ∧
        (∀ j, partitionedIdealRadius α m + 1 ≤ T j) ∧
        (∀ j, (Fintype.card (BoundedCoefficientExponent
          (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
        (∀ j, (rowSets j).card * T j ≤ (r : ℝ)) ∧
        ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp g) →
          (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
          (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
          (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
            (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4) := by
  obtain ⟨A, hA, hbound⟩ := exists_allocatedCommonProductRadiusLog_bound m
  refine ⟨A, hA, ?_⟩
  intro p g hp hg pRadius R
  obtain ⟨hlog, hpos, hone, hinv, _⟩ := allocatedCommonProductRadius_bounds m hp hg
  refine ⟨⟨hlog, hbound hp hg⟩, fun _ => ⟨hpos, hone, hinv.le⟩, ?_⟩
  intro G _ I _ n B _ α _ rowSets _ hdim hvars hI hn
  dsimp only
  have hgeo := allocatedCanonicalSlice_source_geometry B rowSets hp hg hdim hvars hI hn
    (fun _ => 0) (fun _ => le_refl 0) (fun _ => Real.exp_nonneg g)
    (fun _ => hpos.le) (fun _ => le_refl (allocatedCommonProductRadius m p g))
  refine ⟨hgeo.1, hgeo.2.1, hgeo.2.2.1, hgeo.2.2.2.1, hgeo.2.2.2.2.1, ?_⟩
  intro C hC hCg
  have hgeometry := allocatedCanonicalSlice_source_geometry B rowSets hp hg hdim hvars hI hn
    C hC hCg (fun _ => hpos.le) (fun _ => le_refl (allocatedCommonProductRadius m p g))
  refine ⟨?_, hgeometry.2.2.2.2.2.1, hgeometry.2.2.2.2.2.2⟩
  intro j
  have hT : 1 ≤ allocatedIdealCoverSupport (G := G) B rowSets j := by
    linarith [hgeometry.2.2.1 j, partitionedIdealRadius_nonneg α m]
  calc
    _ = C j * (((Fintype.card (I j) : ℝ) + 1) * (1 * R j)) := by ring
    _ ≤ C j * (((Fintype.card (I j) : ℝ) + 1) *
        (allocatedIdealCoverSupport (G := G) B rowSets j * R j)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT hpos.le) (by positivity)) (hC j)
    _ ≤ _ := hgeometry.2.2.2.2.2.1 j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

theorem preparedUniformEarlyRadius_eighth
    {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
    [∀ j, Nonempty (rowSets j)] {p g Pchart : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hdim : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j, C j ≤ Real.exp Pchart) (hallow : Pchart + 1 ≤ g) :
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m p g
    let T := allocatedIdealCoverSupport (G := G) B rowSets
    let r := allocatedProductIdealSiteRadius (G := G) B rowSets
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 8) ∧
      (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 8) ∧
      (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 8) := by
  intro R T r
  obtain ⟨_, _, hfamilies⟩ :=
    (Classical.choose_spec (exists_preparedUniformEarlyRadius m)).2 hp hg
  have hgeometry := hfamilies (G := G) B rowSets hdim hvars hI hn
  have hsmall := hgeometry.2.2.2.2.2
  have hdoubled := hsmall (fun j => 2 * C j)
    (fun j => mul_nonneg (by norm_num) (hC j))
    (fun j => twice_chartCoefficient_le_exp (hchart j) hallow)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    nlinarith only [hdoubled.1 j]
  · intro j
    nlinarith only [hdoubled.2.1 j]
  · intro j
    nlinarith only [hdoubled.2.2 j]

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedCenteredMarginalProjectionBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

structure PreparedCenteredMarginalProjectionBounds (nX : ℕ) (Pmaster Plate Pproj : ℝ) : Prop where
  Pproj_nonneg : 0 ≤ Pproj
  master_projection : Pmaster ≤ Pproj
  late_projection : Plate ≤ Pproj
  m_projection : (m : ℝ) ≤ Pproj
  variables_projection : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pproj
  X_projection : (Fintype.card (Fin nX) : ℝ) ≤ Pproj
  frame_projection : (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pproj
  coefficient_projection : ∀ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pproj
  I_projection : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pproj
  n_projection : ∀ j, (n j : ℝ) ≤ Pproj
  J_projection : ∀ j, (Fintype.card (J j) : ℝ) ≤ Pproj
  Rinv_projection : ∀ j, (R j)⁻¹ ≤ Real.exp Pproj
  σinv_projection : ∀ j, (σ j)⁻¹ ≤ Real.exp Pproj
  S_projection : (S.value : ℝ) ≤ Real.exp Pproj
  root_projection : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ Real.exp Pproj
  profile_projection : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pproj

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredShortJointBadProduct
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

def PreparedShortCertifiedSameScaleBadProductInterface (B Elog Vlog : ℝ) (Q : ℕ) : Prop :=
  let Ps := (B + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m
  ∀ {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp B)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp B) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp B)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {ρ Rs Smax : ℝ}
    (_hρ : 0 < ρ) (_hρPs : 1 / ρ ≤ Real.exp B)
    (stride : Fin nX → ℕ) (_hstride : ∀ x, 0 < stride x)
    (_hSmax : 0 ≤ Smax) (_hSmaxPs : Smax ≤ Real.exp B) (_hstrideMax : ∀ x, ((stride x * ((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℕ) : ℝ) ≤ Smax)
    (H : Fin nX → ℝ)
    (_hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (_hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (_hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) (hwidth : ∀ z, 0 < width z)
    (_hwide : ∀ z, ρ * H z.2 ≤ width z)
    , let Dphysical := fun z : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ =>
      allocatedCoefficientDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
    ∃ read : (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
        AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ,
      (∀ z, allocatedReadNoise (read z) = z) ∧
      (∀ z, Dphysical z ≠ 0 →
        ∀ (primes : Finset ℕ) (hne : ∀ p : primes, NeZero p.val),
          letI := hne
          ∀ (depth : ℕ → ℕ) (q : ℕ) (hq : 0 < q),
            letI : NeZero q := ⟨hq.ne'⟩
            ∀ hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q,
              coefficientDeckChartEvent U bW b hb o q
                (allocatedChartResiduePrimePowerWitness
                  (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)
                  (modularInitialRankStrength m (nX + m * M) : ℝ) primes depth q hdiv
                  (fun v => (z v : ZMod q)))
                (affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))) ↔
              ∀ p : primes, allocatedActualModulusBad
                (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)
                (preparedInitialRankSpatialEmbedding (m := m) nX M)
                (preparedInitialRankKernelEmbedding (m := m) nX M)
                (preparedInitialRankPrincipalEmbedding prep nX M
                  (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value))
                (modularInitialRankStrength m (nX + m * M) : ℝ)
                (p.val ^ depth p.val) (read z)) ∧
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 3 * (physicalBadProductAccuracy Elog Vlog) ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      0 < (quantitativeBadPrimeRadius Elog) ∧ ((quantitativeBadPrimeRadius Elog) : ℝ) ≤ Real.exp (Elog + 3) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
            (if (∏ x, stride x) ^ 2 *
              (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * (quantitativeBadPrimeRadius Elog)) <
                ∏ p ∈ primes, p ^ largestTestedBadDepth depth
                  (fun p a z => allocatedActualPrimeBad (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M)
                    (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) primes ((modularInitialRankStrength m ((nX + m * M : ℕ)) : ℝ)) p a (read z)) p z
              then (1 : ℝ) else 0)) ≤ Real.exp (-Elog)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

omit [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))] in

theorem preparedCenteredShortJoint_badProduct_of_read
    (B0 Elog Vlog : ℝ) (Q : ℕ)
    (hsource : PreparedShortCertifiedSameScaleBadProductInterface prep U b S B0 Elog Vlog Q)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp B0)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp B0) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp B0)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {ρ Rs Smax : ℝ}
    (hρ : 0 < ρ) (hρPs : 1 / ρ ≤ Real.exp B0)
    (stride : Fin nX → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp B0) (hstrideMax : ∀ x, ((stride x * ((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℕ) : ℝ) ≤ Smax)
    (H : Fin nX → ℝ)
    (hsize : ∀ x, Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)

    (center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (read : (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ)
    (hread : ∀ a z, allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center a z ≠ 0 → AllocatedPhysicalRankReadCertificate (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o (allocatedCenteredConditionalPolynomial U poly c a) (allocatedCenteredConditionalPolynomial_mem U poly hm c a) (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) z (read a z)) :
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ _hlocal : ∀ a, 0 < selectedResidueDensityMass stride cells width (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center a),
    ∀ (bases : Finset (Fin nX → ℤ)) (hbases : bases.Nonempty),
      ∃ htotal : 0 < selectedJointDensityMass bases stride cells width (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center),
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (selectedJointFiniteLaw bases hbases stride cells width hwidth hZ (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center)
            (allocatedCenteredJointDensity_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) htotal).mean
            (fun az => let a := az.1.val; let z := az.2.val
              if (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius Elog) <
        ∏ p ∈ primes, p ^ largestTestedBadDepth depth
          (fun p d z => allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M)
            (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ) p d (read a z)) p z then (1 : ℝ) else 0) ≤ Real.exp (-Elog) := by
  let density := allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center
  have hconditional (a : Fin nX → ℤ) :=
    hsource bW hb o C V hC hV hR hσ hσ1 Cinv hCinv hchart hsmall hAP hCP hVP μ ν
      (allocatedCenteredConditionalPolynomial U poly c a) (allocatedCenteredConditionalPolynomial_degree U poly c a hp)
      (allocatedCenteredConditionalPolynomial_mem U poly hm c a) hρ hρPs stride hstride hSmax hSmaxPs hstrideMax H hsize
      (fun j => (allocatedCenteredConditionalPolynomial_rank U poly c a hp H Rs j).mpr (hrank j))
      hRs cells hcells width hwidth hwide
  dsimp only at hconditional
  simp_rw [allocatedCenteredConditionalPolynomial_density U poly hm c _ (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) b hb o hR hσ S center hc] at hconditional
  choose hD0 hZ hDpos chosen hnoise hcert hmass hlower hupper hRbad hRbound htail using hconditional
  refine ⟨hZ 0, hDpos, ?_⟩
  intro bases hbases
  have htotal : 0 < selectedJointDensityMass bases stride cells width density := by
    have hbound := selectedJointDensityMass_bounds bases hbases stride cells width density
      (fun a => ⟨hlower a, hupper a⟩)
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hbound.1
  refine ⟨htotal, ?_⟩
  intro primes hprime
  let : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
  intro depth hdepth
  have hmix := selectedJointFiniteLaw_conditional_event_le bases hbases stride cells width hwidth (hZ 0)
    density hD0 htotal hDpos (fun a z =>
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius Elog) <
      ∏ p ∈ primes, p ^ largestTestedBadDepth depth
        (fun p d z => allocatedActualPrimeBad
          (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)
          (preparedInitialRankSpatialEmbedding (m := m) nX M)
          (preparedInitialRankKernelEmbedding (m := m) nX M)
          (preparedInitialRankPrincipalEmbedding prep nX M
            (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes
          (modularInitialRankStrength m (nX + m * M) : ℝ) p d (read a z)) p z) (ε := Real.exp (-Elog))
  apply (show _ = _ from ?_).trans_le (hmix ?_)
  · congr 1
    funext az
    dsimp only
    split_ifs <;> rfl
  intro a
  have ht := htail a primes hprime depth hdepth
  have heq := selectedResidueDensityPMF_certifiedRead_badProduct_congr
    (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o (allocatedCenteredConditionalPolynomial U poly c a) (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
    (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ)
    stride cells width hwidth (hZ 0) (density a) (hD0 a) (hDpos a)
    (chosen a) (read a) (hcert a) (hread a) primes depth
    ((∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius Elog))
  rw [heq] at ht
  apply le_of_eq_of_le ?_ ht
  apply tsum_congr
  intro z
  congr 1
  split_ifs <;> rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedCenteredShortProbabilityBadProduct
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

omit [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))] in

theorem exists_preparedCenteredShortProbability_badProduct
    (B0 Elog Vlog : ℝ) (Q : ℕ)
    (hsource : PreparedShortCertifiedSameScaleBadProductInterface prep U b S B0 Elog Vlog Q)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp B0)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp B0) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp B0)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {ρ Rs Smax : ℝ}
    (hρ : 0 < ρ) (hρPs : 1 / ρ ≤ Real.exp B0)
    (stride : Fin nX → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp B0) (hstrideMax : ∀ x, ((stride x * ((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℕ) : ℝ) ≤ Smax)
    (H : Fin nX → ℝ)
    (hsize : ∀ x, Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)

    (bases : Finset (Fin nX → ℤ)) (hbases : bases.Nonempty)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
    (htotal : ∀ center, 0 < selectedJointDensityMass bases stride cells width
      (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center)) :
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (centeredFiniteProbabilityMeasure μ (fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hmass (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (allocatedCenteredJointDensity_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (htotal center))).real
            {z | (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius Elog) <
              ∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p
                (read z.1 z.2.1.val z.2.2.val)} ≤ Real.exp (-Elog) := by
  obtain ⟨c, hcmeas, hc⟩ := exists_measurable_subtractive_constant_center
    (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U bW
  obtain ⟨sample, read, hread⟩ := exists_allocatedCentered_recovered_sample_reads
    (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) c hc
  refine ⟨c, hcmeas, hc, sample, read, hread, ?_⟩
  intro primes hprime
  let : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
  intro depth hdepth
  let law := fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hmass (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (allocatedCenteredJointDensity_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (htotal center)
  have hweight : ∀ x, Measurable (fun center => (law center).weight x) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells width hwidth hmass
      (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_measurable_center (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm) htotal
  refine allocatedCentered_badProduct_probability_le
    (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ)
    c hcmeas (fun x => x.1.val) (fun x => x.2.val) law
    (fun center x => read center x.1.val x.2.val) ?_ primes depth
    ((∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius Elog)) μ hweight ?_
  · intro center x hx
    have hdensity := (selectedJointFiniteLaw_support bases hbases stride cells width hwidth hmass
      (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (allocatedCenteredJointDensity_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center)
      (htotal center) x hx).2.ne'
    exact ((hread center x.1.val x.2.val).2 hdensity).2.2.2.2.2
  · intro center
    obtain ⟨hZ, hlocal, hbound⟩ := preparedCenteredShortJoint_badProduct_of_read prep U b S
      B0 Elog Vlog Q hsource bW hb o C V hC hV hR hσ hσ1 Cinv hCinv hchart hsmall
      hAP hCP hVP μ ν poly hp hm hρ hρPs stride hstride hSmax hSmaxPs hstrideMax
      H hsize hrank hRs cells hcells width hwidth hwide center (c center) (hc center)
      (read center) (fun a z hz => ((hread center a z).2 hz).2.2.2.2.2)
    obtain ⟨hjoint, hbound⟩ := hbound bases hbases
    have ht := hbound primes hprime depth hdepth
    apply le_of_eq_of_le ?_ ht
    congr 1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredShortMeasurableBadProduct
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

omit [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))] in

theorem exists_preparedCentered_short_measurableBadProduct
    (B0 Elog Vlog : ℝ) (Q : ℕ)
    (hsource : PreparedShortCertifiedSameScaleBadProductInterface prep U b S B0 Elog Vlog Q)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp B0)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp B0) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp B0)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {ρ Rs Smax : ℝ}
    (hρ : 0 < ρ) (hρPs : 1 / ρ ≤ Real.exp B0)
    (stride : Fin nX → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp B0) (hstrideMax : ∀ x, ((stride x * ((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℕ) : ℝ) ≤ Smax)
    (H : Fin nX → ℝ)
    (hsize : ∀ x, Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)

    (bases : Finset (Fin nX → ℤ)) (hbases : bases.Nonempty)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
    (htotal : ∀ center, 0 < selectedJointDensityMass bases stride cells width
      (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center)) :
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      let law := fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hmass (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (allocatedCenteredJointDensity_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (htotal center)
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U × (bases × rectangularWeightIndices 0 width 1)),
          MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ law).real bad ≤ Real.exp (-Elog) ∧
          (∀ center x, 0 < (law center).weight x →
            ((center,x) ∈ bad ↔ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius Elog) < ∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead x.1.val (read center x.1.val x.2.val)))) ∧
          ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law,
            z ∈ bad ↔ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius Elog) < ∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) := by
  obtain ⟨c, hcmeas, hc, sample, read, hread, htail⟩ :=
    exists_preparedCenteredShortProbability_badProduct prep U b S B0 Elog Vlog Q hsource
      bW hb o C V hC hV hR hσ hσ1 Cinv hCinv hchart hsmall hAP hCP hVP μ ν
      poly hp hm hρ hρPs stride hstride hSmax hSmaxPs hstrideMax H hsize hrank hRs
      cells hcells width hwidth hwide bases hbases hmass htotal
  refine ⟨c, hcmeas, hc, sample, read, hread, ?_⟩
  dsimp only
  intro primes hprime
  let : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
  intro depth hdepth
  exact exists_allocatedCentered_measurable_framed_bad_tail
    (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ)
    c hcmeas sample read hread stride cells width hwidth hmass bases hbases htotal μ
    primes depth ((∏ x, stride x) ^ 2 *
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius Elog))
    (htail primes hprime depth hdepth)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredShortJointGoodData
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m nX : ℕ} {G : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem allocatedCentered_recovered_joint_good_set
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [IsProbabilityMeasure μ]
    (bases : Finset ((Fin nX) → ℤ)) (hbases : bases.Nonempty) (stride : (Fin nX) → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (width : Option (LayerSamplerVariables G I n B) × (Fin nX) → ℝ) (hwidth : ∀ z, 0 < width z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
    (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells width
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center))
    (c : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ∀ j, U j)
    (sample : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ((Fin nX) → ℤ) →
      (Option (LayerSamplerVariables G I n B) × (Fin nX) → ℤ) →
        CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ((Fin nX) → ℤ) →
      (Option (LayerSamplerVariables G I n B) × (Fin nX) → ℤ) →
        AllocatedActualCoefficientIndex G (Fin nX) I E n B → ℤ)
    (hread : ∀ center a, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center (c center) a (sample center a) (read center a))
    (e : Fin 2 × Fin nX ↪ G) (κ : ℝ)
    (primes : Finset ℕ) [∀ p : primes, NeZero p.val] (depth : ℕ → ℕ) (cutoff : ℕ)
    (εmod εsp : ℝ) :
    let law := fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) (hD center)
    let joint := centeredFiniteProbabilityMeasure μ law
    ∀ (modularBad : Set (CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
          (bases × rectangularWeightIndices 0 width 1))),
      MeasurableSet modularBad → joint.real modularBad ≤ εmod →
      (∀ center x, 0 < (law center).weight x →
        ((center,x) ∈ modularBad ↔ cutoff < ∏ p ∈ primes, p ^ largestTestedBadDepth depth
          (allocatedActualPrimeBad inactive spatial kernel block primes C) p
          (allocatedJointFrameRead x.1.val (read center x.1.val x.2.val)))) →
      joint.real {z | spatialMatrixBlockBad e width (κ / 2) z.2.2.val} ≤ εsp →
      ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
          (bases × rectangularWeightIndices 0 width 1)),
        bad = modularBad ∪ {z | spatialMatrixBlockBad e width (κ / 2) z.2.2.val} ∧
        MeasurableSet bad ∧ joint.real bad ≤ εmod + εsp ∧
        ∀ᵐ z ∂joint, z ∉ bad →
          AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
            (c z.1) z.2.1.val z.2.2.val (sample z.1 z.2.1.val z.2.2.val)
            (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) ∧
          (∏ p ∈ primes, p ^ largestTestedBadDepth depth
            (allocatedActualPrimeBad inactive spatial kernel block primes C) p
            (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val))) ≤ cutoff ∧
          ∀ t : Fin 2, κ / 2 < |Matrix.det (fun i j : Fin nX =>
            spatialMatrixNormalizedEntries e width z.2.2.val (t,j,i))| := by
  intro law joint modularBad hmodularBad hmodmass hmodular hspmass
  have hweight : ∀ x, Measurable (fun center => (law center).weight x) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells width hwidth hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) hD
  have hrecovered := allocatedCentered_recovered_sample_ae B U bW b hb o S hR hσ poly hm
    inactive spatial kernel block C μ bases hbases stride cells width hwidth hmass hD
    c sample read hread
  have hgood := centeredFinite_spatial_modular_good_set μ law hweight
    (fun x => x.2.val) width e κ modularBad hmodularBad hmodmass hspmass
    (fun z => ∏ p ∈ primes, p ^ largestTestedBadDepth depth
      (allocatedActualPrimeBad inactive spatial kernel block primes C) p
      (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)))
    cutoff hmodular
    (fun z => AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      (c z.1) z.2.1.val z.2.2.val (sample z.1 z.2.1.val z.2.2.val)
      (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)))
    (hrecovered.mono (fun z hz => hz.2.2))
  exact ⟨_, rfl, hgood⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_preparedCentered_short_jointGoodData (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (B0 Vlog gainLog gain : ℝ) (Q : ℕ)
    (_hsource : PreparedShortCertifiedSameScaleBadProductInterface prep U b S B0 (gainLog + 8) Vlog Q)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp B0)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp B0) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp B0)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {ρ Rs Smax : ℝ}
    (_hρ : 0 < ρ) (_hρPs : 1 / ρ ≤ Real.exp B0)
    (stride : Fin nX → ℕ) (_hstride : ∀ x, 0 < stride x)
    (_hSmax : 0 ≤ Smax) (_hSmaxPs : Smax ≤ Real.exp B0) (_hstrideMax : ∀ x, ((stride x * ((max Q ((quantitativeBadPrimeRadius (gainLog + 8)) ^ 2) : ℕ)) : ℕ) : ℝ) ≤ Smax)
    (N : Fin nX → ℕ)
    (_hsize : ∀ x, Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun x => (N x : ℝ)) Rs (U j) (poly j))
    (_hRs : Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (_hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) (hwidth : ∀ z, 0 < width z)
    (_hwide : ∀ z, ρ * (N z.2 : ℝ) ≤ width z)

    (bases : Finset (Fin nX → ℤ)) (hbases : bases.Nonempty)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
    (htotal : ∀ center, 0 < selectedJointDensityMass bases stride cells width
      (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center))
    {P : ℝ} (_hP : 0 ≤ P) (_hB0P : B0 ≤ P)
    (_hg : 0 ≤ gainLog) (_hgP : gainLog + 8 ≤ P) (_hgain : Real.exp (-gainLog) ≤ gain)
    (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤ P)
    (_hX : (nX : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) ≤ P)
    (_hn : ∀ j, ((preparedSamplerTransverse prep) j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (RankPreparationLayer.Coord (prep j)) : ℝ) ≤ P)
    (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hsP : ∀ x, (stride x : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (_hspSize : ∀ x, Real.exp ((P + A) ^ A) ≤ (N x : ℝ))
    (_hspRank : Real.exp ((P + A) ^ A) ≤ Rs)
    (_hwidthEq : width = narrowTrimmedSpatialWidths (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) W τ ξ N)
    (_hnX : 0 < nX) (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (_hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride width z)
    (_hspWide : ∀ i,
      Real.exp (smoothMatrixBlockWidthLogBudget (2 * nX * nX) nX 2 (gainLog + 8)) ≤
        spatialMatrixIndexWidth e stride width i)
    (_hLip : 2 / spatialMatrixBlockThreshold nX (jointSpatialError gainLog) *
      ((nX * nX.factorial : ℕ) : ℝ) ≤ Real.exp P),
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      let law := fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hmass (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (allocatedCenteredJointDensity_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (htotal center)
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U ×
          (bases × rectangularWeightIndices 0 width 1)),
          MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ law).real bad ≤ (gain / 4) / 4 ∧
          ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, z ∉ bad →
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c z.1) z.2.1.val z.2.2.val (sample z.1 z.2.1.val z.2.2.val) (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.2.val (t,j,i))| := by
  obtain ⟨A, hA, hspatial⟩ := exists_allocated_centered_spatial_matrix_exceptional m
  refine ⟨A, hA, ?_⟩
  intro nX M X₀ J₀ prep U b R σ S B0 Vlog gainLog gain Q hsource E _ bW hb o C V hC hV
    hR hσ hσ1 Cinv hCinv hchart hsmall hAP hCP hVP _ _ _ _ μ _ _ ν _ _ poly hp hm
    ρ Rs Smax hρ hρPs stride hstride hSmax hSmaxPs hstrideMax N hsize hrank hRs
    cells hcells width hwidth hwide bases hbases hmass htotal P hP hB0P hg hgP hgain
    hmSize hK hX hdim hRP hσP hcount hI hn hJ hLP hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    hspSize hspRank hwidthEq hnX e hscale hspWide hLip
  subst width
  obtain ⟨c, hcmeas, hc, sample, read, hread, hmodular⟩ :=
    exists_preparedCentered_short_measurableBadProduct prep U b S B0 (gainLog + 8) Vlog Q hsource
      bW hb o C V hC hV hR hσ hσ1 Cinv hCinv hchart hsmall hAP hCP hVP μ ν
      poly hp hm hρ hρPs stride hstride hSmax hSmaxPs hstrideMax (fun x => (N x : ℝ))
      hsize hrank hRs cells hcells _ hwidth hwide bases hbases hmass htotal
  have hExp := Real.exp_le_exp.mpr hB0P
  have hsp := hspatial (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S hb o μ ν hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ
    (hAP.trans hExp) hLP (fun j => (hCP j).trans hExp) (fun j => (hVP j).trans hExp)
    poly hp hm stride hstride hsP hW hWP hτ hτP hξ hξ1 hξP N hspSize hrank hspRank
    cells hcells bases hbases hwidth hmass htotal hnX e
    (jointSpatialError_pos gainLog) (by linarith : 0 ≤ gainLog + 8)
    (jointSpatialError_inverse_le_exp gainLog) hscale hspWide hLip
  refine ⟨c, hcmeas, hc, sample, read, hread, ?_⟩
  dsimp only
  intro primes hprime
  let : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
  intro depth hdepth
  obtain ⟨modularBad, hmmeas, hmmass, hmexact, _⟩ := hmodular primes hprime depth hdepth
  obtain ⟨bad, _, hbmeas, hbadmass, hgood⟩ := allocatedCentered_recovered_joint_good_set
    (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ)
    μ bases hbases stride cells _ hwidth hmass htotal c sample read hread e
    (spatialMatrixBlockThreshold nX (jointSpatialError gainLog)) primes depth
    ((∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8))) (Real.exp (-(gainLog + 8)))
    (jointSpatialError gainLog / 2 + 6 * positiveProjectionAccuracy P)
    modularBad hmmeas hmmass hmexact hsp
  refine ⟨bad, hbmeas, ?_, hgood⟩
  exact hbadmass.trans (by
    simpa only [← add_assoc] using jointExceptionalGainBudget hg hgP hgain)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedCenteredShortJointGoodPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_preparedCentered_short_jointGoodPolynomial (m : ℕ) :
    ∃ A Asp : ℕ, 4 ≤ A ∧ 2 ≤ Asp ∧
    (∀ {P₀ gainLog : ℝ} {n : ℕ}, 0 ≤ P₀ → 0 < n → (n : ℝ) ≤ P₀ →
      0 ≤ gainLog → gainLog ≤ P₀ →
      (spatialMatrixBlockThreshold n (jointSpatialError gainLog))⁻¹ ≤
        Real.exp ((P₀ + Asp) ^ Asp)) ∧
    ∀ {nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (B0 Vlog gainLog gain : ℝ) (Q : ℕ)
    (_hsource : PreparedShortCertifiedSameScaleBadProductInterface prep U b S B0 (gainLog + 8) Vlog Q)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp B0)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp B0) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp B0)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {ρ Rs Smax : ℝ}
    (_hρ : 0 < ρ) (_hρPs : 1 / ρ ≤ Real.exp B0)
    (stride : Fin nX → ℕ) (_hstride : ∀ x, 0 < stride x)
    (_hSmax : 0 ≤ Smax) (_hSmaxPs : Smax ≤ Real.exp B0) (_hstrideMax : ∀ x, ((stride x * ((max Q ((quantitativeBadPrimeRadius (gainLog + 8)) ^ 2) : ℕ)) : ℕ) : ℝ) ≤ Smax)
    (N : Fin nX → ℕ)
    (_hsize : ∀ x, Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun x => (N x : ℝ)) Rs (U j) (poly j))
    (_hRs : Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (_hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) (hwidth : ∀ z, 0 < width z)
    (_hwide : ∀ z, ρ * (N z.2 : ℝ) ≤ width z)

    (bases : Finset (Fin nX → ℤ)) (hbases : bases.Nonempty)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
    (htotal : ∀ center, 0 < selectedJointDensityMass bases stride cells width
      (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center))
    {P₀ P : ℝ} (_hP₀ : 0 ≤ P₀) (_hnP₀ : (nX : ℝ) ≤ P₀)
    (_hgP₀ : gainLog ≤ P₀) (_hcutoffP : (P₀ + Asp) ^ Asp ≤ P)
    (_hP : 0 ≤ P) (_hB0P : B0 ≤ P)
    (_hg : 0 ≤ gainLog) (_hgP : gainLog + 8 ≤ P) (_hgain : Real.exp (-gainLog) ≤ gain)
    (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤ P)
    (_hX : (nX : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) ≤ P)
    (_hn : ∀ j, ((preparedSamplerTransverse prep) j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (RankPreparationLayer.Coord (prep j)) : ℝ) ≤ P)
    (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hsP : ∀ x, (stride x : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (_hspSize : ∀ x, Real.exp ((P + A) ^ A) ≤ (N x : ℝ))
    (_hspRank : Real.exp ((P + A) ^ A) ≤ Rs)
    (_hwidthEq : width = narrowTrimmedSpatialWidths (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) W τ ξ N)
    (_hnX : 0 < nX) (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))),
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      let law := fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hmass (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (allocatedCenteredJointDensity_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) (htotal center)
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U ×
          (bases × rectangularWeightIndices 0 width 1)),
          MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ law).real bad ≤ (gain / 4) / 4 ∧
          ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, z ∉ bad →
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c z.1) z.2.1.val z.2.2.val (sample z.1 z.2.1.val z.2.2.val) (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.2.val (t,j,i))| := by
  obtain ⟨A₀, _, hgood⟩ := exists_preparedCentered_short_jointGoodData m
  obtain ⟨Asp, hAsp, hcutoff⟩ := exists_jointSpatialError_polynomial_budget
  let A := max A₀ 4
  have hA : 4 ≤ A := le_max_right _ _
  have hA₀ : A₀ ≤ A := le_max_left _ _
  refine ⟨A, Asp, hA, hAsp,
    fun hP₀ hn hnP₀ hg hgP₀ => (hcutoff hP₀ hn hnP₀ hg hgP₀).1, ?_⟩
  intro nX M X₀ J₀ prep U b R σ S B0 Vlog gainLog gain Q hsource E _ bW hb o C V hC hV
    hR hσ hσ1 Cinv hCinv hchart hsmall hAP hCP hVP _ _ _ _ μ _ _ ν _ _ poly hp hm
    ρ Rs Smax hρ hρPs stride hstride hSmax hSmaxPs hstrideMax N hsize hrank hRs
    cells hcells width hwidth hwide bases hbases hmass htotal P₀ P hP₀ hnP₀ hgP₀ hcutoffP
    hP hB0P hg hgP hgain hmSize hK hX hdim hRP hσP hcount hI hn hJ hLP hsP W τ ξ
    hW hWP hτ hτP hξ hξ1 hξP hspSize hspRank hwidthEq hnX e
  have hthreshold (a : ℕ) (ha : a ≤ A) :
      Real.exp ((P + a) ^ a) ≤ Real.exp ((P + A) ^ A) := by
    have hAr : (4 : ℝ) ≤ A := by exact_mod_cast hA
    have har : (a : ℝ) ≤ A := by exact_mod_cast ha
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by positivity) (by linarith : P + (a : ℝ) ≤ P + A) a).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P + A) ha)
  obtain ⟨_, hLip, hlogwide⟩ := hcutoff hP₀ hnX hnP₀ hg hgP₀
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P :=
    hAP.trans (Real.exp_le_exp.mpr hB0P)
  have hwidthBudget := jointExceptionalSpatialWidthBudget
    (J := PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep
      (modularInitialBlockCount m (nX + m * M)))
      (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) hP hW hWP hτ hτP hξ hξ1 hξP
    N stride hstride hsP hprofile (hlogwide.trans hcutoffP)
    (fun x => (hthreshold 4 hA).trans (hspSize x)) e
  have hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth stride width z := by
    rw [hwidthEq]
    exact hwidthBudget.1
  have hspWide : ∀ i,
      Real.exp (smoothMatrixBlockWidthLogBudget (2 * nX * nX) nX 2 (gainLog + 8)) ≤
        spatialMatrixIndexWidth e stride width i := by
    rw [hwidthEq]
    exact hwidthBudget.2
  exact hgood prep U b S B0 Vlog gainLog gain Q hsource bW hb o C V hC hV
    hR hσ hσ1 Cinv hCinv hchart hsmall hAP hCP hVP μ ν poly hp hm
    hρ hρPs stride hstride hSmax hSmaxPs hstrideMax N hsize hrank hRs
    cells hcells width hwidth hwide bases hbases hmass htotal hP hB0P hg hgP hgain
    hmSize hK hX hdim hRP hσP hcount hI hn hJ hLP hsP hW hWP hτ hτP hξ hξ1 hξP
    (fun x => (hthreshold A₀ hA₀).trans (hspSize x))
    ((hthreshold A₀ hA₀).trans hspRank) hwidthEq hnX e hscale hspWide
    (hLip.trans (Real.exp_le_exp.mpr hcutoffP))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedForecastRequiredPowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredShortForecastGoodConclusion
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) : Prop :=
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U ×
          (bases × rectangularWeightIndices 0 width 1)),
          MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ law).real bad ≤ (gain / 4) / 4 ∧
          ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, z ∉ bad →
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c z.1) z.2.1.val z.2.2.val (sample z.1 z.2.1.val z.2.2.val) (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.2.val (t,j,i))|

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredShortForecastGoodProperty
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (stride : Fin nX → ℕ)
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) : Prop :=
  PreparedCenteredShortForecastGoodConclusion prep U b S bW hb o hR hσ μ poly hm
    stride width bases gainLog gain Q e law

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredShortForecastProductiveGoodModel
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

def PreparedCenteredForecastProductiveConclusion
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    {nX : ℕ} (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N : Fin nX → ℕ)
    (widths : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)) (gainLog : ℝ)
    (law : CoefficientTorus (K := LayerSamplerVariables G I n B) U →
      FiniteProbabilityWeights (bases × rectangularWeightIndices 0 widths 1)) : Prop :=
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    ∀ (test : (Fin nX → ℝ) → ℝ), (∀ x, |test x| ≤ 1) →
    ∀ gain : ℝ, Real.exp (-gainLog) ≤ gain →
      gain ≤ (𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) →
    let productive := Finset.univ.filter (fun z : bases × rectangularWeightIndices 0 widths 1 =>
      Function.Injective (fun q : Sites => jointIntegerPhysicalSite q.val (z.1.val,z.2.val)) ∧
        gain / 2 ≤ 𝔼 q : Sites, test
          (fun i => (jointIntegerPhysicalSite q.val (z.1.val,z.2.val) i : ℝ)))
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 widths 1) | z.2 ∈ productive} ∧
      gain / 4 ≤ joint.real {z | z.2 ∈ productive} ∧
      (∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun s => c s.1))) ∧
        allocatedAffineDensity B U basis hb o hR hσ S p hm c
          (fun k v => (jointIntegerFrame (z.2.1.val,z.2.2.val) k v : ℝ)) ≠ 0) ∧
      ∀ z : bases × rectangularWeightIndices 0 widths 1, ∀ q : Sites,
        jointIntegerPhysicalSite q.val (z.1.val,z.2.val) ∈ integerBox N

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local instance 2000] fullBooleanRowSetFintype

structure PreparedCenteredForecastProductiveBounds
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    (Pchart Qstride Pmaster Plate Pphysical coarseTarget gainLog Pprod D : ℝ) : Prop where
  hnX : 0 < nX
  hσ1 : ∀ j, σ j ≤ 1
  hsmall : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) →
    (∀ j, C j ≤ Real.exp Pchart) →
    ∀ j, C j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1 / 4
  hMaster : 0 ≤ Pmaster
  hLate : Pmaster ≤ Plate
  hd : AllocatedComparisonDimensions (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (Fin (0 + 1)) (fun j : Fin m => (boundedBooleanJetRows (Fin 1) (j.val + 1) : Type)) D
  hD : D ≤ Pmaster
  hnMaster : (nX : ℝ) ≤ Pmaster
  hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster
  hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate
  hS : (S.value : ℝ) ≤ Real.exp Plate
  hchartMaster : Pchart ≤ Pmaster
  hstrideMaster : Qstride ≤ Pmaster
  hProd : 4 * (Plate + 8) ^ 2 ≤ Pprod
  hg : 0 ≤ gainLog
  hGainMaster : gainLog + (nX : ℝ) + 8 ≤ Pmaster
  hτeq : τ = Real.exp (-(gainLog + (nX : ℝ) + 8))
  hξLate : (normalizedTupleNarrowWidth (Fin nX)
    (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selection
    (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
      Pdetect (allocatedModelTestLog uSource pModel) (allocatedModelTestLog uSource pModel) ((forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))))
        (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j))
          ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastCap) / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedSourceEvaluation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)

theorem localLaw_complexMean_eq_fullSliceLaw_site (f : A.Site → ℂ) :
    C.localLaw.complexMean f =
      (C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean
        (fun t => f (C.site t.val t.property)) := by
  let f' : (LayerSamplerVariables G I n B → ℤ) → ℂ :=
    fun x => if hx : x ∈ integerBox A.sides then f ⟨x, hx⟩ else 0
  calc
    C.localLaw.complexMean f = C.localLaw.complexMean (fun site => f' site.val) := by
      apply congrArg C.localLaw.complexMean
      funext site
      simp only [f', dif_pos site.property]
    _ = (C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean
        (fun t => f' (C.parameter t.val)) := C.localLaw_complexMean_eq_fullSliceLaw f'
    _ = _ := by
      apply congrArg (C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean
      funext t
      simp only [f', dif_pos (C.parameter_mem t.val t.property)]
      rfl

end AllocatedExternalLocalChart

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NativeSliceLawVerticalPartners
namespace OAI

section

namespace Erdos3
open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_sliceLaw_localPivot_weighted_native_vertical_partners
    {Ω K X σ τ : Type*} [Fintype Ω] [Fintype K] [Fintype X] [DecidableEq X]
    {L : K → Type*} {Llocal : Ω → K → Type*}
    [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)]
    [∀ a k, LieRing (Llocal a k)] [∀ a k, LieAlgebra ℚ (Llocal a k)]
    {s : ℕ} {d : K → ℕ} {sLocal dLocal : Ω → K → ℕ}
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)]
    [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
    [∀ a k, TopologicalSpace (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, IsTopologicalAddGroup (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, ContinuousSMul ℝ (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, T2Space (ℝ ⊗[ℚ] Llocal a k)]
    (D : ∀ k, RationalFilteredNilmanifold (L k) s (d k))
    (Dlocal : ∀ a k, RationalFilteredNilmanifold (Llocal a k) (sLocal a k) (dLocal a k))
    {w : σ → ℕ} {wLocal : τ → ℕ}
    (Q : ∀ k, (D k).Niltest w) (P : ∀ a k, (Dlocal a k).Niltest wLocal)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    {N : X → ℕ} (stride : Ω → K → ℕ)
    (S : ∀ a k, ResidueBoxSlice N (stride a k))
    (hstride : ∀ a ∈ H, ∀ k, 0 < stride a k)
    (hlen : ∀ a k i, 0 < (S a k).length i)
    (pointAmbient : Ω → integerBox N → σ → ℤ) (pointLocal : Ω → K → integerBox N → τ → ℤ)
    (twist : Ω → K → integerBox N → ℂ) {pNative pLocal r q : ℝ}
    (hpLocal : 0 ≤ pLocal) (hr : 0 ≤ r) (hpq : pNative ≤ q)
    (hprecision : pLocal + r + 1 ≤ q)
    (hQ : ∀ k, (Q k).ComplexityLE pNative)
    (hcap : ∀ k, ((Q k).normBound : ℝ) ≤ 1)
    (hP : ∀ a ∈ H, ∀ k, (P a k).ComplexityLE pLocal)
    (htwist : ∀ a ∈ H, ∀ k t, ‖twist a k t‖ ≤ 1)
    (hcorr : ∀ a ∈ H, ∀ k, Real.exp (-r) ≤
      ‖((S a k).fullSliceLaw (hlen a k)).complexMean (fun t =>
        ((P a k).eval (pointLocal a k t) * twist a k t) * (Q k).eval (pointAmbient a t))‖) :
    ∃ (freq : ∀ k, L k →ₗ[ℚ] ℚ) (V : ∀ k, (D k).Niltest w) (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card K) * outer.mass H ≤
        outer.mass retained ∧
      (∀ k, (V k).ComplexityLE pNative ∧ (V k).orbit = (Q k).orbit ∧
        (V k).normBound = (Q k).normBound ∧ (V k).lipBound = (Q k).lipBound ∧
        ((V k).normBound : ℝ) ≤ 1) ∧
      (∀ k i, rationalLogHeight (freq k ((D k).basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s → ∀ x,
        (V k).observable (z • x) =
          character ((realifyFunctional (freq k) z.coord : ℝ) : CircleFourier.Circle) *
            (V k).observable x) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s →
        z ∈ (D k).realLattice → ∃ n : ℤ, realifyFunctional (freq k) z.coord = n) ∧
      (∀ k (z : (D k).RealGroup) (c : ℂ),
        (∀ x, (Q k).observable (z • x) = c * (Q k).observable x) →
        ∀ x, (V k).observable (z • x) = c * (V k).observable x) ∧
      ∀ a ∈ retained, ∀ k, Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) ≤
        ‖((S a k).fullSliceLaw (hlen a k)).complexMean (fun t =>
          ((P a k).eval (pointLocal a k t) * twist a k t) * (V k).eval (pointAmbient a t))‖ := by
  classical
  have hfiniteCorr (a : Ω) (ha : a ∈ H) (k : K) :
      Real.exp (-r) ≤ ‖𝔼 t ∈ (S a k).fullSlicePoints,
        ((P a k).eval (pointLocal a k t) * twist a k t) * (Q k).eval (pointAmbient a t)‖ := by
    rw [← (S a k).fullSliceLaw_complexMean_eq_expect_points (hlen a k) (hstride a ha k)]
    exact hcorr a ha k
  obtain ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hint,
      hpres, hselected⟩ := exists_localPivot_weighted_native_vertical_partners
    D Dlocal Q P outer H hH (fun a k => (S a k).fullSlicePoints)
    pointAmbient pointLocal twist hpLocal hr hpq hprecision hQ hcap hP
    (fun a ha k t _ => htwist a ha k t) hfiniteCorr
  refine ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hint, hpres, ?_⟩
  intro a ha k
  rw [(S a k).fullSliceLaw_complexMean_eq_expect_points (hlen a k) (hstride a (hsub ha) k)]
  exact hselected a ha k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateInnerSourceGain
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

theorem preparedFiniteForwardFixedCenterThreshold_le_seed_half
    (A : ℕ) (constants : ℕ → ℕ) (stage : ℕ)
    {x gainLog stageLog : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x)
    (hg : 0 ≤ gainLog) (hs : 0 ≤ stageLog) :
    Real.exp (-(2 * preparedFiniteForwardModelPrecision A constants stage x gainLog stageLog +
      4 * preparedFiniteForwardWork A constants stage x + 8)) ≤ Real.exp (-x) / 2 := by
  have hwork : x + 1 ≤ preparedFiniteForwardWork A constants stage x := by
    simpa only [Nat.cast_one, pow_one] using
      preparedFiniteForward_shiftedPower_le_work A 1 constants stage hA (by omega) hx
  have hw0 := preparedFiniteForwardWork_nonneg A constants stage hx
  have hprefix := (preparedFiniteForward_prefix_bounds A constants stage hx).2.1
  have hfloor : x + 1 ≤
      2 * preparedFiniteForwardModelPrecision A constants stage x gainLog stageLog +
        4 * preparedFiniteForwardWork A constants stage x + 8 := by
    unfold preparedFiniteForwardModelPrecision
    linarith only [hwork, hw0, hprefix, hg, hs]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hhalf : 2 * Real.exp (-(x + 1)) ≤ Real.exp (-x) := by
    calc
      _ ≤ Real.exp 1 * Real.exp (-(x + 1)) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have ht := Real.exp_le_exp.mpr (neg_le_neg hfloor)
  linarith only [ht, hhalf]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativePositiveNativeRuleCanonical
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

noncomputable def preparedRelativeEndpointCapExponent (s : ℕ) : ℕ :=
  2 + (∑ m : Fin (s + 1), preparedConcreteSlicedForecastPrimitiveCapExponent
    m.val 1 1 (preparedCommonRadiusPrimitiveExponent s)) +
      preparedCommonRadiusDensityCapNestedExponent s

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeDetectionEmptyTags
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

@[simp] theorem physicalGridFactorInput_of_isEmpty
    {X : Type*} {m : ℕ} {J : Fin m → Type*} [IsEmpty (Σ j, J j)]
    (period : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    physicalGridFactorInput period p t = 0 := by
  funext a
  exact isEmptyElim a

namespace NormalizedPolynomialTwist

variable {X Y : Type*} [Fintype X] [Fintype Y]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

variable [IsEmpty Y]

@[simp] theorem eval_eraseEmptyTags
    {m m' : ℕ} {J : Fin m → Type*} {J' : Fin m' → Type*}
    [∀ j, Fintype (J j)] [∀ j, Fintype (J' j)] [IsEmpty (Σ j, J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (p' : ∀ j, VectorPolynomial X ℝ (J' j → ℝ)) (u : X → ℤ) :
    (W.eraseEmptyTags (Σ j, J' j)).eval N p' u = W.eval N p u := by
  simp only [eval, eraseEmptyTags, physicalGridFactorInput_of_isEmpty]
  rfl

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end


