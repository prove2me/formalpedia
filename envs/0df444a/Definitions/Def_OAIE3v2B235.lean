-- Prove2me | Definitions.Def_OAIE3v2B235
-- name    : OAIE3v2B235
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:52:28.144717+00:00
-- url     : https://prove2.me/theorems/8de72cc2-6666-468f-b0d9-01225ee51aeb
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 240 of 311
-- statement:
--   Definitions bundle 240 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B199`, `OAIE3v2B206`, `OAIE3v2B210`, `OAIE3v2B211`, `OAIE3v2B212`, `OAIE3v2B213`, `OAIE3v2B216`, `OAIE3v2B217` of this split.
--
--   Modules: `Estimates/AllocatedAnchoredRecoveredSource.lean`, `Estimates/AllocatedCenteredJointProductivity.lean`, `Estimates/AllocatedCenteredNarrowAmplitudeNormalization.lean`, `Estimates/AllocatedFixedScaleJointMarginal.lean`, `Estimates/AllocatedNarrowJointCollision.lean`, `Estimates/AllocatedOriginalSampleCongruenceOutput.lean`, `Estimates/AllocatedProfileDimensions.lean`, `Geometry/SelectedJointSpatialCutoff.lean`, `Lattices/AllocatedAffineFixedPathRationalReference.lean`, `Lattices/AllocatedAffineScaleEnvelope.lean`, `Lattices/AllocatedCenteredBadPrimeSurrogate.lean`, `Lattices/AllocatedModularRankAffineFullWitness.lean`, `Lattices/AllocatedModularRankAffineProbability.lean`, `Lattices/SelectedResidueCutoffDomination.lean`, `Linear/AllocatedCenteredMeasurableFramedBadTail.lean`, `Linear/AllocatedCenteredSpatialMatrixExceptional.lean`, `Linear/AllocatedModularRankActualRead.lean`, `Linear/AllocatedModularRankActualRefreshBad.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/AllocatedShortRankWitnessWidth.lean`, `Polynomial/AllocatedCenteredConditionalPolynomial.lean`, `Probability/PreparedModularGeneralCenteredLaw.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B206
import Definitions.Def_OAIE3v2B210
import Definitions.Def_OAIE3v2B211
import Definitions.Def_OAIE3v2B212
import Definitions.Def_OAIE3v2B213
import Definitions.Def_OAIE3v2B216
import Definitions.Def_OAIE3v2B217

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)] {D : ℝ}

variable (h : AllocatedComparisonDimensions (G := G) B α O D) {p e : ℝ} (hp : 0 ≤ p)

include h hp

theorem allocatedKernelLog_le_envelope :
    allocatedKernelLog G α O p ≤ allocatedKernelEnvelope m D p := by
  have hi (j : Fin m) := kernelInverseLog_le_envelope h.nonneg hp h.cube h.kernel_variables
    (h.rows j) (h.layer_degree B j)
  have hs : (∑ j : Fin m, kernelInverseLog (Fintype.card α) (Fintype.card G)
      (Fintype.card (O j)) (j.val+1) p) ≤ (m : ℝ)*kernelInverseEnvelope D p := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hi j)
  unfold allocatedKernelLog allocatedKernelEnvelope
  gcongr
  exact h.cube

theorem allocatedCoefficientFrontLog_le_envelope (j : Fin m) :
    coefficientFrontLog (Fintype.card (O j))
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
      (allocatedKernelLog G α O p) (4*(p+8)) e ≤ allocatedFrontEnvelope m D p e := by
  have hD := h.nonneg
  have hk := allocatedKernelLog_le_envelope B h hp
  have hk0 := (allocatedKernelLog_bounds G α O hp).1
  have hn := h.coefficients j
  have hj := h.rows j
  have hf := h.profile
  have ht : 0 ≤ 4*(p+8) := by positivity
  have hc : affineCoefficientCommonBudget
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
      (allocatedKernelLog G α O p) (4*(p+8)) ≤
      allocatedKernelEnvelope m D p+D+(D+D+(D+1)*(4*(p+8))) := by
    unfold affineCoefficientCommonBudget affineProfileLogBound
    gcongr
  have hc0 := affineCoefficientCommonBudget_nonneg
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))) hk0 ht
  dsimp only [coefficientFrontLog, allocatedFrontEnvelope, coefficientLogAllowance]
  gcongr

theorem allocatedKernelReplacementLog_le_envelope :
    allocatedKernelReplacementLog (G := G) B α O p e ≤ (m : ℝ)*allocatedFrontEnvelope m D p e := by
  unfold allocatedKernelReplacementLog
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
      allocatedCoefficientFrontLog_le_envelope B h hp j (e := e))

end Erdos3.VectorPolynomial

end

end OAI
end

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

theorem selectedJointFiniteLaw_realTest_measurable
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (f : B → (K × I → ℤ) → ℝ) :
    Measurable (fun c =>
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mean
        (fun z => f z.1.val z.2.val)) :=
  Finset.measurable_sum _ (fun z _ =>
    (selectedJointFiniteLaw_weight_measurable A hA modulus T W hW hZ D hDm hD0 hD z).mul_const _)

theorem selectedJointFiniteLaw_realTest_integrable
    (μ : Measure C) [IsFiniteMeasure μ]
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (f : B → (K × I → ℤ) → ℝ) (hf : ∀ a z, |f a z| ≤ 1) :
    Integrable (fun c =>
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mean
        (fun z => f z.1.val z.2.val)) μ := by
  apply Integrable.of_bound
    (selectedJointFiniteLaw_realTest_measurable A hA modulus T W hW hZ D hDm hD0 hD f).aestronglyMeasurable 1
  apply ae_of_all
  intro c
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ((selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mean_mem_Icc
    (fun z => f z.1.val z.2.val) (fun z => abs_le.mp (hf z.1.val z.2.val)))

end Joint

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

variable (N : X → ℕ) (hN : ∀ i, 0 < N i)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

omit [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
theorem allocatedOriginalPathLaw_subtractConstant_eq_centered
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (htotal : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedJointBaseDensity B U b hb o hR hσ S X
        (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))))
    (hcenter : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)) :
    allocatedOriginalPathLaw B U b hb o hR hσ S X
      (fun j => subtractConstant (c j).val (poly j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))
      N hN hW hτ hξ stride cells hmass bases hbases htotal =
    selectedJointFiniteLaw bases hbases stride cells widths
      (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) hcenter := by
  unfold allocatedOriginalPathLaw
  simp only [allocatedJointBaseDensity_subtractConstant_centered B U b hb o hR hσ S poly hmem center c hc]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFixedScaleJointMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_fixed_scale_centered_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∃ (_hwidths : ∀ z, 0 < widths z) (_hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
      ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
        let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm center
        (∀ base, |selectedResidueDensityMass stride T widths (density base) - 1| ≤
          3 * positiveProjectionAccuracy P) ∧
        ∀ (bases : Finset (X → ℤ)), bases.Nonempty →
          let Z := selectedJointDensityMass bases stride T widths density
          |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2 := by
  classical
  obtain ⟨A, hA, hnorm⟩ := exists_allocated_narrow_normalization m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths
  obtain ⟨hwidths, hZ, _⟩ := hnorm B U basis S hb o μ ν hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP
    p hp hm stride hs hsP hW hWP hτ hτP hξ hξ1 hξP N hsize hrank hRank T hT
  refine ⟨hwidths, hZ, ?_⟩
  intro center
  obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
  let pc := fun j => subtractConstant (c j).val (p j)
  let hmc := fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)
  have hpc (j : Fin m) : DegreeLE (1 : X → ℕ) (j.val + 1) (pc j) :=
    (hp j).subtractConstant (c j).val
  have hrankc (j : Fin m) :
      HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pc j) :=
    (hasLayerSamplingRank_subtractConstant_iff (Nat.zero_lt_succ _) _ _ (U j)
      (c j).val (p j)).mpr (hrank j)
  obtain ⟨_, _, hlocal, hjoint⟩ := hnorm B U basis S hb o μ ν hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP
    pc hpc hmc stride hs hsP hW hWP hτ hτP hξ hξ1 hξP N hsize hrankc hRank T hT
  change (∀ base, |selectedResidueDensityMass stride T widths
      (allocatedJointBaseDensity B U basis hb o hR hσ S X pc hmc base) - 1| ≤
        3 * positiveProjectionAccuracy P) at hlocal
  change ∀ bases : Finset (X → ℤ), bases.Nonempty →
    let Z := selectedJointDensityMass bases stride T widths
      (allocatedJointBaseDensity B U basis hb o hR hσ S X pc hmc)
    |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2 at hjoint
  have hdensity := allocatedJointBaseDensity_subtractConstant_centered
    B U basis hb o hR hσ S p hm center c hc
  change allocatedJointBaseDensity B U basis hb o hR hσ S X pc hmc =
    allocatedCenteredJointDensity B U basis hb o hR hσ S p hm center at hdensity
  rw [hdensity] at hlocal hjoint
  exact ⟨hlocal, hjoint⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_fixedScale_joint_marginal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ AllocatedFixedScaleJointMarginalStatement m A := by
  obtain ⟨A₁, _, hone⟩ := exists_allocated_fixedScale_centered_oneSite_comparison m
  obtain ⟨A₂, _, hnorm⟩ := exists_allocated_fixed_scale_centered_normalization m
  let A := max (max A₁ A₂) 256
  have hA : 256 ≤ A := le_max_right _ _
  have hA₁A : A₁ ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have hA₂A : A₂ ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨A, by omega, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density
  have hthreshold (a : ℕ) (ha : a ≤ A) :
      Real.exp ((P + a) ^ a) ≤ Real.exp ((P + A) ^ A) := by
    have hAr : (256 : ℝ) ≤ A := by exact_mod_cast hA
    have har : (a : ℝ) ≤ A := by exact_mod_cast ha
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by positivity) (by linarith only [har] : P + (a : ℝ) ≤ P + A) a).trans
      (pow_le_pow_right₀ (by linarith only [hP, hAr] : (1 : ℝ) ≤ P + A) ha)
  obtain ⟨hwidths, hmass, hone⟩ := hone B U basis S hb o μ ν
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
    hW hWP hτ hτP hξ hξ1 hξP N
    (fun x => (hthreshold A₁ hA₁A).trans (hsize x)) hrank
    ((hthreshold A₁ hA₁A).trans hRank) T hT
  obtain ⟨_, _, hnorm⟩ := hnorm B U basis S hb o μ ν
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
    hW hWP hτ hτP hξ hξ1 hξP N
    (fun x => (hthreshold A₂ hA₂A).trans (hsize x)) hrank
    ((hthreshold A₂ hA₂A).trans hRank) T hT
  have hN (x) : 0 < N x := by exact_mod_cast (Real.exp_pos _).trans_le (hsize x)
  have hmarginSize (x) : 4 ≤ τ * (N x : ℝ) :=
    spatialTrimMargin_size_of_exp_size hP hτ hτP
      ((spatial_threshold_large hP hA).trans (hsize x))
  have hproper := spatialTrimMargin_proper hτhalf N hN hmarginSize
  have hbases : bases.Nonempty := trimmedIntegerBox_nonempty N _ hproper
  have hD (center) : 0 < selectedJointDensityMass bases stride T widths (density center) :=
    ((hnorm center).2 bases hbases).2.2.1
  have hlocal (center) (a) : 0 < selectedResidueDensityMass stride T widths (density center a) :=
    (positiveProjectionAccuracy_normalizer hP ((hnorm center).1 a)).2.2.1
  refine ⟨hN, hwidths, hproper, hmass, hD, ?_, ?_⟩
  · intro center
    have h := (hnorm center).2 bases hbases
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  · intro root hroot hrootSum φ hφ
    have hfit := narrowTrimmedSpatial_site_width hW hτ hξ1 root hrootSum N hN
    have hmeas (a) (z) : Measurable (fun center => density center a z) :=
      allocatedCenteredJointDensity_measurable_center B U basis hb o hR hσ S p hm a z
    have hnonneg (center) (a) (z) : 0 ≤ density center a z :=
      allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center a z
    have hmix (a : X → ℤ) (ψ : (X → ℝ) → ℂ) (hψ : ∀ v, ‖ψ v‖ ≤ 1) :
        ‖(∫ center, ∑' z, ((selectedResidueDensityPMF stride T widths hwidths hmass (density center a)
            (hnonneg center a) (hlocal center a) z).toReal : ℂ) * ψ (physicalAffineSite root z) ∂μ) -
          ∑' z, ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
            ψ (physicalAffineSite root z)‖ ≤ 6 * positiveProjectionAccuracy P := by
      exact allocatedFixedScale_center_mixture_compare B U basis hb o hR hσ S μ ν hσ1
        C V hC hV Cinv hCinv hchart hsmall p hm stride T widths hwidths hmass a root
        (fun center => hlocal center a) (fun center => (hnorm center).1 a)
        (fun center φ hφ => hone a root hroot center φ hφ) ψ hψ
    have h := fixedScaleJointMarginalTransfer μ root N (spatialTrimMargin τ N) hproper
      stride T widths hwidths hmass hfit density hmeas hnonneg hD hlocal
      (fun center a => (hnorm center).1 a) hmix φ hφ
    refine ⟨h.1, h.2.trans ?_⟩
    have hboundary := spatialTrimMargin_error_bound N hN hmarginSize
    nlinarith only [hboundary]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {E : Fin m → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)] [Fintype A]
    {N : ℕ}

theorem modularDeckPolynomial_kernel_resample_long_top
    (inactive : LayerSamplerAxis I n → Prop)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (j : Fin m) (i : E j) (e : A × Fin (j.val + 1) ↪ G) (c : A → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) :
    homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularDeckPolynomial (resampleCoefficientDeckCoordinate r j i
          (kernelRankCoefficientSlot (layerSamplerDegree I n) e) c) j i)) =
      killCompl (allocatedLongEmbedding inactive).injective
        (homogeneousComponent (j.val + 1)
          (modularUnselectedCoefficientPolynomial (j.val + 1)
            (kernelRankCoefficientSlot (layerSamplerDegree I n) e) (fun q => r j q i))) +
      ∑ a, c a • ∏ k ∈ kernelRankBlock
        (B := fun d : {d : LayerSamplerAxis I n // ¬ inactive d} => B d.val)
        (fun d => layerSamplerDegree I n d.val) e a, X k := by
  rw [homogeneousComponent_conditionPolynomial_top _ _ _ v _
    (modularDeckPolynomial_degree _ j i)]
  rw [modularDeckPolynomial_resample_top r j i _
    (kernelRankCoefficientSlot_injective _ e (Nat.zero_lt_succ _))
    (kernelRankCoefficientSlot_degree _ e), map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change killCompl (samplerLongEmbedding inactive (layerSamplerDegree I n)).injective
    (MvPolynomial.monomial (kernelRankCoefficientSlot (layerSamplerDegree I n) e a).val (c a)) = _
  rw [← samplerLongEmbedding_kernelExponent inactive (layerSamplerDegree I n) e a,
    killCompl_monomial_mapDomain, kernelRankCoefficientSlot_monomial]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

noncomputable def allocatedActualCoefficientSlot
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedSelectedCoefficientIndex X E inactive L → AllocatedActualCoefficientIndex G X I E n B
  | ⟨_j, .inl x, l⟩ => .inl (some (.inl (spatial l)), x.val)
  | ⟨j, .inr (.inl i), l⟩ => .inr (.inl ⟨j,
      kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j) l, i⟩)
  | ⟨j, .inr (.inr a), l⟩ => .inr (.inr ⟨⟨j, a.val⟩,
      principalCoefficientSlot (layerSamplerDegree I n) ⟨j, a.val⟩ (block j a l)⟩)

theorem allocatedActualCoefficientSlot_injective
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩) :
    Function.Injective (allocatedActualCoefficientSlot (X := X) (E := E) inactive spatial kernel block) := by
  rintro ⟨j, o, l⟩ ⟨k, p, q⟩ he
  cases o with
  | inl x =>
    cases p with
    | inl y =>
      have hjk : j = k := Fin.ext (x.property.trans y.property.symm)
      subst k
      change Sum.inl (some (Sum.inl (spatial l)), x.val) =
        Sum.inl (some (Sum.inl (spatial q)), y.val) at he
      have hp := Sum.inl.inj he
      have hl : l = q := spatial.injective
        (Sum.inl.inj (Option.some.inj (congrArg Prod.fst hp)))
      have hxy : x = y := Subtype.ext (congrArg Prod.snd hp)
      subst q
      subst y
      rfl
    | inr p => cases p <;> cases he
  | inr o =>
    cases p with
    | inl y => cases o <;> cases he
    | inr p =>
      cases o with
      | inl i =>
        cases p with
        | inl t =>
          have hh := Sum.inl.inj (Sum.inr.inj he)
          have hjk : j = k := congrArg Sigma.fst hh
          subst k
          have hp : (kernelRankCoefficientSlot (B := B) (layerSamplerDegree I n) (kernel j) l, i) =
              (kernelRankCoefficientSlot (B := B) (layerSamplerDegree I n) (kernel j) q, t) := by
            simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hh
          have hl : l = q := kernelRankCoefficientSlot_injective
            (layerSamplerDegree I n) (kernel j) (Nat.zero_lt_succ _) (congrArg Prod.fst hp)
          have hit : i = t := congrArg Prod.snd hp
          subst q
          subst t
          rfl
        | inr a => cases he
      | inr a =>
        cases p with
        | inl t => cases he
        | inr b =>
          have hh := Sum.inr.inj (Sum.inr.inj he)
          have haxis : (⟨j, a.val⟩ : LayerSamplerAxis I n) = ⟨k, b.val⟩ := congrArg Sigma.fst hh
          have hjk : j = k := congrArg Sigma.fst haxis
          subst k
          have hab : a = b := Subtype.ext (by
            simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using haxis)
          subst b
          have hslot : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, a.val⟩
              (block j a l) = principalCoefficientSlot (layerSamplerDegree I n) ⟨j, a.val⟩
              (block j a q) := by
            exact eq_of_heq (Sigma.mk.inj hh).2
          have hblocks := principalCoefficientSlot_injective (G := G)
            (layerSamplerDegree I n) ⟨j, a.val⟩ (Nat.zero_lt_succ _) hslot
          have hl : l = q := (block j a).injective hblocks
          subst q
          rfl

noncomputable def allocatedActualCoefficientEmbedding
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedSelectedCoefficientIndex X E inactive L ↪ AllocatedActualCoefficientIndex G X I E n B :=
  ⟨allocatedActualCoefficientSlot inactive spatial kernel block,
    allocatedActualCoefficientSlot_injective inactive spatial kernel block⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

def allocatedCongruenceCoefficientSplit (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    AllocatedCongruenceCoefficientIndex X E inactive L ≃
      AllocatedSmoothRankCoefficientIndex X inactive L ⊕ AllocatedDeckRankCoefficientIndex E L where
  toFun k := match k with
    | ⟨j,.inl x,l⟩ => .inl ⟨j,.inl x,l⟩
    | ⟨j,.inr (.inl e),l⟩ => .inr ⟨j,e,l⟩
    | ⟨j,.inr (.inr i),l⟩ => .inl ⟨j,.inr i,l⟩
  invFun k := match k with
    | .inl ⟨j,.inl x,l⟩ => ⟨j,.inl x,l⟩
    | .inr ⟨j,e,l⟩ => ⟨j,.inr (.inl e),l⟩
    | .inl ⟨j,.inr i,l⟩ => ⟨j,.inr (.inr i),l⟩
  left_inv := by rintro ⟨j,(x | e | i),l⟩ <;> rfl
  right_inv := by rintro (⟨j,(x | i),l⟩ | ⟨j,e,l⟩) <;> rfl

def allocatedCongruenceCoefficientEmbedding (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    AllocatedCongruenceCoefficientIndex X E inactive L ↪
      AllocatedSelectedCoefficientIndex X E inactive L :=
  Function.Embedding.sigmaMap (Function.Embedding.refl _)
    (fun j => Function.Embedding.prodMap (allocatedCongruenceOutputEmbedding inactive j)
      (Function.Embedding.refl _))

noncomputable def allocatedCongruenceActualCoefficientEmbedding
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedCongruenceCoefficientIndex X E inactive L ↪ AllocatedActualCoefficientIndex G X I E n B :=
  (allocatedCongruenceCoefficientEmbedding inactive L).trans
    (allocatedActualCoefficientEmbedding inactive spatial kernel block)

noncomputable def allocatedMixedSelectedValues (inactive : LayerSamplerAxis I n → Prop)
    {L N : ℕ} (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    AllocatedCongruenceCoefficientIndex X E inactive L → ℤ :=
  Sum.elim x (fun j => (deck j).val) ∘ allocatedCongruenceCoefficientSplit inactive L

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

noncomputable def allocatedRankComponentSelectedSlot
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (j : Fin m) : (o : AllocatedCongruenceRankOutput X E inactive j) →
      Fin L → AllocatedRankComponentCoefficient (G := G) (B := B) inactive j o
  | .inl _ => spatialKernelRankSlot spatial
  | .inr (.inl _) => kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j)
  | .inr (.inr i) => canonicalPrincipalSubblockSlot (layerSamplerDegree I n)
      ⟨j, .inr i.val⟩ (block j (allocatedCongruenceIntegerEmbedding inactive j i))

theorem allocatedRankComponentSelectedSlot_injective
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j) :
    Function.Injective (allocatedRankComponentSelectedSlot inactive spatial kernel block j o) := by
  rcases o with x | i | a
  · exact spatialKernelRankSlot_injective spatial
  · exact kernelRankCoefficientSlot_injective (layerSamplerDegree I n) (kernel j)
      (Nat.zero_lt_succ _)
  · exact canonicalPrincipalSubblockSlot_injective (layerSamplerDegree I n)
      ⟨j, .inr a.val⟩ (Nat.zero_lt_succ _)
      (block j (allocatedCongruenceIntegerEmbedding inactive j a))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

def allocatedMixedCoefficientEquiv (inactive : LayerSamplerAxis I n → Prop) (L : ℕ)
    (R : Type*) [AddCommGroup R] :
    ((AllocatedSmoothRankCoefficientIndex X inactive L ⊕ AllocatedDeckRankCoefficientIndex E L) → R) ≃+
      (AllocatedCongruenceCoefficientIndex X E inactive L → R) where
  toFun f := f ∘ allocatedCongruenceCoefficientSplit inactive L
  invFun f := f ∘ (allocatedCongruenceCoefficientSplit inactive L).symm
  left_inv f := by funext j; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  right_inv f := by funext j; simp only [Function.comp_apply, Equiv.symm_apply_apply]
  map_add' _ _ := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankActualRead
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial
variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

theorem allocatedTaggedRankPolynomial_original
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    allocatedTaggedRankPolynomial inactive j noise r projection spatial kernel block
      (allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block) v o =
        allocatedOriginalTaggedTop inactive j noise r projection v o := by
  rcases o with x | i | a
  · have hs : allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block
        (.inl x) = fun l => noise (spatialKernelRankSlot spatial l,x.val) := by
      funext l
      rfl
    simp only [allocatedTaggedRankPolynomial, allocatedOriginalTaggedTop, hs]
    rw [extend_selected_original _ (spatialKernelRankSlot_injective spatial) (fun d => noise (d,x.val))]
  · have hs : allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block
        (.inr (.inl i)) = fun l => r j (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel l) i := by
      funext l
      rfl
    simp only [allocatedTaggedRankPolynomial, allocatedDegreeRankPolynomial,
      allocatedOriginalTaggedTop, modularDeckPolynomial, resampleCoefficientDeckCoordinate_apply, hs]
    rw [extend_selected_original _ (kernelRankCoefficientSlot_injective
      (layerSamplerDegree I n) kernel (Nat.zero_lt_succ _)) (fun q => r j q i)]
  · have hs : allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block
        (.inr (.inr a)) = fun l => projection a
          (canonicalPrincipalSubblockSlot (layerSamplerDegree I n) ⟨j,a.val⟩ (block a) l) := by
      funext l
      rfl
    simp only [allocatedTaggedRankPolynomial, allocatedDegreeRankPolynomial,
      allocatedOriginalTaggedTop, hs]
    exact congrArg
      (fun coefficients : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N =>
        homogeneousComponent (j.val + 1)
          (conditionPolynomial (allocatedLongEmbedding inactive)
            (allocatedLongEmbedding inactive).injective v
            (modularBoundedCoefficientPolynomial (j.val + 1) coefficients)))
      (extend_selected_original _ (canonicalPrincipalSubblockSlot_injective
        (G := G) (layerSamplerDegree I n) ⟨j,a.val⟩ (Nat.zero_lt_succ _) (block a)) (projection a))

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineProbability
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ} {R : Type*}

def allocatedSelectedSmoothAffine [Semiring R]
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (stride : X → R) (residue : Option (LayerSamplerVariables G I n B) × X → R)
    (z : AllocatedSmoothRankCoefficientIndex X inactive L → R) :
    AllocatedSmoothRankCoefficientIndex X inactive L → R
  | ⟨j,.inl x,l⟩ => residue (some (.inl (spatial l)),x.val) + stride x.val * z ⟨j,.inl x,l⟩
  | ⟨j,.inr i,l⟩ => z ⟨j,.inr i,l⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankActualRefreshBad
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

def allocatedCongruenceCoefficientReindex
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    ((Σ j : Fin m, AllocatedCongruenceRankOutput X E inactive j) × Fin L) ≃
      AllocatedCongruenceCoefficientIndex X E inactive L where
  toFun k := ⟨k.1.1, k.1.2, k.2⟩
  invFun k := (⟨k.1,k.2.1⟩,k.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

omit [Fintype X] [∀ j, Fintype (E j)] in

theorem allocatedOriginalCongruenceTop_congr_outputs
    (inactive : LayerSamplerAxis I n → Prop) (M : ℕ)
    (f g : AllocatedActualCoefficientIndex G X I E n B → ZMod M)
    (hnoise : allocatedReadNoise f = allocatedReadNoise g)
    (hdeck : allocatedReadDeck f = allocatedReadDeck g)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ = allocatedReadProjection g ⟨j,Sum.inr i⟩)
    (j : Fin m) (v : LayerSamplerVariables G I n B → ZMod M)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    allocatedOriginalTaggedTop inactive j (allocatedReadNoise f) (allocatedReadDeck f)
      (fun a => allocatedReadProjection f ⟨j,a.val⟩) v
      (allocatedCongruenceOutputEmbedding inactive j o) =
    allocatedOriginalTaggedTop inactive j (allocatedReadNoise g) (allocatedReadDeck g)
      (fun a => allocatedReadProjection g ⟨j,a.val⟩) v
      (allocatedCongruenceOutputEmbedding inactive j o) := by
  rcases o with x | i | a
  · simp only [allocatedCongruenceOutputEmbedding_spatial, allocatedOriginalTaggedTop, hnoise]
  · simp only [allocatedCongruenceOutputEmbedding_deck, allocatedOriginalTaggedTop, hdeck]
  · simp only [allocatedCongruenceOutputEmbedding_integer, allocatedOriginalTaggedTop, hinteger]

theorem allocatedResidueModulusBad_congr_outputs
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ) (M : ℕ) [NeZero M]
    (f g : AllocatedActualCoefficientIndex G X I E n B → ZMod M)
    (hnoise : allocatedReadNoise f = allocatedReadNoise g)
    (hdeck : allocatedReadDeck f = allocatedReadDeck g)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ = allocatedReadProjection g ⟨j,Sum.inr i⟩) :
    allocatedResidueModulusBad inactive C M f = allocatedResidueModulusBad inactive C M g := by
  unfold allocatedResidueModulusBad
  simp only [allocatedOriginalCongruenceTop_congr_outputs inactive M f g hnoise hdeck hinteger]

theorem allocatedResiduePrimePowerWitness_congr_outputs
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (f g : AllocatedActualCoefficientIndex G X I E n B → ZMod M)
    (hnoise : allocatedReadNoise f = allocatedReadNoise g)
    (hdeck : allocatedReadDeck f = allocatedReadDeck g)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ = allocatedReadProjection g ⟨j,Sum.inr i⟩) :
    allocatedResiduePrimePowerWitness inactive C P A M hdiv f =
      allocatedResiduePrimePowerWitness inactive C P A M hdiv g := by
  unfold allocatedResiduePrimePowerWitness
  apply propext
  apply forall_congr'
  intro p
  apply Eq.to_iff
  apply allocatedResidueModulusBad_congr_outputs
  · funext q
    exact congrArg (ZMod.castHom (hdiv p) (ZMod (p.val ^ A p.val))) (congrFun hnoise q)
  · funext j q i
    exact congrArg (ZMod.castHom (hdiv p) (ZMod (p.val ^ A p.val)))
      (congrFun (congrFun (congrFun hdeck j) q) i)
  · intro j i
    funext q
    exact congrArg (ZMod.castHom (hdiv p) (ZMod (p.val ^ A p.val))) (congrFun (hinteger j i) q)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

theorem allocatedChartResiduePrimePowerWitness_read
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (f : AllocatedActualCoefficientIndex G X I E n B → ZMod M) :
    allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (allocatedReadNoise f) (allocatedReadCoefficientChartResidues f) =
      allocatedResiduePrimePowerWitness inactive C P A M hdiv f := by
  unfold allocatedChartResiduePrimePowerWitness
  apply allocatedResiduePrimePowerWitness_congr_outputs
  · rfl
  · rfl
  · intro j i
    rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedCenteredConditionalPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {X : Type*} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable (c : ∀ j, U j) (a : X → ℤ)

variable {G : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ x, Fintype (B x)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

omit [Fintype X] in
theorem allocatedCenteredConditionalPolynomial_density
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedCoefficientDensity B U b hb o hR hσ S
      (affineSampleCoefficientTorus U (allocatedCenteredConditionalPolynomial U poly c a)
        (allocatedCenteredConditionalPolynomial_mem U poly hmem c a)
        (fun k x => (z (k,x) : ℝ))) =
      allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z := by
  exact congrFun (congrFun
    (allocatedJointBaseDensity_subtractConstant_centered B U b hb o hR hσ S poly hmem center c hc) a) z

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedAnchoredRecoveredSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
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

theorem exists_allocatedPhysical_recovered_sample_read :
    ∃ (sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
      (read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ),
      ∀ z, allocatedReadNoise (read z) = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        (canonicalCoefficientSample U b hb o (sample z) =
          affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ∧
        (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
          mixedArraySupported (allocatedLayerCenters B U b S j)
            (allocatedLayerWidths B U b S j)
            (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample z j)) ∧
        (∀ (j : Fin m) (i : Fin (n j))
          (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
          allocatedReadProjection (read z) ⟨j, Sum.inr i⟩ e = (sample z j).2 i e) ∧
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q)))) := by
  have hex (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
      ∃ (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
        (f : AllocatedActualCoefficientIndex G X I E n B → ℤ),
        allocatedReadNoise f = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        (canonicalCoefficientSample U b hb o x =
          affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ∧
        (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (x j) ∧
          mixedArraySupported (allocatedLayerCenters B U b S j)
            (allocatedLayerWidths B U b S j)
            (allocatedLayerIntegerPMFs B U b hR hσ S j) (x j)) ∧
        (∀ (j : Fin m) (i : Fin (n j))
          (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
          allocatedReadProjection f ⟨j, Sum.inr i⟩ e = (x j).2 i e) ∧
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q)))) := by
    by_cases hz : allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) = 0
    · refine ⟨fun _ => (0, 0),
        allocatedMixedFullArray (Sum.elim z (fun _ => 0)) (fun _ => 0) (fun _ => 0), rfl, ?_⟩
      intro h
      exact (h hz).elim
    · obtain ⟨x, hx, _⟩ := canonicalCoefficientDensity_recover_unique U b hb o
        (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerPMFs B U b hR hσ S) hz
      have hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2 := by
        intro a
        exact (hx.2 a.1.1).1 a.1.2 a.2
      obtain ⟨f, hfnoise, hfint, hfevent⟩ := exists_allocatedCoefficient_integer_event_read
        U bW b hb o (affineSampleCoefficientArray U poly hm (fun k x => (z (k,x) : ℝ)))
        x hx.1 hsmall z
      exact ⟨x, f, hfnoise, fun _ => ⟨hx.1, hx.2, hfint, hfevent⟩⟩
  choose sample read hread using hex
  exact ⟨sample, read, hread⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredJointProductivity
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

attribute [local irreducible] selectedJointFiniteLaw selectedJointReference selectedResidueFiniteLaw

theorem selectedJointFiniteLaw_integral_productivity
    {C B K I R Y : Type*} [MeasurableSpace C] [Fintype K] [Fintype I] [Fintype R]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (μ : Measure C) [IsProbabilityMeasure μ]
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (sites : FiniteProbabilityWeights R)
    (image : B → (K × I → ℤ) → R → Y) (test : Y → ℝ)
    {σ η parent : ℝ} (hσ : 0 < σ) (hη : η ≤ σ / 8) (hparent : σ ≤ parent)
    (htest : ∀ y, test y ≤ 1)
    (hmarginal : ∀ r,
      let F := fun c => (selectedJointFiniteLaw A hA modulus T W hW hZ (D c)
        (hD0 c) (hD c)).complexMean (fun z => (test (image z.1.val z.2.val r) : ℂ))
      Integrable F μ ∧ ‖(∫ c, F c ∂μ) - (parent : ℂ)‖ ≤ η)
    (hcollision : ∀ c,
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mean
        (fun z => noninjectivityIndicator (image z.1.val z.2.val)) ≤ σ / 16) :
    σ / 4 ≤ ∫ c,
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mass
        (Finset.univ.filter (fun z => Function.Injective (image z.1.val z.2.val) ∧
          σ / 2 ≤ sites.mean (fun r => test (image z.1.val z.2.val r)))) ∂μ := by
  let law := fun c => selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)
  let sampledImage := fun (z : A × rectangularWeightIndices 0 W 1) r => image z.1.val z.2.val r
  have hi (f : B → (K × I → ℤ) → ℝ) (hf : ∀ a z, |f a z| ≤ 1) :
      Integrable (fun c => (law c).mean (fun z => f z.1.val z.2.val)) μ :=
    selectedJointFiniteLaw_realTest_integrable A hA modulus T W hW hZ μ D hDm hD0 hD f hf
  have hiBad : Integrable (fun c => (law c).mean
      (fun z => noninjectivityIndicator (sampledImage z))) μ := by
    apply hi (fun a z => noninjectivityIndicator (image a z))
    intro a z
    simp only [noninjectivityIndicator]
    split_ifs <;> norm_num
  have hiProd : Integrable (fun c => (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (sampledImage z) ∧ σ / 2 ≤
        sites.mean (fun r => test (sampledImage z r))))) μ := by
    simp only [← FiniteProbabilityWeights.mean_indicator, Finset.mem_filter,
      Finset.mem_univ, true_and]
    apply hi (fun a z => if Function.Injective (image a z) ∧
      σ / 2 ≤ sites.mean (fun r => test (image a z r)) then 1 else 0)
    intro a z
    split_ifs <;> norm_num
  have hbadmean : (∫ c, (law c).mean
      (fun z => noninjectivityIndicator (sampledImage z)) ∂μ) ≤ σ / 16 := by
    have h := integral_mono hiBad (integrable_const (σ / 16)) hcollision
    simpa only [integral_const, probReal_univ, one_smul] using h
  exact integral_productive_injective_mass_of_complex_marginals μ law sites sampledImage test
    hσ hη hparent htest (fun r => (hmarginal r).1) (fun r => (hmarginal r).2)
    hiBad hiProd hbadmean

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X Sites : Type*} [Fintype G] [Fintype X] [Fintype Sites] [Nonempty Sites]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]

theorem allocatedCenteredJoint_productivity
    (bases : Finset (X → ℤ)) (hbases : bases.Nonempty) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (widths : Option (LayerSamplerVariables G I n B) × X → ℝ)
    (hwidths : ∀ z, 0 < widths z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells widths
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center))
    (site : Sites → LayerSamplerVariables G I n B → ℤ)
    (test : (X → ℤ) → ℝ) {gain error parent : ℝ}
    (hgain : 0 < gain) (herror : error ≤ gain / 8) (hparent : gain ≤ parent)
    (htest : ∀ y, test y ≤ 1) :
    let density := allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem
    let law := fun center => selectedJointFiniteLaw bases hbases stride cells widths hwidths hmass
      (density center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) (hD center)
    (∀ q, Integrable (fun center => (law center).complexMean
      (fun z => (test (jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) : ℂ))) μ ∧
      ‖(∫ center, (law center).complexMean
        (fun z => (test (jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) : ℂ)) ∂μ) -
          (parent : ℂ)‖ ≤ error) →
    (∀ center, (law center).mean
      (fun z => noninjectivityIndicator (fun q => jointIntegerPhysicalSite (site q)
        (z.1.val,z.2.val))) ≤ gain / 16) →
    let productive := Finset.univ.filter (fun z : bases × rectangularWeightIndices 0 widths 1 =>
      Function.Injective (fun q => jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) ∧
        gain / 2 ≤ 𝔼 q : Sites, test (jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)))
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 widths 1) | z.2 ∈ productive} ∧
      gain / 4 ≤ joint.real {z | z.2 ∈ productive} ∧
      (∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun s => c s.1))) ∧
        allocatedAffineDensity B U b hb o hR hσ S poly hmem c
          (fun k v => (jointIntegerFrame (z.2.1.val,z.2.2.val) k v : ℝ)) ≠ 0) := by
  intro density law hmarginal hcollision productive joint
  have hDm (a : X → ℤ) z : Measurable (fun center => density center a z) :=
    allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S poly hmem a z
  have hD0 := allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem
  have hp := selectedJointFiniteLaw_integral_productivity bases hbases stride cells widths
    hwidths hmass μ density hDm hD0 hD (FiniteProbabilityWeights.uniform Sites)
    (fun a z q => jointIntegerPhysicalSite (site q) (a,z)) test
    hgain herror hparent htest hmarginal hcollision
  have hp' : gain / 4 ≤ ∫ center, (law center).mass productive ∂μ := by
    simpa only [FiniteProbabilityWeights.uniform_mean] using hp
  have hweight z : Measurable (fun center => (law center).weight z) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells widths hwidths hmass
      density hDm hD0 hD z
  apply centeredFiniteProbabilityMeasure_productive_family μ law hweight productive _ _ hp'
  intro center z hz
  obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
  refine ⟨c, hc, ?_⟩
  have hd := (selectedJointFiniteLaw_support bases hbases stride cells widths hwidths hmass
    (density center) (hD0 center) (hD center) z hz).2
  change 0 < allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem
    center z.1.val z.2.val at hd
  rw [allocatedCenteredJointDensity_eq_affine B U b hb o hR hσ S poly hmem center c hc] at hd
  exact hd.ne'

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredNarrowAmplitudeNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_centered_narrow_amplitude_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    ∃ (hwidths : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
      (∀ (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) (base : X → ℤ) (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
        (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
          (Lip : ℝ) ≤ Real.exp P →
        ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
          ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (amplitude (fun t => (z t : ℝ) / widths t) * (density center base z : ℂ))) -
          ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
            ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
              amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
          3 * positiveProjectionAccuracy P) ∧
      ∀ center base, |selectedResidueDensityMass stride T widths (density center base) - 1| ≤
          3 * positiveProjectionAccuracy P ∧
        ∃ (hD0 : ∀ z, 0 ≤ density center base z)
          (hD : 0 < selectedResidueDensityMass stride T widths (density center base)),
          ∀ (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
            (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
              (Lip : ℝ) ≤ Real.exp P →
            ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
              ((selectedResidueDensityPMF stride T widths hwidths hZ
                (density center base) hD0 hD z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)) -
              ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
                ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
              6 * positiveProjectionAccuracy P := by
  obtain ⟨A, hA, hnormalization⟩ := exists_allocated_narrow_amplitude_normalization m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths density
  have hcenter (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    ∃ (hwidths : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
      (∀ (base : X → ℤ) (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
        (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
          (Lip : ℝ) ≤ Real.exp P →
        ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
          ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (amplitude (fun t => (z t : ℝ) / widths t) * (density center base z : ℂ))) -
          ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
            ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
              amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
          3 * positiveProjectionAccuracy P) ∧
      ∀ base, |selectedResidueDensityMass stride T widths (density center base) - 1| ≤
          3 * positiveProjectionAccuracy P ∧
        ∃ (hD0 : ∀ z, 0 ≤ density center base z)
          (hD : 0 < selectedResidueDensityMass stride T widths (density center base)),
          ∀ (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
            (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
              (Lip : ℝ) ≤ Real.exp P →
            ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
              ((selectedResidueDensityPMF stride T widths hwidths hZ
                (density center base) hD0 hD z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)) -
              ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
                ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
              6 * positiveProjectionAccuracy P := by
    obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
    have hp' (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (subtractConstant (c j).val (p j)) :=
      (hp j).subtractConstant _
    have hm' := fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)
    have hrank' (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j)
        (subtractConstant (c j).val (p j)) :=
      (hasLayerSamplingRank_subtractConstant_iff (by omega) _ _ _ _ _).mpr (hrank j)
    have h := hnormalization B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv
      hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP
      (fun j => subtractConstant (c j).val (p j)) hp' hm' stride hs hsP hW hWP hτ hτP hξ hξ1 hξP
      N hsize hrank' hRank T hT
    have heq := allocatedJointBaseDensity_subtractConstant_centered B U basis hb o hR hσ S p hm
      center c hc
    obtain ⟨hw, hZ, hraw, hnorm⟩ := h
    refine ⟨hw, hZ, ?_, ?_⟩
    · intro base amplitude hamp Lip hLip hLipP
      have hh := hraw base amplitude hamp hLip hLipP
      simpa only [density, ← heq, allocatedJointBaseDensity] using hh
    · intro base
      obtain ⟨hmass, _, _, _⟩ := hnorm base
      have hmass' : |selectedResidueDensityMass stride T widths (density center base) - 1| ≤
          3 * positiveProjectionAccuracy P := by
        dsimp only [density]
        rw [← heq]
        unfold allocatedJointBaseDensity
        exact hmass
      have hD0' : ∀ z, 0 ≤ density center base z := fun z =>
        allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center base z
      have hD' := (positiveProjectionAccuracy_normalizer hP hmass').2.2.1
      refine ⟨hmass', hD0', hD', ?_⟩
      intro amplitude hamp Lip hLip hLipP
      have hh := selectedResidueDensityPMF_error_of_bounded_test stride T widths hw hZ
        (density center base) hD0' hD'
        (fun z => amplitude (fun t => (z t : ℝ) / widths t)) (fun _ => hamp _)
        (ε := 3 * positiveProjectionAccuracy P)
        (by simpa only [density, ← heq, allocatedJointBaseDensity] using
          hraw base amplitude hamp hLip hLipP) hmass'
      exact hh.trans_eq (by ring)
  obtain ⟨hwidths, hZ, _, _⟩ := hcenter 0
  refine ⟨hwidths, hZ, ?_, ?_⟩
  · intro center base amplitude hamp Lip hLip hLipP
    obtain ⟨_, _, hraw, _⟩ := hcenter center
    exact hraw base amplitude hamp hLip hLipP
  · intro center base
    obtain ⟨_, _, _, hnorm⟩ := hcenter center
    exact hnorm base

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedNarrowJointCollision
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)

local notation "K" => LayerSamplerVariables G I n B

include hC hV hσ1 hCinv hchart hsmall in

theorem allocatedFixedScaleJoint_collision_small
    {X Tsite : Type*} [Fintype X] [DecidableEq X] [Fintype Tsite] [DecidableEq Tsite]
    (point : (X → ℤ) → (Option K × X → ℤ) → CoefficientTorus («K» := K) U)
    {P δ : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card K : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent K (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hSP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
    (site : Tsite → K → ℤ) (hsite : Function.Injective site) (i : X)
    (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (modulus : X → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (hmodP : (modulus i : ℝ) ≤ Real.exp P)
    (cells : Finset (ColumnResiduePattern (Option K) X modulus)) (hcells : cells.Nonempty)
    (W : Option K × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {ρ N : ℝ} (hρ : 0 < ρ) (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P))
    (hN : Real.exp (allocatedFixedScaleCollisionLog m P) ≤ N)
    (hwidth : ∀ k, ρ*N ≤ W (some k,i)) :
    let D := fun a z => allocatedCoefficientDensity B U b hb o hR hσ S (point a z)
    ∀ (hD0 : ∀ a z, 0 ≤ D a z)
      (hD : 0 < selectedJointDensityMass bases modulus cells W D),
    1/2 ≤ selectedJointDensityMass bases modulus cells W D →
    (selectedJointFiniteLaw bases hbases modulus cells W hW hZ D hD0 hD).mean
      (fun z => noninjectivityIndicator
        (fun t => jointIntegerPhysicalSite (site t) (z.1.val,z.2.val))) ≤ δ := by
  intro D hD0 hD hlower
  apply selectedJointFiniteLaw_collision_small_with_cap bases hbases site hsite i hP hδ hδP
    hK hbound modulus hmodulus hmodP cells hcells W hW hZ hscale hρ hρP
    hN hwidth D hD0 hD hlower
  intro a z
  exact allocatedCoefficientDensity_fixedScale_le_exp B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall hP hm hK hRP hσP hcount hI hn hJ hAP hSP hCP hVP _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineFixedPathRationalReference
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

variable (H parameterStep : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (start : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (parameterStep j : ℤ) * t.val ∧
    start j + (parameterStep j : ℤ) * t.val < allocatedPrincipalSides B U basis S j)
variable (hH : ∀ j, 0 < H j)

variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "N" => (∏ l, primes l ^ exponent l)
local instance affineFixedPathCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleCongruenceOutput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical
open BooleanCubeKernel

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "sides" => allocatedPrincipalSides B U basis S

noncomputable def allocatedOriginalSampleDeckValue
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty sides)
    (j : Fin m) (e : E j) : ℤ :=
  MvPolynomial.eval (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
    (modularBoundedCoefficientPolynomial (j.val + 1) (fun d => deck j d e))

end Erdos3.VectorPolynomial

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

theorem selectedResidueFiniteLaw_cutoff_le_event
    (F : (K × I → ℝ) → ℝ) (bad : (K × I → ℤ) → Prop)
    (hF : ∀ z : K × I → ℤ, ‖fun t => (z t : ℝ) / V t‖ ≤ 1 →
      F (fun t => (z t : ℝ) / V t) ≤ if bad z then 1 else 0) :
    (selectedResidueFiniteLaw q T V hV hZ).mean
        (fun z => F (fun t => (z.val t : ℝ) / V t)) ≤
      (((selectedResidueSmoothPMF q T V hV hZ).map (fun z => decide (bad z))) true).toReal := by
  rw [← selectedResidueFiniteLaw_event_eq_map_true]
  apply FiniteProbabilityWeights.mean_mono_positive_support
  intro z hz
  exact hF z.val (selectedResidueFiniteLaw_normalized_norm_le q T V hV hZ z hz)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SelectedJointSpatialCutoff
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem selectedJointFiniteLaw_spatial_cutoff_bound
    {B K I : Type*} [Fintype K] [Fintype I]
    (bases : Finset B) (hbases : bases.Nonempty)
    (q : I → ℕ) (T : Finset (ColumnResiduePattern K I q))
    (V : K × I → ℝ) (hV : ∀ t, 0 < V t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass bases q T V D)
    (F : (K × I → ℝ) → ℝ) (hF : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1)
    (small large : (K × I → ℤ) → Prop)
    (hcut : ∀ z, ‖fun t => (z t : ℝ) / V t‖ ≤ 1 →
      (if small z then (1 : ℝ) else 0) ≤ F (fun t => (z t : ℝ) / V t) ∧
      F (fun t => (z t : ℝ) / V t) ≤ if large z then 1 else 0)
    {ε η δ : ℝ}
    (hprior : (((selectedResidueSmoothPMF q T V hV hZ).map
      (fun z => decide (large z))) true).toReal ≤ δ)
    (hmass : ∀ a, |selectedResidueDensityMass q T V (D a) - 1| ≤ η)
    (htest : ∀ a,
      |(∑' z, (selectedResidueSmoothPMF q T V hV hZ z).toReal *
        (F (fun t => (z t : ℝ) / V t) * D a z)) -
        ∑' z, (selectedResidueSmoothPMF q T V hV hZ z).toReal *
          F (fun t => (z t : ℝ) / V t)| ≤ ε) :
    (selectedJointFiniteLaw bases hbases q T V hV hZ D hD0 hD).mean
      (fun z => if small z.2.val then (1 : ℝ) else 0) ≤ δ + (η + ε) := by
  have hdom := FiniteProbabilityWeights.mean_mono_positive_support
    (selectedJointFiniteLaw bases hbases q T V hV hZ D hD0 hD)
    (f := fun z => if small z.2.val then (1 : ℝ) else 0)
    (g := fun z => F (fun t => (z.2.val t : ℝ) / V t))
    (fun z hz => (hcut z.2.val
      (selectedJointFiniteLaw_normalized_norm_le q T V bases hbases hV hZ D hD0 hD z hz)).1)
  have hcmp := selectedJointFiniteLaw_weighted_reference_real_comparison
    bases hbases q T V hV hZ D hD0 hD
    (fun _ z => F (fun t => (z t : ℝ) / V t))
    (fun _ z => by rw [abs_of_nonneg (hF _).1]; exact (hF _).2) hmass htest
  have href : (selectedJointReference bases hbases q T V hV hZ).mean
      (fun z => F (fun t => (z.2.val t : ℝ) / V t)) =
      (selectedResidueFiniteLaw q T V hV hZ).mean
        (fun z => F (fun t => (z.val t : ℝ) / V t)) := by
    change ((FiniteProbabilityWeights.uniformFinset bases hbases).prod
      (selectedResidueFiniteLaw q T V hV hZ)).mean _ = _
    rw [FiniteProbabilityWeights.mean_prod]
    dsimp only
    rw [FiniteProbabilityWeights.mean_const]
  rw [href] at hcmp
  have hp := (selectedResidueFiniteLaw_cutoff_le_event q T V hV hZ F large
    (fun z hz => (hcut z hz).2)).trans hprior
  linarith [(abs_le.mp hcmp).2]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

 theorem allocatedAffineLength_ready {D P Prho Pk target F T : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk) (ht : 0 ≤ target)
    (hF : 0 ≤ F) (hT : 0 ≤ T)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (hS : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T) ≤ S.value) :
    let e := allocatedAffineCoefficientAccuracyLog m D P Prho Pk target
    let E := allocatedAffineReferenceAccuracyLog m D P Prho Pk target
    Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value ∧
      1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp (-E) ∧
      Real.exp (progressionSliceLengthLog D E F T) ≤ S.value := by
  intro e E
  obtain ⟨he, hE, _, hEL, hf, hs⟩ :=
    allocatedAffineLengthLog_bounds m hdim.nonneg hP hr hk ht hF hT
  refine ⟨?_, ?_, (Real.exp_le_exp.mpr hs).trans hS⟩
  · exact (Real.exp_le_exp.mpr ((allocatedKernelReplacementLog_le_envelope B hdim hP).trans hf)).trans hS
  · have hES : Real.exp E ≤ S.value := (Real.exp_le_exp.mpr hEL).trans hS
    have hS1 : (1 : ℝ) ≤ S.value := (Real.one_le_exp_iff.mpr hE).trans hES
    have hpow : (S.value : ℝ) ≤ (S.value : ℝ) ^ (layerTailDegree m + 1) := by
      simpa only [pow_one] using pow_le_pow_right₀ hS1 (Nat.succ_le_succ (Nat.zero_le _))
    calc
      _ ≤ 1 / Real.exp E := one_div_le_one_div_of_le (Real.exp_pos _) (hES.trans hpow)
      _ = _ := by rw [Real.exp_neg, one_div]

 theorem allocatedAffineLength_slice_ready [DecidableEq α]
    {D P Prho Pk target F T δ : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk) (ht : 0 ≤ target)
    (hF : 0 ≤ F) (hT : 0 ≤ T)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (hS : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T) ≤ S.value)
    (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S j : ℤ))
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (modulus : ℕ) (hm : 0 < modulus) (hmT : (modulus : ℝ) ≤ Real.exp T) :
    let grid := allocatedGridAxis (I := I) U basis S.value
    let Tuple := PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    let embed := fun j : Tuple => (⟨j.1.val, j.2⟩ : PrincipalTupleIndex B (layerSamplerDegree I n))
    let E := allocatedAffineReferenceAccuracyLog m D P Prho Pk target
    (∀ j : Tuple, 0 < step (embed j)) →
    (∀ j : Tuple, δ * allocatedPrincipalSides B U basis S (embed j) ≤
      ((integerProgressionSupport (c (embed j)) (step (embed j) : ℤ) (H (embed j))).card : ℝ)) →
    (∀ j : Tuple, 2 ≤ H (embed j)) ∧
    (∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H (embed j)) ∧
    (∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H (embed j)) <
      MeasureTheory.volume.real (scalarCubeDomain α)) ∧
    (∑ j : Tuple, (modulus : ℝ) / H (embed j)) ≤ Real.exp (-E) ∧
    (∀ j : Tuple, (step (embed j) : ℝ) / allocatedPrincipalSides B U basis S (embed j) ≤
      Real.exp (-E)) := by
  intro grid Tuple embed E hstep hdense
  have hlen (j : Tuple) : allocatedPrincipalSides B U basis S (embed j) = S.value :=
    allocatedPrincipalSides_long B U basis S j.1.val j.1.property j.2.1 j.2.2
  have hready := allocatedAffineLength_ready B U basis hdim hP hr hk ht hF hT S hS
  have hE := (allocatedAffineLengthLog_bounds m hdim.nonneg hP hr hk ht hF hT).2.1
  have hslices := progressionSlice_scale_bounds (α := α)
    (fun j : Tuple => H (embed j)) (fun j : Tuple => step (embed j)) (fun j : Tuple => c (embed j))
    hdim.nonneg hE hF hT (hdim.active_tuples B grid) hdim.cube hδ hδF hm hmT hready.2.2 hstep
    (fun j => by simpa only [hlen j] using hsubset (embed j))
    (fun j => by simpa only [hlen j] using hdense j)
  simpa only [hlen] using hslices

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedCenteredBadPrimeSurrogate
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
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) (rankC : ℝ)

def allocatedPhysicalPrimePowerEvent
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) (p a : ℕ) [NeZero p] : Prop :=
  letI : ∀ r : ({p} : Finset ℕ), NeZero r.val := singleton_prime_neZero p
  coefficientDeckChartEvent U bW b hb o (p ^ a)
    (allocatedChartResiduePrimePowerWitness inactive rankC {p} (fun _ => a) (p ^ a)
      (singleton_prime_power_dvd p a) (fun v => (z v : ZMod (p ^ a))))
    (affineCoefficientCoverSample U poly hm (p ^ a) (fun k x => (z (k,x) : ℝ)))

variable {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem allocatedPhysicalPrimePowerEvent_center_measurableSet
    {T : Type*} [MeasurableSpace T] (c : T → ∀ j, U j) (hc : Measurable c)
    (base : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (p a : ℕ) [NeZero p] :
    MeasurableSet {center | allocatedPhysicalPrimePowerEvent B U bW b hb o
      (fun j => translate (fun x => (base x : ℝ)) (subtractConstant (c center j).val (poly j)))
      (fun j => coefficients_translate_mem (U j) (fun x => (base x : ℝ)) _
        (coefficients_subtractConstant_mem (U j) (c center j) (poly j) (hm j)))
      inactive rankC z p a} := by
  unfold allocatedPhysicalPrimePowerEvent
  exact coefficientDeckChartEvent_center_measurableSet U bW b hb o poly hm c hc base z (p ^ a) _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCenteredMeasurableFramedBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]

theorem allocatedOriginalCongruenceTop_congr_slopes
    (inactive : LayerSamplerAxis I n → Prop) (M : ℕ)
    (f g : AllocatedActualCoefficientIndex G X I E n B → ZMod M)
    (hnoise : ∀ (k : LayerSamplerVariables G I n B) (x : X),
      allocatedReadNoise f (some k,x) = allocatedReadNoise g (some k,x))
    (hdeck : allocatedReadDeck f = allocatedReadDeck g)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ = allocatedReadProjection g ⟨j,Sum.inr i⟩)
    (j : Fin m) (v : LayerSamplerVariables G I n B → ZMod M)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    allocatedOriginalTaggedTop inactive j (allocatedReadNoise f) (allocatedReadDeck f)
      (fun a => allocatedReadProjection f ⟨j,a.val⟩) v
      (allocatedCongruenceOutputEmbedding inactive j o) =
    allocatedOriginalTaggedTop inactive j (allocatedReadNoise g) (allocatedReadDeck g)
      (fun a => allocatedReadProjection g ⟨j,a.val⟩) v
      (allocatedCongruenceOutputEmbedding inactive j o) := by
  rcases o with x | i | a
  · exact spatialRankPolynomial_conditioned_top_congr (allocatedLongEmbedding inactive)
      (fun k => allocatedReadNoise f (k,x.val)) (fun k => allocatedReadNoise g (k,x.val))
      (fun k => hnoise k x.val) v v
  · simp only [allocatedCongruenceOutputEmbedding_deck, allocatedOriginalTaggedTop, hdeck]
  · simp only [allocatedCongruenceOutputEmbedding_integer, allocatedOriginalTaggedTop, hinteger]

variable [Fintype X] [∀ j, Fintype (E j)]

theorem allocatedResidueModulusBad_congr_slopes
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ) (M : ℕ) [NeZero M]
    (f g : AllocatedActualCoefficientIndex G X I E n B → ZMod M)
    (hnoise : ∀ (k : LayerSamplerVariables G I n B) (x : X),
      allocatedReadNoise f (some k,x) = allocatedReadNoise g (some k,x))
    (hdeck : allocatedReadDeck f = allocatedReadDeck g)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ = allocatedReadProjection g ⟨j,Sum.inr i⟩) :
    allocatedResidueModulusBad inactive C M f = allocatedResidueModulusBad inactive C M g := by
  unfold allocatedResidueModulusBad
  simp only [allocatedOriginalCongruenceTop_congr_slopes inactive M f g hnoise hdeck hinteger]

end Erdos3.VectorPolynomial

end

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

omit [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
theorem allocatedCentered_joint_weight_measurable : ∀ x, Measurable (fun center => (jointLaw center).weight x) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells width hwidth hZ
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) hD

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCenteredSpatialMatrixExceptional
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {B G P : Type*} [Fintype G] [Fintype P] {n : ℕ}
variable (hn : 0 < n) (e : Fin 2 × Fin n ↪ G)
variable (bases : Finset B) (hbases : bases.Nonempty)
variable (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
variable (T : Finset (ColumnResiduePattern (Option (G ⊕ P)) (Fin n) q))
variable (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
variable (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
variable {ηprior E : ℝ} (hpriorPos : 0 < ηprior) (hE : 0 ≤ E) (hpriorExp : ηprior⁻¹ ≤ Real.exp E)
variable (hwide : ∀ i, Real.exp (smoothMatrixBlockWidthLogBudget (2 * n * n) n 2 E) ≤
  spatialMatrixIndexWidth e q V i)
variable (D : B → (Option (G ⊕ P) × Fin n → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
variable (hD : 0 < selectedJointDensityMass bases q T V D)
local notation "κ" => spatialMatrixBlockThreshold n ηprior
local notation "cutoff" => spatialMatrixBlockCutoff (P := P) e κ

include hn hq hscale hpriorPos hE hpriorExp hwide in

theorem spatialMatrixBlock_joint_tilted_cutoff_bound
    {ηnorm εtest : ℝ}
    (hmass : ∀ a, |selectedResidueDensityMass q T V (D a) - 1| ≤ ηnorm)
    (htest : ∀ a,
      |(∑' z, (selectedResidueSmoothPMF q T V hV hZ z).toReal *
        (cutoff (fun t => (z t : ℝ) / V t) * D a z)) -
        ∑' z, (selectedResidueSmoothPMF q T V hV hZ z).toReal *
          cutoff (fun t => (z t : ℝ) / V t)| ≤ εtest) :
    (selectedJointFiniteLaw bases hbases q T V hV hZ D hD0 hD).mean
      (fun z => if spatialMatrixBlockBad e V (κ / 2) z.2.val then (1 : ℝ) else 0) ≤
      ηprior / 2 + (ηnorm + εtest) := by
  have hκ := spatialMatrixBlockThreshold_pos hn hpriorPos
  have hprior := spatialMatrixBlock_bad_probability_of_exp_width hn e q hq T V hV hZ hscale
    hpriorPos hE hpriorExp hwide
  apply selectedJointFiniteLaw_spatial_cutoff_bound bases hbases q T V hV hZ D hD0 hD
    cutoff (spatialMatrixBlockCutoff_range e κ) (spatialMatrixBlockBad e V (κ / 2))
    (spatialMatrixBlockBad e V κ) _ hprior hmass htest
  intro z hz
  apply spatialMatrixBlockCutoff_indicator_bounds e V hκ z
  intro t
  exact (norm_le_pi_norm (fun t => (z t : ℝ) / V t) t).trans hz

include hn hq hscale hpriorPos hE hpriorExp hwide in

theorem spatialMatrixBlock_joint_tilted_cutoff_bound_complex
    {ηnorm εtest : ℝ}
    (hmass : ∀ a, |selectedResidueDensityMass q T V (D a) - 1| ≤ ηnorm)
    (htest : ∀ a,
      ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hZ z).toReal : ℂ) *
        ((cutoff (fun t => (z t : ℝ) / V t) : ℂ) * (D a z : ℂ))) -
        ∑' z, ((selectedResidueSmoothPMF q T V hV hZ z).toReal : ℂ) *
          (cutoff (fun t => (z t : ℝ) / V t) : ℂ)‖ ≤ εtest) :
    (selectedJointFiniteLaw bases hbases q T V hV hZ D hD0 hD).mean
      (fun z => if spatialMatrixBlockBad e V (κ / 2) z.2.val then (1 : ℝ) else 0) ≤
      ηprior / 2 + (ηnorm + εtest) := by
  apply spatialMatrixBlock_joint_tilted_cutoff_bound hn e bases hbases q hq T V hV hZ hscale
    hpriorPos hE hpriorExp hwide D hD0 hD hmass
  intro a
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_tsum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using htest a

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_centered_spatial_matrix_exceptional (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {nX : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (nX : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × (Fin nX)) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : (Fin nX) → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : (Fin nX) → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    ∀ (bases : Finset (Fin nX → ℤ)) (hbases : bases.Nonempty)
      (hwidths : ∀ z, 0 < widths z)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z)
      (htotal : ∀ center, 0 < selectedJointDensityMass bases stride T widths (density center))
      (_hnX : 0 < nX) (e : Fin 2 × Fin nX ↪ G)
      {ηprior Ewidth : ℝ}, 0 < ηprior → 0 ≤ Ewidth → ηprior⁻¹ ≤ Real.exp Ewidth →
      (∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride widths z) →
      (∀ i, Real.exp (smoothMatrixBlockWidthLogBudget (2 * nX * nX) nX 2 Ewidth) ≤
        spatialMatrixIndexWidth e stride widths i) →
      2 / spatialMatrixBlockThreshold nX ηprior * ((nX * nX.factorial : ℕ) : ℝ) ≤ Real.exp P →
      let law := fun center => selectedJointFiniteLaw bases hbases stride T widths hwidths hZ
        (density center) (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
        (htotal center)
      (centeredFiniteProbabilityMeasure μ law).real
        {z | spatialMatrixBlockBad e widths (spatialMatrixBlockThreshold nX ηprior / 2) z.2.2.val} ≤
          ηprior / 2 + 6 * positiveProjectionAccuracy P := by
  obtain ⟨A, hA, hnormalization⟩ := exists_allocated_centered_narrow_amplitude_normalization m
  refine ⟨A, hA, ?_⟩
  intro nX G _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths density bases hbases hwidths hZ htotal hnX e
    ηprior Ewidth hpriorPos hEwidth hpriorExp hscale hwide hLipBudget law
  obtain ⟨_, _, hraw, hmass⟩ := hnormalization B U basis S hb o μ ν hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall hP hmSize hK (by simpa only [Fintype.card_fin] using hX)
    hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP hW hWP
    hτ hτP hξ hξ1 hξP N hsize hrank hRank T hT
  let κ := spatialMatrixBlockThreshold nX ηprior
  have hκ : 0 < κ := spatialMatrixBlockThreshold_pos hnX hpriorPos
  let amplitude := fun x : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ =>
    (spatialMatrixBlockCutoff e κ x : ℂ)
  have hamp (x) : ‖amplitude x‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (spatialMatrixBlockCutoff_range e κ x).1]
    exact (spatialMatrixBlockCutoff_range e κ x).2
  have hlip := Complex.isometry_ofReal.lipschitz.comp (spatialMatrixBlockCutoff_lipschitz
    (P := PrincipalTupleIndex B (layerSamplerDegree I n)) e hκ)
  have hlip' : LipschitzWith (⟨2 / κ, by positivity⟩ * ((nX * nX.factorial : ℕ) : ℝ≥0))
      amplitude := by
    simpa only [one_mul, Function.comp_def] using hlip
  have hweight (z) : Measurable (fun center => (law center).weight z) :=
    allocatedCenteredJointFiniteLaw_weight_measurable B U basis hb o hR hσ S p hm
      bases hbases stride T widths hwidths hZ htotal z
  apply centeredFiniteProbabilityMeasure_noise_event_le μ law hweight
    (fun z => spatialMatrixBlockBad e widths (κ / 2) z.2.val)
  intro center
  have h := spatialMatrixBlock_joint_tilted_cutoff_bound_complex hnX e bases hbases stride hs T
    widths hwidths hZ hscale hpriorPos hEwidth hpriorExp hwide
    (density center) (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
    (htotal center) (fun base => (hmass center base).1)
    (fun base => hraw center base amplitude hamp hlip'
      (by change 2 / κ * ((nX * nX.factorial : ℕ) : ℝ) ≤ Real.exp P
          exact hLipBudget))
  exact h.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

end OAI
end


