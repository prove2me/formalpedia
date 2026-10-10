-- Prove2me | Definitions.Def_OAIErdos3B147
-- name    : OAIErdos3B147
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T23:48:34.273598+00:00
-- url     : https://prove2.me/theorems/44123078-ec6e-42ac-a436-3a0f23fe68f9
-- title:
--   OpenAI Erdős-3 split, definitions bundle 148 of 177
-- statement:
--   Definitions bundle 148 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B146`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 148 available.
--
--   Modules: `OAI.Erdos3.ResidueBoxSlice.denseCoordinate_geometry`, `OAI.Erdos3.ResidueBoxSlice.fiberParameterStride_le`, `OAI.Erdos3.ResidueBoxSlice.fiberParameter_dense_geometry`, `OAI.Erdos3.ResidueBoxSlice.fiberParameter_dense_of_keep`, `OAI.Erdos3.ResidueBoxSlice.fiberParameter_regular_of_threshold`, `OAI.Erdos3.ResidueBoxSlice.fiberPrincipalParameter_inside`, `OAI.Erdos3.VectorPolynomial.AllocatedEarlyNativeSourceGeometryGeneral.noConfusion`, `OAI.Erdos3.VectorPolynomial.AllocatedFullContinuousCoefficientIndex`, `OAI.Erdos3.VectorPolynomial.AllocatedFullSmoothCoefficientIndex`, `OAI.Erdos3.VectorPolynomial.CoefficientIntegerScalarIndex`, `OAI.Erdos3.VectorPolynomial.PreparedModularGeneralDetectorFreeSpatialBounds`, `OAI.Erdos3.VectorPolynomial.PreparedModularGeneralDetectorSamplingBounds`, `OAI.Erdos3.VectorPolynomial.affineCongruenceScalarDecidableEq`, `OAI.Erdos3.VectorPolynomial.affineCongruenceScalarFintype`, `OAI.Erdos3.VectorPolynomial.affineFullWitnessDeckDecidableEq`, `OAI.Erdos3.VectorPolynomial.affineFullWitnessDeckFintype`, `OAI.Erdos3.VectorPolynomial.affineFullWitnessSelectedDeckDecidableEq`, `OAI.Erdos3.VectorPolynomial.affineFullWitnessSelectedDeckFintype`, `OAI.Erdos3.VectorPolynomial.affineFullWitnessSmoothFintype`, `OAI.Erdos3.VectorPolynomial.affineWitnessDeckIndexDecidableEq`, `OAI.Erdos3.VectorPolynomial.affineWitnessDeckIndexFintype`, `OAI.Erdos3.VectorPolynomial.allocatedActualModulusBad`, `OAI.Erdos3.VectorPolynomial.allocatedActualModulusBad_eq_residue`, `OAI.Erdos3.VectorPolynomial.allocatedActualPrimeBad`, `OAI.Erdos3.VectorPolynomial.allocatedActualPrimeBad_depth`, `OAI.Erdos3.VectorPolynomial.allocatedActualPrimeBad_eq_rankBad`, `OAI.Erdos3.VectorPolynomial.allocatedActualPrimeBad_iff_modulusBad`, `OAI.Erdos3.VectorPolynomial.allocatedAffineMixedModulusBad`, `OAI.Erdos3.VectorPolynomial.allocatedChartActualResidues`, `OAI.Erdos3.VectorPolynomial.allocatedChartActualResidues_deck`, `OAI.Erdos3.VectorPolynomial.allocatedChartActualResidues_integer`, `OAI.Erdos3.VectorPolynomial.allocatedChartActualResidues_noise`, `OAI.Erdos3.VectorPolynomial.allocatedChartResiduePrimePowerWitness`, `OAI.Erdos3.VectorPolynomial.allocatedChartResiduePrimePowerWitness_iff_actual`, `OAI.Erdos3.VectorPolynomial.allocatedChartResiduePrimePowerWitness_read`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientIntegerPMF`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceAffineCoefficients`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceIsSpatial`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceNaturalStride`, `OAI.Erdos3.VectorPolynomial.allocatedDeckFullEmbedding`, `OAI.Erdos3.VectorPolynomial.allocatedDeckFullSlot`, `OAI.Erdos3.VectorPolynomial.allocatedDeckFullSlot_injective`, `OAI.Erdos3.VectorPolynomial.allocatedDetectedGain`, `OAI.Erdos3.VectorPolynomial.allocatedDetectedKernelCutoff`, `OAI.Erdos3.VectorPolynomial.allocatedFullCoefficientSplit`, `OAI.Erdos3.VectorPolynomial.allocatedFullSmoothAffine`, `OAI.Erdos3.VectorPolynomial.allocatedFullSmoothScalarPMF`, `OAI.Erdos3.VectorPolynomial.allocatedLayerSupported_normalized_mass`, `OAI.Erdos3.VectorPolynomial.allocatedLayerSupported_normalized_mass_uniform`, `OAI.Erdos3.VectorPolynomial.allocatedMixedAffineSelectedValues`, `OAI.Erdos3.VectorPolynomial.allocatedMixedFullArray`, `OAI.Erdos3.VectorPolynomial.allocatedMixedFullArray_continuous`, `OAI.Erdos3.VectorPolynomial.allocatedMixedFullArray_deck`, `OAI.Erdos3.VectorPolynomial.allocatedMixedFullArray_integer`, `OAI.Erdos3.VectorPolynomial.allocatedMixedFullArray_noise`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalCongruenceTop_congr_outputs`, `OAI.Erdos3.VectorPolynomial.allocatedPrincipalRankCenter`, `OAI.Erdos3.VectorPolynomial.allocatedPrincipalRankWidth`, `OAI.Erdos3.VectorPolynomial.allocatedReadCoefficientChartResidues`, `OAI.Erdos3.VectorPolynomial.allocatedReadCoefficientChartResidues_sampler`, `OAI.Erdos3.VectorPolynomial.allocatedReadFullSmooth`, `OAI.Erdos3.VectorPolynomial.allocatedResidueModulusBad`, `OAI.Erdos3.VectorPolynomial.allocatedResidueModulusBad_congr_outputs`, `OAI.Erdos3.VectorPolynomial.allocatedResiduePrimePowerWitness`, `OAI.Erdos3.VectorPolynomial.allocatedResiduePrimePowerWitness_congr_outputs`, `OAI.Erdos3.VectorPolynomial.allocatedResiduePrimePowerWitness_iff_actual`, `OAI.Erdos3.VectorPolynomial.allocatedSelectedNoiseOffset`, `OAI.Erdos3.VectorPolynomial.allocatedSelectedSmoothAffine`, `OAI.Erdos3.VectorPolynomial.allocatedSelectedSmoothCenter`, `OAI.Erdos3.VectorPolynomial.allocatedSelectedSmoothWidth`, `OAI.Erdos3.VectorPolynomial.allocatedShortRankSelectedWidth`, `OAI.Erdos3.VectorPolynomial.allocatedSmoothFullEmbedding`, `OAI.Erdos3.VectorPolynomial.allocatedSmoothFullSlot`, `OAI.Erdos3.VectorPolynomial.allocatedSmoothFullSlot_injective`, `OAI.Erdos3.VectorPolynomial.coefficientIntegerDeckChartResidues`, `OAI.Erdos3.VectorPolynomial.coefficientIntegerScalars`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_layer_axes`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_physical_root`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_variable_count`, `OAI.Erdos3.VectorPolynomial.spatialReferenceDeckDecidableEq`, `OAI.Erdos3.VectorPolynomial.spatialReferenceDeckFintype`, `OAI.Erdos3.VectorPolynomial.spatialReferenceSmoothFintype`, `OAI.Erdos3.aeval_coordinate_scaling_monomial`, `OAI.Erdos3.affineSpatialCoefficients`, `OAI.Erdos3.exists_finite_normalized_chart_corrections`, `OAI.Erdos3.exists_finite_rank_triangular_correction_enumeration`, `OAI.Erdos3.exists_rank_triangular_equiv`, `OAI.Erdos3.finiteRankCorrectionSolutions`, `OAI.Erdos3.finiteRankCorrectionSolutions_reindex`, `OAI.Erdos3.kernelZeroTupleFromSumIntegerBox`, `OAI.Erdos3.mixedLiftPolynomial_scaled_coefficients`, `OAI.Erdos3.mixedLiftPolynomial_scaled_mass`, `OAI.Erdos3.normalizedAxes_homogeneousComponent_commute`, `OAI.Erdos3.normalizedChartCoefficientMatrix`, `OAI.Erdos3.normalizedChartCoefficientMatrix_coeff_aeval`, `OAI.Erdos3.normalizedChartCoefficientMatrix_diagonal`, `OAI.Erdos3.normalizedChartCoefficientMatrix_triangular`, `OAI.Erdos3.normalizedChartCorrectionSolutions`, `OAI.Erdos3.normalizedChartDiagonal`, `OAI.Erdos3.normalizedChartDiagonal_pos_le_one`, `OAI.Erdos3.normalizedChartTagWeight`, `OAI.Erdos3.normalizedChart_coeff_of_tag_le`, `OAI.Erdos3.normalizedChart_zero_monomial`, `OAI.Erdos3.normalizedMass_homogeneousComponent_projection_le`, `OAI.Erdos3.normalizedMass_neg_weightedHomogeneousComponent_le`, `OAI.Erdos3.normalizedPolynomialMass_neg`, `OAI.Erdos3.normalizedRealPolynomialChart_tag_coordinate_difference`, `OAI.Erdos3.normalizedRealPolynomialChart_tag_difference`, `OAI.Erdos3.normalizedRealPolynomialChart_tag_support`, `OAI.Erdos3.principalZeroTupleFromSumIntegerBox`, `OAI.Erdos3.scaleMvPolynomialAxes_neg`, `_private.Geometry.FiniteNormalizedChartCorrection.0.OAI.Erdos3.normalizedChartCorrectionSolutions_coefficients`, `_private.Geometry.FiniteNormalizedChartCorrection.0.OAI.Erdos3.normalizedChart_hom_tag_difference`, `_private.Geometry.FiniteNormalizedChartCorrection.0.OAI.Erdos3.normalizedChart_hom_tag_support`, `_private.Geometry.FiniteNormalizedChartCorrection.0.OAI.Erdos3.normalizedChart_spatial_support`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B129
import Definitions.Def_OAIErdos3B136
import Definitions.Def_OAIErdos3B138
import Definitions.Def_OAIErdos3B171

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedCoefficientIntegerMarginal
namespace OAI

section

namespace Erdos3
open MeasureTheory

namespace VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

abbrev CoefficientIntegerScalarIndex (K : Type*) {m : ℕ} (n : Fin m → ℕ) :=
  Σ j : Fin m, BoundedCoefficientExponent K (j.val + 1) × Fin (n j)

def coefficientIntegerScalars {K : Type*} {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    (a : CoefficientSamplerArrays (K := K) I n) (q : CoefficientIntegerScalarIndex K n) : ℤ :=
  (a q.1).2 q.2.2 q.2.1

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedCoefficientIntegerPMF :
    PMF (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) :=
  independentProductPMF (fun q => allocatedLayerIntegerPMFs B U b hR hσ S q.1 q.2.2 q.2.1)

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankFullProductLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

noncomputable def allocatedPrincipalRankCenter : ℝ :=
  (3 * principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card / 2) *
    ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))

noncomputable def allocatedPrincipalRankWidth : ℝ :=
  (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card / 2) *
    ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

abbrev AllocatedFullSmoothCoefficientIndex (G X : Type*) (I : Fin m → Type*)
    (n : Fin m → ℕ) (B : LayerSamplerAxis I n → Type*) :=
  (Option (LayerSamplerVariables G I n B) × X) ⊕
    (Σ j : Fin m, BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) × Fin (n j))

abbrev AllocatedFullContinuousCoefficientIndex (G : Type*) (I : Fin m → Type*)
    (n : Fin m → ℕ) (B : LayerSamplerAxis I n → Type*) :=
  Σ j : Fin m, BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) × I j

def allocatedFullCoefficientSplit :
    AllocatedActualCoefficientIndex G X I E n B ≃
      AllocatedFullSmoothCoefficientIndex G X I n B ⊕
        (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E ⊕
          AllocatedFullContinuousCoefficientIndex G I n B) where
  toFun t := match t with
    | .inl x => .inl (.inl x)
    | .inr (.inl d) => .inr (.inl d)
    | .inr (.inr ⟨⟨j,.inl i⟩,q⟩) => .inr (.inr ⟨j,q,i⟩)
    | .inr (.inr ⟨⟨j,.inr i⟩,q⟩) => .inl (.inr ⟨j,q,i⟩)
  invFun t := match t with
    | .inl (.inl x) => .inl x
    | .inr (.inl d) => .inr (.inl d)
    | .inr (.inr ⟨j,q,i⟩) => .inr (.inr ⟨⟨j,.inl i⟩,q⟩)
    | .inl (.inr ⟨j,q,i⟩) => .inr (.inr ⟨⟨j,.inr i⟩,q⟩)
  left_inv := by rintro (x | d | ⟨⟨j,(i | i)⟩,q⟩) <;> rfl
  right_inv := by rintro ((x | ⟨j,q,i⟩) | d | ⟨j,q,i⟩) <;> rfl

noncomputable def allocatedSmoothFullSlot
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩) :
    AllocatedSmoothRankCoefficientIndex X inactive L → AllocatedFullSmoothCoefficientIndex G X I n B
  | ⟨_j,.inl x,l⟩ => .inl (some (.inl (spatial l)),x.val)
  | ⟨j,.inr i,l⟩ => .inr ⟨j,
      principalCoefficientSlot (layerSamplerDegree I n) ⟨j,.inr i.val⟩
        (block j ⟨.inr i.val,i.property⟩ l), i.val⟩

theorem allocatedSmoothFullSlot_injective
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩) :
    Function.Injective (allocatedSmoothFullSlot (X := X) inactive spatial block) := by
  rintro ⟨j,(x | i),l⟩ ⟨k,(y | a),q⟩ he
  · have hjk : j = k := Fin.ext (x.property.trans y.property.symm)
    subst k
    have hp := Sum.inl.inj he
    have hl : l = q := spatial.injective
      (Sum.inl.inj (Option.some.inj (congrArg Prod.fst hp)))
    have hxy : x = y := Subtype.ext (congrArg Prod.snd hp)
    subst q
    subst y
    rfl
  · cases he
  · cases he
  · have hh := Sum.inr.inj he
    have hjk : j = k := congrArg Sigma.fst hh
    subst k
    have hp := eq_of_heq (Sigma.mk.inj hh).2
    have hia : i = a := Subtype.ext (congrArg Prod.snd hp)
    subst a
    have hblocks := principalCoefficientSlot_injective (G := G)
      (layerSamplerDegree I n) ⟨j,.inr i.val⟩ (Nat.zero_lt_succ _) (congrArg Prod.fst hp)
    have hl : l = q := (block j ⟨.inr i.val,i.property⟩).injective hblocks
    subst q
    rfl

noncomputable def allocatedSmoothFullEmbedding
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩) :
    AllocatedSmoothRankCoefficientIndex X inactive L ↪ AllocatedFullSmoothCoefficientIndex G X I n B :=
  ⟨allocatedSmoothFullSlot inactive spatial block, allocatedSmoothFullSlot_injective inactive spatial block⟩

noncomputable def allocatedDeckFullSlot (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G) :
    AllocatedDeckRankCoefficientIndex E L → CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E
  | ⟨j,e,l⟩ => ⟨j,kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j) l,e⟩

theorem allocatedDeckFullSlot_injective (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G) :
    Function.Injective (allocatedDeckFullSlot (I := I) (E := E) (n := n) (B := B) kernel) := by
  rintro ⟨j,e,l⟩ ⟨k,f,q⟩ he
  have hjk : j = k := congrArg Sigma.fst he
  subst k
  have hp := eq_of_heq (Sigma.mk.inj he).2
  have hl : l = q := kernelRankCoefficientSlot_injective
    (layerSamplerDegree I n) (kernel j) (Nat.zero_lt_succ _) (congrArg Prod.fst hp)
  have hef : e = f := congrArg Prod.snd hp
  subst q
  subst f
  rfl

noncomputable def allocatedDeckFullEmbedding (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G) :
    AllocatedDeckRankCoefficientIndex E L ↪ CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E :=
  ⟨allocatedDeckFullSlot kernel, allocatedDeckFullSlot_injective kernel⟩

def allocatedMixedFullArray {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) :
    AllocatedActualCoefficientIndex G X I E n B → R :=
  Sum.elim smooth (Sum.elim deck continuous) ∘ allocatedFullCoefficientSplit

@[simp] theorem allocatedMixedFullArray_noise {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) (x) :
    allocatedReadNoise (allocatedMixedFullArray smooth deck continuous) x = smooth (.inl x) := rfl

@[simp] theorem allocatedMixedFullArray_deck {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) (j) (q) (e) :
    allocatedReadDeck (allocatedMixedFullArray smooth deck continuous) j q e = deck ⟨j,q,e⟩ := rfl

@[simp] theorem allocatedMixedFullArray_integer {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) (j) (q) (i) :
    allocatedReadProjection (allocatedMixedFullArray smooth deck continuous) ⟨j,.inr i⟩ q =
      smooth (.inr ⟨j,q,i⟩) := rfl

@[simp] theorem allocatedMixedFullArray_continuous {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) (j) (q) (i) :
    allocatedReadProjection (allocatedMixedFullArray smooth deck continuous) ⟨j,.inl i⟩ q =
      continuous ⟨j,q,i⟩ := rfl

def allocatedReadFullSmooth {R : Type*}
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    AllocatedFullSmoothCoefficientIndex G X I n B → R
  | .inl x => allocatedReadNoise f x
  | .inr ⟨j,q,i⟩ => allocatedReadProjection f ⟨j,.inr i⟩ q

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedFullSmoothScalarPMF
    (noisePMF : Option (LayerSamplerVariables G I n B) × X → PMF ℤ) :
    AllocatedFullSmoothCoefficientIndex G X I n B → PMF ℤ
  | .inl x => noisePMF x
  | .inr ⟨j,q,i⟩ => allocatedLayerIntegerPMFs B U basis hR hσ S j i q

variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (noiseCenter noiseWidth : Fin L → X → ℝ)

noncomputable def allocatedSelectedSmoothCenter : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ
  | ⟨_j,.inl x,l⟩ => noiseCenter l x.val
  | ⟨j,.inr i,_l⟩ => allocatedPrincipalRankCenter B U basis S j i.val

noncomputable def allocatedSelectedSmoothWidth : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ
  | ⟨_j,.inl x,l⟩ => noiseWidth l x.val
  | ⟨j,.inr i,_l⟩ => allocatedPrincipalRankWidth B U basis S j i.val

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineProbability
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def affineSpatialCoefficients {A B R : Type*} [Semiring R]
    (spatial : B → Prop) (stride : B → ℕ) (offset : B → A → R)
    (c : B → A → R) : B → A → R :=
  fun b i => if spatial b then (stride b : R) * c b i + offset b i else c b i

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {L : ℕ} {R : Type*}

def allocatedCongruenceIsSpatial (inactive : LayerSamplerAxis I n → Prop)
    (j : Fin m) : AllocatedCongruenceRankOutput X E inactive j → Prop
  | .inl _ => True
  | .inr _ => False

def allocatedCongruenceAffineCoefficients [Semiring R]
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → R)
    (offset c : AllocatedCongruenceCoefficientIndex X E inactive L → R) :
    AllocatedCongruenceCoefficientIndex X E inactive L → R
  | ⟨j,.inl x,l⟩ => offset ⟨j,.inl x,l⟩ + stride x.val * c ⟨j,.inl x,l⟩
  | ⟨j,.inr o,l⟩ => c ⟨j,.inr o,l⟩

noncomputable def allocatedMixedAffineSelectedValues
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → ℤ)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    {N : ℕ} (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    AllocatedCongruenceCoefficientIndex X E inactive L → ℤ :=
  allocatedCongruenceAffineCoefficients inactive stride offset
    (allocatedMixedSelectedValues inactive x deck)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ} {R : Type*}

def allocatedFullSmoothAffine [Semiring R] (stride : X → R)
    (residue : Option (LayerSamplerVariables G I n B) × X → R)
    (z : AllocatedFullSmoothCoefficientIndex G X I n B → R) :
    AllocatedFullSmoothCoefficientIndex G X I n B → R
  | .inl t => residue t + stride t.2 * z (.inl t)
  | .inr t => z (.inr t)

def allocatedSelectedNoiseOffset [Semiring R]
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (residue : Option (LayerSamplerVariables G I n B) × X → R) :
    AllocatedCongruenceCoefficientIndex X E inactive L → R
  | ⟨_j,.inl x,l⟩ => residue (some (.inl (spatial l)),x.val)
  | ⟨_j,.inr _,_l⟩ => 0

def allocatedSelectedSmoothAffine [Semiring R]
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (stride : X → R) (residue : Option (LayerSamplerVariables G I n B) × X → R)
    (z : AllocatedSmoothRankCoefficientIndex X inactive L → R) :
    AllocatedSmoothRankCoefficientIndex X inactive L → R
  | ⟨j,.inl x,l⟩ => residue (some (.inl (spatial l)),x.val) + stride x.val * z ⟨j,.inl x,l⟩
  | ⟨j,.inr i,l⟩ => z ⟨j,.inr i,l⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

def allocatedCongruenceNaturalStride (inactive : LayerSamplerAxis I n → Prop)
    (stride : X → ℕ) (j : Fin m) : AllocatedCongruenceRankOutput X E inactive j → ℕ
  | .inl x => stride x.val
  | .inr _ => 1

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance affineCongruenceScalarFintype
    (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedCongruenceScalarIndex X E inactive L) := inferInstance

noncomputable local instance affineCongruenceScalarDecidableEq
    (inactive : LayerSamplerAxis I n → Prop) :
    DecidableEq (AllocatedCongruenceScalarIndex X E inactive L) := Classical.decEq _

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

def allocatedResidueModulusBad
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ) (M : ℕ) [NeZero M]
    (f : AllocatedActualCoefficientIndex G X I E n B → ZMod M) : Prop :=
  ∃ v : LayerSamplerVariables G I n B → ZMod M, ∃ j : Fin m,
    ∃ w : AllocatedCongruenceRankOutput X E inactive j → ZMod M,
      (∃ o, IsUnit (w o)) ∧ (M : ℝ) ^ (-C) <
        (𝔼 u : Fin j.val → LayerSamplerLongVariables inactive G B → ZMod M,
          if polynomialLinearRow (polynomialIterDifference j.val
            (∑ o, w o • allocatedOriginalTaggedTop inactive j
              (allocatedReadNoise f) (allocatedReadDeck f)
              (fun a => allocatedReadProjection f ⟨j,a.val⟩) v
              (allocatedCongruenceOutputEmbedding inactive j o)) u) = 0 then 1 else 0)

def allocatedActualModulusBad
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (M : ℕ) [NeZero M]
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  allocatedCongruenceModulusBad inactive (allocatedReadNoise f) (allocatedReadDeck f)
    (fun j a => allocatedReadProjection f ⟨j,a.val⟩) spatial kernel block C M
    (fun z => (allocatedCongruenceIntegerSelectedCoefficients inactive
      (allocatedReadNoise f) (allocatedReadDeck f)
      (fun j a => allocatedReadProjection f ⟨j,a.val⟩) spatial kernel block z : ZMod M))

theorem allocatedActualModulusBad_eq_residue
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (M : ℕ) [NeZero M]
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedActualModulusBad inactive spatial kernel block C M f =
      allocatedResidueModulusBad inactive C M (fun i => (f i : ZMod M)) := by
  unfold allocatedActualModulusBad allocatedCongruenceModulusBad
    allocatedCongruenceRankFailureProbability allocatedResidueModulusBad
  simp only [allocatedCongruenceIntegerSelectedCoefficients_reduce,
    allocatedCongruenceRankPolynomial_original]
  rfl

def allocatedResiduePrimePowerWitness
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (fM : AllocatedActualCoefficientIndex G X I E n B → ZMod M) : Prop :=
  ∀ p : P, allocatedResidueModulusBad inactive C (p.val ^ A p.val)
    (fun i => ZMod.castHom (hdiv p) (ZMod (p.val ^ A p.val)) (fM i))

theorem allocatedResiduePrimePowerWitness_iff_actual
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedResiduePrimePowerWitness inactive C P A M hdiv (fun i => (f i : ZMod M)) ↔
      ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val) f := by
  unfold allocatedResiduePrimePowerWitness
  apply forall_congr'
  intro p
  rw [allocatedActualModulusBad_eq_residue]
  have hcast : (fun i => ZMod.castHom (hdiv p) (ZMod (p.val ^ A p.val)) (f i : ZMod M)) =
      (fun i => (f i : ZMod (p.val ^ A p.val))) := by
    funext i
    exact map_intCast _ _
  rw [hcast]

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

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]
variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)

def allocatedActualPrimeBad (p a : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  ∃ hp : p ∈ P, letI : NeZero p := inferInstanceAs (NeZero (⟨p, hp⟩ : P).val)
    allocatedActualModulusBad inactive spatial kernel block C (p ^ a) f

theorem allocatedActualPrimeBad_iff_modulusBad (p : P) (a : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedActualPrimeBad inactive spatial kernel block P C p.val a f ↔
      allocatedActualModulusBad inactive spatial kernel block C (p.val ^ a) f := by
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨p.property, h⟩

theorem allocatedActualPrimeBad_eq_rankBad (p a : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedActualPrimeBad inactive spatial kernel block P C p a f =
      allocatedCongruenceRankBad inactive (allocatedReadNoise f) (allocatedReadDeck f)
        (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block P C p a
        (allocatedCongruenceIntegerSelectedCoefficients inactive
          (allocatedReadNoise f) (allocatedReadDeck f)
          (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block) := rfl

theorem allocatedActualPrimeBad_depth (A : ℕ → ℕ) (p : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P C) p f =
      allocatedCongruenceBadDepth inactive (allocatedReadNoise f) (allocatedReadDeck f)
        (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block P A C p := by
  unfold allocatedCongruenceBadDepth largestTestedBadDepth
  apply congrArg (fun t : Finset ℕ => t.sup id)
  apply Finset.filter_congr
  intro a _
  exact (allocatedActualPrimeBad_eq_rankBad inactive spatial kernel block P C p a f).to_iff

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance affineWitnessDeckIndexFintype :
    Fintype (AllocatedDeckRankCoefficientIndex E L) := inferInstance
noncomputable local instance affineWitnessDeckIndexDecidableEq :
    DecidableEq (AllocatedDeckRankCoefficientIndex E L) := Classical.decEq _

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

def allocatedAffineMixedModulusBad (stride : X → ℕ)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    (C : ℝ) (M : ℕ) [NeZero M]
    (x : (AllocatedSmoothRankCoefficientIndex X inactive L ⊕
      AllocatedDeckRankCoefficientIndex E L) → ZMod M) : Prop :=
  allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C M
    (allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : ZMod M))
      (fun j => (offset j : ZMod M)) (allocatedMixedCoefficientEquiv inactive L (ZMod M) x))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights
attribute [local irreducible] allocatedActualModulusBad allocatedMixedFullArray independentProductPMF

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance affineFullWitnessSmoothFintype :
    Fintype (AllocatedFullSmoothCoefficientIndex G X I n B) := inferInstance
noncomputable local instance affineFullWitnessDeckFintype :
    Fintype (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := inferInstance
noncomputable local instance affineFullWitnessDeckDecidableEq :
    DecidableEq (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := Classical.decEq _
noncomputable local instance affineFullWitnessSelectedDeckFintype :
    Fintype (AllocatedDeckRankCoefficientIndex E L) := inferInstance
noncomputable local instance affineFullWitnessSelectedDeckDecidableEq :
    DecidableEq (AllocatedDeckRankCoefficientIndex E L) := Classical.decEq _

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedSpatialCoefficientReferenceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

def coefficientIntegerDeckChartResidues {K : Type*} {m : ℕ}
    {n : Fin m → ℕ} {E : Fin m → Type*} (q : ℕ)
    (a : CoefficientIntegerScalarIndex K n → ℤ)
    (deck : CoefficientDeckResidues (K := K) E q) :
    CoefficientChartResidues K n E q :=
  fun j e => Sum.elim (fun i => (a ⟨j,e,i⟩ : ZMod q)) (deck j e)

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

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

def allocatedReadCoefficientChartResidues {M : ℕ}
    (f : AllocatedActualCoefficientIndex G X I E n B → ZMod M) :
    CoefficientChartResidues (LayerSamplerVariables G I n B) n E M :=
  fun j q => Sum.elim (fun i => allocatedReadProjection f ⟨j,Sum.inr i⟩ q)
    (allocatedReadDeck f j q)

def allocatedChartActualResidues {M : ℕ}
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M) :
    AllocatedActualCoefficientIndex G X I E n B → ZMod M :=
  allocatedMixedFullArray
    (Sum.elim noise (fun ⟨j,q,i⟩ => chart j q (Sum.inl i)))
    (fun ⟨j,q,i⟩ => chart j q (Sum.inr i)) (fun _ => 0)

@[simp] theorem allocatedChartActualResidues_noise {M : ℕ}
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M) :
    allocatedReadNoise (allocatedChartActualResidues noise chart) = noise := rfl

@[simp] theorem allocatedChartActualResidues_deck {M : ℕ}
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M) :
    allocatedReadDeck (allocatedChartActualResidues noise chart) =
      fun j q i => chart j q (Sum.inr i) := rfl

@[simp] theorem allocatedChartActualResidues_integer {M : ℕ}
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M)
    (j : Fin m) (i : Fin (n j)) :
    allocatedReadProjection (allocatedChartActualResidues noise chart) ⟨j,Sum.inr i⟩ =
      fun q => chart j q (Sum.inl i) := rfl

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

def allocatedChartResiduePrimePowerWitness
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M) : Prop :=
  allocatedResiduePrimePowerWitness inactive C P A M hdiv
    (allocatedChartActualResidues noise chart)

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

theorem allocatedChartResiduePrimePowerWitness_iff_actual
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (allocatedReadNoise (fun i => (f i : ZMod M)))
      (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod M))) ↔
      ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val) f := by
  rw [allocatedChartResiduePrimePowerWitness_read]
  exact allocatedResiduePrimePowerWitness_iff_actual inactive spatial kernel block C P A M hdiv f

omit [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in

theorem allocatedReadCoefficientChartResidues_sampler
    (M : ℕ) (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j))
      (q : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ q = (x j).2 i q) :
    allocatedReadCoefficientChartResidues (fun i => (f i : ZMod M)) =
      coefficientSamplerChartResidues M x (fun j q i => ((allocatedReadDeck f j q i : ℤ) : ZMod M)) := by
  funext j q i
  cases i with
  | inl i => exact congrArg (fun z : ℤ => (z : ZMod M)) (hinteger j i q)
  | inr i => rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (B) {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable local instance spatialReferenceSmoothFintype :
    Fintype (AllocatedFullSmoothCoefficientIndex G X I n B) := inferInstance
noncomputable local instance spatialReferenceDeckFintype :
    Fintype (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := inferInstance
noncomputable local instance spatialReferenceDeckDecidableEq :
    DecidableEq (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := Classical.decEq _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedShortRankSelectedWidth {L : ℕ}
    (spatial : Fin L ↪ G) (stride : X → ℕ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) :
    AllocatedSmoothRankCoefficientIndex X (allocatedShortAxis (I := I) U basis S.value) L → ℝ :=
  allocatedSelectedSmoothWidth B U basis S (allocatedShortAxis (I := I) U basis S.value)
    (fun l x => residueProfileWidth stride V (some (.inl (spatial l)),x))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteRankTriangularFinset
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def finiteRankCorrectionSolutions {I : Type*} [Fintype I]
    (A : Matrix I I ℝ) (c : I → ℝ) (B : ℝ) (q : ℕ) :
    Set ((I → ℝ) × (I → ℚ)) :=
  {sr | (∀ i, |sr.1 i| ≤ B) ∧
    (∀ i, ∃ z : ℤ, sr.2 i = (z : ℚ) / q) ∧
    ∀ i, c i = ∑ j, A i j * sr.1 j + (sr.2 i : ℝ)}

theorem finiteRankCorrectionSolutions_reindex
    {I J : Type*} [Fintype I] [Fintype J] (e : J ≃ I)
    (A : Matrix I I ℝ) (c : I → ℝ) (B : ℝ) (q : ℕ)
    (sr : (I → ℝ) × (I → ℚ)) :
    sr ∈ finiteRankCorrectionSolutions A c B q ↔
      ((fun i => sr.1 (e i)), (fun i => sr.2 (e i))) ∈
        finiteRankCorrectionSolutions (fun i j => A (e i) (e j)) (fun i => c (e i)) B q := by
  constructor
  · intro hs
    refine ⟨fun i => hs.1 (e i), fun i => hs.2.1 (e i), ?_⟩
    intro i
    dsimp only
    have hsum : (∑ j, A (e i) (e j) * sr.1 (e j)) =
        ∑ j : I, A (e i) j * sr.1 j := e.sum_comp (fun j : I => A (e i) j * sr.1 j)
    rw [hsum]
    exact hs.2.2 (e i)
  · intro hs
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simpa only [e.apply_symm_apply] using hs.1 (e.symm i)
    · intro i
      simpa only [e.apply_symm_apply] using hs.2.1 (e.symm i)
    · intro i
      have hi := hs.2.2 (e.symm i)
      dsimp only at hi
      have hsum : (∑ j, A i (e j) * sr.1 (e j)) =
          ∑ j : I, A i j * sr.1 j := e.sum_comp (fun j : I => A i j * sr.1 j)
      simpa only [e.apply_symm_apply, hsum] using hi

theorem exists_rank_triangular_equiv {I : Type*} [Fintype I]
    (rank : I → ℕ) (A : Matrix I I ℝ)
    (htri : ∀ i j, rank j ≤ rank i → j ≠ i → A i j = 0) :
    ∃ e : Fin (Fintype.card I) ≃ I,
      (∀ i j, i ≤ j → rank (e j) ≤ rank (e i)) ∧
      ∀ i j, i < j → A (e i) (e j) = 0 := by
  obtain ⟨e, he⟩ := exists_finite_descending_rank_equiv rank
  refine ⟨e, he, ?_⟩
  intro i j hij
  exact htri (e i) (e j) (he i j hij.le)
    (fun h => hij.ne (e.injective h).symm)

theorem exists_finite_rank_triangular_correction_enumeration
    {I : Type*} [Fintype I] (q : ℕ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B)
    (rank : I → ℕ) (A : Matrix I I ℝ) (c : I → ℝ)
    (htri : ∀ i j, rank j ≤ rank i → j ≠ i → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) (hdiagBound : ∀ i, |A i i| ≤ 1) :
    ∃ m : ℕ, m ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ Fintype.card I ∧
      ∃ candidate : Fin m → ((I → ℝ) × (I → ℚ)),
        (∀ j, candidate j ∈ finiteRankCorrectionSolutions A c B q) ∧
        ∀ sr, sr ∈ finiteRankCorrectionSolutions A c B q → ∃ j, candidate j = sr := by
  obtain ⟨e, _, he⟩ := exists_rank_triangular_equiv rank A htri
  let A' : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℝ :=
    fun i j => A (e i) (e j)
  let c' : Fin (Fintype.card I) → ℝ := fun i => c (e i)
  obtain ⟨m, hm, candidate, hmem, hcover⟩ :=
    exists_triangular_rational_correction_enumeration q hq B hB (Fintype.card I) A' c'
      he (fun i => hdiag (e i)) (fun i => hdiagBound (e i))
  let candidate' : Fin m → ((I → ℝ) × (I → ℚ)) :=
    fun j => (fun i => (candidate j).1 (e.symm i), fun i => (candidate j).2 (e.symm i))
  refine ⟨m, hm, candidate', ?_, ?_⟩
  · intro j
    apply (finiteRankCorrectionSolutions_reindex e A c B q (candidate' j)).mpr
    simpa only [candidate', e.symm_apply_apply, finiteRankCorrectionSolutions,
      triangularCorrectionSolutions, A', c'] using hmem j
  · intro sr hsr
    have hsr' := (finiteRankCorrectionSolutions_reindex e A c B q sr).mp hsr
    obtain ⟨j, hj⟩ := hcover (fun i => sr.1 (e i), fun i => sr.2 (e i)) hsr'
    refine ⟨j, ?_⟩
    dsimp only [candidate']
    rw [hj]
    simp only [e.apply_symm_apply]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteNormalizedChartCorrection
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {U B : Type*}

noncomputable def normalizedChartTagWeight : U ⊕ B → ℕ :=
  Sum.elim (fun _ => 0) (fun _ => 1)

theorem normalizedChart_spatial_support (P : MvPolynomial U ℝ) :
    rename (Sum.inl : U → U ⊕ B) P ∈ weightedSupportLE normalizedChartTagWeight 0 := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval (fun _ : U => 0) normalizedChartTagWeight
  · intro i
    exact weightedSupportLE_X _ (Sum.inl i)
  · intro α _
    simp [Finsupp.weight_apply]

theorem normalizedRealPolynomialChart_tag_support
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (i : U ⊕ B) :
    normalizedRealPolynomialChart H A i ∈
      weightedSupportLE normalizedChartTagWeight (normalizedChartTagWeight i) := by
  cases i with
  | inl i =>
    change C ((H i)⁻¹) * X (Sum.inl i) ∈ weightedSupportLE
      (normalizedChartTagWeight (U := U) (B := B)) 0
    exact weightedSupportLE_mul
      (w := normalizedChartTagWeight (U := U) (B := B)) (d := 0) (e := 0)
      (weightedSupportLE_C _ 0 ((H i)⁻¹)) (weightedSupportLE_X _ (Sum.inl i))
  | inr i =>
    change X (Sum.inr i) - rename Sum.inl (A i) ∈ weightedSupportLE
      (normalizedChartTagWeight (U := U) (B := B)) 1
    exact (weightedSupportLE (normalizedChartTagWeight (U := U) (B := B)) 1).sub_mem
      (weightedSupportLE_X _ (Sum.inr i))
      (weightedSupportLE_mono (Nat.zero_le 1) (normalizedChart_spatial_support (A i)))

theorem normalizedRealPolynomialChart_tag_coordinate_difference
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (i : U ⊕ B) :
    normalizedRealPolynomialChart H A i -
      normalizedRealPolynomialChart H (fun _ => 0) i ∈
        weightedSupportLT normalizedChartTagWeight (normalizedChartTagWeight i) := by
  cases i with
  | inl i =>
    simp only [normalizedRealPolynomialChart_inl, sub_self]
    exact Submodule.zero_mem _
  | inr i =>
    change (X (Sum.inr i) - rename Sum.inl (A i)) -
      (X (Sum.inr i) - rename Sum.inl (0 : MvPolynomial U ℝ)) ∈
        weightedSupportLT (normalizedChartTagWeight (U := U) (B := B)) 1
    rw [map_zero, sub_zero, sub_sub_cancel_left]
    exact (weightedSupportLT (normalizedChartTagWeight (U := U) (B := B)) 1).neg_mem
      (weightedSupportLE_lt_succ (normalizedChart_spatial_support (A i)))

theorem normalizedChart_hom_tag_support
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (i : U ⊕ B) :
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A)) (X i) ∈
      weightedSupportLE normalizedChartTagWeight (normalizedChartTagWeight i) := by
  rw [aeval_X]
  exact normalizedRealPolynomialChart_tag_support H A i

theorem normalizedChart_hom_tag_difference
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (i : U ⊕ B) :
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A)) (X i) -
      (aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ => 0))) (X i) ∈
        weightedSupportLT normalizedChartTagWeight (normalizedChartTagWeight i) := by
  rw [aeval_X, aeval_X]
  exact normalizedRealPolynomialChart_tag_coordinate_difference H A i

theorem normalizedRealPolynomialChart_tag_difference
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (α : (U ⊕ B) →₀ ℕ) :
    aeval (R := ℝ) (normalizedRealPolynomialChart H A) (monomial α 1) -
      aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ => 0)) (monomial α 1) ∈
        weightedSupportLT normalizedChartTagWeight (Finsupp.weight normalizedChartTagWeight α) :=
  weightedComparison_monomial_one
    (normalizedChartTagWeight (U := U) (B := B)) normalizedChartTagWeight
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A))
    (aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ => 0)))
    (normalizedChart_hom_tag_support H A)
    (normalizedChart_hom_tag_support H (fun _ => 0))
    (normalizedChart_hom_tag_difference H A) α

theorem aeval_coordinate_scaling_monomial {I : Type*}
    (c : I → ℝ) (α : I →₀ ℕ) :
    aeval (R := ℝ) (fun i => C (c i) * X i) (monomial α 1) =
      monomial α (α.prod (fun i n => c i ^ n)) := by
  classical
  rw [aeval_monomial]
  simp only [map_one, one_mul, Finsupp.prod,
    mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, monomial_eq]

noncomputable def normalizedChartDiagonal (H : U → ℝ) (α : (U ⊕ B) →₀ ℕ) : ℝ :=
  α.prod (fun i n => (Sum.elim (fun u => (H u)⁻¹) (fun _ : B => 1) i) ^ n)

theorem normalizedChart_zero_monomial (H : U → ℝ) (α : (U ⊕ B) →₀ ℕ) :
    aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ : B => 0)) (monomial α 1) =
      monomial α (normalizedChartDiagonal H α) := by
  have h : normalizedRealPolynomialChart H (fun _ : B => 0) =
      fun i => C (Sum.elim (fun u => (H u)⁻¹) (fun _ : B => 1) i) * X i := by
    funext i
    cases i <;> simp [normalizedRealPolynomialChart]
  rw [h]
  exact aeval_coordinate_scaling_monomial _ α

theorem normalizedChart_coeff_of_tag_le (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (α β : (U ⊕ B) →₀ ℕ)
    (h : Finsupp.weight normalizedChartTagWeight α ≤ Finsupp.weight normalizedChartTagWeight β) :
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A) (monomial α 1)).coeff β =
      if α = β then normalizedChartDiagonal H α else 0 := by
  classical
  have hd := normalizedRealPolynomialChart_tag_difference H A α
  have hz : (aeval (R := ℝ) (normalizedRealPolynomialChart H A) (monomial α 1) -
      aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ => 0)) (monomial α 1)).coeff β = 0 := by
    by_contra hn
    exact (not_lt_of_ge h) (hd (mem_support_iff.mpr hn))
  rw [coeff_sub, normalizedChart_zero_monomial, coeff_monomial] at hz
  exact sub_eq_zero.mp hz

theorem normalizedChartDiagonal_pos_le_one (H : U → ℝ) (hH : ∀ i, 1 ≤ H i)
    (α : (U ⊕ B) →₀ ℕ) :
    0 < normalizedChartDiagonal H α ∧ normalizedChartDiagonal H α ≤ 1 := by
  classical
  have hscale (i : U ⊕ B) :
      0 < Sum.elim (fun u => (H u)⁻¹) (fun _ : B => (1 : ℝ)) i ∧
        Sum.elim (fun u => (H u)⁻¹) (fun _ : B => (1 : ℝ)) i ≤ 1 := by
    cases i with
    | inl i => exact ⟨inv_pos.mpr (lt_of_lt_of_le zero_lt_one (hH i)),
        inv_le_one_of_one_le₀ (hH i)⟩
    | inr i => exact ⟨zero_lt_one, le_rfl⟩
  unfold normalizedChartDiagonal Finsupp.prod
  refine ⟨Finset.prod_pos (fun i _ => pow_pos (hscale i).1 _), ?_⟩
  exact Finset.prod_le_one (fun i _ => pow_nonneg (hscale i).1.le _)
    (fun i _ => pow_le_one₀ (hscale i).1.le (hscale i).2)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {U V : Type*}

def normalizedChartCorrectionSolutions
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ) (B : ℝ) (q : ℕ) :
    Set (MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℚ) :=
  {sr | sr.1.support ⊆ S ∧ sr.2.support ⊆ S ∧
    (∀ α, |sr.1.coeff α| ≤ B) ∧
    (∀ α, ∃ z : ℤ, sr.2.coeff α = (z : ℚ) / q) ∧
    P = aeval (R := ℝ) (normalizedRealPolynomialChart H A) sr.1 +
      MvPolynomial.map (Rat.castHom ℝ) sr.2}

noncomputable def normalizedChartCoefficientMatrix
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) : Matrix S S ℝ :=
  fun β α =>
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A) (monomial α.val 1)).coeff β.val

theorem normalizedChartCoefficientMatrix_triangular
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (α β : S)
    (h : Finsupp.weight normalizedChartTagWeight β.val ≤
      Finsupp.weight normalizedChartTagWeight α.val) (hne : β ≠ α) :
    normalizedChartCoefficientMatrix H A S α β = 0 := by
  classical
  have hval : β.val ≠ α.val := fun he => hne (Subtype.ext he)
  simp only [normalizedChartCoefficientMatrix, normalizedChart_coeff_of_tag_le H A β.val α.val h,
    hval, ite_false]

theorem normalizedChartCoefficientMatrix_diagonal
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (α : S) :
    normalizedChartCoefficientMatrix H A S α α ≠ 0 ∧
      |normalizedChartCoefficientMatrix H A S α α| ≤ 1 := by
  classical
  rw [normalizedChartCoefficientMatrix,
    normalizedChart_coeff_of_tag_le H A α.val α.val le_rfl]
  simp only [ite_true]
  obtain ⟨hpos, hle⟩ := normalizedChartDiagonal_pos_le_one H hH α.val
  exact ⟨hpos.ne', (abs_of_pos hpos).trans_le hle⟩

theorem normalizedChartCoefficientMatrix_coeff_aeval
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (slow : MvPolynomial (U ⊕ V) ℝ)
    (hsupport : slow.support ⊆ S) (β : S) :
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A) slow).coeff β.val =
      ∑ α : S, normalizedChartCoefficientMatrix H A S β α * slow.coeff α.val := by
  classical
  unfold normalizedChartCoefficientMatrix
  conv_lhs => rw [← polynomialOfFiniteCoefficientVector_reconstruct S slow hsupport]
  rw [polynomialOfFiniteCoefficientVector, map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro α _
  simp only [aeval_monomial, MvPolynomial.algebraMap_eq, map_one, one_mul, coeff_C_mul]
  exact mul_comm _ _

theorem normalizedChartCorrectionSolutions_coefficients
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ) (B : ℝ) (q : ℕ)
    (sr : MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℚ)
    (hsr : sr ∈ normalizedChartCorrectionSolutions H A S P B q) :
    ((fun α : S => sr.1.coeff α.val), (fun α : S => sr.2.coeff α.val)) ∈
      finiteRankCorrectionSolutions (normalizedChartCoefficientMatrix H A S)
        (fun α : S => P.coeff α.val) B q := by
  classical
  rcases hsr with ⟨hslow, _, hbound, hgrid, hidentity⟩
  refine ⟨fun α => hbound α.val, fun α => hgrid α.val, ?_⟩
  intro β
  have heq := congrArg (fun polynomial : MvPolynomial (U ⊕ V) ℝ => polynomial.coeff β.val) hidentity
  rw [MvPolynomial.coeff_add, coeff_map,
    normalizedChartCoefficientMatrix_coeff_aeval H A S sr.1 hslow β] at heq
  exact heq

theorem exists_finite_normalized_chart_corrections
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q) :
    ∃ m : ℕ, m ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ S.card ∧
      ∃ candidate : Fin m → (MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℚ),
        (∀ j, candidate j ∈ normalizedChartCorrectionSolutions H A S P B q) ∧
        ∀ sr, sr ∈ normalizedChartCorrectionSolutions H A S P B q →
          ∃ j, candidate j = sr := by
  classical
  let rank := fun α : S => Finsupp.weight normalizedChartTagWeight α.val
  obtain ⟨n, hn, vectors, _, hcover⟩ :=
    exists_finite_rank_triangular_correction_enumeration q hq B hB rank
      (normalizedChartCoefficientMatrix H A S) (fun α : S => P.coeff α.val)
      (normalizedChartCoefficientMatrix_triangular H A S)
      (fun α => (normalizedChartCoefficientMatrix_diagonal H hH A S α).1)
      (fun α => (normalizedChartCoefficientMatrix_diagonal H hH A S α).2)
  let polynomials := fun j : Fin n =>
    (polynomialOfFiniteCoefficientVector S (vectors j).1,
      polynomialOfFiniteCoefficientVector S (vectors j).2)
  have hpolynomials (sr) (hsr : sr ∈ normalizedChartCorrectionSolutions H A S P B q) :
      ∃ j, polynomials j = sr := by
    obtain ⟨j, hj⟩ := hcover _
      (normalizedChartCorrectionSolutions_coefficients H A S P B q sr hsr)
    refine ⟨j, ?_⟩
    dsimp only [polynomials]
    rw [hj]
    exact Prod.ext (polynomialOfFiniteCoefficientVector_reconstruct S sr.1 hsr.1)
      (polynomialOfFiniteCoefficientVector_reconstruct S sr.2 hsr.2.1)
  obtain ⟨m, hm, candidate, hvalid, _, hcomplete⟩ :=
    exists_filtered_finite_enumeration polynomials
      (fun sr => sr ∈ normalizedChartCorrectionSolutions H A S P B q)
  refine ⟨m, ?_, candidate, hvalid, ?_⟩
  · exact hm.trans (by simpa only [Fintype.card_coe] using hn)
  · intro sr hsr
    exact hcomplete sr hsr (hpolynomials sr hsr)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedMixedLiftNormalizedMass
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial

theorem scaleMvPolynomialAxes_neg {V : Type*} (T : V → ℝ) (p : MvPolynomial V ℝ) :
    scaleMvPolynomialAxes T (-p) = -scaleMvPolynomialAxes T p := by
  ext α
  simp only [scaleMvPolynomialAxes_coeff, coeff_neg, neg_mul]

theorem normalizedPolynomialMass_neg {V : Type*} (p : MvPolynomial V ℝ) :
    realPolynomialMass (-p) = realPolynomialMass p := by
  simp only [realPolynomialMass, support_neg, coeff_neg, abs_neg]

theorem normalizedAxes_homogeneousComponent_commute {V : Type*}
    (T : V → ℝ) (w : V → ℕ) (n : ℕ) (p : MvPolynomial V ℝ) :
    scaleMvPolynomialAxes T (weightedHomogeneousComponent w n p) =
      weightedHomogeneousComponent w n (scaleMvPolynomialAxes T p) := by
  classical
  ext α
  simp only [scaleMvPolynomialAxes_coeff, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem normalizedMass_homogeneousComponent_projection_le {V : Type*}
    (w : V → ℕ) (n : ℕ) (p : MvPolynomial V ℝ) :
    realPolynomialMass (weightedHomogeneousComponent w n p) ≤ realPolynomialMass p := by
  classical
  have hs : (weightedHomogeneousComponent w n p).support ⊆ p.support := by
    intro α hα
    rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hα
    split_ifs at hα with h
    · exact mem_support_iff.mpr hα
    · exact False.elim (hα rfl)
  rw [realPolynomialMass_eq_sum_of_support_subset _ _ hs]
  apply Finset.sum_le_sum
  intro α _
  rw [coeff_weightedHomogeneousComponent]
  split_ifs <;> simp only [le_refl, abs_zero, abs_nonneg]

theorem normalizedMass_neg_weightedHomogeneousComponent_le {V : Type*}
    (T : V → ℝ) (w : V → ℕ) (n : ℕ) (p : MvPolynomial V ℝ) :
    realPolynomialMass (scaleMvPolynomialAxes T (-weightedHomogeneousComponent w n p)) ≤
      realPolynomialMass (scaleMvPolynomialAxes T p) := by
  rw [scaleMvPolynomialAxes_neg, normalizedPolynomialMass_neg,
    normalizedAxes_homogeneousComponent_commute]
  exact normalizedMass_homogeneousComponent_projection_le w n _

end Erdos3

end

section

namespace Erdos3
open Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedLiftPolynomial_scaled_coefficients [Fintype V]
    (e : J → V →₀ ℕ) (he : Function.Injective e)
    (a : (I → J → ℝ) × (Fin n → J → ℤ))
    (T : V → ℝ) (hT : ∀ v, 0 < T v) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hc : ∀ i j, |a.1 i j| * monomialScale T (e j) ≤ R)
    (hz : ∀ i j, |(a.2 i j : ℝ) / basisAxisScale b i| * monomialScale T (e j) ≤ R)
    (α : V →₀ ℕ) (d : D) :
    |(mixedLiftPolynomial W b o e a d).coeff α| ≤
      C * (((Fintype.card I : ℝ) + 1) * R) / monomialScale T α := by
  apply mixedLiftPolynomial_coefficient_bound W b o e he a T hT (by positivity)
  intro j d
  exact mixedRealPoint_scaled_coordinate_bound W b o hC hR
    (monomialScale_pos T hT (e j)) hchart _ _ (fun i => hc i j) (fun i => hz i j) d

variable [Fintype V]

theorem mixedLiftPolynomial_scaled_mass
    (e : J → V →₀ ℕ) (he : Function.Injective e)
    (a : (I → J → ℝ) × (Fin n → J → ℤ))
    (T : V → ℝ) (hT : ∀ v, 0 < T v) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hc : ∀ i j, |a.1 i j| * monomialScale T (e j) ≤ R)
    (hz : ∀ i j, |(a.2 i j : ℝ) / basisAxisScale b i| * monomialScale T (e j) ≤ R)
    {s : ℕ} (hdegree : ∀ j, (e j).sum (fun _ k => k) ≤ s) (d : D) :
    realPolynomialMass (scaleMvPolynomialAxes T (mixedLiftPolynomial W b o e a d)) ≤
      ((s + 1 : ℕ) : ℝ) * ((Fintype.card V + 1 : ℕ) : ℝ) ^ s *
        (C * (((Fintype.card I : ℝ) + 1) * R)) := by
  apply (scaleMvPolynomialAxes_mass_le T hT _
    (fun α => mixedLiftPolynomial_scaled_coefficients W b o e he a T hT hC hR
      hchart hc hz α d)).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast polynomial_support_card_le _ (mixedLiftPolynomial_degree W b o e a hdegree d)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

include hσ1 hC hchart

theorem allocatedLayerSupported_normalized_mass (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (i : J j) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val a i)) ≤
      ((j.val + 2 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ (j.val + 1) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have hs := (allocatedArraySupported_iff_rows Subtype.val (layerSamplerBox B U b S)
    (layerContinuousPrincipalSlots B j) (constantCoefficientSlot _ _) (R j) (σ j)
    (allocatedLayerIntegerPMFs B U b hR hσ S j) a).mp ha
  apply mixedLiftPolynomial_scaled_mass (euclideanSubspace (U j)) (b j) (o j)
    Subtype.val Subtype.val_injective a _ hT (hC j) (hR j).le (hchart j)
  · intro k d
    exact continuousPolynomialDensity_coefficient_le_radius Subtype.val _ hT _ _
      (layerContinuousPrincipalSlots_not_constant B j k) (hR j) (hσ j) (hσ1 j) (hs.1 k) d
  · intro k d
    exact allocatedIntegerCoefficient_le_radius
      (layerIntegerPrincipalSlots B j k) (constantCoefficientSlot _ _)
      (j.val + 1) (basisAxisScale (b j) k) S.value (layerTailDegree m) (Nat.zero_lt_succ _)
      (basisAxisScale_pos (b j) k) S.positive (layerSamplerBox B U b S) hT
      (layerSamplerBox_le B U b S) Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (hσ1 j) (S.gap j k) (S.width j)
      (layerIntegerPrincipalSlots_not_constant B j k) rfl
      (layerSamplerSides_integer_principal B U b R S.value j k) d (hs.2 k d)
  · intro d
    exact d.property

theorem allocatedLayerSupported_normalized_mass_uniform
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (i : J j) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val a i)) ≤
      ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
  apply (allocatedLayerSupported_normalized_mass B U b o hR hσ S hσ1 C hC hchart j a ha i).trans
  calc
    _ ≤ ((j.val + 2 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ (j.val + 1) * 1 :=
      mul_le_mul_of_nonneg_left (hsmall j) (by positivity)
    _ ≤ ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
      rw [mul_one]
      apply mul_le_mul
      · exact_mod_cast (show j.val + 2 ≤ m + 1 by omega)
      · exact pow_le_pow_right₀ (by norm_cast; omega) (by omega)
      · positivity
      · positivity

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SharedWidthAllocatedDetectedSpatialNativeSourceGeneral
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable abbrev allocatedDetectedGain (s variableCount : ℕ)
    (Pdetect : Polynomial ℕ) (p q α : ℝ) : ℝ :=
  (Real.exp (-((5 * p + 20) * variableCount + p + 2)) * (α / 2)) *
    Real.exp (-((q + sampledSupportedSlicedDetectionConstant s Pdetect) ^
      sampledSupportedSlicedDetectionConstant s Pdetect)) ^ (2 ^ (s + 1))

noncomputable abbrev allocatedDetectedKernelCutoff (s : ℕ) (G : Type) [Fintype G]
    (variableCount : ℕ) (Pdetect : Polynomial ℕ) (p q α : ℝ) : ℕ :=
  scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
    (allocatedDetectedGain s variableCount Pdetect p q α / 2)

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (pDetect qDetect α : ℝ)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (pDetect qDetect α : ℝ)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralProductivityEarlyGain
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (pDetect qDetect α : ℝ)
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

structure AllocatedEarlyNativeSourceGeometryGeneral
    (Pchart P D target Pk Prho Qstride pDetect : ℝ) (K : ℝ≥0) where
  hP : 0 ≤ P
  hRP : ∀ j, R j ≤ Real.exp P
  hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P
  hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P
  hcount : ∀ j : Fin m, (Fintype.card
    (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P
  hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D
  hPk : 0 ≤ Pk
  hPrho : 0 ≤ Prho
  htarget : 0 ≤ target
  hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target (pDetect + 1)
    (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value
  η : ℝ
  hη0 : 0 ≤ η
  hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4))
  ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0
  t : ℝ
  htone : t ≤ 1
  hs : AllocatedAffineCoveredComparison.{0, 0, _, _, _, _, _} (G := G) B rows
    (Real.exp (-(pDetect + 1))) η ρ t htone
  hρ : ∀ partition, 0 < ρ partition
  hρ1 : ∀ partition, ρ partition ≤ 1
  hρlog : ∀ partition, (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho
  hσsmall : ∀ j, σ j ≤ t
  T : Fin m → ℝ
  hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j
  hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
        ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j
  siteRadius : ℝ≥0
  hrone : 1 ≤ siteRadius
  hradius : ∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)
  hbudgets : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp Pchart) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
    (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
    (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)
  hK : ∀ j, (R j)⁻¹ ≤ K

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorGeometricBoundsGeneral
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))

theorem preparedModularGeneralDetector_variable_count {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) :
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * D := by
  change ((Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n))) : ℝ) ≤ _
  rw [Fintype.card_sum, Nat.cast_add]
  linarith [hdim.kernel_variables, hdim.tuples]

theorem preparedModularGeneralDetector_layer_axes {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) :
    (∀ j, (Fintype.card (I j) : ℝ) ≤ D) ∧ (∀ j, (n j : ℝ) ≤ D) := by
  constructor
  · intro j
    have hcard : Fintype.card (I j) ≤ Fintype.card (LayerSamplerAxis I n) :=
      Fintype.card_le_of_injective (fun i : I j => (⟨j, Sum.inl i⟩ : LayerSamplerAxis I n))
        (by intro x y h; exact Sum.inl_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
    exact (Nat.cast_le.mpr hcard).trans hdim.axes

  · intro j
    have hcard : Fintype.card (Fin (n j)) ≤ Fintype.card (LayerSamplerAxis I n) :=
      Fintype.card_le_of_injective (fun i : Fin (n j) => (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n))
        (by intro x y h; exact Sum.inr_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
    rw [Fintype.card_fin] at hcard
    exact (Nat.cast_le.mpr hcard).trans hdim.axes

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem preparedModularGeneralDetector_physical_root {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hDP : D ≤ P) (hS : (S.value : ℝ) ≤ Real.exp P) :
    allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ Real.exp (2 * P + 8) := by
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * P :=
    (preparedModularGeneralDetector_variable_count B rowSets hdim).trans (by linarith)
  have hvarsExp : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp (P + 8) := by
    calc
      _ ≤ 2 * P := hvars
      _ ≤ Real.exp 8 * Real.exp P := mul_le_mul
        (by linarith [Real.add_one_le_exp (8 : ℝ)])
        (by linarith [Real.add_one_le_exp P]) hP (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  rw [allocatedPhysicalRootBudget_zero]
  calc
    _ ≤ Real.exp (P + 8) * Real.exp P :=
      mul_le_mul hvarsExp hS (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedModularGeneralDetectorSamplingBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m dim nX : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {T : Type*} [Fintype T] (stride : Fin nX → ℕ)

structure PreparedModularGeneralDetectorSamplingBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) (P L target Pphysical Qstride Pk : ℝ) : Prop where
  sample_nonneg : 0 ≤ r.Psample
  mass_nonneg : 0 ≤ r.Pmass
  projection_one : 1 ≤ r.Pproj
  primitive_projection : P ≤ r.Pproj
  late_projection : L ≤ r.Pproj
  gain_projection : P + 32 ≤ r.Pproj
  period_projection : ((m + 1 : ℕ) : ℝ) * Pk ≤ r.Pproj
  profile_projection : (probabilityProfileLipschitz : ℝ) ≤ Real.exp r.Pproj
  projection_mass : r.Pproj ≤ r.Pmass
  mass_sample : r.Pmass ≤ r.Psample
  cover_base : r.coverLog ≤ r.baseAmbient
  cover_sample : r.coverLog ≤ r.Psample
  ambient_sample : r.ambient ≤ r.Psample
  sample_side : r.Psample ≤ r.Pside
  projection_side : r.Pproj ≤ r.Pside
  mass_side : r.Pmass ≤ r.Pside
  primitive_side : P ≤ r.Pside
  late_side : L ≤ r.Pside
  physical_side : Pphysical ≤ r.Pside
  target_side : target ≤ r.Pside
  X_sample : (Fintype.card (Fin nX) : ℝ) ≤ r.Psample
  frame_sample : (Fintype.card (Option (Fin dim) × Fin nX) : ℝ) ≤ r.Psample
  ambient_dimension_sample : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ r.Psample
  jet_sample : ((∑ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.Psample
  stride_scale_nonneg : 0 ≤ Real.exp Qstride
  stride_scale_sample : Real.exp Qstride ≤ Real.exp r.Psample
  stride_sample : ∀ i, (stride i : ℝ) ≤ Real.exp r.Psample
  tau_pos : 0 < Real.exp (-Pphysical)
  precision_pos : 0 < Real.exp (-target)
  tau_sample : 1 / Real.exp (-Pphysical) ≤ Real.exp r.Psample
  epsilon_sample : 1 / Real.exp (-target) ≤ Real.exp r.Psample
  eta_sample : (Real.exp (-target))⁻¹ ≤ Real.exp r.Psample
  X_mass : (Fintype.card (Fin nX) : ℝ) ≤ r.Pmass
  frame_mass : (Fintype.card (Option (Fin dim) × Fin nX) : ℝ) ≤ r.Pmass
  ambient_dimension_mass : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ r.Pmass
  jet_mass : ((∑ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.Pmass
  stride_mass : ∀ i, (stride i : ℝ) ≤ Real.exp r.Pmass
  tau_mass : 1 / Real.exp (-Pphysical) ≤ Real.exp r.Pmass
  X_projection : (Fintype.card (Fin nX) : ℝ) ≤ r.Pproj
  variables_projection : (Fintype.card T : ℝ) ≤ r.Pproj
  frame_projection : (Fintype.card (Option T × Fin nX) : ℝ) ≤ r.Pproj
  stride_projection : ∀ i, (stride i : ℝ) ≤ Real.exp r.Pproj
  tau_projection : (Real.exp (-Pphysical))⁻¹ ≤ Real.exp r.Pproj

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularGeneralDetectorFreeSpatialBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

structure PreparedModularGeneralDetectorFreeSpatialBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) (τ : ℝ) : Prop where
  tau_pos : 0 < τ
  tau_sample : 1 / τ ≤ Real.exp r.Psample
  tau_mass : 1 / τ ≤ Real.exp r.Pmass
  tau_projection : τ⁻¹ ≤ Real.exp r.Pproj
  tau_native : τ⁻¹ ≤ Real.exp r.Pnative
  tau_side : τ⁻¹ ≤ Real.exp r.Pside

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelPrincipalFiberSliceLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G D : Type*} [Fintype G] [DecidableEq G] [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (LG : G → ℕ) (L : PrincipalTupleIndex B h → ℕ)

def kernelZeroTupleFromSumIntegerBox
    (z : integerBox (Sum.elim LG L)) : ∀ g, IntegerScalarCubeBox Empty (LG g) :=
  fun g _ => ⟨z.val (Sum.inl g), Finset.mem_Ico.mpr
    ⟨(neg_nonpos.mpr (Int.natCast_nonneg _)).trans
      ((mem_integerBox (Sum.elim LG L) z.val).mp z.property (Sum.inl g)).1,
      ((mem_integerBox (Sum.elim LG L) z.val).mp z.property (Sum.inl g)).2⟩⟩

def principalZeroTupleFromSumIntegerBox
    (z : integerBox (Sum.elim LG L)) : PrincipalIntegerTuples B h Empty L :=
  fun j _ => ⟨z.val (Sum.inr j), Finset.mem_Ico.mpr
    ⟨(neg_nonpos.mpr (Int.natCast_nonneg _)).trans
      ((mem_integerBox (Sum.elim LG L) z.val).mp z.property (Sum.inr j)).1,
      ((mem_integerBox (Sum.elim LG L) z.val).mp z.property (Sum.inr j)).2⟩⟩

namespace ResidueBoxSlice

variable {B h LG L}
variable {keep : G ⊕ PrincipalTupleIndex B h → Prop} [DecidablePred keep] {q : ℕ}
variable (S : ResidueBoxSlice (fun k : {k // keep k} => Sum.elim LG L k.val) q)
variable (hlen : ∀ k, 0 < S.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < ((Sum.elim LG L k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

include hlen hfixed in
theorem fiberPrincipalParameter_inside (j : PrincipalTupleIndex B h)
    (t : Fin (S.fiberParameterLength (Sum.inr j))) :
    0 ≤ S.fiberParameterStart fixed (Sum.inr j) +
      (fiberParameterStride (keep := keep) (q := q) (Sum.inr j) : ℤ) * t.val ∧
      S.fiberParameterStart fixed (Sum.inr j) +
        (fiberParameterStride (keep := keep) (q := q) (Sum.inr j) : ℤ) * t.val < L j :=
  S.fiberParameter_inside hlen fixed hfixed (Sum.inr j) t

end ResidueBoxSlice
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedDenseFiberSliceForecastGeometry
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

theorem denseCoordinate_geometry {X : Type*} {N : X → ℕ} {q : ℕ}
    (S : ResidueBoxSlice N q) (i : X) {cost : ℝ}
    (hq : 0 < q) (hN : 0 < N i)
    (hdense : Real.exp (-cost) * (N i : ℝ) ≤ S.length i)
    (hfloor : 2 ≤ Real.exp (-cost) * (N i : ℝ)) :
    2 ≤ S.length i ∧
      0 ≤ (S.start i : ℝ) / N i ∧
      Real.exp (-cost) / 2 ≤ (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i ∧
      (S.start i : ℝ) / N i +
        (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i < 1 ∧
      (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i ≤ 1 ∧
      (q : ℝ) ≤ 2 * Real.exp cost := by
  have hlenR : (2 : ℝ) ≤ S.length i := hfloor.trans hdense
  have hlen : 2 ≤ S.length i := by exact_mod_cast hlenR
  have hinside (t : Fin (S.length i)) :
      0 ≤ (S.start i : ℤ) + (q : ℤ) * (t.val : ℤ) ∧
      (S.start i : ℤ) + (q : ℤ) * (t.val : ℤ) < N i := by
    constructor
    · positivity
    · exact_mod_cast S.inside i t.val t.isLt
  have hbounds := affineInterval_normalized_bounds hN hlen hq hinside
  have hNR : (0 : ℝ) < N i := by exact_mod_cast hN
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsub : ((S.length i - 1 : ℕ) : ℝ) = (S.length i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hhalf : Real.exp (-cost) * (N i : ℝ) / 2 ≤
      ((S.length i - 1 : ℕ) : ℝ) := by
    rw [hsub]
    linarith
  have hscaled : (q : ℝ) * Real.exp (-cost) / 2 ≤
      (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i := by
    apply (le_div_iff₀ hNR).mpr
    have h := mul_le_mul_of_nonneg_left hhalf hq0
    nlinarith
  have hwidth : Real.exp (-cost) / 2 ≤
      (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i := by
    calc
      Real.exp (-cost) / 2 ≤ (q : ℝ) * Real.exp (-cost) / 2 := by
        nlinarith [Real.exp_pos (-cost)]
      _ ≤ _ := hscaled
  have hprod : (q : ℝ) * Real.exp (-cost) ≤ 2 := by
    linarith [hscaled.trans hbounds.2.2.2]
  have hcancel : Real.exp (-cost) * Real.exp cost = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hstep : (q : ℝ) ≤ 2 * Real.exp cost := by
    calc
      (q : ℝ) = ((q : ℝ) * Real.exp (-cost)) * Real.exp cost := by
        rw [mul_assoc, hcancel, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod (Real.exp_pos cost).le
  exact ⟨hlen, by simpa only [Int.cast_natCast] using hbounds.1, hwidth,
    by simpa only [Int.cast_natCast] using hbounds.2.2.1, hbounds.2.2.2, hstep⟩

theorem fiberParameterStride_le {X : Type*} {keep : X → Prop}
    [DecidablePred keep] {q : ℕ} (i : X) :
    fiberParameterStride (keep := keep) (q := q) i ≤ q := by
  unfold fiberParameterStride
  split <;> omega

theorem fiberParameter_dense_of_keep {X : Type*} {keep : X → Prop}
    [DecidablePred keep] {N : X → ℕ} {q : ℕ}
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    {density : ℝ} (hdense : ∀ k, density * (N k.val : ℝ) ≤ S.length k)
    (hq : 0 < q) (i : X) (hi : keep i) :
    density * (N i : ℝ) ≤ S.fiberParameterLength i ∧
      0 < fiberParameterStride (keep := keep) (q := q) i := by
  constructor
  · rw [fiberParameterLength_of_keep S i hi]
    exact hdense ⟨i, hi⟩
  · simpa only [fiberParameterStride, if_pos hi] using hq

theorem fiberParameter_regular_of_threshold {X Y : Type*} {keep : X → Prop}
    [DecidablePred keep] {N : X → ℕ} {q H : ℕ}
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    {density : ℝ} (hdense : ∀ k, density * (N k.val : ℝ) ≤ S.length k)
    (hq : 0 < q) (hkeep : ∀ i, H ≤ N i → keep i) (index : Y → X) :
    (∃ y, N (index y) < H) ∨
      ((∀ y, density * (N (index y) : ℝ) ≤ S.fiberParameterLength (index y)) ∧
        ∀ y, 0 < fiberParameterStride (keep := keep) (q := q) (index y)) := by
  classical
  by_cases hsmall : ∃ y, N (index y) < H
  · exact Or.inl hsmall
  · right
    have hret (y : Y) : keep (index y) :=
      hkeep (index y) (Nat.le_of_not_gt fun h => hsmall ⟨y, h⟩)
    exact ⟨fun y => (S.fiberParameter_dense_of_keep hdense hq (index y) (hret y)).1,
      fun y => (S.fiberParameter_dense_of_keep hdense hq (index y) (hret y)).2⟩

theorem fiberParameter_dense_geometry {X : Type*} {keep : X → Prop}
    [DecidablePred keep] {N : X → ℕ} {q : ℕ}
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ) (i : X) (hi : keep i) {cost : ℝ}
    (hq : 0 < q) (hN : 0 < N i)
    (hdense : Real.exp (-cost) * (N i : ℝ) ≤ S.length ⟨i, hi⟩)
    (hfloor : 2 ≤ Real.exp (-cost) * (N i : ℝ)) :
    let lower := (S.fiberParameterStart fixed i : ℝ) / N i
    let width := (fiberParameterStride (keep := keep) (q := q) i : ℝ) *
      ((S.fiberParameterLength i - 1 : ℕ) : ℝ) / N i
    2 ≤ S.fiberParameterLength i ∧ 0 ≤ lower ∧
      Real.exp (-cost) / 2 ≤ width ∧ lower + width < 1 ∧
      |lower| + |width| ≤ 1 := by
  dsimp only
  simp only [fiberParameterLength, fiberParameterStart, fiberParameterStride,
    dif_pos hi, if_pos hi, Int.cast_natCast]
  have h := S.denseCoordinate_geometry ⟨i, hi⟩ hq hN hdense hfloor
  have hw : 0 ≤ (q : ℝ) * ((S.length ⟨i, hi⟩ - 1 : ℕ) : ℝ) / N i :=
    (by positivity : (0 : ℝ) ≤ Real.exp (-cost) / 2).trans h.2.2.1
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  rw [abs_of_nonneg h.2.1, abs_of_nonneg hw]
  exact h.2.2.2.1.le

end Erdos3.ResidueBoxSlice

end

end OAI

end


