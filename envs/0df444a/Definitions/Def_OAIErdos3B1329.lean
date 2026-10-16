-- Prove2me | Definitions.Def_OAIErdos3B1329
-- name    : OAIErdos3B1329
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T20:11:43.351795+00:00
-- url     : https://prove2.me/theorems/7b692930-a83f-4a1b-8d9c-d7284e42432a
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1330 of 1352
-- statement:
--   Definitions bundle 1330 of 1352 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1328`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1330 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.slicedComparisonSourceLog`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.slicedGeometryDimension`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.slicedGeometryRadiusLog`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.comparisonGridLog`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_normalized_top_tag`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_polynomial_remainder`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_remainder_at_site`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_torus_dist`, `OAI.Erdos3.VectorPolynomial.PreparedActualForecastShortIndex`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedActualForecastShortSelection_nonempty`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSamplerBlock_four`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSamplerBlock_single_uniform`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSamplerBlock_transverse_uniform`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSampler_block_sum_le_principal_card`, `OAI.Erdos3.VectorPolynomial.exists_allocated_centered_spatial_matrix_exceptional`, `OAI.Erdos3.VectorPolynomial.exists_preparedCenteredShortProbability_badProduct`, `OAI.Erdos3.VectorPolynomial.exists_preparedCentered_short_measurableBadProduct`, `OAI.Erdos3.VectorPolynomial.layerSampler_block_sum_le_principal_card`, `OAI.Erdos3.VectorPolynomial.physicalGridFactorInput_dist_le_of_integer_remainders`, `OAI.Erdos3.VectorPolynomial.preparedActualForecastGridVolume`, `OAI.Erdos3.VectorPolynomial.preparedActualForecastGridVolume_mul_active_heights`, `OAI.Erdos3.VectorPolynomial.preparedActualForecastGridVolume_one_le`, `OAI.Erdos3.VectorPolynomial.preparedActualForecastGridVolume_pos`, `OAI.Erdos3.VectorPolynomial.preparedActualForecastJacobian_eq_ratio`, `OAI.Erdos3.VectorPolynomial.preparedActualForecastJacobian_ratio_budget`, `OAI.Erdos3.VectorPolynomial.preparedActualForecastJacobian_ratio_le_exp`, `OAI.Erdos3.VectorPolynomial.preparedActualForecastJacobian_ratio_uniform_le_exp`, `OAI.Erdos3.VectorPolynomial.preparedActualForecastSetup`, `OAI.Erdos3.VectorPolynomial.preparedActualForecastShortSelection`, `OAI.Erdos3.VectorPolynomial.preparedActualForecastShortSelection_exhaustive`, `OAI.Erdos3.VectorPolynomial.preparedActualForecastShortSelection_injective`, `OAI.Erdos3.VectorPolynomial.preparedActualForecastShortSelection_small`, `OAI.Erdos3.VectorPolynomial.preparedActualForecast_radius_bounds`, `OAI.Erdos3.VectorPolynomial.preparedCenteredMarginalExponent`, `OAI.Erdos3.VectorPolynomial.preparedForecastGridVolume`, `OAI.Erdos3.aeval_frozen_integer_top`, `OAI.Erdos3.normalizedRealPolynomialChart_top_inr`, `OAI.Erdos3.principalTupleIndex_block_sum_le_card`, `OAI.Erdos3.spatialMatrixBlock_joint_tilted_cutoff_bound`, `OAI.Erdos3.spatialMatrixBlock_joint_tilted_cutoff_bound_complex`, `OAI.Erdos3.unitCircle_dist_div_integer_parts`, `_private.Sampling.PreparedActualForecastSetup.0.OAI.Erdos3.VectorPolynomial.forecastRows_one_le`, `_private.Sampling.PreparedActualForecastSetup.0.OAI.Erdos3.VectorPolynomial.ratioJacobian_product_le_exp`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1328
import Definitions.Def_OAIErdos3B1330

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedPrimitiveGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

namespace ActualFixedSpatialForecastSetup
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)

noncomputable def slicedGeometryDimension : ℝ := s.P + (layerTailDegree m + 1 : ℕ) + 1
noncomputable def slicedGeometryRadiusLog : ℝ := s.P + s.Pscale

end ActualFixedSpatialForecastSetup
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem enlargedPreparedCommonSamplerBlock_single_uniform (Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    uniformSpectrumBlockCount a.1.val 1 (a.1.val + 1) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  have hrows : 1 ≤ (boundedBooleanJetRows (Fin 1) (a.1.val + 1)).card := by
    apply Nat.succ_le_of_lt
    apply Finset.card_pos.mpr
    refine ⟨∅, ?_⟩
    simp only [mem_boundedBooleanJetRows, Finset.card_empty, Nat.zero_le]
  apply le_trans _ (enlargedPreparedCommonSamplerBlock_uniform L Jalloc 0
    (Nat.zero_le m) a)
  unfold uniformSpectrumBlockCount majorArcSpectrumExponent majorArcCoverExponent
  gcongr
  simpa only [mul_one] using Nat.mul_le_mul_left (a.1.val + 1) hrows

theorem enlargedPreparedCommonSamplerBlock_four (Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    4 ≤ Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  apply le_trans _ (enlargedPreparedCommonSamplerBlock_single_uniform L Jalloc a)
  unfold uniformSpectrumBlockCount majorArcSpectrumExponent majorArcCoverExponent
    majorArcErrorExponent
  simp only [mul_one]
  omega

theorem enlargedPreparedCommonSamplerBlock_transverse_uniform (Jalloc : ℕ)
    (j : Fin m) (i : Fin (preparedSamplerTransverse L j)) :
    uniformSpectrumBlockCount j.val 1 (j.val + 1) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc ⟨j, Sum.inr i⟩) :=
  enlargedPreparedCommonSamplerBlock_single_uniform L Jalloc ⟨j, Sum.inr i⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators

theorem principalTupleIndex_block_sum_le_card {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (degree : D → ℕ)
    (hdegree : ∀ d, 1 ≤ degree d) :
    (∑ d, Fintype.card (B d)) ≤ Fintype.card (PrincipalTupleIndex B degree) := by
  simp only [PrincipalTupleIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  apply Finset.sum_le_sum
  intro d _
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (Fintype.card (B d)) (hdegree d)

namespace VectorPolynomial

theorem layerSampler_block_sum_le_principal_card {m : ℕ}
    (I : Fin m → Type*) [∀ j, Fintype (I j)] (n : Fin m → ℕ)
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] :
    (∑ a, Fintype.card (B a)) ≤
      Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) :=
  principalTupleIndex_block_sum_le_card B (layerSamplerDegree I n)
    (fun _ => Nat.succ_le_succ (Nat.zero_le _))

theorem enlargedPreparedCommonSampler_block_sum_le_principal_card
    {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m) (Jalloc : ℕ) :
    (∑ a, Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a)) ≤
      Fintype.card (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock L Jalloc)
        (layerSamplerDegree (PreparedSamplerContinuous L) (preparedSamplerTransverse L))) :=
  layerSampler_block_sum_le_principal_card (PreparedSamplerContinuous L)
    (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

section Generic

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

abbrev PreparedActualForecastShortIndex := AllocatedShortIntegerAxis U b S.value

def preparedActualForecastShortSelection :
    PreparedActualForecastShortIndex B U b S → Σ j : Fin m, Fin (n j) :=
  Subtype.val

theorem preparedActualForecastShortSelection_injective :
    Function.Injective (preparedActualForecastShortSelection B U b S) :=
  Subtype.val_injective

theorem preparedActualForecastShortSelection_small
    (a : PreparedActualForecastShortIndex B U b S) :
    basisAxisScale (b (preparedActualForecastShortSelection B U b S a).1)
      (preparedActualForecastShortSelection B U b S a).2 ≤
      S.value ^ ((preparedActualForecastShortSelection B U b S a).1.val + 1) :=
  a.property

theorem preparedActualForecastShortSelection_exhaustive
    (a : LayerSamplerAxis I n) (ha : allocatedShortAxis U b S.value a) :
    ∃ i : PreparedActualForecastShortIndex B U b S,
      (⟨(preparedActualForecastShortSelection B U b S i).1,
        Sum.inr (preparedActualForecastShortSelection B U b S i).2⟩ :
          LayerSamplerAxis I n) = a := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl a => exact False.elim ha
  | inr a => exact ⟨⟨⟨j, a⟩, ha⟩, rfl⟩

end Generic

section Prepared

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m) (Jalloc : ℕ)
variable {G : Type*} [Fintype G]
variable {Jout : Fin m → Type*} [∀ j, Fintype (Jout j)]
variable (U : ∀ j, Submodule ℝ (Jout j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
  (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale (G := G) (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)

theorem enlargedPreparedActualForecastShortSelection_nonempty
    (a : PreparedActualForecastShortIndex (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S) :
    Nonempty (EnlargedPreparedCommonSamplerBlock L Jalloc
      ⟨(preparedActualForecastShortSelection (EnlargedPreparedCommonSamplerBlock L Jalloc)
        U b S a).1,
        Sum.inr (preparedActualForecastShortSelection
          (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S a).2⟩) :=
  Fintype.card_pos_iff.mp (enlargedPreparedCommonSamplerBlock_positive L Jalloc _)

end Prepared

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical BigOperators

section Grid

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def preparedActualForecastGridVolume : ℝ :=
  ∏ a : PreparedActualForecastShortIndex B U b S,
    (basisAxisScale (b (preparedActualForecastShortSelection B U b S a).1)
      (preparedActualForecastShortSelection B U b S a).2 : ℝ)

theorem preparedActualForecastGridVolume_one_le :
    1 ≤ preparedActualForecastGridVolume B U b S := by
  unfold preparedActualForecastGridVolume
  apply Finset.one_le_prod
  intro a _
  exact_mod_cast basisAxisScale_pos
    (b (preparedActualForecastShortSelection B U b S a).1)
    (preparedActualForecastShortSelection B U b S a).2

theorem preparedActualForecastGridVolume_pos :
    0 < preparedActualForecastGridVolume B U b S :=
  lt_of_lt_of_le zero_lt_one (preparedActualForecastGridVolume_one_le B U b S)

end Grid

section EnlargedPrepared

variable {m : ℕ} {X₀ J₀ : Type}
variable (prep : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ
  (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock prep Jalloc) U b R σ)

noncomputable abbrev preparedForecastGridVolume : ℝ :=
  preparedActualForecastGridVolume (EnlargedPreparedCommonSamplerBlock prep Jalloc) U b S

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]

end EnlargedPrepared

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem preparedActualForecastGridVolume_mul_active_heights :
    preparedActualForecastGridVolume B U b S *
      (∏ a : AllocatedActiveIntegerAxis U b S.value,
        (basisAxisScale (b a.val.1) a.val.2 : ℝ)) =
      ∏ j : Fin m, ∏ i : Fin (n j), (basisAxisScale (b j) i : ℝ) := by
  let p : (Σ j : Fin m, Fin (n j)) → Prop :=
    fun a => basisAxisScale (b a.1) a.2 ≤ S.value ^ (a.1.val + 1)
  let activeEquiv : {a // ¬p a} ≃ AllocatedActiveIntegerAxis U b S.value :=
    { toFun := fun a => ⟨a.val, Nat.lt_of_not_ge a.property⟩
      invFun := fun a => ⟨a.val, Nat.not_le.mpr a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hactive : (∏ a : {a // ¬p a}, (basisAxisScale (b a.val.1) a.val.2 : ℝ)) =
      ∏ a : AllocatedActiveIntegerAxis U b S.value,
        (basisAxisScale (b a.val.1) a.val.2 : ℝ) :=
    Fintype.prod_equiv activeEquiv _ _ (fun _ => rfl)
  have h := Fintype.prod_subtype_mul_prod_subtype p
    (fun a : Σ j : Fin m, Fin (n j) => (basisAxisScale (b a.1) a.2 : ℝ))
  rw [hactive, Fintype.prod_sigma] at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped Classical BigOperators

section Generic
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {X : Type*} [Fintype X]

theorem preparedActualForecastJacobian_eq_ratio (τ : ℝ) :
    forecastGeometricJacobian (X := X) (I := I) U b R S.value
      (preparedActualForecastGridVolume B U b S) τ =
    (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)) *
      ((τ / 8) ^ Fintype.card X)⁻¹ *
      (∏ a : Σ j, I j, R a.1)⁻¹ *
      (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1)⁻¹ := by
  have hcombined : coveredJetArrayScale (O := fun _ : Fin m => Unit) U *
      preparedActualForecastGridVolume B U b S *
        (∏ a : AllocatedActiveIntegerAxis U b S.value,
          (basisAxisScale (b a.val.1) a.val.2 : ℝ)) =
      (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j))⁻¹ := by
    rw [mul_assoc, preparedActualForecastGridVolume_mul_active_heights]
    simp only [coveredJetArrayScale, Fintype.card_unit, pow_one,
      mixedDensityCovolumeRatio, div_eq_mul_inv, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib, mul_inv_rev, inv_inv]
    ring
  have hactive : (∏ a, allocatedActiveIntegerGridScale U b R S.value a) =
      (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1) *
        (∏ a : AllocatedActiveIntegerAxis U b S.value,
          (basisAxisScale (b a.val.1) a.val.2 : ℝ)) := by
    simp only [allocatedActiveIntegerGridScale, Finset.prod_mul_distrib]
  have hden : coveredJetArrayScale (O := fun _ : Fin m => Unit) U *
      preparedActualForecastGridVolume B U b S * (τ / 8) ^ Fintype.card X *
        (∏ a : Σ j, I j, R a.1) * (∏ a, allocatedActiveIntegerGridScale U b R S.value a) =
      (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j))⁻¹ *
        (τ / 8) ^ Fintype.card X * (∏ a : Σ j, I j, R a.1) *
        (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1) := by
    rw [hactive]
    calc
      _ = (coveredJetArrayScale (O := fun _ : Fin m => Unit) U *
          preparedActualForecastGridVolume B U b S *
            (∏ a : AllocatedActiveIntegerAxis U b S.value,
              (basisAxisScale (b a.val.1) a.val.2 : ℝ))) *
          (τ / 8) ^ Fintype.card X * (∏ a : Σ j, I j, R a.1) *
          (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1) := by ring
      _ = _ := by rw [hcombined]
  rw [forecastGeometricJacobian, hden]
  simp only [mul_inv_rev, inv_inv]
  ring

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem ratioJacobian_product_le_exp {A : Type*} [Fintype A] {P : ℝ}
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (hb : ∀ a, f a ≤ Real.exp P) :
    (∏ a, f a) ≤ Real.exp ((Fintype.card A : ℝ) * P) := by
  calc
    _ ≤ ∏ _a : A, Real.exp P := Finset.prod_le_prod (fun a _ => hf a) (fun a _ => hb a)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]

theorem preparedActualForecastJacobian_ratio_le_exp
    (hR : ∀ j, 0 < R j) {τ P : ℝ} (hτ : 0 < τ)
    (hτinv : τ⁻¹ ≤ Real.exp P) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P) :
    forecastGeometricJacobian (X := X) (I := I) U b R S.value
      (preparedActualForecastGridVolume B U b S) τ ≤
    Real.exp ((m : ℝ) * P + (Fintype.card X : ℝ) * (P + 3) +
      (Fintype.card (Σ j, I j) : ℝ) * P +
      (Fintype.card (AllocatedActiveIntegerAxis U b S.value) : ℝ) * P) := by
  have hchart : (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)) ≤
      Real.exp ((m : ℝ) * P) := by
    simpa only [Fintype.card_fin] using ratioJacobian_product_le_exp
      (fun j => mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j))
      (fun j => (mixedDensityCovolumeRatio_pos (euclideanSubspace (U j)) (b j)).le) hratio
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      convert Real.add_one_le_exp (1 : ℝ) using 1
      norm_num
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hsp : ((τ / 8) ^ Fintype.card X)⁻¹ ≤
      Real.exp ((Fintype.card X : ℝ) * (P + 3)) := by
    rw [← inv_pow]
    have hi : (τ / 8)⁻¹ ≤ Real.exp (P + 3) := by
      calc
        _ = 8 * τ⁻¹ := by rw [inv_div, div_eq_mul_inv]
        _ ≤ Real.exp 3 * Real.exp P :=
          mul_le_mul h8 hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    exact (pow_le_pow_left₀ (inv_nonneg.mpr (div_pos hτ (by norm_num)).le) hi _).trans_eq
      (Real.exp_nat_mul _ _).symm
  have hcontinuous : (∏ a : Σ j, I j, R a.1)⁻¹ ≤
      Real.exp ((Fintype.card (Σ j, I j) : ℝ) * P) := by
    simpa only [← Finset.prod_inv_distrib] using ratioJacobian_product_le_exp
      (fun a : Σ j, I j => (R a.1)⁻¹)
      (fun a => inv_nonneg.mpr (hR a.1).le) (fun a => hRinv a.1)
  have hactive : (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1)⁻¹ ≤
      Real.exp ((Fintype.card (AllocatedActiveIntegerAxis U b S.value) : ℝ) * P) := by
    simpa only [← Finset.prod_inv_distrib] using ratioJacobian_product_le_exp
      (fun a : AllocatedActiveIntegerAxis U b S.value => (R a.val.1)⁻¹)
      (fun a => inv_nonneg.mpr (hR a.val.1).le) (fun a => hRinv a.val.1)
  have hcs := mul_le_mul hchart hsp
    (inv_nonneg.mpr (pow_nonneg (div_pos hτ (by norm_num)).le _)) (Real.exp_nonneg _)
  have hcsc := mul_le_mul hcs hcontinuous
    (inv_nonneg.mpr (Finset.prod_nonneg (fun a _ => (hR a.1).le))) (by positivity)
  have hfull := mul_le_mul hcsc hactive
    (inv_nonneg.mpr (Finset.prod_nonneg (fun a _ => (hR a.val.1).le))) (by positivity)
  rw [preparedActualForecastJacobian_eq_ratio]
  simpa only [← Real.exp_add] using hfull

theorem preparedActualForecastJacobian_ratio_uniform_le_exp
    (hR : ∀ j, 0 < R j) {τ P : ℝ} (hP : 0 ≤ P) (hτ : 0 < τ)
    (hτinv : τ⁻¹ ≤ Real.exp P) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P) :
    forecastGeometricJacobian (X := X) (I := I) U b R S.value
      (preparedActualForecastGridVolume B U b S) τ ≤
    Real.exp (((m : ℝ) + Fintype.card X + Fintype.card (Σ j, I j) +
      Fintype.card (Σ j : Fin m, Fin (n j))) * (P + 3)) := by
  apply (preparedActualForecastJacobian_ratio_le_exp B U b S hR hτ hτinv hRinv hratio).trans
  apply Real.exp_le_exp.mpr
  have hcard : (Fintype.card (AllocatedActiveIntegerAxis U b S.value) : ℝ) ≤
      Fintype.card (Σ j : Fin m, Fin (n j)) := by
    exact_mod_cast (Fintype.card_subtype_le
      (fun a : Σ j : Fin m, Fin (n j) =>
        S.value ^ (a.1.val + 1) < basisAxisScale (b a.1) a.2))
  have hmul := mul_le_mul_of_nonneg_right hcard hP
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hi0 : (0 : ℝ) ≤ Fintype.card (Σ j, I j) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ Fintype.card (Σ j : Fin m, Fin (n j)) := Nat.cast_nonneg _
  nlinarith

end Generic

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical BigOperators

theorem preparedActualForecastJacobian_ratio_budget
    {m M nX : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    {G : Type*} [Fintype G]
    (B : LayerSamplerAxis (PreparedSamplerContinuous prep)
      (preparedSamplerTransverse prep) → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    {pRadius gainLog Pchart : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog) (hChart : 0 ≤ Pchart)
    (hR : ∀ j, 0 < R j) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hratio : ∀ j, mixedDensityCovolumeRatio
      (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart) :
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let Pκ := ((nX + m + m * M : ℕ) : ℝ) *
      (pRadius + gainLog + nX + Pchart + 11)
    0 < forecastGeometricJacobian (X := Fin nX) (I := PreparedSamplerContinuous prep)
      U b R S.value (preparedActualForecastGridVolume B U b S) τ ∧
    0 ≤ Pκ ∧
    forecastGeometricJacobian (X := Fin nX) (I := PreparedSamplerContinuous prep)
      U b R S.value (preparedActualForecastGridVolume B U b S) τ ≤ Real.exp Pκ := by
  intro τ Pκ
  let P := pRadius + gainLog + nX + Pchart + 8
  have hn : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp only [P]; linarith
  have hrP : pRadius ≤ P := by dsimp only [P]; linarith
  have hcP : Pchart ≤ P := by dsimp only [P]; linarith
  have htP : gainLog + nX + 8 ≤ P := by dsimp only [P]; linarith
  have hτ : 0 < τ := Real.exp_pos _
  have hτinv : τ⁻¹ ≤ Real.exp P := by
    change (Real.exp (-(gainLog + (nX : ℝ) + 8)))⁻¹ ≤ Real.exp P
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr htP
  have hdim : Fintype.card (Σ j, PreparedSamplerContinuous prep j) +
      Fintype.card (Σ j : Fin m, Fin (preparedSamplerTransverse prep j)) ≤ m * M := by
    simp only [Fintype.card_sigma, Fintype.card_fin, ← Finset.sum_add_distrib]
    calc
      _ = ∑ j : Fin m, Fintype.card (prep j).Coord := by
        apply Finset.sum_congr rfl
        intro j _
        simpa only [PreparedSamplerContinuous, Fintype.card_fin] using preparedSampler_axis_card prep j
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum (fun j _ => hCoord j)
      _ = m * M := by simp
  have hdimR := Nat.cast_le (α := ℝ).mpr hdim
  simp only [Nat.cast_add, Nat.cast_mul] at hdimR
  have hκ := preparedActualForecastJacobian_ratio_uniform_le_exp
    (X := Fin nX) B U b S hR hP hτ hτinv
    (fun j => (hRinv j).trans (Real.exp_le_exp.mpr hrP))
    (fun j => (hratio j).trans (Real.exp_le_exp.mpr hcP))
  refine ⟨forecastGeometricJacobian_pos U b hR S.value
    (preparedActualForecastGridVolume_pos B U b S) hτ, ?_, ?_⟩
  · dsimp only [Pκ]
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  · apply hκ.trans (Real.exp_le_exp.mpr ?_)
    have hmult := mul_le_mul_of_nonneg_right
      (show (m : ℝ) + Fintype.card (Fin nX) +
        Fintype.card (Σ j, PreparedSamplerContinuous prep j) +
        Fintype.card (Σ j : Fin m, Fin (preparedSamplerTransverse prep j)) ≤
        ((nX + m + m * M : ℕ) : ℝ) by
          simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul]
          linarith) (show 0 ≤ P + 3 by linarith)
    apply hmult.trans_eq
    dsimp only [Pκ, P]
    ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem forecastRows_one_le (j : ℕ) :
    1 ≤ (boundedBooleanJetRows (Fin 1) (j + 1)).card := by
  apply Finset.one_le_card.mpr
  exact ⟨∅, by simp only [mem_boundedBooleanJetRows, Finset.card_empty, Nat.zero_le]⟩

theorem preparedActualForecast_radius_bounds
    {m : ℕ} (hm : 0 < m) {Vars : Type} [Fintype Vars]
    (T : Fin m → ℝ) (radius : ℝ≥0)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent Vars (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ)) :
    (3 : ℝ) ≤ radius ∧
      ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent Vars (j.val + 1)) : ℝ) ≤ radius := by
  have hcount (j : Fin m) :
      (1 : ℝ) ≤ Fintype.card (BoundedCoefficientExponent Vars (j.val + 1)) := by
    have : Nonempty (BoundedCoefficientExponent Vars (j.val + 1)) := ⟨⟨0, by simp⟩⟩
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr this)
  have hT0 (j : Fin m) : 0 ≤ T j :=
    (mul_nonneg (Nat.cast_nonneg _) (by positivity)).trans (hT j)
  have hTradius (j : Fin m) : T j ≤ (radius : ℝ) :=
    (le_mul_of_one_le_left (hT0 j) (by exact_mod_cast forecastRows_one_le j.val)).trans (hradius j)
  constructor
  · let j : Fin m := ⟨0, hm⟩
    have hj := (hT j).trans (hTradius j)
    have hc := hcount j
    norm_num only [j, Nat.zero_add, pow_one] at hj
    linarith
  · intro j
    have hf : (1 : ℝ) ≤ 2 * 2 ^ (j.val + 1) := by
      have := (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) : (1 : ℝ) ≤ 2 ^ (j.val + 1))
      linarith
    exact (le_mul_of_one_le_right (Nat.cast_nonneg _) hf).trans ((hT j).trans (hTradius j))

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
local notation "G" => EnlargedPreparedCommonKernel m Jalloc
local notation "I" => PreparedSamplerContinuous L
local notation "n" => preparedSamplerTransverse L
local notation "B" => EnlargedPreparedCommonSamplerBlock L Jalloc
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

noncomputable def preparedActualForecastSetup {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Pbad Ppres PF Pκ κ : ℝ}
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hPbad : 0 ≤ Pbad) (hPpres : 0 ≤ Ppres) (hPF : 0 ≤ PF) (hPκ : 0 ≤ Pκ)
    (hκ : 0 ≤ κ) (hκcap : κ ≤ Real.exp Pκ)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4) :
    ActualFixedSpatialForecastSetup (X := Fin nX) (Eout := Eout)
      («G» := G) («I» := I) («n» := n) (A := PreparedActualForecastShortIndex («G» := G) B U b S)
      B U b S (nX + m * M) (preparedActualForecastShortSelection («G» := G) B U b S)
      (Real.exp (-(gainLog + (nX : ℝ) + 8))) (1 / 2) := by
  let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
  let D : ℝ := allocatedComparisonDimension m pnum
  let P : ℝ := D + nX + 8
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hCoord
  have hd : AllocatedComparisonDimensions («G» := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D :=
    allocatedComparisonDimensions_of_primitive B (fun _ => Subtype.val)
      (by simp) (fun _ => Subtype.val_injective) (Nat.cast_nonneg _)
      (Nat.cast_le.mpr hvars) (fun j => Nat.cast_le.mpr (hI j)) (fun j => Nat.cast_le.mpr (hn j))
  have hP : 1 ≤ P := by dsimp only [P]; have := hd.nonneg; have := Nat.cast_nonneg (α := ℝ) nX; linarith
  have hDP : D ≤ P := by dsimp only [P]; have := Nat.cast_nonneg (α := ℝ) nX; linarith
  have hdimEq : (∑ j, Fintype.card (J j) : ℕ) = Fintype.card (LayerSamplerAxis I n) := by
    simp only [LayerSamplerAxis, Fintype.card_sigma, Fintype.card_sum, Fintype.card_fin]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [PreparedSamplerContinuous, Fintype.card_fin] using
      (allocatedAmbientDimension_eq U b o j).symm
  have hDmod : Fintype.card (Fin nX) + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ nX + m * M := by
    simp only [Fintype.card_fin]
    apply Nat.add_le_add_left
    calc
      _ = ∑ j : Fin m, Fintype.card (L j).Coord := by
        apply Finset.sum_congr rfl
        intro j _
        rw [allocatedLatticeDimension_eq U b o hb bW j]
        exact preparedSampler_axis_card L j
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum (fun j _ => hCoord j)
      _ = m * M := by simp
  have hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P := by
    have hh := Nat.cast_le (α := ℝ).mpr (enlargedPreparedCommonSampler_block_sum_le_principal_card L Jalloc)
    rw [Nat.cast_sum] at hh
    exact hh.trans (hd.tuples.trans hDP)
  have hscale : 0 ≤ D + pRadius + 1 := by linarith only [hd.nonneg, hpRadius]
  have hscaleRadius : pRadius ≤ D + pRadius + 1 := by linarith only [hd.nonneg]
  obtain ⟨hr3, hrcoeff⟩ := preparedActualForecast_radius_bounds hm T radius hT hradius
  obtain ⟨hτlog, hτ, _, _, hτinv, _⟩ := preparedEarlySpatialWidth nX hGain
  let transition := scalarSourceTransitionBound
  let Pcap := max 1 (scalarCubePrimitiveEnvelope Empty transition 1 0 1)
  have hPcap : 1 ≤ Pcap := le_max_left _ _
  refine {
    hm := hm
    hDmod := hDmod
    hselected := preparedActualForecastShortSelection_injective («G» := G) B U b S
    selectedNonempty := enlargedPreparedActualForecastShortSelection_nonempty L Jalloc U b S
    D := D, P := P, Pcap := Pcap, pcap := Pcap
    Pscale := D + pRadius + 1, Pbad := Pbad, Ppres := Ppres
    Pτ := gainLog + nX + 8, PK := pRadius, PF := PF, Pκ := Pκ, κ := κ
    hD := hd, hP := hP, hDP := hDP, haxes := hd.axes
    hdim := by rw [hdimEq]; exact hd.axes
    hX := by simp only [Fintype.card_fin]; dsimp only [P]; linarith only [hd.nonneg]
    hblocks := hblocks
    hPcap := hPcap, hpcap := zero_le_one.trans hPcap
    hPcapp := by linarith only [Real.add_one_le_exp Pcap]
    hPscale := hscale, hPbad := hPbad, hPpres := hPpres, hPτ := hτlog
    hPK := hpRadius, hPF := hPF, hPκ := hPκ, hκ := hκ, hκcap := hκcap
    hτ := hτ, hτinv := hτinv.le
    hδslice := by norm_num
    hδsliceInv := by norm_num; linarith only [Real.add_one_le_exp P, hP]
    hR1 := fun a => hRone _, hσ1 := fun a => hσone _
    hsmall := preparedActualForecastShortSelection_small («G» := G) B U b S
    L := transition, hL := scalarSourceTransitionBound_spec.2
    hprimitiveCap := le_max_right _ _
    hB := fun a => enlargedPreparedCommonSamplerBlock_transverse_uniform L Jalloc _ _
    hRinv := fun a => (hRinv _).trans (Real.exp_le_exp.mpr hscaleRadius)
    hslots := ?_
    hBactive := fun a => enlargedPreparedCommonSamplerBlock_four L Jalloc a.val
    forward := forward, hforward := hforward, hforwardBound := hforwardBound
    K := ⟨Real.exp pRadius, Real.exp_nonneg _⟩, hK := hRinv, hKBound := le_rfl
    radius := radius, hr3 := hr3, hradius := hrcoeff
    inverse := inverse, hinverse := hinverse, hchart := hchart
    hbudget := ?_
    hexhaustive := preparedActualForecastShortSelection_exhaustive («G» := G) B U b S }
  · intro a
    have hh := (Nat.cast_le (α := ℝ).mpr (Finset.card_le_univ
      (layerIntegerPrincipalSlots («G» := G) B a.val.1 a.val.2))).trans (hd.coefficients a.val.1)
    exact hh.trans (by linarith only [hpRadius])
  · intro j
    have hinner : 0 ≤ inverse j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (radius : ℝ) * R j)) :=
      mul_nonneg (hinverse j) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le))
    have hrows : (0 : ℝ) ≤ (boundedBooleanJetRows (Fin 1) (j.val + 1)).card := Nat.cast_nonneg _
    have hfactor : (1 : ℝ) ≤
        ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
          (Fintype.card (Finset (Fin 1)) : ℝ) := by
      norm_num only [Fintype.card_finset, Fintype.card_fin, Nat.cast_ofNat, pow_one]
      linarith only [hrows]
    exact (le_mul_of_one_le_left hinner hfactor).trans (hsourceBudget j)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedModelPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

namespace ActualFixedSpatialForecastSetup

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (hR : ∀ j, 0 < R j)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

include s hR

end ActualFixedSpatialForecastSetup
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ (Real.exp (-cost) / 2) s.P s.Pbad s.Ppres)

namespace ActualFixedSpatialSlicedForecastPath

noncomputable def comparisonGridLog (Pu : ℝ) : ℝ :=
  max Pu (max (forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * (cost + 1)))
    ((s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m))

noncomputable def comparisonPrecisionFloor (d : ℕ) (Pu V E : ℝ) : ℕ :=
  max (fixedPathSlicedGridMeshFloor s.D 4 V cost (2 * Pu + (E + 4) + 14))
    (forecastJointGridSamplerFloor d (comparisonGridLog s Pu) (E + 4) V s.PK)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ (Real.exp (-cost) / 2) s.P s.Pbad s.Ppres)

namespace ActualFixedSpatialSlicedForecastPath

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))

end Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ (Real.exp (-cost) / 2) s.P s.Pbad s.Ppres)

namespace ActualFixedSpatialSlicedForecastPath

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : slice.path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {Pu V E : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + Pu + 4) (cost + 1) (2 * Pu + (E + 4) + 14) m))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : slice.path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {Pnative massLog capLog Edata Ptest : ℝ}
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ massLog + E + 8)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center slice.path.center slice.path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center slice.path.base slice.path.noise ≠ 0)
variable (hsampleAt : sampleFn slice.path.noise = slice.path.sample)
variable (hreadAt : readFn slice.path.noise = slice.path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (hcost : 0 ≤ cost) (hPu : 2 ≤ Pu) (hE : 0 ≤ E)
variable (hDsq : s.D * s.D ≤ Pu) (hAL : (s.L : ℝ) ≤ Real.exp Pu)
variable (hτ1 : τ ≤ 1) (hLip : (Lip : ℝ) ≤ Real.exp Pu)
variable (hq : (q : ℝ) ≤ Real.exp V)
variable (hfloor : comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) Pu V E ≤ S.value)
variable (hHP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
    Real.exp (-cost) * S.value ≤ (slice.principalLength ⟨a.val,p⟩ : ℝ))
variable (hHG : ∀ g, Real.exp (-cost) * S.value ≤ (slice.kernelLength g : ℝ))
variable (hstep : (slice.step : ℝ) ≤ 2 * Real.exp cost)
variable (hξsmall : ξ ≤ Real.exp (-(2 * Pu + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ Edata)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (comparisonGridLog s Pu)
  (E + 4) V s.Pτ) ≤ (physicalN i : ℝ))

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedSourceLog
namespace OAI

section

namespace Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A] {Dmod : ℕ} {selected : A → Σ j, Fin (n j)}
variable {τ δslice : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)

end Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup

end

section

namespace Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} {Dmod : ℕ} {selected : A → Σ j, Fin (n j)}
variable {τ δslice : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)

noncomputable def slicedComparisonSourceLog (Ptest : ℝ) : ℝ :=
  2 + s.D * s.D + s.pcap + max 0 Ptest

end Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedRecoveredTagTorusVariation
namespace OAI

section

namespace Erdos3

theorem unitCircle_dist_div_integer_parts {q : ℕ} (hq : 0 < q)
    (center r₀ r₁ : ℝ) (z₀ z₁ : ℤ)
    (hz : (((z₀ : ℝ) / q : ℝ) : UnitAddCircle) =
      (((z₁ : ℝ) / q : ℝ) : UnitAddCircle)) :
    dist (((center + r₀ + z₀) / q : ℝ) : UnitAddCircle)
      (((center + r₁ + z₁) / q : ℝ) : UnitAddCircle) ≤ |r₀ - r₁| / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [add_div, AddCircle.coe_add, hz, dist_add_right, dist_add_left]
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  calc
    _ ≤ ‖r₀ / (q : ℝ) - r₁ / q‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |r₀ - r₁| / q := by rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hqR]

namespace VectorPolynomial

variable {m : ℕ} {X : Type*} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem physicalGridFactorInput_dist_le_of_integer_remainders
    (q : ℕ) (hq : 0 < q) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (u v : X → ℝ) (center r₀ r₁ : ∀ j, J j → ℝ) (z₀ z₁ : ∀ j, J j → ℤ)
    (hu : ∀ j i, eval u (poly j) i = center j i + r₀ j i + (z₀ j i : ℝ))
    (hv : ∀ j i, eval v (poly j) i = center j i + r₁ j i + (z₁ j i : ℝ))
    (hz : ∀ j i, (((z₀ j i : ℝ) / q : ℝ) : UnitAddCircle) =
      (((z₁ j i : ℝ) / q : ℝ) : UnitAddCircle))
    {ε : ℝ} (hε : 0 ≤ ε) (herr : ∀ j i, |r₀ j i - r₁ j i| ≤ ε) :
    dist (physicalGridFactorInput q poly u) (physicalGridFactorInput q poly v) ≤ ε / q := by
  apply (dist_pi_le_iff (div_nonneg hε (Nat.cast_nonneg q))).mpr
  intro z
  change dist (((eval u (poly z.1) z.2 / q : ℝ) : UnitAddCircle))
    (((eval v (poly z.1) z.2 / q : ℝ) : UnitAddCircle)) ≤ _
  rw [hu, hv]
  exact (unitCircle_dist_div_integer_parts hq _ _ _ _ _ (hz z.1 z.2)).trans
    (div_le_div_of_nonneg_right (herr z.1 z.2) (Nat.cast_nonneg q))

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G : Type*} [Fintype G] {I E : Fin m → Type*}
variable [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_remainder_at_site
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (x : LayerSamplerVariables G I n B → ℤ) (j : Fin m) (i : J j) :
    eval (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ)) (poly j) i =
      (c j).val i + mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 (fun k => (x k : ℝ)) i +
      (MvPolynomial.eval x (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
        (Sum.inr ⟨j, i⟩)) : ℝ) := by
  have hr := h.integerFullChart_remainder B U b hb o S hR hσ poly hm hp c a v sample read
    (fun k => (x k : ℝ)) j i
  rw [← eval_jointIntegerPhysicalSite_eq_frame a v, integerSampledRealChart_eval] at hr
  linarith

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_torus_dist
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (q : ℕ) (hq : 0 < q) (x y : LayerSamplerVariables G I n B → ℤ)
    (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q))
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ j i, |mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 (fun k => (x k : ℝ)) i -
      mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 (fun k => (y k : ℝ)) i| ≤ ε) :
    dist (physicalGridFactorInput q poly (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ)))
      (physicalGridFactorInput q poly (fun z => (jointIntegerPhysicalSite y (a, v) z : ℝ))) ≤ ε / q := by
  apply physicalGridFactorInput_dist_le_of_integer_remainders q hq poly
    (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ))
    (fun z => (jointIntegerPhysicalSite y (a, v) z : ℝ))
    (fun j => (c j).val)
    (fun j => mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
      (sample j).1 (sample j).2 (fun k => (x k : ℝ)))
    (fun j => mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
      (sample j).1 (sample j).2 (fun k => (y k : ℝ)))
    (fun j i => MvPolynomial.eval x
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample (Sum.inr ⟨j, i⟩)))
    (fun j i => MvPolynomial.eval y
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample (Sum.inr ⟨j, i⟩)))
    (h.integerFullChart_remainder_at_site B U b hb o S hR hσ poly hm hp c a v sample read x)
    (h.integerFullChart_remainder_at_site B U b hb o S hR hσ poly hm hp c a v sample read y)
    (fun j i => integerPolynomial_eval_addCircle_div_eq _ q x y hxy) hε herr

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRecoveredNormalizedTopChart
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem aeval_frozen_integer_top {σ K : Type*}
    (w : σ → ℕ) (β : σ → MvPolynomial K ℤ)
    (hβ : ∀ z, MvPolynomial.map (Int.castRingHom ℝ) (β z) ∈
      weightedSupportLE (fun _ => 1) (w z))
    (keep : K → Prop) (fixed : {i // ¬keep i} → ℤ)
    (p : MvPolynomial σ ℝ) :
    aeval (fun z => homogeneousComponent (w z)
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β z)))) p =
      freezePolynomial keep (0 : {i // ¬keep i} → ℝ)
        (aeval (fun z => homogeneousComponent (w z)
          (MvPolynomial.map (Int.castRingHom ℝ) (β z))) p) := by
  simp_rw [freezePolynomial_map, freezePolynomial_top keep _
    ((mem_weightedSupportLE_one_iff _ _).mp (hβ _))]
  exact (MvPolynomial.comp_aeval_apply _ (freezePolynomial keep 0) p).symm

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem normalizedRealPolynomialChart_top_inr
    {X Tags K : Type*} (weight : Tags → ℕ) (N : X → ℝ)
    (poly : Tags → MvPolynomial X ℝ)
    (hp : ∀ i, poly i ∈ weightedSupportLE (fun _ : X => 1) (weight i))
    (β : X ⊕ Tags → MvPolynomial K ℝ)
    (hβ : ∀ z, β z ∈ weightedSupportLE (fun _ : K => 1)
      (Sum.elim (fun _ : X => 1) weight z)) (i : Tags) :
    aeval (fun z => homogeneousComponent (Sum.elim (fun _ : X => 1) weight z) (β z))
        (normalizedRealPolynomialChart N (fun i => homogeneousComponent (weight i) (poly i))
          (Sum.inr i)) =
      homogeneousComponent (weight i) (β (Sum.inr i) - aeval (fun x => β (Sum.inl x)) (poly i)) := by
  rw [normalizedRealPolynomialChart_inr, map_sub, aeval_X, aeval_rename, map_sub]
  congr 1
  exact (weightedTop_aeval (fun _ : X => 1) (fun _ : K => 1)
    (fun x => β (Sum.inl x)) (fun x => hβ (Sum.inl x)) (poly i) (weight i) (hp i)).symm

end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_polynomial_remainder
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) (i : J j) :
    aeval (fun x => integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inl x))
      (coordinate (LinearMap.proj i : (J j → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly j)) -
        C ((c j).val i) =
      mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (sample j) i +
        integerSampledRealChart
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inr ⟨j, i⟩) := by
  apply MvPolynomial.funext
  intro x
  rw [map_sub, map_add, eval_C, mixedLiftPolynomial_eval]
  change aeval x (aeval _ _) - _ = _
  rw [comp_aeval_apply]
  simp only [aeval_eq_eval]
  rw [← coordinate_eval₂]
  have hspatial : (fun z => aeval x (integerSampledRealChart
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inl z))) =
      (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
        ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) := by
    funext z
    change aeval x (MvPolynomial.map (Int.castRingHom ℝ)
      (affineFramePolynomial (jointIntegerFrame (a, v)) z)) = _
    rw [affineFramePolynomial_map, affineFramePolynomial_eval]
    rfl
  have hspatial' := hspatial
  simp only [aeval_eq_eval] at hspatial'
  rw [hspatial']
  have heval := eval₂_algebraMap (S := ℝ)
    (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j)
  have heval' : eval₂ (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j) =
      eval (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j) := by
    simpa using heval
  rw [heval']
  exact h.integerFullChart_remainder B U b hb o S hR hσ poly hm hp c a v sample read x j i

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_normalized_top_tag
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (N : X → ℝ) (j : Fin m) (i : J j) :
    aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) z))
      (normalizedRealPolynomialChart N (fullTaggedMajorTopCoordinates J poly) (Sum.inr ⟨j, i⟩)) =
      -homogeneousComponent (j.val + 1)
        (mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (sample j) i) := by
  have hdegree (z : Σ j, J j) :
      coordinate (LinearMap.proj z.2 : (J z.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly z.1) ∈
        weightedSupportLE (fun _ : X => 1) (z.1.val + 1) := by
    apply (mem_weightedSupportLE_iff _ _ _).mpr
    apply (scalar_weightedDegree_le_iff _ _ _).mpr
    intro α hα
    rw [coeff_coordinate, hp z.1 α hα, map_zero]
  change aeval (fun z => homogeneousComponent
    (Sum.elim (fun _ : X => 1) (fun z : Σ j, J j => z.1.val + 1) z)
    (integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) z))
    (normalizedRealPolynomialChart N
      (fun z : Σ j, J j => homogeneousComponent (z.1.val + 1)
        (coordinate (LinearMap.proj z.2 : (J z.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly z.1)))
      (Sum.inr ⟨j, i⟩)) = _
  rw [normalizedRealPolynomialChart_top_inr (fun z : Σ j, J j => z.1.val + 1) N
    (fun z => coordinate (LinearMap.proj z.2 : (J z.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly z.1))
    hdegree _ (allocatedRecoveredIntegerFullChart_support B U b o poly hm c a v sample)]
  have heq := h.integerFullChart_polynomial_remainder B U b hb o S hR hσ poly hm
    hp c a v sample read j i
  have hres : integerSampledRealChart
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inr ⟨j, i⟩) -
      aeval (fun x => integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inl x))
        (coordinate (LinearMap.proj i : (J j → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly j)) =
      -mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (sample j) i -
        C ((c j).val i) := by linear_combination -heq
  rw [hres, map_sub, map_neg]
  have hcenter : homogeneousComponent (j.val + 1)
      (C ((c j).val i) : MvPolynomial (LayerSamplerVariables G I n B) ℝ) = 0 := by
    apply homogeneousComponent_eq_zero
    simp
  rw [hcenter, sub_zero]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredModelMarginalData
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Consumer

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (α τ : ℝ)
variable {P : ℝ}

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

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]

end Consumer
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable def preparedCenteredMarginalExponent (m : ℕ) : ℕ :=
  (exists_allocated_centered_narrow_prescribed_marginal.{0, 0, 0, 0, 0, 0} m).choose

section Consumer

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (α τ : ℝ)
variable {P : ℝ}

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

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

end Consumer
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


