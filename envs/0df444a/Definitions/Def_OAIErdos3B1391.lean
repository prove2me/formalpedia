-- Prove2me | Definitions.Def_OAIErdos3B1391
-- name    : OAIErdos3B1391
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T08:33:42.40623+00:00
-- url     : https://prove2.me/theorems/860b78ea-a8e1-4218-a068-d0277b91e155
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1392 of 1413
-- statement:
--   Definitions bundle 1392 of 1413 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1390`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1392 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.AllocatedSourceNumerics.canonical_projection_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedDetectedGain_lower`, `OAI.Erdos3.VectorPolynomial.allocatedRowSlicedSiteRadius_buffer_le_exp`, `OAI.Erdos3.VectorPolynomial.allocatedSmoothRankCoefficientIndex_card_le`, `OAI.Erdos3.VectorPolynomial.allocated_fullBox_positive_law_at_model_budget`, `OAI.Erdos3.VectorPolynomial.boundedCoefficientExponent_card_mono_embedding`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientIndex_card_from_layer_counts`, `OAI.Erdos3.VectorPolynomial.exists_allocated_grid_times_ambient_lift`, `OAI.Erdos3.VectorPolynomial.preparedInitialRank_dimension_le`, `OAI.Erdos3.VectorPolynomial.preparedInitialRank_layer_card`, `OAI.Erdos3.VectorPolynomial.preparedInitialRank_parameters`, `OAI.Erdos3.VectorPolynomial.preparedInitialRank_smooth_card_le`, `OAI.Erdos3.VectorPolynomial.preparedModularCanonicalDetector_narrow_width_le_one`, `OAI.Erdos3.VectorPolynomial.preparedModularDetector_narrow_width`, `OAI.Erdos3.VectorPolynomial.preparedModularDetector_physical_root_of_variables`, `OAI.Erdos3.VectorPolynomial.preparedModularDetector_scalar_resource_bounds`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_ambient_count`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_block_card`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_blocks`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_chart_sum`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_early_analytic_bounds`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_grid_axes`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_grid_slot_cap`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_jet_counts_of_geometry`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_period_prefactor`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_sampling_bounds`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_sampling_bounds_of_geometry`, `OAI.Erdos3.preparedDeckBasis_card_eq`, `OAI.Erdos3.standardLatticeSection_basis_card_eq`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1378
import Definitions.Def_OAIErdos3B1388
import Definitions.Def_OAIErdos3B1394

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankSmoothWidthBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m L : ℕ} {X : Type*} [Fintype X]
    {I : Fin m → Type*} {n : Fin m → ℕ}

theorem allocatedSmoothRankCoefficientIndex_card_le (hm : 0 < m)
    (inactive : LayerSamplerAxis I n → Prop) :
    Fintype.card (AllocatedSmoothRankCoefficientIndex X inactive L) ≤
      L * (Fintype.card X + ∑ j : Fin m, n j) := by
  have hcount (j : Fin m) : Fintype.card (AllocatedCongruenceIntegerAxis inactive j) ≤ n j := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le
      (fun i : Fin (n j) => ¬ inactive ⟨j, Sum.inr i⟩)
  change Fintype.card (Σ j : Fin m,
    (SpatialDegreeOutput X j ⊕ AllocatedCongruenceIntegerAxis inactive j) × Fin L) ≤ _
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  calc
    _ ≤ ∑ j : Fin m, (Fintype.card (SpatialDegreeOutput X j) + n j) * L :=
      Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right L (Nat.add_le_add_left (hcount j) _))
    _ = L * (Fintype.card X + ∑ j : Fin m, n j) := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib, spatialDegreeOutput_sum_card hm, Nat.mul_comm]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedDeckRankCardinality
namespace OAI

section

namespace Erdos3

variable {J I E : Type*} [Fintype J] [Fintype I] [Fintype E]

theorem standardLatticeSection_basis_card_eq
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)]
    (o : OrthonormalBasis I ℝ W)
    (bW : Module.Basis E ℤ (latticeSection (standardEuclideanLattice J) W)) :
    Fintype.card E = Fintype.card I := by
  rw [← Module.finrank_eq_card_basis bW, ZLattice.rank ℝ,
    Module.finrank_eq_card_basis o.toBasis]

theorem preparedDeckBasis_card_eq
    (U : Submodule ℝ (J → ℝ))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) (euclideanSubspace U))]
    (o : OrthonormalBasis I ℝ (euclideanSubspace U))
    (bW : Module.Basis E ℤ (latticeSection (standardEuclideanLattice J) (euclideanSubspace U))) :
    Fintype.card E = Fintype.card I :=
  standardLatticeSection_basis_card_eq (euclideanSubspace U) o bW

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedEnlargedModularAllocation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {X₀ J₀ : Type} {m : ℕ} (prep : RankPreparationFamily X₀ J₀ m)

section Dimension

variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

include U o bW

theorem preparedInitialRank_layer_card (j : Fin m) :
    Fintype.card (E j) + preparedSamplerTransverse prep j = Fintype.card (prep j).Coord := by
  rw [preparedDeckBasis_card_eq (U j) (o j) (bW j)]
  exact preparedSampler_axis_card prep j

theorem preparedInitialRank_dimension_le (nX M : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) :
    Fintype.card (Fin nX) +
        ∑ j : Fin m, (Fintype.card (E j) + preparedSamplerTransverse prep j) ≤ nX + m * M := by
  simp only [Fintype.card_fin]
  apply Nat.add_le_add_left
  calc
    _ = ∑ j : Fin m, Fintype.card (prep j).Coord :=
      Finset.sum_congr rfl (fun j _ => preparedInitialRank_layer_card prep U o bW j)
    _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum (fun j _ => hM j)
    _ = m * M := by simp

theorem preparedInitialRank_parameters (nX M : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hm : 0 < m) :
    0 ≤ (modularInitialRankStrength m (nX + m * M) : ℝ) ∧
    (Fintype.card (Fin nX) +
      ∑ j : Fin m, (Fintype.card (E j) + preparedSamplerTransverse prep j) ≤ nX + m * M) ∧
    ⌈2 * ((modularInitialRankStrength m (nX + m * M) : ℝ) + (nX + m * M : ℕ) + 10) /
      modularRankSmallBallExponent m⌉₊ ≤ modularInitialBlockCount m (nX + m * M) :=
  ⟨Nat.cast_nonneg _, preparedInitialRank_dimension_le prep U o bW nX M hM,
    modularInitialBlockCount_threshold hm _⟩

end Dimension

theorem preparedInitialRank_smooth_card_le (nX M : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hm : 0 < m)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous prep)
      (preparedSamplerTransverse prep) → Prop) :
    Fintype.card (AllocatedSmoothRankCoefficientIndex (Fin nX) inactive
      (modularInitialBlockCount m (nX + m * M))) ≤
        modularInitialBlockCount m (nX + m * M) * (nX + m * M) := by
  apply (allocatedSmoothRankCoefficientIndex_card_le hm inactive).trans
  apply Nat.mul_le_mul_left
  simp only [Fintype.card_fin]
  apply Nat.add_le_add_left
  calc
    ∑ j : Fin m, preparedSamplerTransverse prep j ≤ ∑ _j : Fin m, M := by
      apply Finset.sum_le_sum
      intro j _
      have h := preparedSampler_axis_card prep j
      have := hM j
      omega
    _ = m * M := by simp

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineSourceAccuracy
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem allocatedRowSlicedSiteRadius_buffer_le_exp (rowSets : Fin m → Finset (Finset α)) :
    2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤
      Real.exp (((m : ℝ) + 2) * Fintype.card α + m + 4) := by
  let A : ℝ := ((m : ℝ) + 2) * Fintype.card α + 3
  have hT : 0 ≤ partitionedIdealRadius α m + 1 := by
    have := partitionedIdealRadius_nonneg α m
    positivity
  have hr : (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ 1 + m * idealSiteBoxRadius α m := by
    change 1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1) ≤ _
    apply add_le_add_right
    calc
      _ ≤ ∑ _j : Fin m, idealSiteBoxRadius α m := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ hT
        exact_mod_cast (Finset.card_le_univ (rowSets j)).trans_eq (Fintype.card_finset (α := α))
      _ = _ := by simp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hone : 1 ≤ Real.exp A := Real.one_le_exp_iff.mpr hA
  calc
    _ ≤ 2 + m * (2 * idealSiteBoxRadius α m) := by nlinarith only [hr]
    _ ≤ 2 + m * Real.exp A := by
      gcongr
      exact idealSiteBoxRadius_buffer_le_exp α m
    _ ≤ ((m : ℝ) + 2) * Real.exp A := by nlinarith only [hone]
    _ ≤ Real.exp ((m : ℝ) + 1) * Real.exp A := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      simpa only [add_assoc, one_add_one_eq_two] using Real.add_one_le_exp ((m : ℝ) + 1)
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [A]; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (E : Fin m → Type*) [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable (hR : ∀ j, 0 < R j) {Pnum : ℝ} (hPnum : 0 ≤ Pnum)
variable (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
variable (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
variable (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
variable (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pnum)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedAmbientGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem exists_allocated_grid_times_ambient_lift
    (gridDensity : AllocatedFrozenJetRows B U b S O → ℝ)
    (g : (JetAmbientIndex O J → UnitAddCircle) → ℝ) {Lg : ℝ≥0}
    (hg : LipschitzWith Lg g) (hgb : ∀ z, g z ∈ Set.Icc (0 : ℝ) 1)
    (hgv : ∀ z : MixedCoveredJetSource I O Q n d,
      z ∈ mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j)) →
      g (coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z)) =
        gridDensity ((coefficientJetAxisSplit O I n grid z.1).1))
    (model : EuclideanJetLayers U O → ℂ)
    (F : (JetAmbientIndex O J → UnitAddCircle) → ℂ) {Lf Cf : ℝ≥0}
    (hF : LipschitzWith Lf F) (hFb : ∀ z, ‖F z‖ ≤ Cf)
    (hFv : ∀ y, model y = F (coveredJetAmbientTorus U 1 y))
    (hzero : ∀ y, y ∉ mixedCoveredJetChart U o b hb bW d ''
      mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j)) → model y = 0) :
    ∃ G : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
      LipschitzWith (Cf * (Lg * d) + Lf) G ∧ (∀ z, ‖G z‖ ≤ Cf) ∧
      ∀ y, model y * (allocatedChartGridMultiplier B U b S O hb o bW d gridDensity y : ℂ) =
        G (coveredJetAmbientTorus U 1 y) := by
  have hgC : LipschitzWith (Lg * d)
      (fun z : JetAmbientIndex O J → UnitAddCircle => (g (d • z) : ℂ)) := by
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitz.comp (hg.comp (ambient_nsmul_lipschitz d))
  have hgbC (z : JetAmbientIndex O J → UnitAddCircle) : ‖(g (d • z) : ℂ)‖ ≤ (1 : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgb _).1]
    exact (hgb _).2
  refine ⟨fun z => F z * (g (d • z) : ℂ), ?_, ?_, ?_⟩
  · simpa only [one_mul] using lipschitz_mul_of_bounds _ _ hF hgC hFb hgbC
  · intro z
    rw [norm_mul]
    exact (mul_le_mul (hFb z) (hgbC z) (norm_nonneg _) (NNReal.coe_nonneg _)).trans_eq (mul_one _)
  · intro y
    dsimp only
    by_cases hy : y ∈ mixedCoveredJetChart U o b hb bW d ''
        mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j))
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [← coveredJetAmbientTorus_nsmul_output, hgv z hz,
        allocatedChartGridMultiplier_apply B U b S O hb o bW d gridDensity z hz, hFv]
    · rw [← hFv, hzero y hy, zero_mul, zero_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "quarter" => (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCanonicalProjectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)

theorem AllocatedSourceNumerics.canonical_projection_bounds
    {P : ℝ} (h : AllocatedSourceNumerics B U b S C V P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (dim : ℕ) {coverLog : ℝ} (hcoverLog : 0 ≤ coverLog) :
    let A := Classical.choose (exists_allocatedCanonicalProjection_budget m dim)
    let budget := (P + coverLog + A) ^ A
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let densityLip : ℝ≥0 := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip : ℝ≥0 := Fintype.card (Finset (Fin dim)) * Real.toNNReal (Real.exp coverLog)
    let reconstructionLip : ℝ≥0 :=
      ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1)) : ℝ≥0)
    cap ≤ Real.exp budget ∧
      ((densityLip * sectionLip * reconstructionLip : ℝ≥0) : ℝ) ≤ Real.exp budget := by
  intro A budget cap densityLip sectionLip reconstructionLip
  have hinput := allocatedCoefficient_fourier_input_budget (J := J) B R σ S.value S.positive C V
    h.nonneg h.degree h.variable_count hR hσ h.radius_inv h.width_inv h.coefficients
    h.real_axes h.integer_axes h.ambient_axes h.profile h.length h.chart h.covolume
  have hdensity : (densityLip : ℝ) ≤ Real.exp (allocatedFourierLogBudget m P) :=
    hinput.2.2.2
  have hpoly : allocatedCanonicalProjectionLog m dim P coverLog ≤ budget :=
    (Classical.choose_spec (exists_allocatedCanonicalProjection_budget m dim)).2 P coverLog
      h.nonneg hcoverLog
  have hfourier : allocatedFourierLogBudget m P ≤
      allocatedCanonicalProjectionLog m dim P coverLog := by
    unfold allocatedCanonicalProjectionLog
    exact (le_add_of_nonneg_right hcoverLog).trans
      (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hrowCost : (canonicalProjectionRowCost m dim : ℝ) ≤
      Real.exp (canonicalProjectionRowCost m dim) := by
    linarith only [Real.add_one_le_exp (canonicalProjectionRowCost m dim : ℝ)]
  have hroweq : (sectionLip : ℝ) * reconstructionLip =
      Real.exp coverLog * (canonicalProjectionRowCost m dim : ℝ) := by
    simp only [sectionLip, reconstructionLip, canonicalProjectionRowCost,
      NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_sum, Real.coe_toNNReal,
      Real.exp_nonneg, Nat.cast_mul, Nat.cast_sum]
    ring
  refine ⟨hinput.2.2.1.trans (Real.exp_le_exp.mpr (hfourier.trans hpoly)), ?_⟩
  calc
    _ = (densityLip : ℝ) * ((sectionLip : ℝ) * reconstructionLip) := by
      simp only [NNReal.coe_mul, mul_assoc]
    _ = (densityLip : ℝ) * (Real.exp coverLog * (canonicalProjectionRowCost m dim : ℝ)) := by rw [hroweq]
    _ ≤ Real.exp (allocatedFourierLogBudget m P) *
        (Real.exp coverLog * Real.exp (canonicalProjectionRowCost m dim)) := by
      gcongr
    _ = Real.exp (allocatedCanonicalProjectionLog m dim P coverLog) := by
      simp only [allocatedCanonicalProjectionLog, Real.exp_add]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hpoly

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

theorem preparedModularGeneralDetector_block_card (a : LayerSamplerAxis I n) :
    Fintype.card (B a) ≤ Fintype.card (LayerSamplerVariables G I n B) := by
  let f : B a → LayerSamplerVariables G I n B := fun x =>
    Sum.inr ⟨a, x, ⟨0, by simp [layerSamplerDegree]⟩⟩
  apply Fintype.card_le_of_injective f
  intro x y h
  have hpair := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr_injective h)).2
  exact congrArg Prod.fst hpair

theorem preparedModularGeneralDetector_blocks {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (a : LayerSamplerAxis I n) :
    (Fintype.card (B a) : ℝ) ≤ 2 * D :=
  (Nat.cast_le.mpr (preparedModularGeneralDetector_block_card (G := G) B a)).trans
    (preparedModularGeneralDetector_variable_count B rowSets hdim)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem preparedModularGeneralDetector_grid_axes {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) :
    (Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} : ℝ) ≤ D :=
  (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hdim.axes

theorem preparedModularGeneralDetector_grid_slot_cap {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) (hDP : D ≤ P) :
    let Qgrid := Real.toNNReal (8 * (D + 1))
    (∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤
        (Qgrid : ℝ)) ∧ (Qgrid : ℝ) ≤ Real.exp (P + 8) := by
  have hnonneg : 0 ≤ 8 * (D + 1) := by linarith [hdim.nonneg]
  dsimp only
  rw [Real.coe_toNNReal _ hnonneg]
  constructor
  · intro a
    have hc := (Nat.cast_le.mpr (Finset.card_le_univ
      (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2))).trans
      (hdim.coefficients (allocatedGridIntegerAxis B U b S a).1)
    linarith
  · have hP := hdim.nonneg.trans hDP
    have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    calc
      _ ≤ 8 * (P + 1) := by linarith
      _ ≤ Real.exp 8 * Real.exp P :=
        mul_le_mul h8 (Real.add_one_le_exp P) (by linarith) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem preparedModularGeneralDetector_ambient_count {P : ℝ}
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P) :
    ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ (m : ℝ) * P := by
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _j : Fin m, P := Finset.sum_le_sum (fun j _ => hJ j)
    _ = _ := by simp

theorem preparedModularGeneralDetector_chart_sum (C : Fin m → ℝ≥0) {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hDP : D ≤ P) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp P) :
    ((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp (3 * P) := by
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hPexp : P ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  have hmexp : (m : ℝ) ≤ Real.exp P := hdim.degree.trans (hDP.trans hPexp)
  push_cast
  calc
    _ ≤ ∑ _j : Fin m, Real.exp P * P := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul (hC j) (hJ j) (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = (m : ℝ) * (Real.exp P * P) := by simp
    _ ≤ Real.exp P * (Real.exp P * Real.exp P) := mul_le_mul hmexp
      (mul_le_mul_of_nonneg_left hPexp (Real.exp_nonneg _)) (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularCanonicalDetectorAmbientConsumer
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

theorem preparedModularDetector_scalar_resource_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) {P : ℝ} (hP : 0 ≤ P) :
    let r := preparedModularCanonicalDetectorResources K P
    0 ≤ r.v ∧ 0 ≤ r.w ∧ 0 ≤ r.Dg ∧ 0 ≤ r.Pbox ∧
      0 ≤ r.Vlog ∧ 0 ≤ r.Nlog ∧ 0 ≤ r.Banalytic ∧ 0 ≤ r.baseAmbient ∧
      P ≤ r.v ∧ P + 1 ≤ r.w ∧ 2 * P ≤ r.Dg ∧ K.m * P ≤ r.Dg ∧
      ((layerTailDegree K.m + 1 : ℕ) : ℝ) ≤ r.Dg ∧ 1 ≤ r.Dg ∧
      r.Dg ≤ r.Banalytic ∧ 4 * P ≤ r.Banalytic ∧ P + 8 ≤ r.Banalytic ∧
      P ≤ r.baseAmbient ∧ 3 * P ≤ r.baseAmbient ∧ 2 * P ≤ r.baseAmbient ∧
      r.Vlog ≤ r.baseAmbient ∧ r.Nlog ≤ r.baseAmbient ∧
      ((layerTailDegree K.m + 1 : ℕ) : ℝ) * P ≤ r.baseAmbient ∧ 2 ≤ r.baseAmbient := by
  intro r
  have hdeg : 0 ≤ ((layerTailDegree K.m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ K.m := Nat.cast_nonneg _
  have hprof : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
  have hmP : (0 : ℝ) ≤ K.m * P := mul_nonneg hm hP
  have hdegP : 0 ≤ ((layerTailDegree K.m + 1 : ℕ) : ℝ) * P := mul_nonneg hdeg hP
  have hv : r.v = P + 8 := rfl
  have hw : r.w = P + 1 := rfl
  have hbox : r.Pbox = 2 * P + 8 := rfl
  have hd : r.Dg = 2 * P + K.m * P + (layerTailDegree K.m + 1 : ℕ) +
      K.m + comparisonProfileBound + 8 := rfl
  have hba : r.Banalytic = r.Dg + 4 * P + 32 := rfl
  have ha : r.baseAmbient = r.Pproj + r.coverLog + r.Vlog + r.Nlog + r.Q +
      (layerTailDegree K.m + 1 : ℕ) * P + 3 * P + comparisonProfileBound + 32 := rfl
  have hproj : 0 ≤ r.Pproj := by change 0 ≤ 4 * (P + 8)^2; positivity
  have hcover : 0 ≤ r.coverLog := by
    change 0 ≤ (r.Pproj + 3 + K.Acover)^K.Acover
    positivity
  have hq : 0 ≤ r.Q := by change 0 ≤ (P + K.Cperiod)^K.Cperiod; positivity
  have hvl : 0 ≤ r.Vlog := by
    change 0 ≤ P^2 * ((layerTailDegree K.m + 1 : ℕ) * P + 1)
    positivity
  have hnl : 0 ≤ r.Nlog := by
    change 0 ≤ (2 * K.m : ℕ) * (2 * P + 16) * (1 + 4 * (2 * P + 8))
    positivity
  have hd0 : 0 ≤ r.Dg := by linarith only [hd, hP, hmP, hdeg, hm, hprof]
  have hba0 : 0 ≤ r.Banalytic := by linarith only [hba, hd0, hP]
  have ha0 : 0 ≤ r.baseAmbient := by
    linarith only [ha, hproj, hcover, hvl, hnl, hq, hdegP, hP, hprof]
  refine ⟨by linarith only [hv, hP], by linarith only [hw, hP], hd0,
    by linarith only [hbox, hP], hvl, hnl, hba0, ha0, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hv]
  · exact hw.ge
  · linarith only [hd, hmP, hdeg, hm, hprof]
  · linarith only [hd, hP, hdeg, hm, hprof]
  · linarith only [hd, hP, hmP, hm, hprof]
  · linarith only [hd, hP, hmP, hdeg, hm, hprof]
  · linarith only [hba, hP]
  · linarith only [hba, hd0]
  · linarith only [hba, hd0, hP]
  all_goals linarith only [ha, hproj, hcover, hvl, hnl, hq, hdegP, hP, hprof]

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin 1)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)


variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))

theorem preparedModularGeneralDetector_early_analytic_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (hm : K.m = m) {P D pDetect : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) (hDP : D ≤ P)
    (hRone : ∀ j, R j ≤ 1) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hV : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hvolumeRatio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hforward : ∀ j, (Cforward j : ℝ) ≤ Real.exp P) (hK : (Ksource : ℝ) ≤ Real.exp P)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp P) (hDetect : pDetect ≤ P) :
    PreparedModularGeneralEarlyAnalyticBounds B rowSets U b S Cforward Ksource
      (preparedModularCanonicalDetectorResources K P) P D pDetect := by
  let r := preparedModularCanonicalDetectorResources K P
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  obtain ⟨hv0, hw0, hdg0, hbox0, hvol0, hnorm0, hba0, hbase0,
    hPv, hPw, h2PDg, hmPDg, htailDg, h1Dg, hDgBa, h4PBa, h8PBa,
    hPBase, h3PBase, h2PBase, hVBase, hNBase, htailBase, h2Base⟩ :=
      preparedModularDetector_scalar_resource_bounds K hP
  have hPDg : P ≤ r.Dg := (by linarith only [hP] : P ≤ 2 * P).trans h2PDg
  have hDDg : D ≤ r.Dg := hDP.trans hPDg
  have hPexp : P ≤ Real.exp P := by linarith only [Real.add_one_le_exp P]
  have hExpv : Real.exp P ≤ Real.exp r.v := Real.exp_le_exp.mpr hPv
  have hExpBa : Real.exp P ≤ Real.exp r.Banalytic :=
    Real.exp_le_exp.mpr ((by linarith only [hP] : P ≤ 4 * P).trans h4PBa)
  obtain ⟨hSlots, hSlotsExp⟩ := preparedModularGeneralDetector_grid_slot_cap B rowSets U b S hdim hDP
  obtain ⟨hI, hn⟩ := preparedModularGeneralDetector_layer_axes B rowSets hdim
  have hCoords := preparedModularGeneralDetector_chart_sum B rowSets Cforward hdim hDP hJ hforward
  have hCoordAnalytic : ((Ksource * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤
      Real.exp r.Banalytic := by
    rw [NNReal.coe_mul]
    calc
      _ ≤ Real.exp P * Real.exp (3 * P) :=
        mul_le_mul hK hCoords (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (4 * P) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr h4PBa
  refine {
    hQgrid := hSlots
    hDg := hdg0
    hvg := hv0
    hwg := hw0
    hcube := hdim.cube.trans hDDg
    hdegree := fun j => (hdim.layer_degree B j).trans hDDg
    hrowsD := ?_
    htail := ?_
    hblocks := fun a => (preparedModularGeneralDetector_blocks B rowSets hdim a).trans (by linarith only [hDP, h2PDg])
    hRv := fun j => (hRone j).trans (Real.one_le_exp hv0)
    hRiGrid := fun j => (hRi j).trans hExpv
    hδw := by linarith only [hDetect, hPw]
    hcoeff := fun j => (hdim.coefficients j).trans (hDP.trans (hPexp.trans hExpv))
    haxesGrid := (preparedModularGeneralDetector_grid_axes B rowSets U b S hdim).trans hDDg
    hfullAxes := hdim.axes.trans hDDg
    hfullOutputs := hdim.outputs.trans hDDg
    hambientCount := ?_
    hprofileBudget := hdim.profile.trans hDDg
    hBanalytic := hba0
    hDanalytic := hDgBa
    hcutoffAnalytic := hcutoff.trans hExpBa
    hcoordAnalytic := hCoordAnalytic
    hgridAnalytic := hSlotsExp.trans (Real.exp_le_exp.mpr h8PBa)
    hI := fun j => (hI j).trans hDP
    hn := fun j => (hn j).trans hDP
    hcoeffEarly := fun j => (hdim.coefficients j).trans hDP
    hRiEarly := hRi
    hVEarly := fun j => (hvolumeRatio j).trans (hV j) }
  · intro j
    simpa only [Fintype.card_coe] using (hdim.rows j).trans hDDg
  · simpa only [hm] using htailDg
  · apply (preparedModularGeneralDetector_ambient_count hJ).trans
    simpa only [hm] using hmPDg

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)


variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

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
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
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

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFullBoxPositiveLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uX uG uI uB uJ
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem allocated_fullBox_positive_law_at_model_budget (m : ℕ) :
    let A := Classical.choose (exists_allocated_fullBox_normalized_approximation.{uX,uG,uI,uB,uJ,0} m)
    ∀ {X : Type uX} {G : Type uG} [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G]
    {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
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
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
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
    (_hRootBudget : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedJointBaseDensity B U basis hb o hR hσ S X p hm
    let Z := selectedJointDensityMass bases stride T widths density
    ∃ (_hN : ∀ x, 0 < N x) (_hbases : bases.Nonempty) (_hbox : (integerBox N).Nonempty)
      (_hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∃ _hnormalizer : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∀ x, 2 * spatialTrimMargin τ N x ≤ N x := by
  intro A X G _ _ _ _ I _ _ n B _ _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hRootBudget hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT
    widths bases density Z
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, _⟩ :=
    (Classical.choose_spec
      (exists_allocated_fullBox_normalized_approximation.{uX,uG,uI,uB,uJ,0} m)).2
      B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall
      hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
      hW hWP hRootBudget hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize hrank hRank T hT
  exact ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin⟩

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorSpatialBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ b, Fintype (B b)]

theorem preparedModularDetector_narrow_width {q Mk nX : ℕ} (selection : Fin q ↪ G)
    {Pphysical coarseTarget : ℝ} (hp : 0 ≤ Pphysical) (htarget : 0 ≤ coarseTarget)
    (hMk : (Mk : ℝ) ≤ Real.exp Pphysical) (hq : ((q + 1 : ℕ) : ℝ) ≤ Pphysical)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical)
    (hnX : (nX : ℝ) ≤ Pphysical) :
    let R := spatialPrimitiveEnvelope Pphysical coarseTarget 0
    let ξLog := 2 * (R + spatialTupleToleranceLog R) + 4
    0 ≤ ξLog ∧
      (normalizedTupleNarrowWidth (Fin nX) (PrincipalTupleIndex B (layerSamplerDegree I n))
        selection Mk Pphysical coarseTarget)⁻¹ ≤ Real.exp ξLog := by
  intro R ξLog
  have hG := (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  have hN := (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hvars
  have hX : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical := by simpa only [Fintype.card_fin] using hnX
  have hR : 0 ≤ R := (spatialPrimitiveEnvelope_bounds hp htarget (le_refl 0)).1
  have ht := spatialTupleToleranceLog_nonneg hR
  refine ⟨by dsimp only [ξLog]; positivity, ?_⟩
  exact (normalizedTupleEarlyParameters_bound
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := Fin nX)
    selection hp htarget (le_refl 0) hMk hq hG hN hX).2

theorem preparedModularDetector_physical_root_of_variables
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    {P : ℝ} (_hP : 0 ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hS : (S.value : ℝ) ≤ Real.exp P) :
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ Real.exp (2 * P + 8) := by
  have hvarsExp : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp P :=
    hvars.trans (by linarith [Real.add_one_le_exp P])
  rw [allocatedPhysicalRootBudget_zero]
  calc
    _ ≤ Real.exp P * Real.exp P :=
      mul_le_mul hvarsExp hS (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularCanonicalDetectorPositive
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

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
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedModularCanonicalDetector_narrow_width_le_one
    (X T : Type*) [Fintype X] [Fintype T] {G : Type*} [Fintype G]
    {q : ℕ} (selection : Fin q ↪ G) (Mk : ℕ) (p E : ℝ) :
    normalizedTupleNarrowWidth X T selection Mk p E ≤ 1 := by
  exact min_le_left _ _

section Consumer

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
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

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

end Consumer

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Consumer

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
local notation "α" => allocatedModelUnitThreshold u pModel Kslice Ctail
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

variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

end Consumer

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedDetectedGain_lower (s count : ℕ) (Pdetect : Polynomial ℕ)
    {p q a α pGain : ℝ} (hα : Real.exp (-a) ≤ α)
    (hlog : slicedDetectionGainLog s (sampledSupportedSlicedDetectionConstant s Pdetect)
      count p q a ≤ pGain) :
    Real.exp (-pGain) / 2 ≤ allocatedDetectedGain s count Pdetect p q α / 2 := by
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact (Real.exp_le_exp.mpr (neg_le_neg hlog)).trans
    (slicedDetectionGain_lower s (sampledSupportedSlicedDetectionConstant s Pdetect) count hα)

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

theorem boundedCoefficientExponent_card_mono_embedding {A T : Type*}
    [Fintype A] [Fintype T] (e : A ↪ T) (h : ℕ) :
    Fintype.card (BoundedCoefficientExponent A h) ≤
      Fintype.card (BoundedCoefficientExponent T h) := by
  let f : BoundedCoefficientExponent A h → BoundedCoefficientExponent T h := fun d =>
    ⟨Finsupp.embDomain e d.val, by
      simpa only [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain] using d.property⟩
  apply Fintype.card_le_of_injective f
  intro a b hab
  exact Subtype.ext ((Finsupp.embDomain_injective e) (congrArg Subtype.val hab))

theorem coefficientAmbientIndex_card_from_layer_counts {K : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] {P : ℝ}
    (hP : 0 ≤ P)
    (hc : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ) ≤ P)
    (hJ : (∑ j : Fin m, (Fintype.card (J j) : ℝ)) ≤ m * P) :
    (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ m * P ^ 2 ∧
      (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ)) ≤ m * P ∧
      ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ m * P := by
  have hsum : (∑ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ)) ≤ m * P := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hc j)
  refine ⟨?_, hsum, ?_⟩
  · calc
      _ = ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ) *
          Fintype.card (J j) := by
        simp only [CoefficientAmbientIndex, CoefficientSlot, Fintype.card_sigma,
          Nat.cast_sum, Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro j _
        change (∑ _d : BoundedCoefficientExponent K (j.val + 1), (Fintype.card (J j) : ℝ)) = _
        simp
      _ ≤ ∑ j : Fin m, P * (Fintype.card (J j) : ℝ) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hc j) (Nat.cast_nonneg _))
      _ = P * ∑ j : Fin m, (Fintype.card (J j) : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ P * (m * P) := mul_le_mul_of_nonneg_left hJ hP
      _ = m * P ^ 2 := by ring
  · simpa only [NNReal.coe_sum, NNReal.coe_natCast] using hsum

theorem preparedModularGeneralDetector_jet_counts_of_geometry
    {m dim : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {O : Fin m → Type*} [∀ j, Fintype (O j)] {D P : ℝ}
    (selection : Fin dim ↪ G)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) O D) (hDP : D ≤ P) :
    ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ) ≤ P := by
  let e : Fin dim ↪ LayerSamplerVariables G I n B :=
    selection.trans Function.Embedding.inl
  intro j
  exact (Nat.cast_le.mpr (boundedCoefficientExponent_card_mono_embedding e (j.val + 1))).trans
    ((hdim.coefficients j).trans hDP)

variable {m dim nX : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {T : Type*} [Fintype T] (stride : Fin nX → ℕ)

theorem preparedModularGeneralDetector_sampling_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (_hm : K.m = m)
    {P L target Pphysical Qstride Pk : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L)
    (hAsample : 2 ≤ K.Asample)
    (hmP : (m : ℝ) ≤ P) (hdimP : (dim : ℝ) ≤ P)
    (hX : (nX : ℝ) ≤ P) (hT : (Fintype.card T : ℝ) ≤ 2 * P)
    (hJ : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ (m : ℝ) * P)
    (hcoeff : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ) ≤ P)
    (htarget : target ≤ P) (hphysical : Pphysical ≤ P)
    (hQstride : Qstride ≤ P) (hPk : Pk ≤ P)
    (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ P) :
    PreparedModularGeneralDetectorSamplingBounds (dim := dim) (J := J) (T := T) stride
      (preparedModularGeneralDetectorResources K dim P L) P L target Pphysical Qstride Pk := by
  let r := preparedModularGeneralDetectorResources K dim P L
  have hL := hP.trans hPL
  have bounds := ((Classical.choose_spec
    (exists_preparedModularGeneralDetector_resource_budget K dim)).2 hP hPL).1
  obtain ⟨_, _, _, _, hmassSample, hAmbientSample, hprojSample, hsampleSide, hLSide, _⟩ :=
    preparedModularGeneralDetectorResources_primitive_domination K dim hP hPL
  have hprojEq : r.Pproj = 4 * (L + 8)^2 := rfl
  have hproj1 : 1 ≤ r.Pproj := by nlinarith only [hprojEq, hL, sq_nonneg L]
  have hLproj : L ≤ r.Pproj := by nlinarith only [hprojEq, hL, sq_nonneg L]
  have hPproj : P ≤ r.Pproj := hPL.trans hLproj
  have h2Pproj : 2 * P ≤ r.Pproj := by
    nlinarith only [hprojEq, hL, hPL, sq_nonneg L]
  have hGainProj : P + 32 ≤ r.Pproj := by
    nlinarith only [hprojEq, hL, hPL, sq_nonneg L]
  have hframeProj : (2 * P + 1) * P ≤ r.Pproj := by
    have hsq : P^2 ≤ L^2 := pow_le_pow_left₀ hP hPL 2
    nlinarith only [hprojEq, hP, hPL, hsq, sq_nonneg L]
  have hprojSqMass : r.Pproj^2 ≤ r.Pmass := by
    change r.Pproj^2 ≤ (r.Pproj + K.Asample)^K.Asample
    have hAs : (0 : ℝ) ≤ K.Asample := Nat.cast_nonneg _
    exact (pow_le_pow_left₀ bounds.Pproj.1 (le_add_of_nonneg_right hAs) 2).trans
      (pow_le_pow_right₀ (by linarith only [hproj1, hAs]) hAsample)
  have hprojMass : r.Pproj ≤ r.Pmass :=
    (by nlinarith only [hproj1] : r.Pproj ≤ r.Pproj^2).trans hprojSqMass
  have hPmass : P ≤ r.Pmass := hPproj.trans hprojMass
  have hPsample : P ≤ r.Psample := hPmass.trans hmassSample
  have hprojSide : r.Pproj ≤ r.Pside := hprojSample.trans hsampleSide
  have hmassSide : r.Pmass ≤ r.Pside := hmassSample.trans hsampleSide
  have hPSide : P ≤ r.Pside := hPL.trans hLSide
  have hPeriodProj : ((m + 1 : ℕ) : ℝ) * Pk ≤ r.Pproj := by
    calc
      _ ≤ ((m + 1 : ℕ) : ℝ) * P := mul_le_mul_of_nonneg_left hPk (Nat.cast_nonneg _)
      _ ≤ (P + 1) * P := mul_le_mul_of_nonneg_right (by push_cast; linarith only [hmP]) hP
      _ ≤ (2 * P + 1) * P := mul_le_mul_of_nonneg_right (by linarith only [hP]) hP
      _ ≤ _ := hframeProj
  have hcoverBase : r.coverLog ≤ r.baseAmbient := by
    change r.coverLog ≤ r.Pproj + r.coverLog + r.Vlog + r.Nlog + r.Q +
      (layerTailDegree K.m + 1 : ℕ) * L + 3 * P + comparisonProfileBound + (2 ^ dim : ℕ) + 32
    have hdeg : 0 ≤ ((layerTailDegree K.m + 1 : ℕ) : ℝ) * L := by positivity
    have hprof : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
    have hpow : (0 : ℝ) ≤ (2^dim : ℕ) := Nat.cast_nonneg _
    linarith only [bounds.Pproj.1, bounds.Vlog.1, bounds.Nlog.1, bounds.Q.1, hdeg, hP, hprof, hpow]
  let A := 9 * (9 * (r.baseAmbient + r.idealQ) + 13) + 5
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    linarith only [bounds.baseAmbient.1, bounds.idealQ.1]
  have hbaseA : r.baseAmbient ≤ A := by
    dsimp only [A]; linarith only [bounds.baseAmbient.1, bounds.idealQ.1]
  have hambient : r.ambient = 2 * affineAmbientMassLog A + 7 * A + 1 := rfl
  have hmasslog := affineAmbientMassLog_nonneg hA0
  have hbaseAmbient : r.baseAmbient ≤ r.ambient := by
    linarith only [hambient, hmasslog, hbaseA, hA0]
  have hcoverSample := hcoverBase.trans (hbaseAmbient.trans hAmbientSample)
  have hFrame : (Fintype.card (Option (Fin dim) × Fin nX) : ℝ) ≤ r.Pmass := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    apply le_trans _ (hframeProj.trans hprojMass)
    exact mul_le_mul (by linarith only [hdimP, hP]) hX (Nat.cast_nonneg _)
      (by linarith only [hP])
  have hFrameProjection : (Fintype.card (Option T × Fin nX) : ℝ) ≤ r.Pproj := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    apply le_trans _ hframeProj
    exact mul_le_mul (by linarith only [hT]) hX (Nat.cast_nonneg _)
      (by linarith only [hP])
  have hmPproj : (m : ℝ) * P ≤ r.Pproj := by
    calc
      _ ≤ P * P := mul_le_mul_of_nonneg_right hmP hP
      _ ≤ (2 * P + 1) * P := mul_le_mul_of_nonneg_right (by linarith only [hP]) hP
      _ ≤ _ := hframeProj
  have hmPmass : (m : ℝ) * P^2 ≤ r.Pmass := by
    calc
      _ = ((m : ℝ) * P) * P := by ring
      _ ≤ r.Pproj * r.Pproj := mul_le_mul hmPproj hPproj hP bounds.Pproj.1
      _ = r.Pproj^2 := (pow_two _).symm
      _ ≤ _ := hprojSqMass
  have hAmb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ r.Pmass := by
    apply ((coefficientAmbientIndex_card_from_layer_counts hP hcoeff (by simpa only [Nat.cast_sum] using hJ)).1).trans hmPmass
  have hJet : ((∑ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ r.Pmass := by
    exact ((coefficientAmbientIndex_card_from_layer_counts hP hcoeff (by simpa only [Nat.cast_sum] using hJ)).2.2).trans (hmPproj.trans hprojMass)
  have hTau : (Real.exp (-Pphysical))⁻¹ = Real.exp Pphysical := by rw [Real.exp_neg, inv_inv]
  have hPrecision : (Real.exp (-target))⁻¹ = Real.exp target := by rw [Real.exp_neg, inv_inv]
  have hTauMass : (Real.exp (-Pphysical))⁻¹ ≤ Real.exp r.Pmass := by
    rw [hTau]
    exact Real.exp_le_exp.mpr (hphysical.trans hPmass)
  have hTauSample : (Real.exp (-Pphysical))⁻¹ ≤ Real.exp r.Psample :=
    hTauMass.trans (Real.exp_le_exp.mpr hmassSample)
  have hPrecisionSample : (Real.exp (-target))⁻¹ ≤ Real.exp r.Psample := by
    rw [hPrecision]
    exact Real.exp_le_exp.mpr (htarget.trans hPsample)
  have hStrideProj (i : Fin nX) : (stride i : ℝ) ≤ Real.exp r.Pproj :=
    (hstride i).trans (Real.exp_le_exp.mpr (hQstride.trans hPproj))
  have hStrideMass (i : Fin nX) : (stride i : ℝ) ≤ Real.exp r.Pmass :=
    (hStrideProj i).trans (Real.exp_le_exp.mpr hprojMass)
  exact {
    sample_nonneg := bounds.Psample.1
    mass_nonneg := bounds.Pmass.1
    projection_one := hproj1
    primitive_projection := hPproj
    late_projection := hLproj
    gain_projection := hGainProj
    period_projection := hPeriodProj
    profile_projection := hprofile.trans (hPproj.trans (by linarith [Real.add_one_le_exp r.Pproj]))
    projection_mass := hprojMass
    mass_sample := hmassSample
    cover_base := hcoverBase
    cover_sample := hcoverSample
    ambient_sample := hAmbientSample
    sample_side := hsampleSide
    projection_side := hprojSide
    mass_side := hmassSide
    primitive_side := hPSide
    late_side := hLSide
    physical_side := hphysical.trans hPSide
    target_side := htarget.trans hPSide
    X_sample := by simpa only [Fintype.card_fin] using hX.trans hPsample
    frame_sample := hFrame.trans hmassSample
    ambient_dimension_sample := hAmb.trans hmassSample
    jet_sample := (hJet.trans hmassSample).trans (by linarith [Real.add_one_le_exp r.Psample])
    stride_scale_nonneg := Real.exp_nonneg _
    stride_scale_sample := Real.exp_le_exp.mpr (hQstride.trans hPsample)
    stride_sample := fun i => (hStrideMass i).trans (Real.exp_le_exp.mpr hmassSample)
    tau_pos := Real.exp_pos _
    precision_pos := Real.exp_pos _
    tau_sample := by simpa only [one_div] using hTauSample
    epsilon_sample := by simpa only [one_div] using hPrecisionSample
    eta_sample := hPrecisionSample
    X_mass := by simpa only [Fintype.card_fin] using hX.trans hPmass
    frame_mass := hFrame
    ambient_dimension_mass := hAmb
    jet_mass := hJet.trans (by linarith [Real.add_one_le_exp r.Pmass])
    stride_mass := hStrideMass
    tau_mass := by simpa only [one_div] using hTauMass
    X_projection := by simpa only [Fintype.card_fin] using hX.trans hPproj
    variables_projection := hT.trans h2Pproj
    frame_projection := hFrameProjection
    stride_projection := hStrideProj
    tau_projection := by rw [hTau]; exact Real.exp_le_exp.mpr (hphysical.trans hPproj) }

theorem preparedModularGeneralDetector_sampling_bounds_of_geometry
    {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (rowSets : Fin m → Finset (Finset (Fin dim)))
    (selection : Fin dim ↪ G)
    (K : PreparedModularCanonicalDetectorResourceConstants) (hm : K.m = m)
    {P L D target Pphysical Qstride Pk : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L)
    (hAsample : 2 ≤ K.Asample)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim)
      (fun j => (rowSets j : Type)) D) (hDP : D ≤ P)
    (hX : (nX : ℝ) ≤ P)
    (hJ : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ (m : ℝ) * P)
    (htarget : target ≤ P) (hphysical : Pphysical ≤ P)
    (hQstride : Qstride ≤ P) (hPk : Pk ≤ P)
    (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride) :
    PreparedModularGeneralDetectorSamplingBounds (dim := dim) (J := J)
      (T := LayerSamplerVariables G I n B) stride
      (preparedModularGeneralDetectorResources K dim P L) P L target Pphysical Qstride Pk := by
  apply preparedModularGeneralDetector_sampling_bounds stride K hm hP hPL hAsample
    (hdim.degree.trans hDP)
    (by simpa only [Fintype.card_fin] using hdim.cube.trans hDP) hX
  · exact (preparedModularGeneralDetector_variable_count B rowSets hdim).trans
      (mul_le_mul_of_nonneg_left hDP (by norm_num))
  · exact hJ
  · exact preparedModularGeneralDetector_jet_counts_of_geometry B selection hdim hDP
  · exact htarget
  · exact hphysical
  · exact hQstride
  · exact hPk
  · exact hstride
  · exact hdim.profile.trans hDP

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorLateCoarseConsumer
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m s : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type} [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

include U b o hb bW

theorem preparedModularGeneralDetector_period_prefactor {P D Pk Qstride pDetect Pnum : ℝ} {nX : ℕ}
    (hP : 0 ≤ P)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hDP : D ≤ P) (hnX : (nX : ℝ) ≤ P) (hPk : Pk ∈ Set.Icc 0 P)
    (hQstride : Qstride ∈ Set.Icc 0 P) (hp : pDetect ∈ Set.Icc 0 P)
    (hPnum : Pnum ∈ Set.Icc 0 P) :
    let r := preparedModularCanonicalDetectorResources (preparedModularGeneralDetectorConstants m s) P
    let O := fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)
    let L := ((m + 1 : ℕ) : ℝ) * Pk
    let qlog := L + nX * Qstride
    let maskLog := (Fintype.card (LayerSamplerAxis I n) : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)
    let labelLog := (∑ j, (n j : ℝ) * L) + ∑ j, (Fintype.card (Q j) : ℝ) * L
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) + maskLog
    P ≤ r.Q ∧ L ∈ Set.Icc 0 r.Q ∧ qlog ∈ Set.Icc 0 r.Q ∧
      maskLog ∈ Set.Icc 0 r.Q ∧ labelLog ∈ Set.Icc 0 r.Q ∧ Fmodel ∈ Set.Icc 0 r.Fpref := by
  intro r O L qlog maskLog labelLog Fmodel
  have hQ (j : Fin m) : (Fintype.card (Q j) : ℝ) ≤ P :=
    ((allocatedProfile_dimensions U b o B hdim hb bW).2 j).trans hDP
  have hn := (preparedModularGeneralDetector_layer_axes B
    (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hdim).2
  have haxes := hdim.axes.trans hDP
  let Cgrid := (preparedModularGeneralDetectorConstants m s).Cgrid
  obtain ⟨hPQ, hL, hq, _, hmask, hlabel, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetector_period_budget.{0,0} m (s + 1) Cgrid)).2
      (A := LayerSamplerAxis I n) (nX := nX) n Q hP hnX hPk hQstride hp haxes (fun j => (hn j).trans hDP) hQ
  have hF := (Classical.choose_spec (exists_canonicalSlicedModelPrefactor_budget.{0,0} m (s + 1))).2
    (I := I) (n := n) (Q := Q) hP hPnum hPk haxes hQ
  refine ⟨hPQ, hL, hq, hmask, hlabel, ?_⟩
  change 0 ≤ Fmodel ∧ Fmodel ≤ _
  have heq : Fmodel = (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L) := by
    dsimp only [Fmodel, maskLog]
    ring
  rw [heq]
  exact hF

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

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
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
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

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

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
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
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


