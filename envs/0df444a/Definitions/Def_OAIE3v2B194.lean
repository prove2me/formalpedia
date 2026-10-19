-- Prove2me | Definitions.Def_OAIE3v2B194
-- name    : OAIE3v2B194
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:45:36.09188+00:00
-- url     : https://prove2.me/theorems/0f98f0c4-ec8e-440e-ab8f-8458eb597244
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 197 of 311
-- statement:
--   Definitions bundle 197 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B170`, `OAIE3v2B172`, `OAIE3v2B176` of this split.
--
--   Modules: `Dynamics/PreparedFiniteForwardActualNativeBudget.lean`, `Estimates/AllocatedApproximationError.lean`, `Estimates/AllocatedEnormousProfiles.lean`, `Estimates/AllocatedFixedScaleJointMarginal.lean`, `Estimates/AllocatedSlicedCoarseSource.lean`, `Estimates/AllocatedTrimmedVectorSite.lean`, `Estimates/CanonicalEmptyLayerGeometry.lean`, `Estimates/NormalizedNativeFamilyMonotone.lean`, `Estimates/PreparedModularGeneralDetectorNativeBounds.lean`, `Estimates/SampledNativeModel.lean`, `Fourier/AllocatedPositiveFourierData.lean`, `Geometry/AllocatedCanonicalSpatialCoarseSource.lean`, `Geometry/CoefficientSquareSpatialBudget.lean`, `Lattices/AllocatedIntegerKernelComparison.lean`, `Lattices/CertifiedAffineCutoffCost.lean`, `Lattices/ContainedFullIntervalResidueIdentity.lean`, `Linear/AllocatedFixedDensityProjection.lean`, `Polynomial/AllocatedCenteredConditionalPolynomial.lean`, `Polynomial/OrdinaryPolynomialPhaseAffineInverse.lean`, `Probability/AllocatedLongIntegralMass.lean`, `Probability/AllocatedLongJetMixture.lean`, `Probability/FullFrozenChartMass.lean`, `Probability/PositiveDensityNormalization.lean`, `Probability/PreparedModularGeneralCenteredLaw.lean`, `Sampling/AveragedNormalizedTwistForecastJointModel.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B170
import Definitions.Def_OAIE3v2B172
import Definitions.Def_OAIE3v2B176

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeModel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct Pointwise BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {f : X → ℂ}

theorem twistedNativeSampleFunctions_balanced {I : Type*} (twist : I → X → ℂ) :
    Balanced ℂ (twistedNativeSampleFunctions w degree p sample twist) := by
  rintro c hc _ ⟨f, hf, rfl⟩
  rcases hf with rfl | ⟨i, g, ⟨G⟩, rfl⟩
  · exact Or.inl (smul_zero c)
  · refine Or.inr ⟨i, c • g, ⟨G.smul c hc⟩, ?_⟩
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end Erdos3

end

section

namespace Erdos3.NativeSampleModel

open CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [instance] VerticalExpansion.finite

end Erdos3.NativeSampleModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

include hR hσ1 henormous in
theorem allocatedEnormous_constant_width :
    8*(probabilityProfileLipschitz : ℝ) ≤ (R j/4)*(basisAxisScale (basis j) i : ℝ) := by
  have ht : tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))) ≤ R j/4 := by
    unfold tailProfileSize
    apply (div_le_iff₀ (by positivity)).mpr
    have hn := Nat.cast_nonneg (α := ℝ)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
    have hp := mul_nonneg (hR j).le hn
    nlinarith [mul_le_mul_of_nonneg_right hσ1 (hR j).le]
  have hLK : (S.value : ℝ) ≤ basisAxisScale (basis j) i := by
    have hpow : S.value ≤ S.value^(layerTailDegree m+1) := by
      calc
        _ = S.value^1 := by simp
        _ ≤ _ := Nat.pow_le_pow_right S.positive (by omega)
    exact_mod_cast hpow.trans henormous.le
  exact (S.width j).trans (mul_le_mul ht hLK (Nat.cast_nonneg _)
    (div_pos (hR j) (by norm_num)).le)

include hR hσ hσ1 henormous in
theorem allocatedEnormous_profile_width_large (d) :
    8*(probabilityProfileLipschitz : ℝ) ≤
      allocatedIntegerProfileWidths (G := G) B R σ j i d * allocatedIntegerProfileScales B U basis S j i d := by
  exact integerPolynomialProfile_width_large
    (P := layerIntegerPrincipalSlots B j i) (j₀ := constantCoefficientSlot _ _)
    (h := j.val+1) (K := basisAxisScale (basis j) i) (L := S.value) (s := layerTailDegree m)
    (hh := Nat.zero_lt_succ _) (hL := S.positive)
    (T := layerSamplerBox B U basis S)
    (hT := fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (hTL := layerSamplerBox_le B U basis S) (e := Subtype.val)
    (he := fun d => d.property.trans (layerDegree_le_tailDegree j))
    (ρ := R j/4) (γ := principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (ε := tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))
    (hγ := principalProfileSize_pos (hR j) _) (hε := tailProfileSize_pos (hR j) (hσ j) _)
    (hgap := S.gap j i) (hεL := S.width j)
    (ha := allocatedEnormous_active B U basis S j i henormous) (henormous := henormous)
    (hconst := allocatedEnormous_constant_width B U basis hR S j i hσ1 henormous)
    (he₀ := rfl) (hprincipal := allocatedEnormous_principalScale B U basis S j i henormous) d

include hR hσ hσ1 henormous in
theorem allocatedEnormous_profile_sum_pos :
    0 < coefficientWeightSum (affineProductProfile (allocatedIntegerProfileCenters (G := G) B R j i)
      (allocatedIntegerProfileWidths B R σ j i)) (allocatedIntegerProfileScales B U basis S j i) :=
  affineProductProfile_sample_sum_pos _ _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i)
    (allocatedIntegerProfileScales_pos B U basis S j i)
    (allocatedEnormous_profile_width_large B U basis hR hσ S j i hσ1 henormous)

noncomputable def allocatedEnormousProfilePMF :
    PMF (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ) :=
  coefficientPMF (affineProductProfile (allocatedIntegerProfileCenters B R j i)
    (allocatedIntegerProfileWidths B R σ j i))
    (affineProductProfile_nonneg _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i))
    (allocatedIntegerProfileScales B U basis S j i) (allocatedIntegerProfileScales_pos B U basis S j i)
    (allocatedIntegerProfile_support B hR hσ j i hσ1)
    (allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityNormalization
namespace OAI

section

namespace Erdos3

theorem positiveProjectionAccuracy_normalizer {p Z : ℝ} (hp : 0 ≤ p)
    (hZ : |Z - 1| ≤ 3 * positiveProjectionAccuracy p) :
    |Z - 1| ≤ Real.exp (-p) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      0 < Z ∧ Z⁻¹ ≤ 2 := by
  have he := positiveProjectionAccuracy_mass_bound hp
  have hhalf := hZ.trans he.2
  have hlo : 1 / 2 ≤ Z := by have h := (abs_le.mp hhalf).1; linarith
  have hhi : Z ≤ 3 / 2 := by have h := (abs_le.mp hhalf).2; linarith
  have hpos : 0 < Z := by linarith
  refine ⟨hZ.trans he.1, ⟨hlo, hhi⟩, hpos, ?_⟩
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hlo
  simpa only [one_div, inv_div, inv_one, div_one, inv_inv] using h

theorem selectedJointDensityMass_positive_accuracy {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty) (modulus : I → ℕ)
    (T : Finset (ColumnResiduePattern K I modulus)) (W : K × I → ℝ)
    (D : B → (K × I → ℤ) → ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hD : ∀ a, |selectedResidueDensityMass modulus T W (D a) - 1| ≤
      3 * positiveProjectionAccuracy p) :
    let Z := selectedJointDensityMass A modulus T W D
    |Z - 1| ≤ Real.exp (-p) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      0 < Z ∧ Z⁻¹ ≤ 2 :=
  positiveProjectionAccuracy_normalizer hp (selectedJointDensityMass_close A hA modulus T W D hD)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedIntegerKernelComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

noncomputable def allocatedIntegerKernelPMF (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
    (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i) : PMF (O j → ℤ) :=
  (allocatedEnormousProfilePMF B U basis hR hσ S j i hσ1 henormous).map
    (fun a => allocatedPartitionedJetMatrix B U basis S x u v rows j *ᵥ a)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedLongJetMixture
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

noncomputable def allocatedLongJetFactor :
    ∀ a : {a // ¬grid a}, CoefficientJetAxisRow O a.val → ℝ
  | ⟨⟨j, .inl i⟩, _⟩ =>
      allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j)
        (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
  | ⟨⟨j, .inr i⟩, ha⟩ =>
      fun z => (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j)
        (Nat.lt_of_not_ge ha) z).toReal

noncomputable def allocatedLongJetDensity (z : AllocatedLongJetRows B U basis S O) : ℝ :=
  ∏ a, allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a (z a)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

omit [Fintype α] in
theorem allocatedPhysicalCube_directions_bound (i : α) (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)| ≤ S.value := by
  cases k with
  | inl g =>
    have hx := Finset.mem_Ico.mp (x g (some i)).property
    change |((x g (some i) : ℤ) : ℝ)| ≤ S.value
    exact_mod_cast abs_le.mpr ⟨hx.1, hx.2.le⟩
  | inr j =>
    have hy := Finset.mem_Ico.mp (y j (some i)).property
    have hbound : |(y j (some i) : ℤ)| ≤ allocatedPrincipalSides B U basis S j :=
      abs_le.mpr ⟨hy.1, hy.2.le⟩
    change |((y j (some i) : ℤ) : ℝ)| ≤ S.value
    exact (by exact_mod_cast hbound : |((y j (some i) : ℤ) : ℝ)| ≤
      allocatedPrincipalSides B U basis S j).trans
        (Nat.cast_le.mpr (allocatedPrincipalSides_le_scale B U basis S j))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ContainedFullIntervalResidueIdentity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (modulus : ℕ) (hm : 0 < modulus)
variable (r : PrincipalTupleIndex B h → Option α → ZMod modulus)
variable (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)

local notation "weights" => principalResidueWeights B h H hH modulus hm r hsize
local notation "tupleMap" => containedProgressionTupleMap B h L H step c hL hsubset

noncomputable def containedProgressionResidueLaw :
    FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) := (weights).fiberLaw tupleMap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedApproximationError
namespace OAI

section

namespace Erdos3

theorem allocated_native_approximation_error
    {u p Q P K cap tau ε : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q)
    (hK : 0 ≤ K) (hcap : 0 ≤ cap)
    (hKP : K ≤ Real.exp p) (hcapP : cap ≤ Real.exp p)
    (htau : tau ≤ Real.exp (-(u + 3)))
    (hP : u + 2 * p + Q + 30 ≤ P)
    (hε : ε ≤ 6 * positiveProjectionAccuracy P) :
    2 * tau + 2 * K * (cap + 2 / Real.exp (-Q)) * ε ≤ Real.exp (-u) := by
  have hP0 : 0 ≤ P := by linarith
  have hεP : ε ≤ 2 * Real.exp (-P) := by
    have h := (positiveProjectionAccuracy_mass_bound hP0).1
    linarith
  have hcapQ : cap + 2 / Real.exp (-Q) ≤ 3 * Real.exp (p + Q) := by
    have h1 := Real.exp_le_exp.mpr (le_add_of_nonneg_right hQ : p ≤ p + Q)
    have h2 := Real.exp_le_exp.mpr (le_add_of_nonneg_left hp : Q ≤ p + Q)
    simp only [Real.exp_neg, div_eq_mul_inv, inv_inv]
    linarith
  have htail : 2 * K * (cap + 2 / Real.exp (-Q)) * ε ≤
      12 * Real.exp (2 * p + Q - P) := by
    calc
      _ ≤ 2 * K * (cap + 2 / Real.exp (-Q)) * (2 * Real.exp (-P)) :=
        mul_le_mul_of_nonneg_left hεP (by positivity)
      _ ≤ 2 * Real.exp p * (3 * Real.exp (p + Q)) * (2 * Real.exp (-P)) := by
        gcongr
      _ = 12 * (Real.exp p * Real.exp (p + Q) * Real.exp (-P)) := by ring
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
  have h3 : 2 * Real.exp (-3 : ℝ) ≤ 1 / 2 := by
    have he : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
    calc
      _ = 2 / Real.exp 3 := by rw [Real.exp_neg, div_eq_mul_inv]
      _ ≤ 2 / (4 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
      _ = _ := by norm_num
  have h30 : 12 * Real.exp (-30 : ℝ) ≤ 1 / 2 := by
    have he : (24 : ℝ) ≤ Real.exp 30 := by linarith [Real.add_one_le_exp (30 : ℝ)]
    calc
      _ = 12 / Real.exp 30 := by rw [Real.exp_neg, div_eq_mul_inv]
      _ ≤ 12 / (24 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
      _ = _ := by norm_num
  have hsmall : 2 * tau ≤ Real.exp (-u) / 2 := by
    calc
      _ ≤ 2 * Real.exp (-(u + 3)) := mul_le_mul_of_nonneg_left htau (by norm_num)
      _ = Real.exp (-u) * (2 * Real.exp (-3)) := by rw [neg_add, Real.exp_add]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h3 (Real.exp_nonneg (-u))]
  have htail' : 2 * K * (cap + 2 / Real.exp (-Q)) * ε ≤ Real.exp (-u) / 2 := by
    apply htail.trans
    calc
      _ ≤ 12 * Real.exp (-u - 30) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
      _ = Real.exp (-u) * (12 * Real.exp (-30)) := by rw [sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h30 (Real.exp_nonneg (-u))]
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientSquareSpatialBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem coefficientErrorPeriod_exp_sq {m M period : ℕ} {P : ℝ} (hP : 0 ≤ P)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ P) (hM : (M : ℝ) ≤ Real.exp P)
    (hperiod : period ≤ M ^ (m + 1)) : (period : ℝ) ≤ Real.exp (P ^ 2) := by
  have hcast : (period : ℝ) ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hperiod
  exact hcast.trans (by
    simpa only [pow_two] using pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hM hP (m + 1) hm)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedPositiveFourierData
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)

include hC hV in
theorem exists_allocated_positive_fourier_data (q : ℕ)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {p : ℝ} (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp p) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp p)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp p) (hLP : (S.value : ℝ) ≤ Real.exp p)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp p) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp p) :
    let Q := positiveComparisonDataBudget m q p
    let b := allocatedFourierLogBudget m (2 * p + 4)
    ((allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) ≤ Real.exp b) ∧
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ) (coeff : F → ℂ),
      (∀ t j d, d.degree ≤ j.val + 1 → ∀ i, |(frequency t j d i : ℝ)| ≤ Real.exp Q) ∧
      (∑ t, ‖coeff t‖) ≤ Real.exp Q ∧
      ∀ z, ‖(allocatedCoefficientDensity B U basis hb o hR hσ S z : ℂ) -
        coefficientTorusFourierSum U frequency coeff z‖ ≤ positiveProjectionAccuracy p := by
  let P := 2 * p + 4
  have hP : 0 ≤ P := by dsimp [P]; linarith
  have hpP : p ≤ P := by dsimp [P]; linarith
  have hE := Real.exp_le_exp.mpr hpP
  have hdata := allocatedCoefficient_fourier_input_budget B (J := J) R σ S.value S.positive C V
    hP (hm.trans hpP) (hK.trans hpP) hR hσ
    (fun j => (hRP j).trans hE) (fun j => (hσP j).trans hE)
    (fun j => (hcount j).trans hpP) (fun j => (hI j).trans hpP) (fun j => (hn j).trans hpP)
    (fun j => (hJ j).trans hpP) (hAP.trans hE) (hLP.trans hE)
    (fun j => (hCP j).trans hE) (fun j => (hVP j).trans hE)
  refine ⟨hdata.2.2.1, ?_⟩
  obtain ⟨F, inst, frequency, coeff, _, hfreq, hcoeff, happ⟩ :=
    exists_allocated_coefficient_uniform_fourier B U basis hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall hP (hm.trans hpP) (hK.trans hpP)
      (fun j => (hRP j).trans hE) (fun j => (hσP j).trans hE)
      (fun j => (hcount j).trans hpP) (fun j => (hI j).trans hpP) (fun j => (hn j).trans hpP)
      (fun j => (hJ j).trans hpP) (hAP.trans hE) (hLP.trans hE)
      (fun j => (hCP j).trans hE) (fun j => (hVP j).trans hE)
      (show 0 < positiveProjectionAccuracy p from Real.exp_pos _)
      (by simp only [positiveProjectionAccuracy, Real.exp_neg, inv_inv]; exact le_rfl)
  let _ := inst
  have hQ := (positiveComparisonDataBudget_bounds m q hp).2.2.2.1
  have hF := allocatedFourierOutputBudget_dominates m hP
  refine ⟨F, inst, frequency, coeff, ?_, ?_, happ⟩
  · exact fun t j d hd i => (hfreq t j d hd i).trans (Real.exp_le_exp.mpr (hF.2.1.trans hQ))
  · exact hcoeff.trans (Real.exp_le_exp.mpr (hF.2.2.trans hQ))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedDensityProjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem spatialWidthFraction_le_allocated_width {K X : Type*} {P W τ : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P) (hτ : 0 ≤ τ)
    (N : X → ℕ) (z : Option K × X) :
    spatialWidthFraction P τ * (N z.2 : ℝ) ≤ trimmedSpatialWidths W τ N z := by
  exact (spatialWidthFraction_le_trimmed_width P hτ N z).trans
    (trimmedSpatialWidths_antitone_budget hW
      (hWP.trans (Real.exp_le_exp.mpr (by linarith))) hτ N z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

noncomputable def allocatedJointBaseDensity (base : X → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) : ℝ :=
  allocatedCoefficientDensity B U b hb o hR hσ S (affineSampleCoefficientTorus U
    (fun j => translate (fun t => (base t : ℝ)) (poly j))
    (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (poly j) (hmem j))
    (fun k t => (z (k, t) : ℝ)))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype X] in
theorem allocatedJointBaseDensity_nonneg (base : X → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    0 ≤ allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem base z :=
  canonicalCoefficientDensity_nonneg U b hb o (allocatedLayerCenters B U b S)
    (allocatedLayerWidths B U b S) (allocatedLayerIntegerPMFs B U b hR hσ S)
    (allocatedLayerWidths_pos B U b hR hσ S) _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

noncomputable def allocatedOriginalPathLaw :
    FiniteProbabilityWeights (bases × rectangularWeightIndices 0 widths 1) :=
  selectedJointFiniteLaw bases hbases stride cells widths hwidths hmass baseDensity
    (allocatedJointBaseDensity_nonneg B U b hb o hR hσ S X poly hmem) htotal

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

theorem exists_allocated_narrow_normalization (m : ℕ) :
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
    let pa := fun (base : X → ℤ) j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun (base : X → ℤ) j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    let density := fun base z => allocatedCoefficientDensity B U basis hb o hR hσ S
      (affineSampleCoefficientTorus U (pa base) (hma base) (fun k d => (z (k, d) : ℝ)))
    ∃ (_hwidths : ∀ z, 0 < widths z) (_hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
      (∀ base, |selectedResidueDensityMass stride T widths (density base) - 1| ≤
        3 * positiveProjectionAccuracy P) ∧
      ∀ (bases : Finset (X → ℤ)), bases.Nonempty →
        let Z := selectedJointDensityMass bases stride T widths density
        |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2 := by
  obtain ⟨A₀, _, hmass⟩ := exists_affine_coefficient_density_mass m
  obtain ⟨b, _, hbnd⟩ := exists_positiveComparisonDataBudget_bound m 0
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + 8 * Polynomial.X + 128 + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths pa hma density
  have h2P : 0 ≤ 2 * P := mul_nonneg (by norm_num) hP
  have hP2P : P ≤ 2 * P := by linarith
  have hτξ : 0 < ξ * τ := mul_pos hξ hτ
  have hτξP : (ξ * τ)⁻¹ ≤ Real.exp (2 * P) := by
    rw [mul_inv_rev]
    calc
      τ⁻¹ * ξ⁻¹ ≤ Real.exp P * Real.exp P := by gcongr
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
  let Q := positiveComparisonDataBudget m 0 P + spatialSamplingBudget (2 * P)
  have hdata := positiveComparisonDataBudget_bounds m 0 hP
  have hdataQ : positiveComparisonDataBudget m 0 P ≤ Q :=
    le_add_of_nonneg_right (h2P.trans (le_spatialSamplingBudget h2P))
  have hspatialQ : spatialSamplingBudget (2 * P) ≤ Q := le_add_of_nonneg_left hdata.1
  have hPQ : P ≤ Q := hdata.2.1.trans hdataQ
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hExp := Real.exp_le_exp.mpr hPQ
  have hcut : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    have hbase : Q + (A₀ : ℝ) ≤ (P + b) ^ b + 8 * P + 128 + A₀ := by
      have h := hbnd P hP
      dsimp [Q, spatialSamplingBudget]
      linarith
    calc
      _ ≤ ((P + b) ^ b + 8 * P + 128 + A₀) ^ A₀ :=
        pow_le_pow_left₀ (add_nonneg hQ (Nat.cast_nonneg A₀)) hbase A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨_, F, inst, frequency, coeff, hfreq, hcoeff, happ⟩ :=
    exists_allocated_positive_fourier_data B U basis hb o S C V hC hV 0
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hmSize hK hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  let _ := inst
  have hspec := allocatedCoefficientDensity_spec B U basis hb o hR hσ S
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hwidths := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ N hN
  have hwidthLower (z : Option (LayerSamplerVariables G I n B) × X) :
      spatialWidthFraction (2 * P) (ξ * τ) * (N z.2 : ℝ) ≤ widths z :=
    (spatialWidthFraction_le_allocated_width h2P hW
      (hWP.trans (Real.exp_le_exp.mpr hP2P)) hτξ.le N z).trans
        (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
  have hη : 0 < positiveProjectionAccuracy P := Real.exp_pos _
  have hηQ : 1 / positiveProjectionAccuracy P ≤ Real.exp Q := by
    simp only [one_div, positiveProjectionAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr (hdata.2.2.1.trans hdataQ)
  have hlocal (base : X → ℤ) :
      ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z,
        |selectedResidueDensityMass stride T widths (density base) - 1| ≤
          3 * positiveProjectionAccuracy P := by
    have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa base j) :=
      degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
    have hranka (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pa base j) :=
      (hasLayerSamplingRank_translate_iff _ _ _ _ _ _ (hp j)).mpr (hrank j)
    obtain ⟨hZ, hclose⟩ := hmass hQ (hX.trans hPQ) (hdim.trans hPQ) U μ
      (Real.exp_nonneg Q) le_rfl frequency
      (fun t j d hd i => (hfreq t j d hd i).trans (Real.exp_le_exp.mpr hdataQ))
      coeff (Real.exp_nonneg Q) le_rfl (hcoeff.trans (Real.exp_le_exp.mpr hdataQ))
      (pa base) hpa (hma base) stride hs (Real.exp_nonneg Q) le_rfl
      (spatialWidthFraction_pos (2 * P) hτξ) hη
      ((spatialWidthFraction_inv_le h2P hτξ hτξP).trans (Real.exp_le_exp.mpr hspatialQ)) hηQ
      (fun d => (hsP d).trans hExp) (fun d => (N d : ℝ))
      (fun d => (Real.exp_le_exp.mpr hcut).trans (hsize d)) hranka
      ((Real.exp_le_exp.mpr hcut).trans hRank) T hT widths hwidths
      hwidthLower
      (allocatedCoefficientDensity B U basis hb o hR hσ S) hspec.2.2.1 hspec.2.2.2.1 hη.le happ
    refine ⟨hZ, ?_⟩
    change |selectedResidueDensityMass stride T widths (density base) - 1| ≤
      2 * positiveProjectionAccuracy P + positiveProjectionAccuracy P at hclose
    linarith
  obtain ⟨hZ, _⟩ := hlocal 0
  have hclose (base) := (hlocal base).choose_spec
  exact ⟨hwidths, hZ, hclose, fun bases hbases =>
    selectedJointDensityMass_positive_accuracy bases hbases stride T widths density hP hclose⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I J : Fin m → Type*} {n : Fin m → ℕ}
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type*)

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}

theorem emptyLayerVariables_card :
    Fintype.card (LayerSamplerVariables G I n B) = Fintype.card G :=
  Fintype.card_congr (emptyLayerVariablesEquiv B)

variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedExternalCandidateRootBudget_empty_layers :
    allocatedExternalCandidateRootBudget B U b S =
      (Fintype.card G : ℝ) * S.value := by
  unfold allocatedExternalCandidateRootBudget
  rw [emptyLayerVariables_card]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedLongIntegralMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := O) a)

noncomputable def allocatedLongProfileDensity (f : (output → ℝ) → ℝ)
    (z : AllocatedLongJetRows B U b S O) : ℝ :=
  (∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)) *
    f (allocatedLongJetRealCoordinates B U b S z) / scale

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedCoarseSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)

noncomputable def allocatedRecenteredCoarseMesh (Q : ℝ≥0) (V ε : ℝ) : ℝ :=
  spatialTupleCoarseMesh (Fintype.card X)
    ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) * anisotropicSpatialDensityCap selection (1 / (M : ℝ)))
    V ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
      (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q)) ε

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

noncomputable def allocatedEarlyRecenteredMesh {dim : ℕ} {G : Type*} [Fintype G]
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) (M modulus : ℕ) (p E : ℝ) : ℝ :=
  allocatedRecenteredCoarseMesh (M := M) X modulus selection (allocatedPrimitiveRootRatio (Real.exp p))
    (Real.exp (coefficientErrorVolumeLog p + 4)) (Real.exp (-E))

theorem allocatedEarlyRecenteredMesh_partition_budget (m : ℕ) {dim : ℕ}
    {G : Type*} [Fintype G] (X : Type*) [Fintype X]
    (selection : Fin dim ↪ G) {M modulus : ℕ} {p E : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp p) (hmod : modulus ≤ M ^ (m + 1)) :
    let r := allocatedEarlyRecenteredMesh X selection M modulus p E
    let T := allocatedEarlyCoarseInput m dim (p + E)
    0 < r ∧ r ≤ 1 / 4 ∧ r⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog T) ∧
      allocatedSpatialCoefficientCap X selection M modulus r ≤
        Real.exp (coarseSpatialPartitionLog T) := by
  let s := p + E
  let R := s + (m + dim + 2 : ℕ)
  let T := allocatedEarlyCoarseInput m dim s
  have hs : 0 ≤ s := add_nonneg hp hE
  have hR2 : 2 ≤ R := by
    dsimp [R]
    push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hR : 0 ≤ R := by linarith only [hR2]
  obtain ⟨hT, hRT, hcubeT, hcapT, hlipT, hmassT⟩ := allocatedEarlyCoarseInput_bounds m dim hs
  change R ≤ T at hRT
  have hpR : p + 1 ≤ R := by
    dsimp [R, s]; push_cast
    linarith only [hE, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hpR' : p ≤ R := by linarith only [hpR]
  have hER : E ≤ R := by
    dsimp [R, s]; push_cast
    linarith only [hp, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hmR : ((m + 1 : ℕ) : ℝ) ≤ R := by
    dsimp [R]; push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) dim]
  have hnR : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ R := by
    simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    dsimp [R]; push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) m]
  have hGR := hG.trans hpR'
  have hXR := hX.trans hpR'
  have hMR := hMP.trans (Real.exp_le_exp.mpr hpR')
  have hmodR := coefficientErrorPeriod_exp_sq hR hmR hMR hmod
  have hΓ : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) ≤ Real.exp (R ^ 3) :=
    (pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hmodR (sq_nonneg R) _ hnR).trans_eq
      (congrArg Real.exp (by ring))
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hC0 := anisotropicSpatialDensityCap_nonneg selection hκ
  have hL0 := anisotropicSpatialDensityLip_nonneg selection hκ
  have hC := anisotropicSpatialDensityCap_exp_bound selection hR hM hMR hnR hGR
  have hfree : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ 2 * R := by
    have hcard := selectedColumn_card selection
    have hb : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ R :=
      (Nat.cast_le.mpr (by omega)).trans hGR
    linarith only [hb, hR]
  have hprofile := spatialProfileLog_le_fixedEnvelope _ _ hR hnR hfree
  have hL : anisotropicSpatialDensityLip selection (1 / (M : ℝ)) ≤
      Real.exp (spatialLipschitzEnvelope R) :=
    (anisotropicSpatialDensityLip_le_exp selection hR hM hMR hnR hGR).trans
      (Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonneg_left hprofile (by norm_num))))
  have hQ : (allocatedPrimitiveRootRatio (Real.exp p) : ℝ) ≤ Real.exp R := by
    rw [(allocatedPrimitiveRootRatio_bounds (Real.exp_pos p).le).1, add_comm]
    exact (one_add_le_exp_succ hp (le_refl (Real.exp p))).trans (Real.exp_le_exp.mpr hpR)
  have hcapInput : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ)) ≤ Real.exp T := by
    calc
      _ ≤ Real.exp (R ^ 3) * Real.exp (anisotropicSpatialCapLog R) := by gcongr
      _ = Real.exp (R ^ 3 + anisotropicSpatialCapLog R) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcapT
  have hlipInput : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * allocatedPrimitiveRootRatio (Real.exp p)) ≤
      Real.exp T := by
    calc
      _ ≤ Real.exp (R ^ 3) * (Real.exp (spatialLipschitzEnvelope R) * Real.exp R) := by gcongr
      _ = Real.exp (R ^ 3 + spatialLipschitzEnvelope R + R) := by
        rw [← Real.exp_add, ← Real.exp_add, add_assoc]
      _ ≤ _ := Real.exp_le_exp.mpr hlipT
  have hmassLog : coefficientErrorVolumeLog p ≤ coefficientErrorVolumeLog R := by
    unfold coefficientErrorVolumeLog
    gcongr
  have hmassInput : Real.exp (coefficientErrorVolumeLog p + 4) ≤ Real.exp T :=
    Real.exp_le_exp.mpr ((add_le_add hmassLog le_rfl).trans hmassT)
  have hε : 0 < Real.exp (-E) := Real.exp_pos _
  have hεInput : (Real.exp (-E))⁻¹ ≤ Real.exp T := by
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr (hER.trans hRT)
  have hsquare : R ^ 2 ≤ R ^ 3 := by
    calc
      R ^ 2 = R ^ 2 * 1 := (mul_one _).symm
      _ ≤ R ^ 2 * R := mul_le_mul_of_nonneg_left (by linarith only [hR2]) (sq_nonneg R)
      _ = R ^ 3 := by ring
  have hmodInput := hmodR.trans (Real.exp_le_exp.mpr (hsquare.trans hcubeT))
  have hΓInput := hΓ.trans (Real.exp_le_exp.mpr hcubeT)
  have hCInput := hC.trans (Real.exp_le_exp.mpr
    (show anisotropicSpatialCapLog R ≤ T from
      (le_add_of_nonneg_left (pow_nonneg hR 3)).trans hcapT))
  have hcap0 := mul_nonneg (pow_nonneg (Nat.cast_nonneg modulus (α := ℝ)) (Fintype.card (Unit ⊕ Fin dim))) hC0
  have hlip0 := mul_nonneg (pow_nonneg (Nat.cast_nonneg modulus (α := ℝ)) (Fintype.card (Unit ⊕ Fin dim)))
    (mul_nonneg hL0 (NNReal.coe_nonneg (allocatedPrimitiveRootRatio (Real.exp p))))
  have hspec := spatialTupleCoarseMesh_spec (Fintype.card X) hcap0
    (Real.exp_pos (coefficientErrorVolumeLog p + 4)).le hlip0 hε
  have hcost := spatialTupleCoarseMesh_partition_budget (Fintype.card X)
    (Fintype.card (Unit ⊕ Fin dim)) hcap0 (Real.exp_pos (coefficientErrorVolumeLog p + 4)).le hlip0
    (Nat.cast_nonneg _) hC0 hε hT (hXR.trans hRT) (hnR.trans hRT)
    hcapInput hmassInput hlipInput hεInput hmodInput hΓInput hCInput
  exact ⟨hspec.1, hspec.2.1, hcost.1, hcost.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedEarlyRecenteredMesh_budget (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {G : Type*} [Fintype G] (X : Type*) [Fintype X]
      (selection : Fin dim ↪ G) {M modulus : ℕ} {p E : ℝ},
      0 ≤ p → 0 ≤ E → (Fintype.card G : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      0 < M → (M : ℝ) ≤ Real.exp p → modulus ≤ M ^ (m + 1) →
      let r := allocatedEarlyRecenteredMesh X selection M modulus p E
      0 < r ∧ r ≤ 1 / 4 ∧ r⁻¹ ≤ Real.exp ((p + E + a) ^ a) ∧
        allocatedSpatialCoefficientCap X selection M modulus r ≤ Real.exp ((p + E + a) ^ a) := by
  obtain ⟨a, ha, hlogs⟩ := exists_allocatedEarlyCoarseLog_bound m dim
  refine ⟨a, ha, ?_⟩
  intro G _ X _ selection M modulus p E hp hE hG hX hM hMP hmod r
  have h := allocatedEarlyRecenteredMesh_partition_budget m X selection hp hE hG hX hM hMP hmod
  have hlog := hlogs (add_nonneg hp hE)
  exact ⟨h.1, h.2.1, h.2.2.1.trans (Real.exp_le_exp.mpr hlog.1),
    h.2.2.2.trans (Real.exp_le_exp.mpr hlog.2)⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorNativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem generalResources_map {α β : Type*} [Semiring α] [Semiring β]
    (f : α →+* β) (K : PreparedModularCanonicalDetectorResourceConstants)
    (dim : ℕ) (P L : α) :
    (preparedModularGeneralDetectorResources K dim P L).map f =
      preparedModularGeneralDetectorResources K dim (f P) (f L) := by
  simp [preparedModularGeneralDetectorResources,
    PreparedModularCanonicalDetectorResources.map, slicedGridGeometryLog,
    affineAmbientPrimitiveBudget, affineAmbientMassLog, map_ofNat]

theorem exists_preparedModularGeneralDetector_resource_budget
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P L : ℝ}, 0 ≤ P → P ≤ L →
      let resources := preparedModularGeneralDetectorResources K dim P L
      resources.Bounds ((P + L + C) ^ C) ∧ resources.total ≤ (P + L + C) ^ C := by
  let diagonal := preparedModularGeneralDetectorResources K dim
    (Polynomial.X : Polynomial ℕ) Polynomial.X
  let bivariate := preparedModularGeneralDetectorResources K dim
    (MvPolynomial.X false : MvPolynomial Bool ℕ) (MvPolynomial.X true)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget diagonal.total
  refine ⟨C, hC, ?_⟩
  intro P L hP hPL resources
  have hL : 0 ≤ L := hP.trans hPL
  let values : Bool → ℝ := fun b => if b then L else P
  let ev : MvPolynomial Bool ℕ →+* ℝ := MvPolynomial.eval₂Hom (Nat.castRingHom ℝ) values
  let evSum : MvPolynomial Bool ℕ →+* ℝ := MvPolynomial.eval₂Hom (Nat.castRingHom ℝ) (fun _ => P + L)
  let evDiag : Polynomial ℕ →+* ℝ := Polynomial.eval₂RingHom (Nat.castRingHom ℝ) (P + L)
  have hmap : bivariate.map ev = resources := by
    simpa [bivariate, resources, ev, values] using
      generalResources_map ev K dim (MvPolynomial.X false) (MvPolynomial.X true)
  have hmapSum : bivariate.map evSum = preparedModularGeneralDetectorResources K dim (P + L) (P + L) := by
    simpa [bivariate, evSum] using
      generalResources_map evSum K dim (MvPolynomial.X false) (MvPolynomial.X true)
  have hmapDiag : diagonal.map evDiag = preparedModularGeneralDetectorResources K dim (P + L) (P + L) := by
    simpa [diagonal, evDiag] using generalResources_map evDiag K dim Polynomial.X Polynomial.X
  have hvalues (i) : 0 ≤ values i := by cases i <;> assumption
  have hdom (i) : values i ≤ P + L := by cases i <;> dsimp [values] <;> linarith
  have hmono : resources.total ≤ (preparedModularGeneralDetectorResources K dim (P + L) (P + L)).total := by
    rw [← hmap, ← hmapSum, generalResources_total_map, generalResources_total_map]
    exact natMv_eval_mono bivariate.total hvalues hdom
  have htotal : resources.total ≤ (P + L + C) ^ C := by
    apply hmono.trans
    rw [← hmapDiag, generalResources_total_map]
    exact hbound (P + L) (add_nonneg hP hL)
  have hnonneg : ∀ x ∈ resources.toList, 0 ≤ x := by
    rw [← hmap]
    change ∀ x ∈ bivariate.toList.map ev, 0 ≤ x
    intro x hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
    exact natMv_eval_nonneg q hvalues
  refine ⟨generalResources_bounds_of_list ?_, htotal⟩
  intro x hx
  exact ⟨hnonneg x hx, (List.single_le_sum hnonneg x hx).trans htotal⟩

theorem exists_preparedModularGeneralDetector_early_native_budget
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P : ℝ}, 0 ≤ P → ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources K dim P L
      r.Pnative ∈ Set.Icc 0 ((2 * P + C) ^ C) ∧
      r.nativeBudget ∈ Set.Icc 0 ((2 * P + C) ^ C) ∧
      r.E ∈ Set.Icc 0 ((2 * P + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedModularGeneralDetector_resource_budget K dim
  refine ⟨C, hC, ?_⟩
  intro P hP L r
  have h := (hbound (P := P) (L := P) hP le_rfl).1
  change (preparedModularGeneralDetectorResources K dim P P).Pnative ∈ _ ∧
    (preparedModularGeneralDetectorResources K dim P P).nativeBudget ∈ _ ∧
    (preparedModularGeneralDetectorResources K dim P P).E ∈ _
  simpa only [two_mul] using And.intro h.Pnative (And.intro h.nativeBudget h.E)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def forecastCorrelationLinearMap {X : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : X → ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun g := r.correlation g forecast
  map_add' g h := by
    simp [FiniteProbabilityWeights.correlation, Pi.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib]
  map_smul' a g := by
    simp only [FiniteProbabilityWeights.correlation, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

noncomputable def forecastSingleSeminorm {X : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : X → ℂ) : Seminorm ℂ (X → ℂ) :=
  (normSeminorm ℂ ℂ).comp (forecastCorrelationLinearMap r forecast)

theorem forecastSingleSeminorm_le {X : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast g : X → ℂ) {cap : ℝ}
    (hcap : ∀ x, ‖forecast x‖ ≤ cap) :
    forecastSingleSeminorm r forecast g ≤ cap * r.mean (fun x => ‖g x‖) := by
  change ‖r.correlation g forecast‖ ≤ _
  unfold FiniteProbabilityWeights.correlation FiniteProbabilityWeights.mean
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real,
    Real.norm_of_nonneg (r.nonneg x)]
  calc
    r.weight x * (‖g x‖ * ‖forecast x‖) ≤ r.weight x * (‖g x‖ * cap) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcap x) (norm_nonneg _))
        (r.nonneg x)
    _ = cap * (r.weight x * ‖g x‖) := by ring

noncomputable def forecastFamilySeminorm {X F : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) : Seminorm ℂ (X → ℂ) :=
  ⨆ f, forecastSingleSeminorm r (forecast f)

theorem forecastFamilySeminorm_bddAbove {X F : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) {cap : ℝ}
    (hcap : ∀ f x, ‖forecast f x‖ ≤ cap) :
    BddAbove (Set.range (fun f => forecastSingleSeminorm r (forecast f))) := by
  apply Seminorm.bddAbove_range_iff.mpr
  intro g
  refine ⟨cap * r.mean (fun x => ‖g x‖), ?_⟩
  rintro _ ⟨f, rfl⟩
  exact forecastSingleSeminorm_le r (forecast f) g (hcap f)

theorem forecastFamilySeminorm_apply {X F : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) {cap : ℝ}
    (hcap : ∀ f x, ‖forecast f x‖ ≤ cap) (g : X → ℂ) :
    forecastFamilySeminorm r forecast g = ⨆ f, ‖r.correlation g (forecast f)‖ := by
  rw [forecastFamilySeminorm, Seminorm.iSup_apply
    (forecastFamilySeminorm_bddAbove r forecast hcap)]
  rfl

theorem forecastFamilySeminorm_le {X F : Type*} [Fintype X] [Nonempty F]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) {cap : ℝ}
    (hcap : ∀ f x, ‖forecast f x‖ ≤ cap) (g : X → ℂ) :
    forecastFamilySeminorm r forecast g ≤ cap * r.mean (fun x => ‖g x‖) := by
  rw [forecastFamilySeminorm_apply r forecast hcap]
  exact ciSup_le (fun f => forecastSingleSeminorm_le r (forecast f) g (hcap f))

theorem forecast_correlation_le_family {X F : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) {cap : ℝ}
    (hcap : ∀ f x, ‖forecast f x‖ ≤ cap) (g : X → ℂ) (f : F) :
    ‖r.correlation g (forecast f)‖ ≤ forecastFamilySeminorm r forecast g := by
  rw [forecastFamilySeminorm_apply r forecast hcap]
  have hb : BddAbove (Set.range (fun i => ‖r.correlation g (forecast i)‖)) := by
    refine ⟨cap * r.mean (fun x => ‖g x‖), ?_⟩
    rintro _ ⟨i, rfl⟩
    exact forecastSingleSeminorm_le r (forecast i) g (hcap i)
  exact le_ciSup hb f

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem forecast_detector_of_atom_approximation
    {X Term : Type*} [Fintype X] [Fintype Term]
    (r : FiniteProbabilityWeights X) (forecast g : X → ℂ)
    (coefficient : Term → ℂ) (atom : Term → X → ℂ)
    {atoms : Set (X → ℂ)} {α M beta : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) (hg : ∀ x, ‖g x‖ ≤ 1)
    (hatom : ∀ i, atom i ∈ atoms)
    (happrox : ∀ x, ‖forecast x - ∑ i, coefficient i * atom i x‖ ≤ α / 8)
    (hmass : (∑ i, ‖coefficient i‖) ≤ M)
    (hbeta : beta ≤ α / (8 * (M + 1)))
    (hlarge : α / 2 ≤ ‖r.correlation g forecast‖) :
    ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖ := by
  have hconj (x : X) :
      ‖star (forecast x) - ∑ i, star (coefficient i) * star (atom i x)‖ ≤
        (α / 2) / (2 * ((1 : ℝ) + 1)) := by
    have h := happrox x
    rw [← norm_star] at h
    simpa only [star_sub, star_sum, star_mul, mul_comm (star (atom _ _)), div_div, mul_assoc,
      show (2 : ℝ) * (2 * (1 + 1)) = 8 by norm_num] using h
  have hmass' : (∑ i, ‖star (coefficient i)‖) ≤ M := by
    simpa only [norm_star] using hmass
  obtain ⟨i, hi⟩ := exists_forecast_detecting_atom r (fun x => star (forecast x)) g
    (fun i => star (coefficient i)) (fun i x => star (atom i x))
    (half_pos hα) zero_le_one hM hg hconj hmass' hlarge
  change (α / 2) / (4 * (M + 1)) ≤ ‖r.correlation g (atom i)‖ at hi
  refine ⟨atom i, hatom i, hbeta.trans ?_⟩
  simpa only [div_div, show (2 : ℝ) * (4 * (M + 1)) = 8 * (M + 1) by ring] using hi

end Erdos3

end

section

namespace Erdos3

theorem forecastAugmented_model_error {u p Q P K Fcap cap tau ε : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q)
    (hK : 0 ≤ K) (hF : 0 ≤ Fcap) (hcap : 0 ≤ cap)
    (hKp : K ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p) (hcapP : cap ≤ Real.exp p)
    (htau : tau ≤ Real.exp (-(u + 3)))
    (hP : u + 2 * p + Q + 32 ≤ P)
    (hε : ε ≤ 6 * positiveProjectionAccuracy P) :
    2 * tau + 2 * (cap + 2 / Real.exp (-Q)) * (K + Fcap) * ε ≤ Real.exp (-u) := by
  have hKP : K + Fcap ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ), Real.exp_pos p]
  have hcapP' : cap ≤ Real.exp (p + 1) :=
    hcapP.trans (Real.exp_le_exp.mpr (by linarith))
  have h := allocated_native_approximation_error hu (show 0 ≤ p + 1 by linarith) hQ
    (add_nonneg hK hF) hcap hKP hcapP' htau (by linarith : u + 2 * (p + 1) + Q + 30 ≤ P) hε
  convert h using 1
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedFiniteForwardDetectorOffset_phase (depth r : ℕ) (hr : r ≤ depth) :
    OrdinaryPolynomialPhase.budget r ≤ (preparedFiniteForwardDetectorOffset depth : ℝ) := by
  apply (OrdinaryPolynomialPhase.budget_le_factorizationInputOffset r).trans
  exact_mod_cast (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (show r ∈ Finset.range (depth + 1) by simpa using Nat.lt_succ_of_le hr) :
    OrdinaryPolynomialPhase.factorizationInputOffset r ≤ preparedFiniteForwardDetectorOffset depth)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedNativeFamilyMonotone
namespace OAI

section

namespace Erdos3

variable {σ Ω : Type*} {w : σ → ℕ} {degree : ℕ} {p q : ℝ}
  {sample : Ω → σ → ℤ} {f : Ω → ℂ}

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

theorem twistedNativeSampleFunctions_mono_of_twist
    {I I' : Type*} (twist : I → Ω → ℂ) (twist' : I' → Ω → ℂ)
    (hpq : p ≤ q) (lift : I → I') (hlift : ∀ i x, twist' (lift i) x = twist i x) :
    twistedNativeSampleFunctions w degree p sample twist ⊆
      twistedNativeSampleFunctions w degree q sample twist' := by
  rintro f (rfl | ⟨i, g, ⟨G⟩, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨lift i, g, ⟨G.mono hpq⟩, by simp only [hlift]⟩

namespace VectorPolynomial
open scoped NNReal

theorem normalizedNativeSampleFunctions_mono
    {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (w : X → ℕ) (degree : ℕ) (sample : Ω → X → ℤ)
    {p q : ℝ} (hpq : p ≤ q) :
    twistedNativeSampleFunctions w degree p sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp p) (Real.exp p)
        ⟨Real.exp p, Real.exp_nonneg _⟩) t => W.eval N poly (sample t)) ⊆
    twistedNativeSampleFunctions w degree q sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp q) (Real.exp q)
        ⟨Real.exp q, Real.exp_nonneg _⟩) t => W.eval N poly (sample t)) := by
  apply twistedNativeSampleFunctions_mono_of_twist _ _ hpq
    (fun W => W.mono (Real.exp_le_exp.mpr hpq) (Real.exp_le_exp.mpr hpq)
      (show (⟨Real.exp p, Real.exp_nonneg _⟩ : ℝ≥0) ≤ ⟨Real.exp q, Real.exp_nonneg _⟩ from
        Real.exp_le_exp.mpr hpq))
  intro W t
  rfl

end VectorPolynomial
end Erdos3

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

noncomputable def allocatedCenteredConditionalPolynomial (j : Fin m) :
    VectorPolynomial X ℝ (J j → ℝ) :=
  translate (fun i => (a i : ℝ)) (subtractConstant (c j).val (poly j))

omit [∀ j, Fintype (J j)] in
include hmem in
theorem allocatedCenteredConditionalPolynomial_mem (j : Fin m) (e : X →₀ ℕ) :
    coefficients (allocatedCenteredConditionalPolynomial U poly c a j) e ∈ U j :=
  coefficients_translate_mem (U j) _ _
    (coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)) e

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedCanonicalSpatialCoarseSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedCanonicalSpatial_cutoff (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} [Fintype G]
      {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
      {X : Type*} [Fintype X] {dim : ℕ} (selection : Fin dim ↪ G)
      {P p target Ecap Qstride Etau : ℝ},
      0 ≤ P → p ∈ Set.Icc 0 P → target ∈ Set.Icc 0 P →
      Ecap ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → Etau ∈ Set.Icc 0 P →
      ((dim + 1 : ℕ) : ℝ) ≤ P →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P →
      (Fintype.card X : ℝ) ≤ P →
      let l := allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau
      normalizedTupleSideLog X (PrincipalTupleIndex B (layerSamplerDegree I n))
        selection p target l ≤ (P + C) ^ C := by
  obtain ⟨a, _, hlate⟩ := exists_allocatedSpatialLateLog_bound m
  let Xpoly : Polynomial ℕ := Polynomial.X
  let latePoly := (Xpoly + Polynomial.C a) ^ a + 3 * Xpoly
  let poly := tupleSideLogEnvelope Xpoly Xpoly latePoly
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro G _ I _ n B _ X _ dim selection P p target Ecap Qstride Etau
    hP hp htarget hEcap hQstride hEtau hdim hvars hX l
  have hl₀ := allocatedSpatialLateLog_nonneg (G := G) B hP hP
  have hl : 0 ≤ l := by dsimp [l]; linarith only [hl₀, hEcap.1, hQstride.1, hEtau.1]
  have hlbound : l ≤ (P + a) ^ a + 3 * P := by
    have hb := hlate B hP hP le_rfl le_rfl hvars
    dsimp only [l]
    linarith only [hb, hEcap.2, hQstride.2, hEtau.2]
  have hG : (Fintype.card G : ℝ) ≤ P := by
    change (Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ P at hvars
    simp only [Fintype.card_sum, Nat.cast_add] at hvars
    linarith only [hvars, Nat.cast_nonneg (α := ℝ)
      (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)))]
  have hindices : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ P := by
    change (Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ P at hvars
    simp only [Fintype.card_sum, Nat.cast_add] at hvars
    linarith only [hvars, Nat.cast_nonneg (α := ℝ) (Fintype.card G)]
  have hqdim : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ P := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
      Nat.add_comm 1] using hdim
  have hs := (normalizedTuple_log_envelopes_of_le X
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection hp.1 htarget.1 hl
    hp.2 hqdim hG hindices hX).2
  apply (hs.trans (tupleSideLogEnvelope_mono hP htarget.1 hl le_rfl htarget.2 hlbound)).trans
  simpa [poly, Xpoly, latePoly, tupleSideLogEnvelope, tupleLateLogEnvelope,
    tupleWidthLogEnvelope, tupleEarlyLogEnvelope, spatialTupleToleranceLog,
    spatialDiscretizationEnvelope, spatialMeshEnvelope, spatialLipschitzCostEnvelope,
    spatialLipschitzEnvelope, spatialDisplacementEnvelope, spatialFixedProfileEnvelope,
    anisotropicSpatialCapLog, coefficientErrorVolumeLog, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardActualNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleLocalResourceBudget
    (m degree Cdetect : ℕ) (K : PreparedModularCanonicalDetectorResourceConstants) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum Pchart Qstride u pModel : ℝ},
      degree ≤ m → 0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      Pchart ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P →
      u ∈ Set.Icc 0 P → pModel ∈ Set.Icc 0 P →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let pDetect := allocatedModelTestLog u pModel
      let gainLog := slicedDetectionGainLog degree Cdetect count
        pDetect pDetect (2 * u + 4 * pModel + 7)
      let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
        Eprofile (pDetect + 2) + 2
      let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
        Pphysical u pModel Prho target gainLog
      ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources K (degree + 1) Pmaster L
      let budget := (P + C) ^ C
      Pmaster ∈ Set.Icc 0 budget ∧ r.Pnative ∈ Set.Icc 0 budget ∧
      r.nativeBudget ∈ Set.Icc 0 budget ∧ r.E ∈ Set.Icc 0 budget := by
  obtain ⟨Cp, _, hprecision⟩ := exists_preparedFiniteScheduleLocalPrecisionBudget m Cdetect
  obtain ⟨Ce, _, hearly⟩ := exists_preparedFiniteScheduleEarlyBudget m 1 Cdetect
  obtain ⟨Cn, _, hnative⟩ :=
    exists_preparedModularGeneralDetector_early_native_budget K (degree + 1)
  let X : Polynomial ℕ := Polynomial.X
  let rawPoly := 7 * X + 12
  let precisionPoly := (rawPoly + Polynomial.C Cp) ^ Cp
  let earlyPoly := (precisionPoly + Polynomial.C Ce) ^ Ce
  let masterPoly := 17 * earlyPoly + 44
  let nativePoly := (2 * masterPoly + Polynomial.C Cn) ^ Cn
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget (masterPoly + nativePoly)
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P Bstruct pnum Pchart Qstride u pModel
    hdegree hP hB hnum hchart hstride hu hmodel hcount hnX hG
    pRadius D pDetect gainLog Pk Pphysical target Eprofile Prho Pmaster L r budget
  let raw : ℝ := 7 * P + 12
  let precision : ℝ := (raw + Cp) ^ Cp
  let early : ℝ := (precision + Ce) ^ Ce
  let master : ℝ := 17 * early + 44
  let native : ℝ := (2 * master + Cn) ^ Cn
  have hraw0 : 0 ≤ raw := by dsimp only [raw]; positivity
  have hPraw : P ≤ raw := by dsimp only [raw]; linarith only [hP]
  have hp : pDetect ∈ Set.Icc 0 raw := by
    dsimp only [pDetect, allocatedModelTestLog, raw]
    constructor <;> linarith only [hu.1, hu.2, hmodel.1, hmodel.2]
  have ha : 2 * u + 4 * pModel + 7 ∈ Set.Icc 0 raw := by
    dsimp only [raw]
    constructor <;> linarith only [hu.1, hu.2, hmodel.1, hmodel.2, hP]
  have liftRaw {a : ℝ} (ha : a ∈ Set.Icc 0 P) : a ∈ Set.Icc 0 raw :=
    ⟨ha.1, ha.2.trans hPraw⟩
  obtain ⟨hrawPrecision, hgain, hkernel, hphysical, htarget⟩ :=
    hprecision degree hdegree (G := G) hraw0 hp ha (liftRaw hstride)
      (hcount.trans hPraw) (hnX.trans hPraw) (hG.trans hPraw)
  change raw ≤ precision at hrawPrecision
  change gainLog ∈ Set.Icc 0 precision at hgain
  change Pk ∈ Set.Icc 0 precision at hkernel
  change Pphysical ∈ Set.Icc 0 precision at hphysical
  change target ∈ Set.Icc 0 precision at htarget
  have hprecision0 : 0 ≤ precision := hraw0.trans hrawPrecision
  have hPprecision : P ≤ precision := hPraw.trans hrawPrecision
  have liftPrecision {a : ℝ} (ha : a ∈ Set.Icc 0 P) : a ∈ Set.Icc 0 precision :=
    ⟨ha.1, ha.2.trans hPprecision⟩
  obtain ⟨hprecisionEarly, hradius, hD, hdata⟩ :=
    hearly (fun _ : Unit => degree) (fun _ : Unit => Cdetect) (G := G)
      (fun _ => pDetect) (fun _ => 2 * u + 4 * pModel + 7) (fun _ => target)
      (by simp) (fun _ => hdegree) (fun _ => le_rfl)
      hprecision0 (liftPrecision hB) (liftPrecision hnum)
      (fun _ => ⟨hp.1, hp.2.trans hrawPrecision⟩)
      (fun _ => ⟨ha.1, ha.2.trans hrawPrecision⟩) (liftPrecision hstride)
      (fun _ => htarget) (hcount.trans hPprecision) (hnX.trans hPprecision)
      (hG.trans hPprecision)
  change precision ≤ early at hprecisionEarly
  change pRadius ∈ Set.Icc 0 early at hradius
  change D ∈ Set.Icc 0 early at hD
  have hrho : Prho ∈ Set.Icc 0 early := (hdata ()).2.2.1
  have hearly0 : 0 ≤ early := hprecision0.trans hprecisionEarly
  have hPearly : P ≤ early := hPprecision.trans hprecisionEarly
  have hdetectEarly : pDetect ≤ early := hp.2.trans (hrawPrecision.trans hprecisionEarly)
  have hmaster0 : 0 ≤ Pmaster := by
    have hchart0 := hchart.1
    have hD0 := hD.1
    have hradius0 := hradius.1
    have hstride0 := hstride.1
    have hphysical0 := hphysical.1
    have hu0 := hu.1
    have hmodel0 := hmodel.1
    have hrho0 := hrho.1
    have htarget0 := htarget.1
    have hgain0 := hgain.1
    have hdetect0 := hp.1
    change 0 ≤ Pchart + D + pRadius + Qstride + Pphysical +
      (u + pModel + pDetect + Prho + target + gainLog + 32)
    positivity
  have hmaster : Pmaster ≤ master := by
    change Pchart + D + pRadius + Qstride + Pphysical +
      (u + pModel + pDetect + Prho + target + gainLog + 32) ≤ 17 * early + 44
    linarith only [hchart.2.trans hPearly, hD.2, hradius.2, hstride.2.trans hPearly,
      hphysical.2.trans hprecisionEarly, hu.2.trans hPearly, hmodel.2.trans hPearly,
      hdetectEarly, hrho.2, htarget.2.trans hprecisionEarly,
      hgain.2.trans hprecisionEarly, hearly0]
  have hmasterBound0 : 0 ≤ master := hmaster0.trans hmaster
  have hnativeBound0 : 0 ≤ native := by dsimp only [native]; positivity
  have htotal : master + native ≤ budget := by
    simpa [masterPoly, nativePoly, earlyPoly, precisionPoly, rawPoly, X,
      master, native, early, precision, raw, budget, Polynomial.eval₂_pow]
      using hpoly P hP
  have hmasterCap : master ≤ budget := by linarith only [htotal, hnativeBound0]
  have hnativeCap : native ≤ budget := by linarith only [htotal, hmasterBound0]
  have hraise : (2 * Pmaster + Cn) ^ Cn ≤ budget := by
    apply le_trans _ hnativeCap
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hmaster]
  obtain ⟨hnative, hbudget, hE⟩ := hnative hmaster0 L
  exact ⟨⟨hmaster0, hmaster.trans hmasterCap⟩,
    ⟨hnative.1, hnative.2.trans hraise⟩,
    ⟨hbudget.1, hbudget.2.trans hraise⟩, ⟨hE.1, hE.2.trans hraise⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedAffineCutoffCost
namespace OAI

section

namespace Erdos3
open scoped Classical

theorem exists_weighted_common_real_grid_vector
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (outer : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < outer.mass S)
    (v : Ω → ι → ℝ) (l : ℕ) (hl : 0 < l) {B p : ℝ}
    (hp : 0 ≤ p) (hB : 0 ≤ B) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hlp : (l : ℝ) ≤ Real.exp p) (hBp : B ≤ Real.exp p)
    (hgrid : ∀ a ∈ S, v a ∈ realDenominatorGrid l)
    (hbound : ∀ a ∈ S, ∀ i, |v a i| ≤ B) :
    ∃ a₀ ∈ S, ∃ T : Finset Ω, T ⊆ S ∧ a₀ ∈ T ∧
      (∀ a ∈ T, v a = v a₀) ∧
      Real.exp (-((p + 3) ^ 3)) * outer.mass S ≤ outer.mass T := by
  let window : Set (ι → ℝ) :=
    {x | x ∈ realDenominatorGrid l ∧ ∀ i, |x i| ≤ B}
  obtain ⟨hfinite, hcard⟩ := finite_card_real_grid_window window l ⌈(l : ℝ) * B⌉₊ hl 0
    (fun _ hx => hx.1) (by intro x hx i; simpa only [Pi.zero_apply, sub_zero] using hx.2 i)
    (Nat.le_ceil _)
  have hcount : (window.ncard : ℝ) ≤ Real.exp ((p + 3) ^ 3) :=
    (Nat.cast_le.mpr hcard).trans (real_grid_window_count_le_exp _ _ hp hB hd hlp hBp)
  obtain ⟨c, _, T, hTS, hT, hc, hmass⟩ :=
    exists_weighted_exponential_constant_fiber outer S hS v window hfinite
      (fun a ha => ⟨hgrid a ha, hbound a ha⟩) hcount
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀,
    fun a ha => (hc a ha).trans (hc a₀ ha₀).symm, hmass⟩

theorem exists_weighted_common_coordinate_grid_vector
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (outer : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < outer.mass S)
    (v : Ω → ι → ℝ) (den : ι → ℕ) (hden : ∀ i, 0 < den i) {p : ℝ}
    (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hdenp : ∀ i, (den i : ℝ) ≤ Real.exp p)
    (hgrid : ∀ a ∈ S, ∀ i, ∃ z : ℤ, (den i : ℝ) * v a i = z)
    (hbound : ∀ a ∈ S, ∀ i, |v a i| ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset Ω, T ⊆ S ∧ a₀ ∈ T ∧
      (∀ a ∈ T, v a = v a₀) ∧
      Real.exp (-((2 * p + 3) ^ 3)) * outer.mass S ≤ outer.mass T := by
  let scaled : Ω → ι → ℝ := fun a i => (den i : ℝ) * v a i
  have hscaled_grid (a) (ha : a ∈ S) : scaled a ∈ realDenominatorGrid 1 := by
    choose z hz using hgrid a ha
    refine ⟨z, ?_⟩
    funext i
    simpa only [Nat.cast_one, Pi.smul_apply, smul_eq_mul, one_mul] using (hz i).symm
  have hscaled_bound (a) (ha : a ∈ S) (i) : |scaled a i| ≤ Real.exp (2 * p) := by
    dsimp only [scaled]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul (hdenp i) (hbound a ha i) (abs_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨a₀, ha₀, T, hTS, haT, hsame, hmass⟩ :=
    exists_weighted_common_real_grid_vector outer S hS scaled 1 (by omega)
      (by positivity : 0 ≤ 2 * p) (Real.exp_nonneg _) (hd.trans (by linarith))
      (by simpa only [Nat.cast_one] using Real.one_le_exp (by positivity : 0 ≤ 2 * p))
      le_rfl hscaled_grid hscaled_bound
  refine ⟨a₀, ha₀, T, hTS, haT, ?_, hmass⟩
  intro a ha
  funext i
  exact mul_left_cancel₀ (by exact_mod_cast (hden i).ne' : (den i : ℝ) ≠ 0)
    (congrFun (hsame a ha) i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FullFrozenChartMass
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial VectorPolynomial

theorem normalizedMass_aeval_frozen_integer_chart_le {σ K : Type*}
    (β : σ → MvPolynomial K ℤ)
    (keep : K → Prop) (T : K → ℝ) (hT : ∀ i, 0 < T i)
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, |(fixed i : ℝ)| ≤ T i.val)
    (p : MvPolynomial σ ℝ) :
    realPolynomialMass
      (scaleMvPolynomialAxes (fun i : {i // keep i} => T i.val)
        (aeval (integerSampledRealChart (fun z => freezePolynomial keep fixed (β z))) p)) ≤
      realPolynomialMass
        (scaleMvPolynomialAxes T (aeval (integerSampledRealChart β) p)) := by
  rw [aeval_frozen_integer_chart]
  exact normalizedMass_freezePolynomial_le keep T hT
    (fun i => (fixed i : ℝ)) hfixed _

end Erdos3

end

end OAI
end


