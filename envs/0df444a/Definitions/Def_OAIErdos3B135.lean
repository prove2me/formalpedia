-- Prove2me | Definitions.Def_OAIErdos3B135
-- name    : OAIErdos3B135
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T14:33:35.933739+00:00
-- url     : https://prove2.me/theorems/3a4f392f-27ec-4afa-8f23-b2d0570f3782
-- title:
--   OpenAI Erdős-3 split, definitions bundle 136 of 140
-- statement:
--   Definitions bundle 136 of 140 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B134`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 136 available.
--
--   Modules: `OAI.Erdos3.ResidueBoxSlice.fiberAffineIntegerPoint`, `OAI.Erdos3.ResidueBoxSlice.fiberAffineIntegerPoint_eq`, `OAI.Erdos3.ResidueBoxSlice.fiberAffinePointInBox`, `OAI.Erdos3.ResidueBoxSlice.fiberFullParameterEquiv`, `OAI.Erdos3.ResidueBoxSlice.fiberFullParameters`, `OAI.Erdos3.ResidueBoxSlice.fiberKeptParameters`, `OAI.Erdos3.ResidueBoxSlice.fiberKernelParameterEquiv`, `OAI.Erdos3.ResidueBoxSlice.fiberParameterLength`, `OAI.Erdos3.ResidueBoxSlice.fiberParameterLength_of_keep`, `OAI.Erdos3.ResidueBoxSlice.fiberParameterLength_pos`, `OAI.Erdos3.ResidueBoxSlice.fiberParameterStart`, `OAI.Erdos3.ResidueBoxSlice.fiberParameterStride`, `OAI.Erdos3.ResidueBoxSlice.fiberParameter_inside`, `OAI.Erdos3.VectorPolynomial.allocatedAxisProfilePolynomial`, `OAI.Erdos3.VectorPolynomial.allocatedGridJetRow_countable`, `OAI.Erdos3.VectorPolynomial.allocatedGridJetRow_measurableSingleton`, `OAI.Erdos3.VectorPolynomial.allocatedLayerCoefficient_scaled_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedLayerLiftCoefficient_radius_bound`, `OAI.Erdos3.VectorPolynomial.allocatedLongJetMask`, `OAI.Erdos3.VectorPolynomial.allocatedLongJetOutputScale`, `OAI.Erdos3.VectorPolynomial.allocatedLongJetTarget`, `OAI.Erdos3.VectorPolynomial.allocatedParameterBox_nonempty`, `OAI.Erdos3.VectorPolynomial.allocatedParameterSite_bound`, `OAI.Erdos3.VectorPolynomial.allocatedParameterSite_sum_bound`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalCube_directions_bound`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalCube_root_bound`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalCube_root_budget`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalCube_root_sum`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalEntryBudget`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalRootBudget`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalRootBudget_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalRootBudget_zero`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalRootBudget_zero_ratio`, `OAI.Erdos3.VectorPolynomial.allocatedPrimitiveRootRatio`, `OAI.Erdos3.VectorPolynomial.allocatedPrimitiveRootRatio_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedSupportedGridJetPMF`, `OAI.Erdos3.VectorPolynomial.allocatedWholeGridJetPMF`, `OAI.Erdos3.containedSupportedProgressionAxisLaw`, `OAI.Erdos3.continuousPolynomialDensity_coefficient_bound`, `OAI.Erdos3.principalAffineIntervalAxisLaw`, `OAI.Erdos3.principalAffineIntervalLaw`, `OAI.Erdos3.principalAffineIntervalPoint`, `OAI.Erdos3.principalAffineIntervalPoint_value`, `OAI.Erdos3.principalZeroTupleFromIntegerBox`, `OAI.Erdos3.principalZeroTupleFromIntegerBox_value`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B134

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedLongMixedCoefficientBound
namespace OAI

section

namespace Erdos3

theorem continuousPolynomialDensity_coefficient_bound {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {a : J → ℝ} (ha : continuousPolynomialDensity e T P j₀ R σ a ≠ 0) (j : J) :
    |a j| * monomialScale T (e j) ≤ 3 * R / 4 :=
  (scaledCoefficientDensity_coefficient_bound e T hT _ _
    (continuousPolynomialDensity_width_pos P j₀ hR hσ) ha j).trans
      (allocatedProfile_term_bound P j₀ hj₀ hR hσ hσ1 j)

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)

include hσ1 in
theorem allocatedLayerCoefficient_scaled_bounds (j : Fin m)
    (a : (I j → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℝ) ×
      (Fin (n j) → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ))
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j) (allocatedLayerWidths B U b S j)
      (allocatedLayerIntegerPMFs B U b hR hσ S j) a) (d) :
    (∀ i, |a.1 i d| * monomialScale (layerSamplerBox B U b S) d.val ≤ R j) ∧
      (∀ i, |(a.2 i d : ℝ) / basisAxisScale (b j) i| *
        monomialScale (layerSamplerBox B U b S) d.val ≤ R j) := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have hs := (allocatedArraySupported_iff_rows Subtype.val (layerSamplerBox B U b S)
    (layerContinuousPrincipalSlots B j) (constantCoefficientSlot _ _) (R j) (σ j)
    (allocatedLayerIntegerPMFs B U b hR hσ S j) a).mp ha
  constructor
  · intro i
    exact (continuousPolynomialDensity_coefficient_bound Subtype.val _ hT _ _
      (layerContinuousPrincipalSlots_not_constant B j i) (hR j) (hσ j) (hσ1 j) (hs.1 i) d).trans
        (by linarith [hR j])
  · intro i
    exact (allocatedIntegerCoefficient_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
      (j.val + 1) (basisAxisScale (b j) i) S.value (layerTailDegree m) (Nat.zero_lt_succ _) (basisAxisScale_pos (b j) i)
      S.positive (layerSamplerBox B U b S) hT (layerSamplerBox_le B U b S) Subtype.val
      (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (hσ1 j) (S.gap j i) (S.width j)
      (layerIntegerPrincipalSlots_not_constant B j i) rfl
      (layerSamplerSides_integer_principal B U b R S.value j i) d (hs.2 i d)).trans (by linarith [hR j])

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

include hσ1 C hC hchart hsmall

end VectorPolynomial
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
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)

include hσ1

theorem allocatedLayerLiftCoefficient_radius_bound
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (j : Fin m) {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C * ‖v‖)
    (a) (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) (i : J j) :
    |mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) a d i| ≤
      (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) /
        monomialScale (layerSamplerBox B U b S) d.val := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have h := allocatedLayerCoefficient_scaled_bounds B U b hR hσ S hσ1 j a ha d
  exact mixedRealPoint_scaled_coordinate_bound _ (b j) (o j) hC (hR j).le
    (monomialScale_pos _ hT d.val) hchart _ _ h.1 h.2 i

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPartitionedProfileJet
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R σ : Fin m → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedAxisProfilePolynomial (R σ : Fin m → ℝ) :
    (a : LayerSamplerAxis I n) → (SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) →
    MvPolynomial (LayerSamplerVariables G I n B) ℝ
  | ⟨j, .inl i⟩, r => monomialArrayPolynomial Subtype.val (fun e =>
      allocatedContinuousProfileCenters B R j i e + allocatedContinuousProfileWidths B R σ j i e * r e)
  | ⟨j, .inr i⟩, r => monomialArrayPolynomial Subtype.val (fun e =>
      allocatedIntegerProfileCenters B R j i e + allocatedIntegerProfileWidths B R σ j i e * r e)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRefinedLongJetComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

noncomputable def allocatedLongJetOutputScale : {a // ¬grid a} → ℝ
  | ⟨⟨_, .inl _⟩, _⟩ => 1
  | ⟨⟨j, .inr i⟩, _⟩ => (basisAxisScale (basis j) i : ℝ)^Fintype.card (O j)

noncomputable def allocatedLongJetTarget
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    ∀ a : {a // ¬grid a}, CoefficientJetAxisRow O a.val → ℝ
  | ⟨⟨j, .inl i⟩, _⟩ => allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y
  | ⟨⟨j, .inr i⟩, _⟩ => fun z => allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y
      (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))

noncomputable def allocatedLongJetMask (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) :
    ∀ a : {a // ¬grid a}, CoefficientJetAxisRow O a.val → ℝ
  | ⟨⟨_, .inl _⟩, _⟩ => fun _ => 1
  | ⟨⟨j, .inr _⟩, _⟩ => allocatedIntegerKernelMask B U basis S x rows j modulus (residue j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (modulus : ℕ) (hmodulus : 0 < modulus)
variable (r : PrincipalTupleIndex
  (fun a : {a // ¬allocatedGridAxis (I := I) U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus)
variable (hsize : ∀ d, (Fintype.card α+1)*modulus ≤
  principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
    (allocatedPrincipalSides B U basis S) d)

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (modulus : ℕ) (hmodulus : 0 < modulus)
variable (r : PrincipalTupleIndex
  (fun a : {a // ¬allocatedGridAxis (I := I) U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus)
variable (hsize : ∀ d, (Fintype.card α+1)*modulus ≤
  principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
    (allocatedPrincipalSides B U basis S) d)

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable (kernelModulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod kernelModulus))

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

noncomputable def allocatedPhysicalRootBudget : ℝ :=
  (∑ k, |(c k : ℝ)|) + Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ)

theorem allocatedPhysicalRootBudget_nonneg : 0 ≤ allocatedPhysicalRootBudget B U basis S c := by
  unfold allocatedPhysicalRootBudget
  positivity

noncomputable def allocatedPhysicalEntryBudget : ℝ :=
  1 + allocatedPhysicalRootBudget B U basis S c + (S.value : ℝ)

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

omit [Fintype α] in
theorem allocatedPhysicalCube_root_bound (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)| ≤ |(c k : ℝ)| + S.value := by
  have hv : |((Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) k : ℤ) : ℝ)| ≤ S.value := by
    cases k with
    | inl g =>
      have hx := Finset.mem_Ico.mp (x g none).property
      change |((x g none : ℤ) : ℝ)| ≤ S.value
      exact_mod_cast abs_le.mpr ⟨hx.1, hx.2.le⟩
    | inr j =>
      have hy := Finset.mem_Ico.mp (y j none).property
      have hbound : |(y j none : ℤ)| ≤ allocatedPrincipalSides B U basis S j :=
        abs_le.mpr ⟨hy.1, hy.2.le⟩
      exact (by exact_mod_cast hbound : |((y j none : ℤ) : ℝ)| ≤
        allocatedPrincipalSides B U basis S j).trans
          (Nat.cast_le.mpr (allocatedPrincipalSides_le_scale B U basis S j))
  unfold allocatedPhysicalCubeRoot
  push_cast
  exact (abs_add_le _ _).trans (add_le_add le_rfl hv)

omit [Fintype α] in
theorem allocatedPhysicalCube_root_sum :
    (∑ k, |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)|) ≤
      allocatedPhysicalRootBudget B U basis S c := by
  calc
    _ ≤ ∑ k, (|(c k : ℝ)| + (S.value : ℝ)) :=
      Finset.sum_le_sum (fun k _ => allocatedPhysicalCube_root_bound B U basis S c x y k)
    _ = _ := by simp [allocatedPhysicalRootBudget, Finset.sum_add_distrib]

omit [Fintype α] in
theorem allocatedPhysicalCube_root_budget (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)| ≤
      allocatedPhysicalRootBudget B U basis S c :=
  (Finset.single_le_sum (fun j _ => abs_nonneg (allocatedPhysicalCubeRoot B U basis S c x y j : ℝ))
    (Finset.mem_univ k)).trans (allocatedPhysicalCube_root_sum B U basis S c x y)

variable [DecidableEq α] [DecidableEq G]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem allocatedParameterSite_bound (t : integerBox sides) (k : LayerSamplerVariables G I n B) :
    |(t.val k : ℝ)| ≤ S.value := by
  have ht := (mem_integerBox sides t.val).mp t.property k
  have hk : sides k ≤ S.value := by
    cases k with
    | inl g => exact le_rfl
    | inr j => exact allocatedPrincipalSides_le_scale B U b S j
  have hk' : (sides k : ℤ) ≤ (S.value : ℤ) := by exact_mod_cast hk
  have ht' : |t.val k| ≤ (S.value : ℤ) := by
    rw [abs_of_nonneg ht.1]
    exact ht.2.le.trans hk'
  exact_mod_cast ht'

theorem allocatedParameterSite_sum_bound (t : integerBox sides) :
    (∑ k, |(t.val k : ℝ)|) ≤ allocatedPhysicalRootBudget B U b S (fun _ => 0) := by
  calc
    _ ≤ ∑ _k : LayerSamplerVariables G I n B, (S.value : ℝ) :=
      Finset.sum_le_sum (fun k _ => allocatedParameterSite_bound B U b S t k)
    _ = _ := by simp [allocatedPhysicalRootBudget]

theorem allocatedParameterBox_nonempty : (integerBox sides).Nonempty := by
  have hpos (k : LayerSamplerVariables G I n B) : 0 < sides k := by
    cases k with
    | inl g => exact S.positive
    | inr j => exact allocatedPrincipalSides_pos B U b S j
  let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
  exact integerBox_nonempty sides

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

noncomputable def allocatedPrimitiveRootRatio (p : ℝ) : ℝ≥0 := Real.toNNReal (p + 1)

theorem allocatedPrimitiveRootRatio_bounds {p : ℝ} (hp : 0 ≤ p) :
    (allocatedPrimitiveRootRatio p : ℝ) = p + 1 ∧
      1 ≤ allocatedPrimitiveRootRatio p ∧
      (allocatedPrimitiveRootRatio p : ℝ) ≤ Real.exp (p + 1) := by
  have heq : (allocatedPrimitiveRootRatio p : ℝ) = p + 1 :=
    Real.coe_toNNReal _ (by linarith)
  refine ⟨heq, ?_, ?_⟩
  · exact_mod_cast (show (1 : ℝ) ≤ allocatedPrimitiveRootRatio p by rw [heq]; linarith)
  · rw [heq]
    linarith [Real.add_one_le_exp (p + 1)]

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedPhysicalRootBudget_zero :
    allocatedPhysicalRootBudget B U b S (fun _ => 0) =
      Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) := by
  simp only [allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add]

theorem allocatedPhysicalRootBudget_zero_ratio {p : ℝ} (hp : 0 ≤ p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p) :
    (1 + allocatedPhysicalRootBudget B U b S (fun _ => 0)) / (S.value : ℝ) ≤
      allocatedPrimitiveRootRatio p := by
  have hS : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hS1 : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  rw [allocatedPhysicalRootBudget_zero, (allocatedPrimitiveRootRatio_bounds hp).1,
    add_div, mul_div_cancel_right₀ _ hS.ne']
  have hinv : 1 / (S.value : ℝ) ≤ 1 := (div_le_one hS).mpr hS1
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalCubeSupportedCell
namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))
local notation "rP" => (fun j : PrincipalTupleIndex BP hP => r (embed j))
local notation "hHP" => (fun j : PrincipalTupleIndex BP hP => hH (embed j))
local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))
local notation "rP" => (fun j : PrincipalTupleIndex BP hP => r (embed j))
local notation "hHP" => (fun j : PrincipalTupleIndex BP hP => hH (embed j))
local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

noncomputable def containedSupportedProgressionAxisLaw :
    FiniteProbabilityWeights (PrincipalAxisTuples (α := α) P L) :=
  (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex BP hP =>
    principalSupportedCoordinateWeights B h H hH q r hcell (embed j))).fiberLaw
      (containedProgressionTupleMap BP hP (principalAxisLength P L) (principalAxisLength P H)
        (principalAxisLength P step) (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j)))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))
local notation "rP" => (fun j : PrincipalTupleIndex BP hP => r (embed j))
local notation "hHP" => (fun j : PrincipalTupleIndex BP hP => hH (embed j))
local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

def fiberParameterLength
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q) (i : X) : ℕ :=
  if hi : keep i then S.length ⟨i, hi⟩ else 1

def fiberParameterStart
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ) (i : X) : ℤ :=
  if hi : keep i then (S.start ⟨i, hi⟩ : ℤ) else fixed ⟨i, hi⟩

def fiberParameterStride (i : X) : ℕ := if keep i then q else 0

omit [Fintype X] [DecidableEq X] in
theorem fiberParameterLength_pos
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (i : X) : 0 < S.fiberParameterLength i := by
  unfold fiberParameterLength
  split
  · exact hlen _
  · exact Nat.zero_lt_one

omit [Fintype X] [DecidableEq X] in
theorem fiberParameterLength_of_keep
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (i : X) (hi : keep i) : S.fiberParameterLength i = S.length ⟨i, hi⟩ := by
  simp only [fiberParameterLength, dif_pos hi]

def fiberFullParameters
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (u : ∀ k, Fin (S.length k)) (i : X) : Fin (S.fiberParameterLength i) :=
  ⟨if hi : keep i then (u ⟨i, hi⟩).val else 0, by
    by_cases hi : keep i
    · simpa only [fiberParameterLength, dif_pos hi] using (u ⟨i, hi⟩).isLt
    · simp only [fiberParameterLength, dif_neg hi, Nat.zero_lt_one]⟩

def fiberKeptParameters
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (v : ∀ i, Fin (S.fiberParameterLength i)) (k : {x // keep x}) : Fin (S.length k) :=
  ⟨(v k.val).val, by
    simpa only [fiberParameterLength, dif_pos k.property] using (v k.val).isLt⟩

def fiberFullParameterEquiv
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q) :
    (∀ k, Fin (S.length k)) ≃ (∀ i, Fin (S.fiberParameterLength i)) where
  toFun := S.fiberFullParameters
  invFun := S.fiberKeptParameters
  left_inv u := by
    funext k
    apply Fin.ext
    simp only [fiberKeptParameters, fiberFullParameters, dif_pos k.property]
  right_inv v := by
    funext i
    apply Fin.ext
    by_cases hi : keep i
    · simp only [fiberFullParameters, fiberKeptParameters, dif_pos hi]
    · have hv : (v i).val < 1 := by
        simpa only [fiberParameterLength, dif_neg hi] using (v i).isLt
      simp only [fiberFullParameters, dif_neg hi]
      omega

def fiberAffineIntegerPoint
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ) (v : ∀ i, Fin (S.fiberParameterLength i)) : X → ℤ :=
  fun i => S.fiberParameterStart fixed i +
    (fiberParameterStride (keep := keep) (q := q) i : ℤ) * (v i).val

omit [Fintype X] [DecidableEq X] in
theorem fiberAffineIntegerPoint_eq
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ) (v : ∀ i, Fin (S.fiberParameterLength i)) :
    S.fiberAffineIntegerPoint fixed v = S.fiberIntegerPoint fixed (S.fiberKeptParameters v) := by
  funext i
  by_cases hi : keep i
  · simp only [fiberAffineIntegerPoint, fiberParameterStart, fiberParameterStride,
      fiberIntegerPoint, finiteSplitPoint, dif_pos hi, if_pos hi,
      point, fiberKeptParameters, Nat.cast_add, Nat.cast_mul]
  · simp only [fiberAffineIntegerPoint, fiberParameterStart, fiberParameterStride,
      fiberIntegerPoint, finiteSplitPoint, dif_neg hi, if_neg hi,
      Nat.cast_zero, zero_mul, add_zero]

def fiberAffinePointInBox
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (v : ∀ i, Fin (S.fiberParameterLength i)) : integerBox N :=
  ⟨S.fiberAffineIntegerPoint fixed v, by
    rw [fiberAffineIntegerPoint_eq]
    exact S.fiberIntegerPoint_mem_integerBox fixed hfixed _⟩

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)

def principalAffineIntervalPoint (t : ∀ j, Fin (H j)) : PrincipalIntegerTuples B h Empty L :=
  fun j _ => ⟨start j + (step j : ℤ) * (t j).val, Finset.mem_Ico.mpr
    ⟨(neg_nonpos.mpr (Int.natCast_nonneg _)).trans (hinside j (t j)).1, (hinside j (t j)).2⟩⟩

omit [Fintype D] [DecidableEq D] [∀ index, Fintype (B index)]
  [∀ index, DecidableEq (B index)] in
@[simp] theorem principalAffineIntervalPoint_value (t : ∀ j, Fin (H j))
    (j : PrincipalTupleIndex B h) (a : Option Empty) :
    (principalAffineIntervalPoint B h L H step start hinside t j a : ℤ) =
      start j + (step j : ℤ) * (t j).val := rfl

variable (hH : ∀ j, 0 < H j)

noncomputable def principalAffineIntervalLaw : FiniteProbabilityWeights (PrincipalIntegerTuples B h Empty L) := by
  letI : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  exact (FiniteProbabilityWeights.uniform (∀ j, Fin (H j))).finitePushforward
    (principalAffineIntervalPoint B h L H step start hinside)

noncomputable def principalAffineIntervalAxisLaw (P : D → Prop) :
    FiniteProbabilityWeights (PrincipalAxisTuples (α := Empty) P L) :=
  (principalAffineIntervalLaw B h L H step start hinside hH).finitePushforward
    (principalAxisRestrict P)

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

theorem fiberParameter_inside
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (i : X) (t : Fin (S.fiberParameterLength i)) :
    0 ≤ S.fiberParameterStart fixed i +
      (fiberParameterStride (keep := keep) (q := q) i : ℤ) * t.val ∧
      S.fiberParameterStart fixed i +
        (fiberParameterStride (keep := keep) (q := q) i : ℤ) * t.val < N i := by
  let zero : ∀ j, Fin (S.fiberParameterLength j) :=
    fun j => ⟨0, S.fiberParameterLength_pos hlen j⟩
  let v := Function.update zero i t
  have hv := (mem_integerBox N _).mp (S.fiberAffinePointInBox fixed hfixed v).property i
  simpa only [fiberAffinePointInBox, fiberAffineIntegerPoint, v, Function.update_self] using hv

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
variable {keep : G ⊕ P → Prop} [DecidablePred keep] {N : G ⊕ P → ℕ} {q : ℕ}

def fiberKernelParameterEquiv
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hkernel : ∀ i, keep (Sum.inl i)) :
    (∀ i, Fin (S.fiberParameterLength (Sum.inl i))) ≃
      (∀ i, Fin (S.length ⟨Sum.inl i, hkernel i⟩)) where
  toFun g i := ⟨(g i).val, by
    simpa only [fiberParameterLength, dif_pos (hkernel i)] using (g i).isLt⟩
  invFun g i := ⟨(g i).val, by
    simpa only [fiberParameterLength, dif_pos (hkernel i)] using (g i).isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ)

def principalZeroTupleFromIntegerBox (z : integerBox L) :
    PrincipalIntegerTuples B h Empty L :=
  fun j _ => ⟨z.val j, Finset.mem_Ico.mpr
    ⟨(neg_nonpos.mpr (Int.natCast_nonneg _)).trans ((mem_integerBox L z.val).mp z.property j).1,
      ((mem_integerBox L z.val).mp z.property j).2⟩⟩

@[simp] theorem principalZeroTupleFromIntegerBox_value (z : integerBox L)
    (j : PrincipalTupleIndex B h) (a : Option Empty) :
    (principalZeroTupleFromIntegerBox B h L z j a : ℤ) = z.val j := rfl

variable {keep : PrincipalTupleIndex B h → Prop} [DecidablePred keep] {q : ℕ}
variable (S : ResidueBoxSlice (fun j : {j // keep j} => L j.val) q)
variable (hlen : ∀ j, 0 < S.length j)
variable (fixed : {j // ¬keep j} → ℤ)
variable (hfixed : ∀ j, 0 ≤ fixed j ∧ fixed j < (L j.val : ℤ))

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
variable {keep : G ⊕ P → Prop} [DecidablePred keep] {N : G ⊕ P → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveFixedSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

universe uα

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "tuples" => principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

noncomputable def allocatedWholeGridJetPMF
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)) :
    ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val)
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => integerMatrixImagePMF
      (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) (j.val + 1) (rows j))
      (allocatedLayerIntegerPMFs B U b hR hσ S j i)

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

instance allocatedGridJetRow_countable
    (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
    Countable (CoefficientJetAxisRow O a.val) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact inferInstanceAs (Countable (O j → ℤ))

instance allocatedGridJetRow_measurableSingleton
    (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
    MeasurableSingletonClass (CoefficientJetAxisRow O a.val) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact inferInstanceAs (MeasurableSingletonClass (O j → ℤ))

noncomputable def allocatedSupportedGridJetPMF
    (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
    PMF (CoefficientJetAxisRow O a.val) := by
  exact ((principalTupleWeights (α := α) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).toPMF.bind
        (fun y => allocatedWholeGridJetPMF B U b hR hσ S x rows y a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) *
    (8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1))
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => j.val + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) *
    (8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1))
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "constantLaw" => allocatedLayerIntegerPMFs B U b hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

end Erdos3.VectorPolynomial

end

end OAI

end


