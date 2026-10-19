-- Prove2me | Definitions.Def_OAIE3v2B197
-- name    : OAIE3v2B197
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:43:48.123255+00:00
-- url     : https://prove2.me/theorems/eeb6b81c-167e-42a0-9ff7-abe0ae0f5e75
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 201 of 311
-- statement:
--   Definitions bundle 201 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B175`, `OAIE3v2B177` of this split.
--
--   Modules: `Estimates/OptionComplementCover.lean`, `Fourier/ForecastInactiveCharacterSite.lean`, `Lattices/ResidueCellNormLengths.lean`, `Lattices/ResiduePrimeDensityError.lean`, `Lattices/RetainedPhysicalCRT.lean`, `Sampling/ContainedProgressionForecastDisintegration.lean`, `Sampling/FixedSpatialKernelProgressionForecastIntegral.lean`, `Sampling/ForecastActiveGridIntegralComparison.lean`, `Sampling/ForecastNativePullbackBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B175
import Definitions.Def_OAIE3v2B177

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OptionComplementCover
namespace OAI

section

universe u v

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

def optionComplementMap : (∀ i, L i) →ₗ⁅ℚ⁆
    (∀ j : {j : Option ι // j ≠ none}, optionLieSpace L₀ L j.val) :=
  liePiMap (optionComplementMaps (L₀ := L₀) (L := L))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ContainedProgressionForecastDisintegration
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

def progressionPrincipalResidue (q : ℕ)
    (r : PrincipalTupleIndex B h → Option α → ZMod q) :
    PrincipalTupleIndex B h → Option α → ZMod q :=
  fun j a => (if a = none then (c j : ZMod q) else 0) + (step j : ZMod q) * r j a

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ForecastInactiveCharacterSite
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {A J K H : Type*} [Fintype A] [DecidableEq A]
  [Fintype J] [DecidableEq J]

noncomputable def forecastInactiveCharacterCoefficient
    (poly : J → MvPolynomial (A ⊕ (K × H)) ℤ) (N : ℕ) [NeZero N]
    (p : FiniteProbabilityWeights (A → ZMod N)) (χ : AddChar (J → ZMod N) ℂ)
    (r : K → H → ZMod (orderOf χ)) : ℂ :=
  finiteImageCharacteristic p
    (fun t j => (integerLongPolynomialOutput poly
      (fun k => ((r k.1 k.2).val : ℤ)) N t j : ZMod N)) χ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResiduePrimeDensityError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def primeCoordinateMassRatio {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : ℝ :=
  ((primeCoordinateCell lo N q I x).card : ℝ) / (translatedIntegerBox lo N).card /
    productFiberMass (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight I x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def residuePrimeCoordinateMassRatio {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : ℝ :=
  (Fintype.card (ResiduePrimeCoordinateCell lo N M a q I x) : ℝ) /
    Fintype.card (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a) /
    productFiberMass (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight I x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueCellNormLengths
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def residueCellOutsideDensity {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) (f : (σ → ℤ) → ℝ) :
    (∀ i : {i // i ∉ K}, σ → ZMod (q i.val)) → ℝ :=
  observedProductDensity (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
    (@FiniteProbabilityWeights.uniform (ResiduePrimeCoordinateCell lo N M a q K base) _ ⟨u⟩)
    (fun z => primeCoordinateObservation (fun i : {i // i ∉ K} => q i.val) (fun k => (z.val k).val))
    (fun z => f (fun k => (z.val k).val))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT
namespace OAI

section

namespace Erdos3

open scoped Classical

noncomputable def affineSampleProductCoupling {ι J σ : Type*} [Fintype J] [Fintype σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)] :
    ∀ i, FiniteProbabilityCoupling
      (primeCoordinateReference (σ := Option J × σ) q i)
      (primeCoordinateReference (σ := σ) q i) :=
  fun i => affineSampleCoupling (J := J) (I := σ) (q := q i)

noncomputable def affineResidueTruncatedPairing {ι J σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype J] [Fintype σ] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (D : Finset (Finset ι)) (w : (∀ i, Option J × σ → ZMod (q i)) → ℝ)
    (f : (∀ i, σ → ZMod (q i)) → ℝ) : ℝ :=
  productTruncatedPairing (affineSampleProductCoupling (J := J) (σ := σ) q) D w f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedSpatialKernelProgressionForecastIntegral
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def fixedSpatialKernelOriginalForecastSource (sample : Sample) : Measure Domain :=
  ((unitBoxMeasure G).prod (unitBoxMeasure Input)).map
    (fun p => (fixedSpatialKernelMap W L z p.1,
      allocatedOriginalSampleLiftMap B U basis S lower width sample p.2))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis L a}, Unit)
local notation "ContinuousAxis" => (Σ j : Fin m, I j)
local notation "IntegerAxis" => AllocatedActiveIntegerAxis U basis L

def forecastActiveAxisEquiv : Output ≃ ContinuousAxis ⊕ IntegerAxis where
  toFun a := match a with
    | ⟨⟨⟨j, Sum.inl i⟩, _⟩, _⟩ => Sum.inl ⟨j, i⟩
    | ⟨⟨⟨j, Sum.inr i⟩, h⟩, _⟩ => Sum.inr ⟨⟨j, i⟩, Nat.lt_of_not_ge h⟩
  invFun a := match a with
    | Sum.inl ⟨j, i⟩ => ⟨⟨⟨j, Sum.inl i⟩, not_false⟩, ()⟩
    | Sum.inr a => ⟨⟨⟨a.val.1, Sum.inr a.val.2⟩, Nat.not_le.mpr a.property⟩, ()⟩
  left_inv a := by
    rcases a with ⟨⟨⟨j, i | i⟩, ha⟩, u⟩ <;> cases u <;> rfl
  right_inv a := by
    rcases a with ⟨j, i⟩ | ⟨⟨j, i⟩, ha⟩ <;> rfl

def forecastActiveCoordinateJoin (c : ContinuousAxis → ℝ) (z : IntegerAxis → ℝ) :
    Output → ℝ :=
  fun a => Sum.elim c z (forecastActiveAxisEquiv (I := I) U basis L a)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastActiveGridIntegralComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical NNReal

variable {X : Type*} [Fintype X]
variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis L a}, Unit)
local notation "Cont" => (Σ j : Fin m, I j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis L

def forecastJointAxisEquiv : Spatial ⊕ Output ≃ Cont ⊕ (X ⊕ IntAxis) where
  toFun a := match a with
    | .inl s => .inr (.inl s.1)
    | .inr a => match forecastActiveAxisEquiv U basis L a with
      | .inl c => .inl c
      | .inr z => .inr (.inr z)
  invFun a := match a with
    | .inl c => .inr ((forecastActiveAxisEquiv U basis L).symm (.inl c))
    | .inr (.inl x) => .inl ⟨x, .inl ()⟩
    | .inr (.inr z) => .inr ((forecastActiveAxisEquiv U basis L).symm (.inr z))
  left_inv a := by
    rcases a with ⟨x, u | e⟩ | a
    · cases u; rfl
    · exact e.elim
    · obtain ⟨c | z, rfl⟩ := (forecastActiveAxisEquiv U basis L).symm.surjective a
      all_goals simp only [Equiv.apply_symm_apply]
  right_inv a := by
    rcases a with c | x | z
    all_goals simp only [Equiv.apply_symm_apply]

def forecastJointCoordinateJoinEquiv :
    ((Cont → ℝ) × ((X ⊕ IntAxis) → ℝ)) ≃ᵐ ((Spatial → ℝ) × (Output → ℝ)) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Cont ⊕ (X ⊕ IntAxis) => ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Spatial ⊕ Output => ℝ)
      (forecastJointAxisEquiv (X := X) (I := I) U basis L).symm).trans
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Spatial ⊕ Output => ℝ)))

def forecastJointCoordinateJoin (c : Cont → ℝ) (z : (X ⊕ IntAxis) → ℝ) :
    (Spatial → ℝ) × (Output → ℝ) :=
  (fun a => z (.inl a.1),
   forecastActiveCoordinateJoin U basis L c (fun a => z (.inr a)))

end Erdos3.VectorPolynomial

end

end OAI
end


