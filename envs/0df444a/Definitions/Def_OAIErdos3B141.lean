-- Prove2me | Definitions.Def_OAIErdos3B141
-- name    : OAIErdos3B141
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T16:17:19.040635+00:00
-- url     : https://prove2.me/theorems/04d9772e-299a-42f6-95c5-68ccd91efd03
-- title:
--   OpenAI Erdős-3 split, definitions bundle 142 of 149
-- statement:
--   Definitions bundle 142 of 149 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B140`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 142 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleLiftMap`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSamplePrincipal`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleShift`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleSliceInput`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleSliceSubstitution`, `OAI.Erdos3.VectorPolynomial.allocatedPrincipalSides_long_of_not_short`, `OAI.Erdos3.VectorPolynomial.allocatedSampleNormalizedCoefficients`, `OAI.Erdos3.VectorPolynomial.allocatedSampleProfileNoise`, `OAI.Erdos3.VectorPolynomial.allocatedSampleRestrictedProfileNoise`, `OAI.Erdos3.VectorPolynomial.allocatedShortAxis`, `OAI.Erdos3.VectorPolynomial.allocatedShortAxisDecidable`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientTorus_continuous`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B134

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRelativeChildSliceGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

noncomputable def allocatedSampleNormalizedCoefficients (sample : Sample) :
    (a : LayerSamplerAxis I n) → SamplerCoefficientSlot G B degree a → ℝ
  | ⟨j, .inl i⟩, e => (sample j).1 i e / allocatedContinuousProfileScales B U basis S j e
  | ⟨j, .inr i⟩, e => ((sample j).2 i e : ℝ) / allocatedIntegerProfileScales B U basis S j i e

noncomputable def allocatedSampleProfileNoise (sample : Sample) :
    (a : LayerSamplerAxis I n) → SamplerCoefficientSlot G B degree a → ℝ
  | ⟨j, .inl i⟩, e =>
    (allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inl i⟩ e -
      allocatedContinuousProfileCenters B R j i e) / allocatedContinuousProfileWidths B R σ j i e
  | ⟨j, .inr i⟩, e =>
    (allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inr i⟩ e -
      allocatedIntegerProfileCenters B R j i e) / allocatedIntegerProfileWidths B R σ j i e

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
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

def allocatedShortAxis (L : ℕ) : LayerSamplerAxis I n → Prop
  | ⟨_, .inl _⟩ => False
  | ⟨j, .inr i⟩ => basisAxisScale (basis j) i ≤ L ^ (j.val + 1)

noncomputable instance allocatedShortAxisDecidable (L : ℕ) :
    DecidablePred (allocatedShortAxis (I := I) U basis L) := Classical.decPred _

theorem allocatedPrincipalSides_long_of_not_short (a : LayerSamplerAxis I n)
    (ha : ¬allocatedShortAxis (I := I) U basis S.value a) (b : B a) (v : Fin (degree a)) :
    allocatedPrincipalSides B U basis S ⟨a, b, v⟩ = S.value := by
  rcases a with ⟨j, i⟩
  cases i with
  | inl i => rfl
  | inr i =>
    have hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i := Nat.lt_of_not_ge ha
    simp only [allocatedPrincipalSides, layerSamplerSides, heterogeneousSamplerSides,
      layerSamplerDenominators, Sum.elim_inr, layerSamplerDegree,
      integerAxisSideLength, hactive, ↓reduceIte]

variable (P : LayerSamplerAxis I n → Prop)

noncomputable def allocatedSampleRestrictedProfileNoise (sample : Sample) :
    ActiveProfileCoefficientIndex G B degree P → ℝ :=
  fun e => allocatedSampleProfileNoise B U basis S sample e.1.val e.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

noncomputable def allocatedOriginalSamplePrincipal (sample : Sample) (a : Active) (b : B a.val) : ℝ :=
  allocatedSampleNormalizedCoefficients B U basis S sample a.val
    (principalCoefficientSlot degree a.val b) / R a.val.1

noncomputable def allocatedOriginalSampleShift (sample : Sample) (a : Active) : ℝ :=
  allocatedSampleNormalizedCoefficients B U basis S sample a.val
    (constantCoefficientSlot vars (degree a.val)) / R a.val.1

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def allocatedOriginalSampleLiftMap (sample : Sample) (x : Input → ℝ) : Output → ℝ :=
  (fun o => allocatedOriginalSampleShift B U basis S sample o.1) +
    jointSlicedPrincipal (allocatedOriginalSamplePrincipal B U basis S sample) lower width x

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

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
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def allocatedOriginalSampleSliceSubstitution : vars → MvPolynomial Input ℝ
  | .inl g => MvPolynomial.C ((x g none : ℝ) / S.value)
  | .inr ⟨a, b, i⟩ =>
      if ha : short a then
        MvPolynomial.C ((u ⟨⟨a, ha⟩, b, i⟩ none : ℝ) / sides ⟨a, b, i⟩)
      else MvPolynomial.C (lower ⟨a, ha⟩ (b, i)) +
        MvPolynomial.C (width ⟨a, ha⟩ (b, i)) * MvPolynomial.X ⟨⟨a, ha⟩, b, i⟩

noncomputable def allocatedOriginalSampleSliceInput (y : Input → ℝ) : vars → ℝ
  | .inl g => (x g none : ℝ) / S.value
  | .inr ⟨a, b, i⟩ =>
      if ha : short a then (u ⟨⟨a, ha⟩, b, i⟩ none : ℝ) / sides ⟨a, b, i⟩
      else lower ⟨a, ha⟩ (b, i) + width ⟨a, ha⟩ (b, i) * y ⟨⟨a, ha⟩, b, i⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical
open Module

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (scale : LayerSamplerScale (G := G) B U basis R σ)

local notation "Vars" => LayerSamplerVariables G I n B
local notation "sides" => Sum.elim (fun _ : G => scale.value) (allocatedPrincipalSides B U basis scale)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientPairCover
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory

variable {K : Type*} [finiteK : Fintype K] {m : ℕ} {J : Fin m → Type*}
  [finiteCoordinates : ∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientAmbientTorus_continuous : Continuous (coefficientAmbientTorus (K := K) U) := by
  apply continuous_pi
  intro a
  exact (continuous_apply a.2).comp ((subspaceAmbientTorus_continuous (U a.1.1)).comp
    ((continuous_apply a.1).comp (coefficientCoordinateTorus_continuous U)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

end OAI

end


