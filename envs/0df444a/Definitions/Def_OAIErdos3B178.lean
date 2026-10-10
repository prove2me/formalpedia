-- Prove2me | Definitions.Def_OAIErdos3B178
-- name    : OAIErdos3B178
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T05:32:06.584451+00:00
-- url     : https://prove2.me/theorems/5930bbb6-f026-4e30-a47e-ceb7c6c8ce02
-- title:
--   OpenAI Erdős-3 split, definitions bundle 179 of 181
-- statement:
--   Definitions bundle 179 of 181 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B177`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 179 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.allocatedActiveContainedProgression`, `OAI.Erdos3.VectorPolynomial.allocatedAmbientNormalizationLog`, `OAI.Erdos3.VectorPolynomial.exists_canonicalSlicedNative_input_budget`, `OAI.Erdos3.VectorPolynomial.forecastDensityNormalizedAtom`, `OAI.Erdos3.VectorPolynomial.forecastNormalizedResidueFactor`, `OAI.Erdos3.VectorPolynomial.forecastNormalizedResidues`, `OAI.Erdos3.forecastSiteMixtureCoefficient`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B055
import Definitions.Def_OAIErdos3B152

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastContinuousRetainedExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w uR

variable {R : Type uR} {A : Type u} {S : Type v}
variable [Fintype R] [Fintype A] [Fintype S]
variable (e : R → A → ScalarSiteExpansion.{v,w} S)

noncomputable def forecastSiteMixtureCoefficient (c : R → ℂ)
    (t : Σ r, ∀ a, (e r a).Term) : ℂ :=
  c t.1 * siteFamilyCoefficient (e t.1) t.2

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X J : Type*} [Fintype G] [Fintype X]
  [Fintype J] [DecidableEq J]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)
variable (s : Empty ↪ J) (root : J → ℤ) (D : Matrix Empty J ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}

variable (hR : ∀ j, R j ≠ 0) (hB : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, 4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
  (hprincipal : ∀ j : {a : LayerSamplerAxis I n // ¬P a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
  (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
  (r : ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) P → ℝ) (hr : ∀ e, |r e| ≤ 1)


include hR ha hδ hprincipal hw hl hr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X J : Type*} [Fintype G] [Fintype X]
  [Fintype J] [DecidableEq J]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)
variable (s : Empty ↪ J) (root : J → ℤ) (D : Matrix Empty J ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (hR : ∀ j, R j ≠ 0) (hB : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, 4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
  (hprincipal : ∀ j : {a : LayerSamplerAxis I n // ¬P a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
  (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
  (r : ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) P → ℝ) (hr : ∀ e, |r e| ≤ 1)


attribute [local instance] ScalarSiteExpansion.termFinite

include hR ha hδ hprincipal hw hl hr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X J : Type*} [Fintype G] [Fintype X]
  [Fintype J] [DecidableEq J]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)
variable (s : Empty ↪ J) (root : J → ℤ) (D : Matrix Empty J ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}

variable (hR : ∀ j, R j ≠ 0) (hB : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, 4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
  (hprincipal : ∀ j : {a : LayerSamplerAxis I n // ¬P a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
  (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
  (r : ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) P → ℝ) (hr : ∀ e, |r e| ≤ 1)


include hR ha hδ hprincipal hw hl hr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

end Erdos3

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X J : Type*} [Fintype G] [Fintype X]
  [Fintype J] [DecidableEq J]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)
variable (s : Empty ↪ J) (root : J → ℤ) (D : Matrix Empty J ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (hR : ∀ j, R j ≠ 0) (hB : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, 4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
  (hprincipal : ∀ j : {a : LayerSamplerAxis I n // ¬P a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
  (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
  (r : ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) P → ℝ) (hr : ∀ e, |r e| ≤ 1)

local notation "ContinuousCoord" => ((Spatial → ℝ) × (Output → ℝ))

attribute [local instance] ScalarSiteExpansion.termFinite

include hR ha hδ hprincipal hw hl hr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

variable {ContinuousCoord : Type*} [PseudoMetricSpace ContinuousCoord]
variable (density : ContinuousCoord → ℝ) (H : ℝ) (hH : 1 ≤ H)
variable (hdensity : ∀ y, ‖density y‖ ≤ H)
variable (densityLip : ℝ≥0) (hLip : LipschitzWith densityLip density)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedModularGeneralNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

def allocatedAmbientNormalizationLog {A : Type*} [Semiring A]
    (dim : ℕ) (D V Q E : A) : A :=
  (dim + 1 : ℕ) * D * (8 + Q + E) + (dim : ℕ) * D * (V + 1)

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {X : Type*} [Fintype X] (N q : X → ℕ) {τ : ℝ}

local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_canonicalSlicedNative_input_budget (m dim Amass Aanalytic : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {P D p v F Prho Pk target Banalytic pGeometry Ecoarse gain : ℝ} {nX : ℕ},
      0 ≤ P → D ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P → v ∈ Set.Icc 0 P →
      F ∈ Set.Icc 0 P → Prho ∈ Set.Icc 0 P → Pk ∈ Set.Icc 0 P →
      target ∈ Set.Icc 0 P → Banalytic ∈ Set.Icc 0 P →
      pGeometry ∈ Set.Icc 0 P → Ecoarse ∈ Set.Icc 0 P →
      gain ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Emodel := (D + p + v + F + Prho + Pk + target + Amass) ^ Amass
      let analytic := (D + p + v + F + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic
      let Espatial := coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim (pGeometry + Ecoarse))
      let volumeLog := allocatedAmbientNormalizationLog dim (nX : ℝ) pGeometry pGeometry pGeometry
      let Pvolume := (nX : ℝ) + volumeLog
      let budget := (P + C) ^ C
      P ≤ budget ∧ Emodel ∈ Set.Icc 0 budget ∧ analytic ∈ Set.Icc 0 budget ∧
        Espatial ∈ Set.Icc 0 budget ∧ Pvolume ∈ Set.Icc 0 budget ∧
        volumeLog ≤ Pvolume ∧ (nX : ℝ) ≤ gain + 8 + Emodel + Espatial + Pvolume := by
  obtain ⟨Aspatial, _, hspatial⟩ := exists_allocatedEarlyCoarseLog_bound m dim
  let X : Polynomial ℕ := Polynomial.X
  let massPoly := (7 * X + Polynomial.C Amass) ^ Amass
  let analyticPoly := (8 * X + Polynomial.C Aanalytic) ^ Aanalytic
  let spatialPoly := (2 * X + Polynomial.C Aspatial) ^ Aspatial
  let volumePoly := X + allocatedAmbientNormalizationLog dim X X X X
  obtain ⟨C, hC, hbound⟩ :=
    exists_natPolynomial_eval_budget (X + massPoly + analyticPoly + spatialPoly + volumePoly)
  refine ⟨C, hC, ?_⟩
  intro P D p v F Prho Pk target Banalytic pGeometry Ecoarse gain nX hP hD hp hv hF hPrho hPk
    htarget hBanalytic hGeometry hEcoarse hgain hnX Emodel analytic Espatial volumeLog Pvolume budget
  let massBound := (7 * P + Amass) ^ Amass
  let analyticBound := (8 * P + Aanalytic) ^ Aanalytic
  let spatialBound := (2 * P + Aspatial) ^ Aspatial
  let volumeBound := P + allocatedAmbientNormalizationLog dim P P P P
  have hsum : P + massBound + analyticBound + spatialBound + volumeBound ≤ budget := by
    simpa [X, massPoly, analyticPoly, spatialPoly, volumePoly, massBound, analyticBound,
      spatialBound, volumeBound, allocatedAmbientNormalizationLog, Polynomial.eval₂_pow] using hbound P hP
  have hD0 : 0 ≤ D := hD.1
  have hp0 : 0 ≤ p := hp.1
  have hv0 : 0 ≤ v := hv.1
  have hF0 : 0 ≤ F := hF.1
  have hPrho0 : 0 ≤ Prho := hPrho.1
  have hPk0 : 0 ≤ Pk := hPk.1
  have htarget0 : 0 ≤ target := htarget.1
  have hBanalytic0 : 0 ≤ Banalytic := hBanalytic.1
  have hGeometry0 : 0 ≤ pGeometry := hGeometry.1
  have hEcoarse0 : 0 ≤ Ecoarse := hEcoarse.1
  have hmass0 : 0 ≤ Emodel := by dsimp [Emodel]; positivity
  have hanalytic0 : 0 ≤ analytic := by dsimp [analytic]; positivity
  have hspatial0 : 0 ≤ Espatial :=
    (coarseSpatialLogs_nonneg (allocatedEarlyCoarseInput_bounds m dim
      (add_nonneg hGeometry.1 hEcoarse.1)).1).2
  have hvolume0 : 0 ≤ volumeLog := by
    dsimp [volumeLog, allocatedAmbientNormalizationLog]
    positivity
  have hPvolume0 : 0 ≤ Pvolume := add_nonneg (Nat.cast_nonneg _) hvolume0
  have hm : Emodel ≤ massBound := by
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hD.2, hp.2, hv.2, hF.2, hPrho.2, hPk.2, htarget.2]
  have ha : analytic ≤ analyticBound := by
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hD.2, hp.2, hv.2, hF.2, hPrho.2, hPk.2, htarget.2, hBanalytic.2]
  have hs : Espatial ≤ spatialBound := by
    apply (hspatial (add_nonneg hGeometry.1 hEcoarse.1)).2.trans
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hGeometry.2, hEcoarse.2]
  have hvb : Pvolume ≤ volumeBound := by
    dsimp only [Pvolume, volumeLog, volumeBound, allocatedAmbientNormalizationLog]
    gcongr <;> first | assumption | exact hGeometry.2
  have hm0 : 0 ≤ massBound := by dsimp [massBound]; positivity
  have ha0 : 0 ≤ analyticBound := by dsimp [analyticBound]; positivity
  have hs0 : 0 ≤ spatialBound := by dsimp [spatialBound]; positivity
  have hv0 : 0 ≤ volumeBound := by
    dsimp [volumeBound, allocatedAmbientNormalizationLog]
    positivity
  refine ⟨?_, ⟨hmass0, ?_⟩, ⟨hanalytic0, ?_⟩, ⟨hspatial0, ?_⟩,
    ⟨hPvolume0, ?_⟩, ?_, ?_⟩
  · linarith only [hsum, hm0, ha0, hs0, hv0]
  · linarith only [hsum, hm, hP, ha0, hs0, hv0]
  · linarith only [hsum, ha, hP, hm0, hs0, hv0]
  · linarith only [hsum, hs, hP, hm0, ha0, hv0]
  · linarith only [hsum, hvb, hP, hm0, ha0, hs0]
  · exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  · dsimp only [Pvolume]
    linarith only [hgain.1, hmass0, hspatial0, hvolume0]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators
universe uI uQ

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedActiveContainedTupleMap
namespace OAI

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
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "sides" => allocatedPrincipalSides B U basis S

noncomputable def allocatedActiveContainedProgression
    (step H : Input → ℕ) (c : Input → ℤ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (v : ∀ j, IntegerScalarCubeBox Empty (H j)) :
    PrincipalAxisTuples (α := Empty) (fun a => ¬short a) sides :=
  fun j i => ⟨(containedProgressionCubeMap Empty S.value (H j) (step j) (c j)
    S.positive (hsubset j) (v j) i : ℤ), by
      simpa only [principalAxisLength, allocatedPrincipalSides_not_short B U basis S j.1 j.2]
        using (containedProgressionCubeMap Empty S.value (H j) (step j) (c j)
          S.positive (hsubset j) (v j) i).property⟩

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

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastOriginalSampleResidueFactor
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (P : LayerSamplerAxis I n → Prop)
variable {A Y Site : Type*} [Fintype A] [Fintype Y]
variable (selected : A → Σ j : Fin m, Fin (n j)) (R : Fin m → ℝ)
variable (e : A → ScalarSiteExpansion Site) (k : ∀ a, (e a).Term) (site : Site)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (M : ℕ) (hd : ∀ a, (e a).period (k a) ∣ M)

noncomputable def forecastNormalizedResidues
    (label : ∀ j, Fin (n j) ⊕ E j → ZMod M) : ∀ a, ZMod ((e a).period (k a)) :=
  fun a => ZMod.castHom (hd a) (ZMod ((e a).period (k a)))
    (label (selected a).1 (.inl (selected a).2))

noncomputable def forecastNormalizedResidueFactor
    (ψ : AddChar (∀ j, Fin (n j) ⊕ E j → ZMod M) ℂ)
    (f : (Y → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit) → ℝ) → ℂ)
    (label : ∀ j, Fin (n j) ⊕ E j → ZMod M)
    (x : (Y → ℝ) × (LayerSamplerAxis I n → ℝ)) : ℂ :=
  star (ψ label) * f (x.1, forecastNormalizedActiveCoordinates P x.2) *
    siteFamilyFactor e k site (forecastNormalizedResidues selected e k M hd label)
      (forecastNormalizedInactiveCoordinates selected R x.2)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X Spatial : Type*} [Fintype G] [Fintype X] [Fintype Spatial]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastDensityPhysicalApproximation
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)


variable (density : ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ) → ℝ)
variable (cap lip : ℝ≥0)
variable (hbound : ∀ y, |density y| ≤ (cap : ℝ)) (hLips : LipschitzWith lip density)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)


variable (density : ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ) → ℝ)
variable (cap lip : ℝ≥0)
variable (hbound : ∀ y, |density y| ≤ (cap : ℝ)) (hLips : LipschitzWith lip density)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (density : ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ) → ℝ)
variable (cap lip : ℝ≥0)
variable (hbound : ∀ y, |density y| ≤ (cap : ℝ)) (hLips : LipschitzWith lip density)

noncomputable def forecastDensityNormalizedAtom
    {A Site : Type*} [Fintype A]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    {Nmod : ℕ} [NeZero Nmod]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod Nmod) ℂ)
    (e : A → ScalarSiteExpansion Site) (k : ∀ a, (e a).Term) (site : Site)
    (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
    (u : X → ℤ) (deck : ∀ j, Eout j → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) : ℂ :=
  ((density
    ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
      forecastNormalizedActiveCoordinates short
        (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
    star (χ (fun output => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (w j).2 (deck j)) output : ZMod Nmod))) *
    siteFamilyFactor e k site
      (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
      (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
        basisAxisScale (basis (selected a).1) (selected a).2)) /
    (((cap : ℝ) + 1 : ℝ) : ℂ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

end Erdos3.VectorPolynomial

end

end OAI

end


