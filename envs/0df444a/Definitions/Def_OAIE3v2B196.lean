-- Prove2me | Definitions.Def_OAIE3v2B196
-- name    : OAIE3v2B196
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:57:58.581649+00:00
-- url     : https://prove2.me/theorems/ac664339-ac83-40b2-aac8-d94a27dd71f4
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 199 of 311
-- statement:
--   Definitions bundle 199 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B176`, `OAIE3v2B177` of this split.
--
--   Modules: `Estimates/AllocatedBufferedAmbientCutoff.lean`, `Estimates/AllocatedCoveredSiteExpansion.lean`, `Estimates/AllocatedNaturalFullSiteScale.lean`, `Estimates/AllocatedOriginalExponentialCover.lean`, `Estimates/AllocatedRefinedLongJetComparison.lean`, `Estimates/AllocatedSlicedCoarseSource.lean`, `Estimates/PreparedFiniteForwardFixedCenterThreshold.lean`, `Geometry/AllocatedAmbientLongBox.lean`, `Geometry/AllocatedFullSiteSupport.lean`, `Geometry/PrincipalCubeSupportedCell.lean`, `Lattices/AllocatedAffineRadiusLog.lean`, `Lattices/AllocatedLocalResidueReconstruction.lean`, `Lattices/AllocatedResidueInterpolationMixture.lean`, `Lattices/AllocatedSupportedSlicedResidueGrid.lean`, `Lattices/AllocatedSupportedSlicedResidueJet.lean`, `Polynomial/CandidateNestedDegreeNetSchedule.lean`, `Polynomial/ForecastSlicedEarlyUnrestrictedPolynomialBudget.lean`, `Polynomial/PreparedFiniteNestedForwardAllDegreePaddedSource.lean`, `Probability/AllocatedFixedPositiveDensity.lean`, `Probability/AllocatedProgressionDensityIdentity.lean`, `Probability/ContainedSupportedProgressionJetLaw.lean`, `Probability/PreparedModularGeneralCenteredLaw.lean`, `Sampling/AllocatedClippedFullGridGlobal.lean`, `Sampling/AllocatedFullGridSiteFactors.lean`, `Sampling/AllocatedGridNaturalWindow.lean`, `Sampling/AllocatedGridlessProfileBound.lean`, `Sampling/AllocatedPhysicalGridMask.lean`, `Sampling/AllocatedSupportedSlicedGridMarginal.lean`, `Sampling/AllocatedSupportedSlicedInactiveGridSite.lean`, `Sampling/ForecastInactiveFixedSupport.lean`, `Sampling/ForecastInactiveSlicedFixedScalarCapBudget.lean`, `Sampling/ForecastNativePullbackBudget.lean`, `Sampling/PreparedActualSlicedForecastSetup.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B176
import Definitions.Def_OAIE3v2B177

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

noncomputable def allocatedLongJetTarget
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    ∀ a : {a // ¬grid a}, CoefficientJetAxisRow O a.val → ℝ
  | ⟨⟨j, .inl i⟩, _⟩ => allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y
  | ⟨⟨j, .inr i⟩, _⟩ => fun z => allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y
      (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFixedPositiveDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

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

include hC hV hσ1 hCinv hchart hsmall in
theorem allocatedCoefficientDensity_fixedScale_le_exp
    {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hSP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    allocatedCoefficientDensity B U b hb o hR hσ S x ≤
      Real.exp (allocatedFourierLogBudget m P) := by
  have hcap := (allocatedCoefficientDensity_bounds B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall x).2
  have hbudget := allocatedCoefficient_fourier_input_budget B R σ S.value S.positive C V
    hP hm hK hR hσ hRP hσP hcount hI hn hJ hAP hSP hCP hVP
  exact hcap.trans hbudget.2.2.1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

noncomputable def principalSupportedCoordinateWeights (t : PrincipalTupleIndex B h) :
    FiniteProbabilityWeights (IntegerScalarCubeBox α (L t)) :=
  (integerScalarCubeWeights α (L t) (hL t)).condition
    (Finset.univ.filter (fun z => (fun i => ((z i : ℤ) : ZMod q)) = r t))
    (FiniteProbabilityWeights.coordinate_fiber_mass_pos
      (fun t => integerScalarCubeWeights α (L t) (hL t))
      (fun t (z : IntegerScalarCubeBox α (L t)) i => ((z i : ℤ) : ZMod q)) r hcell t)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedSupportedProgressionJetLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "weights" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "tupleMap" => containedProgressionTupleMap B h L H step c hL hsubset

noncomputable def containedSupportedProgressionLaw : FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) :=
  (weights).fiberLaw tupleMap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveFixedSupport
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedAmbientLongBox
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

section Box

variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

noncomputable def allocatedLongJetRowBox (T : ℝ) :
    ∀ a : {a // ¬grid a}, Set (CoefficientJetAxisRow O a.val)
  | ⟨⟨j, .inl _⟩, _⟩ => (Metric.closedBall (0 : O j → ℝ) T : Set (O j → ℝ))
  | ⟨⟨j, .inr i⟩, _⟩ =>
      (rectangularWeightIndices (fun _ => 0) (fun _ : O j => (basisAxisScale (basis j) i : ℝ)) T : Set (O j → ℤ))

noncomputable def allocatedLongJetBox (T : ℝ) : Set (AllocatedLongJetRows B U basis S O) :=
  Set.univ.pi (allocatedLongJetRowBox B U basis S O T)

end Box

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalCubeSupportedCell
namespace OAI

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

noncomputable def containedSupportedProgressionAxisLaw :
    FiniteProbabilityWeights (PrincipalAxisTuples (α := α) P L) :=
  (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex BP hP =>
    principalSupportedCoordinateWeights B h H hH q r hcell (embed j))).fiberLaw
      (containedProgressionTupleMap BP hP (principalAxisLength P L) (principalAxisLength P H)
        (principalAxisLength P step) (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j)))

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

omit [Fintype X] in
theorem allocatedCenteredJointDensity_eq_affine
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z =
      allocatedAffineDensity B U b hb o hR hσ S poly hmem c
        (fun k i => (jointIntegerFrame (a, z) k i : ℝ)) := by
  unfold allocatedCenteredJointDensity allocatedAffineDensity
  rw [centeredAffineCoefficientTorus_eq_subtractive, ← hc]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d Ω

noncomputable def allocatedCoveredProfileDensity (f : AllocatedLongJetRows B U b S O → ℝ) :
    EuclideanJetLayers U O → ℝ :=
  restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Q n d =>
    allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 * f ((split z.1).2))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

noncomputable def allocatedFullAmbientSiteCoordinates (z : ambient → ℝ) : LayerSamplerAxis I n → ℝ :=
  fun a =>
    let w := mixedRealCoordinates (euclideanSubspace (U a.1)) (b a.1) (o a.1)
      ((EuclideanSpace.equiv (J a.1) ℝ).symm (fun k => z ⟨a.1, (), k⟩))
    Sum.elim w.1 w.2 a.2 / R a.1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedBufferedAmbientCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

variable (r : ℝ≥0) (hr : 0 < r)

noncomputable def allocatedBufferedAmbientCutoff (z : ambient → ℝ) : ℝ :=
  normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
    (allocatedFullAmbientSiteCoordinates (R := R) U b o z)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedNaturalFullSiteScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (j : Fin m) (i : Fin (n j))

noncomputable def allocatedNaturalFullSiteRatio : ℝ :=
  R j * allocatedPrincipalChartRatio (G := G) B U b (R := R) j i

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedGridNaturalWindow
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
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
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
variable (selected : {a // allocatedGridAxis (I := I) U b S.value a} → Prop)
variable [DecidablePred selected]
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q r hcell

noncomputable def allocatedSelectedGridExtension (g : ((a : {a : gridAxes // selected a}) → CoefficientJetAxisRow O (Subtype.val (Subtype.val a))) → ℂ) (N : ℝ) :
    AllocatedFrozenJetRows B U b S O → ℂ :=
  selectedProductExtension selected (fun a z => (laws a z).toReal) g N

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedGridlessProfileBound
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter

noncomputable def allocatedGridlessCoveredProfile (f : AllocatedLongJetRows B U b S O → ℝ) :
    EuclideanJetLayers U O → ℝ :=
  restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Q n d =>
    (coefficientDeckJetDensity root dirs rows d z.2 / coveredJetArrayScale (O := O) U) *
      f ((split z.1).2))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

noncomputable def allocatedGridlessWeightedKernel
    (g : AllocatedFrozenJetRows B U b S O → ℝ) (f : AllocatedLongJetRows B U b S O → ℝ)
    (z : MixedCoveredJetSource I O Q n d) : ℝ :=
  g ((split z.1).1) * f ((split z.1).2) * coefficientDeckJetDensity root dirs rows d z.2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedLocalResidueReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (H : X → ℝ)
variable {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)

noncomputable def allocatedResidueSpatialKernel
    (r : labels) (v : X → (Unit ⊕ Fin dim) → ℤ) : ℂ :=
  let ker := fun g => (0 : ℤ) + (x g none : ℤ)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker
    (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
  let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  ∏ t, spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
    (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
      (liftResidueMatrix (principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r)))
    modulus f (H t) 4 mesh (v t)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

local notation "labels" => PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus
local notation "terms" => X → SpatialSiteLabel (Fin dim) modulus 4 mesh

noncomputable def allocatedSpatialExpansionCoefficient (r : labels) (t : terms) : ℂ :=
  let ker := fun g => (0 : ℤ) + (x g none : ℤ)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker
    (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
  let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  ∏ z : X, spatialSiteCoefficient (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
    (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
      (liftResidueMatrix (principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r)))
    modulus f 4 mesh (t z)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)

noncomputable def allocatedWholeResidueReconstruction (base : X → ℤ)
    (r : labels) (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q) :=
  physicalResidueReconstruction
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r))
    (allocatedPhysicalCubeDirections B U b S x (wholeReference r)) base
    (boundedColumnResidueRepresentative q a) q

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedCoarseSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

noncomputable def allocatedRecenteredProfileTerm
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) : ℂ :=
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y)
  ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
    ∑ v ∈ window,
      (allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
        (trimmedSpatialRootScale τ N q) hW mesh (principalResidueLabel modulus y) v / (A : ℂ)) *
      test (reconstruct a.val v) * profile y (point (reconstruct a.val v))

noncomputable def allocatedRecenteredProfileMass
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) : ℝ :=
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y)
  ∑ a : cells, selectedResidueCellWeight q cells V a *
    ((∑ v ∈ window, ‖profile y (point (reconstruct a.val v))‖) / A)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidueJet
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

noncomputable def allocatedSupportedSlicedResidueJetPMF
    (rows : Finset (Finset α)) (shift : rows → ℤ) : PMF (rows → ℤ) :=
  (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
    allocatedLayerIntegerPMFs B U basis hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))).bind
    (fun coeff => (conditioned).toPMF.map (fun y =>
      shift + ∑ b, fun t : rows => coeff b *
        integerBooleanBlockJet (fun v k => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ k : ℤ)) t))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidueGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

noncomputable def allocatedSupportedSlicedGridDensity (M : ℕ) (rows : Finset (Finset α))
    (shift z : rows → ℤ) : ℝ :=
  (basisAxisScale (basis j) i : ℝ) ^ rows.card *
    (((allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift).map
      (integerGridResidue M)) (integerGridResidue M z)).toReal

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedInactiveGridSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "coeff" => (fun _ : B (Sigma.mk j (Sum.inr i)) =>
  allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

local notation "radius" => blockJetScaleBound (Fintype.card α) (Fin.val j + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "height" => basisAxisScale (basis j) i

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

noncomputable def allocatedSupportedSlicedPhysicalGridPMF
    (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value) : PMF (rows → ℤ) :=
  (conditioned).toPMF.bind (fun y =>
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
      (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i))

noncomputable def allocatedSupportedSlicedPhysicalGridApproximation
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (F : Finset (rows → Fin M)) (z : rows → ℤ) : ℂ :=
  ∫ zeta, weightedAffineModeratePlateauApproximation coeff sources lower strides (fun _ => 0)
    height radius rows (fun t => booleanCoefficient (fun _ : Finset α => zeta) t) z F
    ∂(constantLaw).toMeasure

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))

local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

noncomputable def allocatedSupportedSlicedInactivePhysicalGridApproximation
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (F : Finset (rows → Fin M)) (z : rows → ℤ) : ℂ :=
  ∫ zeta, affineCubePlateauApproximation sources lower strides height radius rows
    (fun t => booleanCoefficient (fun _ : Finset α => zeta) t) z F ∂(constantLaw).toMeasure

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFullGridSiteFactors
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ}
variable {A S : Type*} [Fintype A] (e : A → ScalarSiteExpansion S)
variable (selected : A → Σ j : Fin m, Fin (n j))

local notation "index" => fun a : A => (Sigma.mk (Sigma.fst (selected a)) (Sum.inr (Sigma.snd (selected a))) : LayerSamplerAxis I n)
local notation "ratio" => fun a : A => allocatedNaturalFullSiteRatio (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))

noncomputable def allocatedFullGridSiteFactor (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) (x : LayerSamplerAxis I n → ℝ) : ℂ :=
  scaledSiteFamilyFactor e (index) (ratio) k s r x

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalExponentialCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

noncomputable def allocatedRecenteredResidueWeight
    (r : labels) (a : cells) (v : X → (Unit ⊕ Fin dim) → ℤ) : ℂ :=
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r
  (allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
    (trimmedSpatialRootScale τ N q) hW mesh (principalResidueLabel modulus (wholeReference r)) v / (A : ℂ)) *
      test (reconstruct a.val v)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_candidateNestedForwardSeed_polynomial_budget
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ) (Q : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x : ℝ}, 0 ≤ x → ∀ outer ≤ outerDepth,
      Q.eval₂ (Nat.castRingHom ℝ)
        (candidateNestedForwardSeed A constants innerDepth outer x) ≤ (x + 2) ^ C := by
  let polys := fun o => Q.comp (candidateNestedForwardSeedPolynomial A constants innerDepth o)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (∑ o ∈ Finset.range (outerDepth + 1), polys o)
  refine ⟨C, hC, ?_⟩
  intro x hx outer ho
  apply le_trans _ (hbound x hx)
  rw [Polynomial.eval₂_finsetSum]
  have hentry := Finset.single_le_sum (f := fun o => (polys o).eval₂ (Nat.castRingHom ℝ) x)
    (fun o _ => natPolynomial_eval_nonneg (polys o) hx) (Finset.mem_range.mpr (Nat.lt_succ_of_le ho))
  simpa only [polys, Polynomial.eval₂_comp, candidateNestedForwardSeed] using hentry

theorem exists_candidateNestedForwardLocal_budget
    (A Cdirect : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ) (hA : 2 ≤ A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x gainLog stageLog : ℝ}, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      ∀ outer ≤ outerDepth, ∀ inner ≤ innerDepth,
      let seed := candidateNestedForwardSeed A constants innerDepth outer x
      seed ∈ Set.Icc 0 ((x + 2) ^ C) ∧
      preparedFiniteForwardParameter A constants inner seed ∈ Set.Icc 0 ((x + 2) ^ C) ∧
      preparedFiniteForwardWork A constants inner seed ∈ Set.Icc 0 ((x + 2) ^ C) ∧
      preparedFiniteForwardCumulative A constants inner seed ∈ Set.Icc 0 ((x + 2) ^ C) ∧
      preparedFiniteForwardModelPrecision A constants inner seed gainLog stageLog ∈
        Set.Icc 0 ((x + 2) ^ C) ∧
      ∀ direct : Bool, preparedFiniteForwardPairedSourcePrecision A Cdirect constants
        inner direct seed gainLog stageLog ∈ Set.Icc 0 ((x + 2) ^ C) := by
  obtain ⟨B, _, hstage⟩ := exists_preparedFiniteForwardStage_budget innerDepth A constants
  obtain ⟨D, _, hpaired⟩ :=
    exists_preparedFiniteForwardPairedSourcePrecision_budget innerDepth A Cdirect constants
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C B) ^ B +
    (Polynomial.X + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbound⟩ :=
    exists_candidateNestedForwardSeed_polynomial_budget A constants innerDepth outerDepth Q
  refine ⟨C, hC, ?_⟩
  intro x gainLog stageLog hx hg hs outer ho inner hi seed
  have hseed : 0 ≤ seed := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  have hxs : x ≤ seed := le_candidateNestedForwardSeed A constants innerDepth outer hA hx
  have hg' : gainLog ∈ Set.Icc 0 seed := ⟨hg.1, hg.2.trans hxs⟩
  have hs' : stageLog ∈ Set.Icc 0 seed := ⟨hs.1, hs.2.trans hxs⟩
  have htotal : seed + (seed + B) ^ B + (seed + D) ^ D ≤ (x + 2) ^ C := by
    simpa [Q, seed, Polynomial.eval₂_pow] using hbound hx outer ho
  have hB0 : 0 ≤ (seed + B) ^ B := by positivity
  have hD0 : 0 ≤ (seed + D) ^ D := by positivity
  have hBup : (seed + B) ^ B ≤ (x + 2) ^ C := by linarith only [htotal, hseed, hD0]
  have hDup : (seed + D) ^ D ≤ (x + 2) ^ C := by linarith only [htotal, hseed, hB0]
  obtain ⟨hparam, hwork, _, _, _, hcum, _, hmodel, _⟩ :=
    hstage seed gainLog stageLog hseed hg' hs' inner hi
  refine ⟨⟨hseed, by linarith only [htotal, hB0, hD0]⟩,
    ⟨hparam.1, hparam.2.trans hBup⟩, ⟨hwork.1, hwork.2.trans hBup⟩,
    ⟨hcum.1, hcum.2.trans hBup⟩, ⟨hmodel.1, hmodel.2.trans hBup⟩, ?_⟩
  intro direct
  have h := hpaired hseed hg' hs' inner hi direct
  exact ⟨h.1, h.2.trans hDup⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineRadiusLog
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) → ℝ)

noncomputable def allocatedAffineLongJetDensity (y : activeInput → ℝ) : (realOutput → ℝ) → ℝ := by
  exact allocatedNormalizedLongJetDensity B U basis S x u rows s hA (fun i => center i + width i * y i)

noncomputable def allocatedAffineLongJetProxy : (realOutput → ℝ) → ℝ :=
  densityMixture (jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val))
    (allocatedAffineLongJetDensity B U basis S x u rows s hA center width)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] [DecidableEq α]
  {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]

noncomputable def allocatedAffinePartitionLog (A T : ℝ≥0) (E F : ℝ)
    (P : LayerSamplerAxis I n → Prop) : ℝ :=
  let Clog := unitProfileCoefficientLog (B := B) A T
  let Elog := E + Fintype.card {a // ¬P a} + 4
  let Qlog := jointAffineSourceInputLog (B := fun a : {a // ¬P a} => B a.val)
    (O := fun a : {a // ¬P a} => O a.val.1) (α := α)
    (fun a => layerSamplerDegree I n a.val) Clog Elog F
  Real.log 16 + 6 * Qlog +
    booleanToleranceC2Log (B := fun a : {a // ¬P a} => B a.val) (α := α)
      (PartitionedProfileNoiseIndex G (G × Option α) α B (layerSamplerDegree I n) P)
      (fun a => layerSamplerDegree I n a.val) m Clog + 1

noncomputable def allocatedAffineToleranceLog (A T : ℝ≥0) (E F : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (allocatedAffinePartitionLog (G := G) (O := O) (α := α) B A T E F)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedPhysicalGridMask
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]
variable (T : Fin m → ℝ)

noncomputable def allocatedPhysicalGridCondition
    (z : AllocatedFrozenJetRows B U b S O) : Prop :=
  ∀ (j : Fin m) (i : Fin (n j)) (hg : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (t : O j), |(z ⟨⟨j, Sum.inr i⟩, hg⟩ t : ℝ) / basisAxisScale (b j) i| ≤ T j * R j

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedGridMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (rows : A → Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

noncomputable def allocatedSupportedSlicedPhysicalJointPMF : PMF (∀ a, rows a → ℤ) :=
  (conditioned).toPMF.bind (fun y => dependentProductPMF (fun a =>
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) ((selected a).1.val + 1)
      (fun t : rows a => (t : Finset α)))
      (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridGlobal
namespace OAI

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
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

noncomputable def allocatedSupportedSlicedFullGridDensity (x : G → IntegerScalarCubeBox α S.value)
    (z : AllocatedFrozenJetRows B U b S rowTypes) : ℝ :=
  ∏ a : gridAxes, (allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step c hH hsubset hcell
    (ig a).1 (ig a).2 (rowSets (ig a).1) x (allocatedGridIntegerValues B U b S rowSets a (z a))).toReal

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedScalarCapBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (Hchild : ℕ)

def slicedFixedZeroGeometryLog {A : Type*} [Semiring A]
    (D v w vq vchild : A) : A :=
  slicedGridGeometryLog D v w (vq + w + 1) +
    (2 * (D + v + 8) + D * (vchild + 1) + 4)

theorem slicedFixedZeroGeometryLog_nonneg {D v w vq vchild : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (hvq : 0 ≤ vq) (hvc : 0 ≤ vchild) :
    0 ≤ slicedFixedZeroGeometryLog D v w vq vchild := by
  unfold slicedFixedZeroGeometryLog slicedGridGeometryLog
  positivity

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem slicedFixedZeroGeometryLog_mono
    {D v w vq vchild D' v' w' vq' vchild' : ℝ}
    (hD0 : 0 ≤ D) (hv0 : 0 ≤ v) (hw0 : 0 ≤ w)
    (hvq0 : 0 ≤ vq) (hvc0 : 0 ≤ vchild)
    (hD : D ≤ D') (hv : v ≤ v') (hw : w ≤ w')
    (hvq : vq ≤ vq') (hvc : vchild ≤ vchild') :
    slicedFixedZeroGeometryLog D v w vq vchild ≤
      slicedFixedZeroGeometryLog D' v' w' vq' vchild' := by
  have hD'0 : 0 ≤ D' := hD0.trans hD
  unfold slicedFixedZeroGeometryLog slicedGridGeometryLog
  gcongr

theorem slicedFixedZeroGeometryLog_eval₂
    (D v w vq vchild : Polynomial ℕ) (x : ℝ) :
    (slicedFixedZeroGeometryLog D v w vq vchild).eval₂ (Nat.castRingHom ℝ) x =
      slicedFixedZeroGeometryLog (D.eval₂ (Nat.castRingHom ℝ) x)
        (v.eval₂ (Nat.castRingHom ℝ) x) (w.eval₂ (Nat.castRingHom ℝ) x)
        (vq.eval₂ (Nat.castRingHom ℝ) x) (vchild.eval₂ (Nat.castRingHom ℝ) x) := by
  simp [slicedFixedZeroGeometryLog, slicedGridGeometryLog, Polynomial.eval₂_pow]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def forecastSlicedEarlyDiagonalBudget (m : ℕ) (r : ℝ) : ℝ :=
  let pTailAll := r + slicedFixedZeroGeometryLog r r r 0 r
  let tailLog := slicedFixedUniformSiteLog m pTailAll 0
  let Pin := r * tailLog
  let Pdec := (r + r) * (r + 2) * modularRankChargeFactor m
  let V := Pin + Pdec + (r + r) + 3
  let Esite := r + r + 1 + r * V
  let pAll := (r + V) + slicedFixedZeroGeometryLog r r r V r
  let Eprod := slicedFixedUniformAccuracyLog m r pAll Esite
  let Q := slicedFixedUniformSiteLog m pAll Eprod
  let O := siteExponentialOutputLog 1 Q
  let Pperiod := V + r * O
  let Pfactor := r + r + O + 1 + r
  let Pnative := Pperiod + Pfactor + r + r + 1
  let Pmass := r + r * V + r * O + 1
  let Pcap := r + Pin + Pdec + 1
  Pnative + Pmass + Pcap

noncomputable def forecastSlicedEarlyPolynomial (m : ℕ) : Polynomial ℕ :=
  let r : Polynomial ℕ := Polynomial.X
  let pTailAll := r + slicedFixedZeroGeometryLog r r r 0 r
  let tailLog := slicedFixedUniformSitePolynomial m pTailAll 0
  let Pin := r * tailLog
  let Pdec := (r + r) * (r + 2) * Polynomial.C (modularRankChargeFactor m)
  let V := Pin + Pdec + (r + r) + 3
  let Esite := r + r + 1 + r * V
  let pAll := (r + V) + slicedFixedZeroGeometryLog r r r V r
  let Eprod := uniformProductAccuracyLog r (slicedFixedUniformSitePolynomial m pAll 0) Esite + 1
  let Q := slicedFixedUniformSitePolynomial m pAll Eprod
  let O := siteExponentialOutputLog 1 Q
  let Pperiod := V + r * O
  let Pfactor := r + r + O + 1 + r
  let Pnative := Pperiod + Pfactor + r + r + 1
  let Pmass := r + r * V + r * O + 1
  let Pcap := r + Pin + Pdec + 1
  Pnative + Pmass + Pcap

theorem forecastSlicedEarlyPolynomial_eval (m : ℕ) (r : ℝ) :
    (forecastSlicedEarlyPolynomial m).eval₂ (Nat.castRingHom ℝ) r =
      forecastSlicedEarlyDiagonalBudget m r := by
  have hcast (k : ℕ) : (Nat.castRingHom ℝ) k = (k : ℝ) := rfl
  simp only [forecastSlicedEarlyPolynomial, forecastSlicedEarlyDiagonalBudget,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_zero, Polynomial.eval₂_one, Polynomial.eval₂_ofNat,
    slicedFixedZeroGeometryLog_eval₂, slicedFixedUniformSitePolynomial_eval,
    uniformProductAccuracyLog_eval₂, slicedFixedUniformAccuracyLog,
    siteExponentialOutputLog, hcast, Polynomial.eval₂_natCast]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedProgressionDensityIdentity
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => (∫ p, FiniteProbabilityWeights.complexMean wholeLaw (fun y =>
  F (Prod.fst ((allocatedCoefficientSplit B U basis S) (Prod.fst p)),
    euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows
      (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))))
  ∂(Measure.prod source (PMF.toMeasure deck)))

noncomputable def allocatedProgressionCoveredExpectation : ℂ := actual

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {X : Type*} [Fintype X]

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (P : LayerSamplerAxis I n → Prop)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (R : Fin m → ℝ)

def forecastNormalizedInactiveCoordinates (v : LayerSamplerAxis I n → ℝ) : A → ℝ :=
  fun a => R (selected a).1 * v ⟨(selected a).1, Sum.inr (selected a).2⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

noncomputable def actualSlicedForecastModelCapLog (m Dmod cardX : ℕ)
    (P Pscale Pbad Ppres Pκ kernelV p w vchild : ℝ) : ℝ :=
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let v := P + Pscale
  let Psm := forecastOriginalSmoothBudget m (P + (cardX + 1) * kernelV)
  let tailLog := slicedFixedUniformSiteLog m
    (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0
  let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
  Pκ + (Psm + D * tailLog + Pdec + 1)

noncomputable def actualSlicedForecastModelPeriodLog (m Dmod cardX : ℕ)
    (P Pscale Pbad Ppres Pκ kernelV p w vchild E : ℝ) : ℝ :=
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let v := P + Pscale
  let Psm := forecastOriginalSmoothBudget m (P + (cardX + 1) * kernelV)
  let tailLog := slicedFixedUniformSiteLog m
    (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0
  let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
  D * tailLog + Pdec + (E + Pκ + Psm) + 3

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_actualSlicedForecastModelCapLog_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (Dmod cardX : ℕ)
      {r P Pscale Pbad Ppres Pκ kernelV p w vchild : ℝ},
      0 ≤ r → (Dmod : ℝ) ≤ r → (cardX : ℝ) ≤ r →
      P ∈ Set.Icc 0 r → Pscale ∈ Set.Icc 0 r → Pbad ∈ Set.Icc 0 r →
      Ppres ∈ Set.Icc 0 r → Pκ ∈ Set.Icc 0 r → kernelV ∈ Set.Icc 0 r →
      p ∈ Set.Icc 0 r → w ∈ Set.Icc 0 r → vchild ∈ Set.Icc 0 r →
      actualSlicedForecastModelCapLog m Dmod cardX
        P Pscale Pbad Ppres Pκ kernelV p w vchild ∈ Set.Icc 0 ((r + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let Dpoly := X + Polynomial.C (layerTailDegree m + 1) + 1
  let Spoly := Polynomial.C (10 * m + 30) * (X + (X + 1) * X + 1) ^ 2
  let Tpoly := slicedFixedUniformSitePolynomial m
    (X + slicedFixedZeroGeometryLog Dpoly (X + X) X 0 X) 0
  let Q := X + (Spoly + Dpoly * Tpoly +
    (X + X) * (X + 2) * Polynomial.C (modularRankChargeFactor m) + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro Dmod cardX r P Pscale Pbad Ppres Pκ kernelV p w vchild
    hr hDmod hcard hP hscale hbad hpres hκ hk hp hw hchild
  let D := P + ((layerTailDegree m + 1 : ℕ) : ℝ) + 1
  let Dr := r + ((layerTailDegree m + 1 : ℕ) : ℝ) + 1
  let v := P + Pscale
  let Psm := forecastOriginalSmoothBudget m (P + (cardX + 1) * kernelV)
  let Rsm := (10 * (m : ℝ) + 30) * (r + (r + 1) * r + 1) ^ 2
  let tail := slicedFixedUniformSiteLog m
    (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0
  let Rtail := slicedFixedUniformSiteLog m
    (r + slicedFixedZeroGeometryLog Dr (r + r) r 0 r) 0
  let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
  let Rdec := (r + r) * (r + 2) * modularRankChargeFactor m
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact add_nonneg (add_nonneg hP.1 (Nat.cast_nonneg _)) zero_le_one
  have hDr0 : 0 ≤ Dr := by dsimp only [Dr]; positivity
  have hDD : D ≤ Dr := by dsimp only [D, Dr]; linarith only [hP.2]
  have hv0 : 0 ≤ v := add_nonneg hP.1 hscale.1
  have hv : v ≤ r + r := add_le_add hP.2 hscale.2
  have hgeom0 := slicedFixedZeroGeometryLog_nonneg hD0 hv0 hw.1 (le_refl 0) hchild.1
  have htail0 : 0 ≤ tail :=
    slicedFixedUniformSiteLog_nonneg m (add_nonneg hp.1 hgeom0) (le_refl 0)
  have htail : tail ≤ Rtail :=
    slicedFixedUniformSiteLog_mono m (add_nonneg hp.1 hgeom0) (le_refl 0)
      (add_le_add hp.2 (slicedFixedZeroGeometryLog_mono hD0 hv0 hw.1
        (le_refl 0) hchild.1 hDD hv hw.2 le_rfl hchild.2)) le_rfl
  have harg0 : 0 ≤ P + (cardX + 1) * kernelV :=
    add_nonneg hP.1 (mul_nonneg (by positivity) hk.1)
  have harg : P + (cardX + 1) * kernelV ≤ r + (r + 1) * r :=
    add_le_add hP.2 (mul_le_mul (add_le_add hcard le_rfl) hk.2 hk.1 (by linarith))
  have hsm0 : 0 ≤ Psm := (forecastOriginalSmoothBudget_bounds m harg0).1
  have hsm : Psm ≤ Rsm := by
    dsimp only [Psm, Rsm, forecastOriginalSmoothBudget]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith only [harg0]) (add_le_add harg le_rfl) 2)
      (by positivity)
  have hdec0 : 0 ≤ Pdec :=
    mul_nonneg (mul_nonneg (add_nonneg hbad.1 hpres.1) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have hdec : Pdec ≤ Rdec := by
    dsimp only [Pdec, Rdec]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (add_le_add hbad.2 hpres.2) (add_le_add hDmod le_rfl)
        (by positivity) (add_nonneg hr hr)) (Nat.cast_nonneg _)
  have hdiag : r + (Rsm + Dr * Rtail + Rdec + 1) ≤ (r + C) ^ C := by
    simpa [Q, Spoly, Dpoly, Tpoly, X, Rsm, Dr, Rtail, Rdec,
      Polynomial.eval₂_pow, slicedFixedUniformSitePolynomial_eval,
      slicedFixedZeroGeometryLog_eval₂] using hbudget r hr
  change 0 ≤ Pκ + (Psm + D * tail + Pdec + 1) ∧
    Pκ + (Psm + D * tail + Pdec + 1) ≤ (r + C) ^ C
  refine ⟨by linarith only [hκ.1, hsm0, mul_nonneg hD0 htail0, hdec0], ?_⟩
  apply le_trans _ hdiag
  exact add_le_add hκ.2 (add_le_add
    (add_le_add (add_le_add hsm (mul_le_mul hDD htail htail0 hDr0)) hdec) le_rfl)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CandidateNestedDegreeNetSchedule
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_candidateNestedForward_polynomial_next_seed (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (constants : ℕ → ℕ) (innerDepth outer : ℕ)
      {x : ℝ}, C ≤ A → 1 ≤ innerDepth → 0 ≤ x →
      P.eval₂ (Nat.castRingHom ℝ)
        (candidateNestedForwardSeed A constants innerDepth outer x) ≤
      candidateNestedForwardSeed A constants innerDepth (outer + 1) x := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_preparedFiniteForward_local_polynomial_le_later_work 1 P
  refine ⟨C, hC, ?_⟩
  intro A constants innerDepth outer x hCA hdepth hx
  let seed := candidateNestedForwardSeed A constants innerDepth outer x
  have hseed : 0 ≤ seed := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  have hzero : (0 : ℝ) ∈ Set.Icc 0 seed := ⟨le_rfl, hseed⟩
  have hsource := preparedFiniteForwardPairedSourcePrecision_nonneg A 0 constants 0 false
    hseed hzero hzero
  have hwork := (preparedFiniteForward_model_scalar_bounds A constants 0 0
    (hC.trans hCA) hseed (by simpa only [Nat.cast_zero] using hseed)).2.1
  have hseedwork := (le_preparedFiniteForwardParameter A constants 0 hseed).trans hwork
  have hfit : seed ∈ Set.Icc 0
      ((preparedFiniteForwardPairedSourcePrecision A 0 constants 0 false seed 0 0 +
        preparedFiniteForwardWork A constants 0 seed + (1 : ℕ)) ^ 1) := by
    refine ⟨hseed, ?_⟩
    simp only [Nat.cast_one, pow_one]
    linarith only [hsource, hseedwork]
  have hpoly := hbound A 0 constants innerDepth hseed hzero hzero hCA hdepth hfit
  simpa only [candidateNestedForwardSeed_succ] using hpoly

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedFiniteNestedForwardAllDegreePaddedSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem le_preparedFiniteNestedForwardAllDegreeSeed {outerDepth innerDepth cutoff : ℕ}
    (A : ℕ) (constants : ℕ → ℕ) {x : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    x ≤ preparedFiniteNestedForwardAllDegreeSeed A constants x k :=
  le_candidateNestedForwardSeed A constants innerDepth k.1.val hA hx

end Erdos3.VectorPolynomial

end

end OAI
end


