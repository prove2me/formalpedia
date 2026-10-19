-- Prove2me | Definitions.Def_OAIE3v2B310
-- name    : OAIE3v2B310
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T09:06:58.21552+00:00
-- url     : https://prove2.me/theorems/98d7cd8a-1127-4d4c-be7e-52598710f569
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 306 of 311
-- statement:
--   Definitions bundle 306 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B292` of this split.
--
--   Modules: `Dynamics/PreparedFiniteNestedFrontNativeBudget.lean`, `Estimates/AllocatedExternalCandidatePreparedPhysicalConclusion.lean`, `Estimates/AllocatedExternalCandidatePrimitiveFrontDescentData.lean`, `Estimates/AllocatedOrdinaryLongPhysicalTerminalConclusion.lean`, `Estimates/AllocatedPrimitiveFrontInitialLong.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeOrdinaryTerminal.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B292

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedFrontNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler.FrontSourceProfile

variable {degree e : ℕ} {p : ℝ} (source : A.FrontSourceProfile degree p e)

theorem exp_neg_familyParameter_le_rawMassLoss (hp : 0 ≤ p) :
    Real.exp (-source.familyParameter) ≤ Real.exp (-source.frontRawMassLoss) :=
  Real.exp_le_exp.mpr (neg_le_neg (source.lossBudget hp).rawMass)

end AllocatedExternalCandidateSampler.FrontSourceProfile
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOrdinaryLongPhysicalTerminalConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound
  HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates associatedGradedMap realPolynomialGroupMap
  AllocatedExternalCandidateProblem.Refinement.problem
  realSymbolHomogeneousPullbackHom CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    (scheduleExponent Cprimitive : ℕ) (x p0 : ℝ)

local notation "fullBudget" => nativePhysicalTerminalFullBudget
  (s + 1) m Cprimitive scheduleExponent x
local notation "affineBudget" => nativePhysicalTerminalAffineBudget (s + 1) scheduleExponent x
local notation "workBudget" => nativePhysicalTerminalWorkBudget (s + 1) scheduleExponent x
local notation "separation" => Real.exp (candidatePrimitiveFreezingCutoff s 1
  (allocatedAffineCanonicalBudget s p0 fullBudget))

theorem conclusion_of_nativeCommonPhysicalTerminal_degreeRule
    {γ : Type} [Fintype γ]
    (hp0 : 0 ≤ p0)
    (hDgeo : D.GeometryComplexityLE p0) (hFgeo : Fmark.GeometryComplexityLE p0)
    (hcForward : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p0)
    (hMap : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p0)
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
    (v : γ → D.filtration.AssociatedGraded)
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule)
    (hvspan : span ℚ (Set.range v) = W.toSubmodule)
    (hγ : (Fintype.card γ : ℝ) ≤ p0)
    (hvHeight : ∀ j i, rationalLogHeight
      ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) ≤ p0)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p0)
    (q : ℝ) (l : ℕ) (hq0 : q ≤ p0) (hl : 0 < l) (hlBound : (l : ℝ) ≤ Real.exp p0)
    (hcost0 : cost ≤ p0)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hshort : ∀ i, ¬initialLong i → (A.sides i : ℝ) ≤ Real.exp p0)
    (hzero : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
        (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
          (fun _ : {i // initialLong i} => 1) ((P.chart z).axisPolynomial initialLong (fun _ => 0))
          ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit)))
    (hσ1 : ∀ j, σ j ≤ 1)
    (Hchart : Fin m → ℝ) (hHchart : ∀ j, 0 ≤ Hchart j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Hchart j * ‖v‖)
    (hsmall : ∀ j, Hchart j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p0)
    (hscore : Real.exp (-p0) ≤ scoreThreshold)
    (hmass : Real.exp (-p0) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget affineBudget + 3) ^ 3)) * massThreshold)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1) (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p0)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hmark : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p0)
    (htop : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0)
    {e : ℕ}
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p0 + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ accuracy)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      (finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s p0 fullBudget)) outputCost)
    (houtput : finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
      (allocatedAffineCanonicalBudget s p0 fullBudget) ≤ outputCost)
    (hterminal : P.NativeCommonPhysicalTerminal c ν hF hφ W
      scheduleExponent Cprimitive x separation) :
    Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  obtain ⟨hpFull, qDim, eQ, lift, history, ⟨data⟩⟩ := hterminal.exists_physicalData
  obtain ⟨out⟩ := P.conclusion_of_affinePhysicalTerminal_bounds_degreeRule
    Fmark φ hφ W c ν hF (eQ.baseChange ℝ) lift
    affineBudget workBudget affineBudget fullBudget separation history data
    p0 hp0 hpFull hDgeo hFgeo hcForward hMap ω hD v hW hvspan hγ hvHeight hvariables
    q l hq0 hl hlBound hcost0 initialLong hshort hzero rfl hσ1 Hchart hHchart hchart hsmall
    hpoly hweight hscore hmass hsurj hξ1 ℓ hℓ hLip hpositive hmark htop hnet outputCost lowerIH
  have hcost : candidateSideCutoffCost separation ≤ outputCost :=
    (allocatedAffineCanonical_cutoffCost_le_recursive s hp0 hpFull).trans houtput
  exact ⟨by simpa only [max_eq_left hcost] using out⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators NNReal

attribute [local irreducible] realPolynomialSymbolHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree
  polynomialOrbitCoordinates realGradedSymbolPolynomial weightedAdaptedRealChartHom
  HasCommonRefilteredOrbitFactors associatedGradedMap

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, Submodule.span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    {Fmark : NilpotentLieFiltration M (s + 1)} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (Mmodel : RationalFilteredNilmanifold M (s + 1) f)
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (ν : Fin f → ℕ)
    (hF : ∀ j, Fmark.layer j = Submodule.span ℚ (Mmodel.basis '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ z ∈ D.filtration.layer j, φ z ∈ Fmark.layer j)

variable {P Mmodel ω hD ν hF hφ}
    {p0 x separation : ℝ} {nGenerators scheduleExponent Cprimitive : ℕ}
    {initialLong : LayerSamplerVariables G I n B → Prop}

local notation "fullBudget" => nativePhysicalTerminalFullBudget
  (s + 1) m Cprimitive scheduleExponent x
local notation "affineBudget" => nativePhysicalTerminalAffineBudget (s + 1) scheduleExponent x
local notation "backendBudget" => allocatedAffineCanonicalBudget s p0 fullBudget
local notation "recursiveBudget" => finiteFreezingRecursiveParameter
  (candidatePrimitivePhysicalBudgetExponent s 1) backendBudget

include hD hF in

theorem OrdinaryLongPhysicalTerminalData.conclusion_of_bounds
    (packet : P.OrdinaryLongPhysicalTerminalData Mmodel ω hD ν hF hφ p0 nGenerators
      initialLong scheduleExponent Cprimitive x separation)
    (hseparation : separation = Real.exp (candidatePrimitiveFreezingCutoff s 1 backendBudget))
    (hσ1 : ∀ j, σ j ≤ 1)
    (Hchart : Fin m → ℝ) (hHchart : ∀ j, 0 ≤ Hchart j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm v‖ ≤ Hchart j * ‖v‖)
    (hsmall : ∀ j, Hchart j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hweight : ∀ y, ‖weight y‖ ≤ Real.exp p0)
    (hscore : Real.exp (-p0) ≤ scoreThreshold)
    (hmass : Real.exp (-p0) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget affineBudget + 3) ^ 3)) * massThreshold)
    (hξ1 : ξ ≤ 1) (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p0)
    (hLip : ∀ y, letI := D.metricSpace; LipschitzWith ℓ (observable y))
    (hpositive : ∀ y z, (observable y z).im = 0 ∧
      0 ≤ (observable y z).re ∧ (observable y z).re ≤ 1)
    {e : ℕ}
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p0 + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ y ∈ integerBox N, ∃ i, ∀ z,
          ‖observable y z - observable (centers i).val z‖ ≤ accuracy)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := Deck) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      recursiveBudget outputCost)
    (houtput : recursiveBudget ≤ outputCost) :
    Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  have hD' := hD
  have hF' := hF
  have hmodel := packet.model_filtration
  cases hmodel
  exact P.conclusion_of_nativeCommonPhysicalTerminal_degreeRule Mmodel φ hφ packet.W
    Mmodel.basis ν hF' scheduleExponent Cprimitive x p0
    packet.nonnegative packet.source_geometry packet.marked_geometry packet.marked_basis_height
    packet.mark_height ω hD' packet.generators packet.graded packet.span
    (by simpa only [Fintype.card_fin] using packet.generator_count)
    packet.generator_height packet.variable_count packet.q packet.denominator packet.q_bound
    packet.denominator_pos packet.denominator_bound packet.cost_bound initialLong packet.short
    packet.zero_factors hσ1 Hchart hHchart hchart hsmall hpoly hweight hscore hmass
    packet.surjective hξ1 ℓ hℓ hLip hpositive (fun i j => packet.mark_height j i)
    packet.top_kernel hnet outputCost lowerIH houtput
    (by simpa only [hseparation] using packet.terminal)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidatePrimitiveFrontDescentData
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M t f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrimitiveFrontQuotientData

variable {FmarkNative P} {p : ℝ} {e : ℕ} {source : A.DegreeSourceProfile s p e}
    (data : P.PrimitiveFrontQuotientData FmarkNative source)

theorem factorFamily_sourceChart_eq (hp : 0 ≤ p) :
    (data.factorFamily hp).sourceChart = data.front.problem.precenterChart data.front.prep.positive_mass :=
  data.sourceChart_eq

theorem factorFamily_correlation_bound (hp : 0 ≤ p) :
    ∀ a ∈ data.retained, ∀ k, Real.exp (-source.front.frontCorrelationLoss) ≤
      ‖(data.factorFamily hp).correlation a k‖ := data.correlation

theorem factorFamily_path_eq (hp : 0 ≤ p) :
    ∀ a ∈ data.retained, ((data.factorFamily hp).sourceChart a).path = a := data.path_eq

theorem factorFamily_center_eq (hp : 0 ≤ p) :
    ∀ a, ((data.factorFamily hp).sourceChart a).centerLift = P.centerLift := data.center_eq

theorem factorFamily_score (hp : 0 ≤ p) :
    ∀ a ∈ data.retained, Real.exp (-positiveKernelPreparationParameter (2 * p)) ≤
      ((data.factorFamily hp).sourceCandidate a).score
        (fun x => (data.front.prep.selected.tests x).observable) weight := data.score

theorem frozen_side (a : A.Path) (i : {i // ¬data.front.keep i}) :
    (A.sides i.val : ℝ) ≤ Real.exp cost := by
  have hkeep : (data.front.problem.precenterChart data.front.prep.positive_mass a).keep =
      data.front.keep := data.front.problem.precenterChart_keep
        data.front.prep.positive_mass data.front.keep data.front.problem_keep a
  exact data.front.problem.precenterChart_frozen data.front.prep.positive_mass a
    ⟨i.val, by rw [hkeep]; exact i.property⟩

include data in
theorem mark_geometry_bound (hp : 0 ≤ p) :
    FmarkNative.GeometryComplexityLE source.front.geometryBudget :=
  data.mark_geometry.mono FmarkNative (source.front.factorGeometryBudget hp).geometry_input

theorem quotient_geometry_bound (hp : 0 ≤ p) :
    data.quotient.GeometryComplexityLE source.front.geometryBudget :=
  data.quotient_geometry.mono data.quotient (source.front.factorGeometryBudget hp).geometry_descent

theorem factorFamily_quotient_filtration (hp : 0 ≤ p) :
    data.quotient.filtration = D.filtration.pivotQuotientFiltration φ (data.factorFamily hp).η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList :=
  data.quotient_filtration

end PrimitiveFrontQuotientData
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {f : ℕ} {FmarkNative : RationalFilteredNilmanifold M t f} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.PrimitiveFrontQuotientData

variable {cost massThreshold scoreThreshold p : ℝ} {e : ℕ}
    {P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked
      observable weight cost massThreshold scoreThreshold}
    {source : A.DegreeSourceProfile s p e}
    (data : P.PrimitiveFrontQuotientData FmarkNative source)

section QuotientTopology

variable [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))]
    [T2Space (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))]

structure DescendedFamily where
  tests : (X → ℤ) → data.quotient.Niltest (fullTaggedVariableWeight (X := X) J)
  unit : ∀ x, (tests x).UnitIntervalValued
  norm1 : ∀ x y, ‖(tests x).observable y‖ ≤ 1
  complexity : ∀ x, (tests x).ComplexityLE
    ((source.front.familyParameter + 2) ^
      RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)
  lipschitz : ∀ x, letI := data.quotient.metricSpace
    LipschitzWith
      ⟨Real.exp ((source.front.familyParameter + 2) ^
        RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s), Real.exp_nonneg _⟩
      (tests x).observable
  recovery : ∀ x (g : D.RealGroup), (tests x).observable (QuotientGroup.mk
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := data.quotient.filtration.lowerCentralSeries_eq_bot)
      (lieQuotientMap data.front.prep.nativeQuotientIdeal) g)) =
      (data.front.prep.selected.tests x).observable (QuotientGroup.mk g)
  contract_original : ∀ x y η, (∀ z, ‖observable x z - observable y z‖ ≤ η) →
    ∀ z, ‖(tests x).observable z - (tests y).observable z‖ ≤ η
  member_nets : ∀ entropy : ℝ → ℝ,
    (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ, (count : ℝ) ≤ entropy η ∧
      ∃ rep : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (rep i).val y‖ ≤ η) →
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ, (count : ℝ) ≤ entropy η ∧
      ∃ rep : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖(tests x).observable y - (tests (rep i).val).observable y‖ ≤ η

end QuotientTopology

end AllocatedExternalCandidateProblem.PrimitiveFrontQuotientData
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPrimitiveFrontInitialLong
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M t f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrimitiveFrontQuotientData

variable {FmarkNative P} {p : ℝ} {e : ℕ} {source : A.DegreeSourceProfile s p e}
    (data : P.PrimitiveFrontQuotientData FmarkNative source)

theorem retained_nonempty : data.retained.Nonempty := by
  by_contra h
  have hzero : A.law.mass data.retained = 0 := by
    rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp [FiniteProbabilityWeights.mass]
  linarith only [data.mass_pos, hzero]

theorem initialLong_excluded_bound (initialShort : ℝ) :
    ∀ i, ¬(data.front.keep i ∧ Real.exp initialShort ≤ (A.sides i : ℝ)) →
      (A.sides i : ℝ) ≤ Real.exp (max cost initialShort) := by
  obtain ⟨a, _⟩ := data.retained_nonempty
  exact allocatedCandidate_initialLong_excluded_bound (fun i => (A.sides i : ℝ))
    data.front.keep (fun i hi => data.frozen_side a ⟨i, hi⟩)

end PrimitiveFrontQuotientData
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeOrdinaryTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type} {Pivot : Type} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (keepLong : LayerSamplerVariables G I n B → Prop)
    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

variable {α : Type} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))
    (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i}))
    (js : List Pivot)
    {dQ : ℕ}
    (Q : RationalFilteredNilmanifold (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
    (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
    (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
        observable x (QuotientGroup.mk g))
    (adapted : (optionProduct Q (fun j => (F.native j).model)).AdaptedModelData)

def ActualAdaptedPivotQuotientLongPhysicalTerminal
    {κ : Type} [Fintype κ]
    (bMark : Basis κ ℚ (∀ i : Option Pivot, optionLieSpace LM (fun j => (F.native j).L) i))
    (ν : κ → ℕ)
    (hMark : ∀ k, (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => ((fun j => (F.native j).model) j).filtration))).layer k = Submodule.span ℚ (bMark '' {i | k ≤ ν i}))
    (hmarkΦ : ∀ k, ∀ z ∈ (adapted.model.filtration).layer k, (optionMarkedLieMap (L := fun j => (F.native j).L) (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker)) z ∈ (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => ((fun j => (F.native j).model) j).filtration))).layer k)
    (scheduleExponent Cprimitive : ℕ) (x separation qVertical qCommon pProj : ℝ) : Prop :=
  ∃ (retained : Finset A.Path) (hsub : retained ⊆ H)
    (hmass : Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
      ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H ≤ A.law.mass retained),
    0 < A.law.mass retained ∧
    ∃ (theta : ∀ j, (F.native j).L →ₗ[ℚ] ℚ)
      (W : LieSubalgebra ℚ (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
      (v : Fin (Fintype.card α) →
        (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
      (den : ℕ),
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule
        ((optionProduct D (fun j => (F.native j).model)).filtration.associatedGradedBasis e ω hF)
        ω W.toSubmodule ∧
      (∀ i k, rationalLogHeight
        (((optionProduct D (fun j => (F.native j).model)).filtration.associatedGradedBasis
          e ω hF).repr (v i) k) ≤ qCommon) ∧
      (∀ j x, x ∈ (optionProduct D (fun j => (F.native j).model)).filtration.realGradedRefiltrationLayer W s →
        realifyFunctional ((pairFrequency (F.η j) (theta j)).comp
          (optionPairProjection j).toLinearMap) x = 0) ∧
      0 < den ∧ (den : ℝ) ≤ Real.exp qCommon ∧
      let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
        scoreThreshold hscore retained hsub hmass
      let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery adapted
      let F₀ := (optionProduct D (fun j => (F.native j).model)).filtration
      let FQ := adapted.model.filtration
      let ψ := optionMarkedLieMap (L := fun j => (F.native j).L)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))
      let hψ := D.optionQuotientMap_mem_layer
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)
      let V := W.map (F₀.associatedGradedMap FQ ψ hψ)
      let vQ := F₀.gradedImageSpanningFamily FQ ψ hψ v
      ∃ denQ : ℕ, 0 < denQ ∧ (denQ : ℝ) ≤ Real.exp ((pProj + 2) ^ 4) ∧ den ∣ denQ ∧
        Submodule.span ℚ (Set.range vQ) = V.toSubmodule ∧
        BasisGradedSubmodule
          (FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers)
          adapted.weight V.toSubmodule ∧
        (∀ a i, rationalLogHeight
          ((FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers).repr
            (vQ a) i) ≤ (pProj + 2) ^ 4) ∧
        (∀ z : target.productive,
          FQ.HasCommonRefilteredOrbitFactors adapted.model.basis adapted.weight adapted.model_layers
            (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) ((pProj + 2) ^ 3 + qCommon) denQ V
            (FQ.weightedAdaptedRealChartHom
              (fun _ : {i // keep i} => 1) (fun _ : {i // keepLong i} => 1)
              ((target.chart z).axisPolynomial keepLong (fun _ => 0))
              ((target.chart z).axisPolynomial_support keepLong (fun _ => 0))
              (FQ.realification.polynomialOrbitCoordinates (fun _ => 1)
                (target.candidate z).orbit))) ∧
        (∀ x ∈ FQ.gradedRefiltrationLayer V s,
          optionMarkedLieMap (L := fun j => (F.native j).L)
            (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker) x = 0 →
          x = 0) ∧
        (∀ (Gmark : NilpotentLieFiltration
            (∀ i : Option Pivot, optionLieSpace LM (fun j => (F.native j).L) i) s)
          (hmarked : ∀ k, ∀ x ∈ FQ.layer k,
            optionMarkedLieMap (L := fun j => (F.native j).L)
              (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker) x ∈
                Gmark.layer k),
          ∀ a ∈ V,
            basisGradeProjection
              (FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers)
              adapted.weight s a = a →
            FQ.associatedGradedMap Gmark
              (optionMarkedLieMap (L := fun j => (F.native j).L)
                (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker))
              hmarked a = 0 → a = 0) ∧
        target.NativeCommonPhysicalTerminal bMark ν hMark hmarkΦ V
          scheduleExponent Cprimitive x separation

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type} {Pivot : Type} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {dMark : ℕ} {Mmark : RationalFilteredNilmanifold LM s dMark} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Mmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Mmark.filtration φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (keepLong : LayerSamplerVariables G I n B → Prop)
    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

variable (js : List Pivot) {dQ : ℕ}
    (Q : RationalFilteredNilmanifold
      (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
    (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
    (hker : ∀ z ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ z = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
        observable x (QuotientGroup.mk g))
    {jointGeo adaptedBudget markInput markBudget : ℝ}
    (geometry : (optionProduct D (fun j => (F.native j).model)).AdaptedMapGeometryData
      (optionProduct Q (fun j => (F.native j).model))
      (optionMarkedLieMap (L := fun j => (F.native j).L)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))) jointGeo adaptedBudget)
    (markGeometry : (optionProduct Q (fun j => (F.native j).model)).FixedSourceAdaptedMarkGeometryData
      (optionProduct Mmark (fun j => (F.native j).model)) geometry.target
      (optionMarkedLieMap (L := fun j => (F.native j).L)
        (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker))
      markInput markBudget)

theorem ordinaryData_of_actualAdaptedPivotQuotientLongPhysicalTerminal
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ Mmark.filtration.layer k)
    (hsurj : ∀ k, ∀ y ∈ Mmark.filtration.layer k,
      ∃ z ∈ D.filtration.layer k, φ z = y)
    {scheduleExponent Cprimitive : ℕ} {x separation qVertical qCommon pProj p0 : ℝ}
    (hp0 : 0 ≤ p0) (hgeometry : adaptedBudget ≤ p0) (hmark : markBudget ≤ p0)
    (hgenerator : jointGeo ≤ p0)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p0)
    (hprojection : (pProj + 2) ^ 4 ≤ p0)
    (hfactor : (pProj + 2) ^ 3 + qCommon ≤ p0)
    (hcost : cost ≤ p0)
    (hshort : ∀ i, ¬keepLong i → (A.sides i : ℝ) ≤ Real.exp p0) :
    let hmarkΦ := D.nativeOptionFixedSourceQuotientMark_mem_layer Mmark
      (D.filtration.pivotAnnihilatorIdeal φ F.η js)
      (by rw [D.filtration.terminal]; exact bot_le) Q hQ
      (fun j => (F.native j).model) φ hker hφ geometry.target
    F.ActualAdaptedPivotQuotientLongPhysicalTerminal keepLong H sourceCenter hpath hcenter hfrozen
      observable weight scoreThreshold hscore geometry.source.basis geometry.source.weight
      geometry.source.layers js Q hQ hker descended hrecovery geometry.target
      markGeometry.target.basis markGeometry.target.weight
      (Mmark.optionAdaptedModel_layers (fun j => (F.native j).model) markGeometry.target) hmarkΦ
      scheduleExponent Cprimitive x separation qVertical qCommon pProj →
    ∃ (retained : Finset A.Path) (hsub : retained ⊆ H)
      (hmass : Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
        ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H ≤ A.law.mass retained),
      0 < A.law.mass retained ∧
      let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
        scoreThreshold hscore retained hsub hmass
      let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery geometry.target
      Nonempty (AllocatedExternalCandidateProblem.OrdinaryLongPhysicalTerminalData
        (D := geometry.target.model)
        (Fmark := NilpotentLieFiltration.pi
          (optionFiltrations Mmark.filtration (fun j => (F.native j).model.filtration)))
        (φ := optionMarkedLieMap (L := fun j => (F.native j).L)
          (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker))
        target markGeometry.target.model
        geometry.target.weight geometry.target.model_layers
        markGeometry.target.weight
        (Mmark.optionAdaptedModel_layers (fun j => (F.native j).model) markGeometry.target) hmarkΦ p0
        (Fintype.card (Fin (finrank ℚ
          (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))))
        keepLong scheduleExponent Cprimitive x separation) := by
  intro hmarkΦ hproduced
  obtain ⟨retained, hsub, hmass, hpos, theta, W, v, den, hv, hW, hvH, hzero,
    hden, hdenBound, denQ, hdenQ, hdenQBound, hdiv, hvQ, hWQ, hvQH, hfactorQ,
    htop, hgradedTop, hterminal⟩ := hproduced
  obtain ⟨hsourceGeo, hmarkedGeo, hforward, hentries, hnativeEntries, hcount, _, _⟩ :=
    geometry.ordinaryResetGeometry markGeometry hp0 hgeometry hmark hgenerator
  refine ⟨retained, hsub, hmass, hpos, ?_⟩
  refine ⟨{
    model_filtration := by
      change NilpotentLieFiltration.pi
        (fun i => (optionFactors Mmark (fun j => (F.native j).model) i).filtration) = _
      congr 1
      funext i
      cases i <;> rfl
    nonnegative := hp0
    source_geometry := hsourceGeo
    marked_geometry := hmarkedGeo
    marked_basis_height := ?_
    mark_height := hnativeEntries
    generator_count := ?_
    variable_count := hvariables
    cost_bound := hcost
    short := hshort
    W := _
    generators := _
    span := hvQ
    graded := hWQ
    generator_height := fun a i => (hvQH a i).trans hprojection
    q := (pProj + 2) ^ 3 + qCommon
    q_bound := hfactor
    denominator := denQ
    denominator_pos := hdenQ
    denominator_bound := hdenQBound.trans (Real.exp_le_exp.mpr hprojection)
    zero_factors := hfactorQ
    top_kernel := htop
    surjective := ?_
    terminal := hterminal
  }⟩
  · intro i j
    exact hforward j i
  · exact hcount
  · exact D.nativeOptionFixedSourceQuotientMark_layer_surjective Mmark
      (D.filtration.pivotAnnihilatorIdeal φ F.η js)
      (by rw [D.filtration.terminal]; exact bot_le) Q hQ
      (fun j => (F.native j).model) φ hker geometry.target hsurj

end AllocatedExternalCandidateSpatialNativeFamily
end
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidatePreparedPhysicalConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

section PrimitiveResult
variable {s : ℕ}
variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {d : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M (s + 1) f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile (s + 1) p e)
    (data : P₀.PrimitiveFrontQuotientData FmarkNative source)

def PrimitiveFrontQuotientCanonicalPhysicalTerminalAt (Cgeometry C Cbasis K T : ℕ)
    (hp : 0 ≤ p)
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ FmarkNative.filtration.layer k) : Prop :=
      let F := data.factorFamily hp
      let pFactor := source.front.factorBudget
      let pGeometry := source.front.geometryBudget
      let qVertical := 3 * source.front.familyParameter + 1
      let pGeo := (pGeometry + 2) ^ 2
      let jointGeo := (pGeometry + 3) ^ 2
      let adaptedBudget := (jointGeo + 2) ^ Cgeometry
      let bnd := adaptedBudget + (pGeo + 3) ^ 5 + pGeo + jointGeo + pGeometry + pFactor + 2
      let localCost := allocatedFrozenTaggedPairBudget (s + 1) C Cbasis pGeo pFactor
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let stageInput := jointCost + (jointCost + K) ^ K
      let initialShortLog := max ((pFactor + 2 + C) ^ C + 7 * pFactor + 22)
        ((stageInput + 2) ^ T)
      let keepLong := fun i => data.front.keep i ∧ Real.exp initialShortLog ≤ (A.sides i : ℝ)
      let qCommon := (stageInput + 2) ^ T + (((stageInput + 2) ^ 2 + 2) ^ 63 + 1) + stageInput + 1
      let pProj := max qCommon 0 + adaptedBudget + 1
      let markInput := nativeOptionFixedSourceQuotientMarkInput pGeometry
      let markBudget := (markInput + 2) ^ nativeOptionFixedSourceMarkExponent.{0, 0}
      adaptedBudget ≤ source.inner.physicalBudget ∧
      markBudget ≤ source.inner.physicalBudget ∧
      jointGeo ≤ source.inner.physicalBudget ∧
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ source.inner.physicalBudget ∧
      (pProj + 2) ^ 4 ≤ source.inner.physicalBudget ∧
      (pProj + 2) ^ 3 + qCommon ≤ source.inner.physicalBudget ∧
      cost ≤ source.inner.physicalBudget ∧
      (∀ i, ¬keepLong i → (A.sides i : ℝ) ≤ Real.exp source.inner.physicalBudget) ∧
      Real.exp (-source.inner.physicalBudget) ≤
        Real.exp (-AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)) ∧
      Real.exp (-source.inner.physicalBudget) ≤
        Real.exp (-(verticalDecompositionBudget qVertical *
          (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code) : ℝ) +
          ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass data.retained ∧
      pGeometry ≤ source.inner.physicalBudget ∧
      source.front.familyParameter ≤ source.inner.physicalBudget ∧
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
        IsModuleTopology.topologicalAddGroup ℝ _
      letI := realification_moduleTopology_t2 data.quotient.basis
      ∃ desc : data.DescendedFamily,
      ∃ geometry : (optionProduct D (fun j => (F.native j).model)).AdaptedMapGeometryData
          (optionProduct data.quotient (fun j => (F.native j).model))
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (lieQuotientMap data.front.prep.nativeQuotientIdeal)) jointGeo adaptedBudget,
      ∃ markGeometry : (optionProduct data.quotient (fun j => (F.native j).model)).FixedSourceAdaptedMarkGeometryData
          (optionProduct FmarkNative (fun j => (F.native j).model)) geometry.target
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (quotientInducedMark data.front.prep.nativeQuotientIdeal φ data.ideal_killed))
          markInput markBudget,
      let hmarkΦ := D.nativeOptionFixedSourceQuotientMark_mem_layer FmarkNative
        data.front.prep.nativeQuotientIdeal data.front.prep.nativeQuotientIdeal_terminal
        data.quotient data.quotient_filtration (fun j => (F.native j).model)
        φ data.ideal_killed hφ geometry.target
      let hMark : ∀ k, (NilpotentLieFiltration.pi (optionFiltrations FmarkNative.filtration
          (fun j => (F.native j).model.filtration))).layer k =
          Submodule.span ℚ (markGeometry.target.basis '' {i | k ≤ markGeometry.target.weight i}) := by
        intro k
        exact FmarkNative.optionAdaptedModel_layers (fun j => (F.native j).model) markGeometry.target k
      F.ActualAdaptedPivotQuotientLongPhysicalTerminal keepLong data.retained P₀.centerLift
        (data.factorFamily_path_eq hp) (fun a _ => data.factorFamily_center_eq hp a)
        (fun a _ i => data.frozen_side a i)
        (fun x => (data.front.prep.selected.tests x).observable) weight
        (Real.exp (-AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)))
        (data.factorFamily_score hp) geometry.source.basis geometry.source.weight
        geometry.source.layers
        (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList
        data.quotient (data.factorFamily_quotient_filtration hp) data.ideal_killed
        (fun x => (desc.tests x).observable) desc.recovery geometry.target
        markGeometry.target.basis markGeometry.target.weight hMark hmarkΦ
        source.inner.scheduleExponent source.inner.Cprimitive source.inner.x source.inner.separation qVertical qCommon pProj

end PrimitiveResult

end
end Erdos3.VectorPolynomial

end

end OAI
end


