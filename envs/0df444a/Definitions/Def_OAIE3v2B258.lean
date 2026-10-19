-- Prove2me | Definitions.Def_OAIE3v2B258
-- name    : OAIE3v2B258
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:09:12.266247+00:00
-- url     : https://prove2.me/theorems/8fc38051-f37e-4672-b26b-e2e030337d83
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 264 of 311
-- statement:
--   Definitions bundle 264 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B248`, `OAIE3v2B249`, `OAIE3v2B251`, `OAIE3v2B302` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidateExponentialFreezingBudget.lean`, `Dynamics/AllocatedExternalCandidateResetSuccessor.lean`, `Estimates/AllocatedCandidateGeneratedFastTerminal.lean`, `Estimates/AllocatedExternalCandidateCoveredFamilySuccessor.lean`, `Estimates/AllocatedExternalCandidateGeneratedFreezingSuccessor.lean`, `Estimates/PreparedCenteredDeterminingSlots.lean`, `Estimates/PreparedDilatedDeterminingSlots.lean`, `Estimates/PreparedRelativeFinalPower.lean`, `Estimates/RelativePatchPositivePowerInduction.lean`, `Geometry/ActualFixedSpatialRetainedModulusBudget.lean`, `Geometry/AllocatedExternalCandidateRefilteredSupportedStep.lean`, `Lattices/ActualFixedSpatialGoodPrimeDeletion.lean`, `Polynomial/AllocatedZeroLayerDegreeScalarConclusion.lean`, `Sampling/PreparedEarlyLateSamplerGeometry.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B248
import Definitions.Def_OAIE3v2B249
import Definitions.Def_OAIE3v2B251
import Definitions.Def_OAIE3v2B302

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateExponentialFreezingBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def budgetRefinement {cost' mass' score' : ℝ}
    (hcost : cost ≤ cost') (hmass : mass' ≤ massThreshold)
    (hscore : score' ≤ scoreThreshold) : P.Refinement cost' mass' score' where
  retained := P.productive
  subset := fun _ hz => hz
  mass := hmass.trans P.mass
  cost_le := hcost
  step z := (P.chart z).step
  step_pos z := (P.chart z).step_pos
  slice z := (P.chart z).slice
  dense z := (P.chart z).dense.mono hcost
  inside _ := Finset.Subset.refl _
  scoreLower z := hscore.trans (P.score z)

@[simp] theorem budgetRefinement_productive {cost' mass' score' : ℝ}
    (hcost : cost ≤ cost') (hmass : mass' ≤ massThreshold)
    (hscore : score' ≤ scoreThreshold) :
    (P.budgetRefinement hcost hmass hscore).problem.productive = P.productive := rfl

@[simp] theorem budgetRefinement_chartValues {cost' mass' score' : ℝ}
    (hcost : cost ≤ cost') (hmass : mass' ≤ massThreshold)
    (hscore : score' ≤ scoreThreshold) (z : P.productive)
    (u : (P.chart z).Variables → ℤ) :
    ((P.budgetRefinement hcost hmass hscore).problem.chart z).chartValues u =
      (P.chart z).chartValues u := rfl

@[simp] theorem budgetRefinement_physical {cost' mass' score' : ℝ}
    (hcost : cost ≤ cost') (hmass : mass' ≤ massThreshold)
    (hscore : score' ≤ scoreThreshold) (z : P.productive)
    (u : (P.chart z).Variables → ℤ) :
    ((P.budgetRefinement hcost hmass hscore).problem.chart z).physical u =
      (P.chart z).physical u := rfl

@[simp] theorem budgetRefinement_candidate_orbit {cost' mass' score' : ℝ}
    (hcost : cost ≤ cost') (hmass : mass' ≤ massThreshold)
    (hscore : score' ≤ scoreThreshold) (z : P.productive) :
    ((P.budgetRefinement hcost hmass hscore).problem.candidate z).orbit =
      (P.candidate z).orbit := rfl

namespace Conclusion

variable {P} {outputCost outputMass outputScore : ℝ}
    (out : P.Conclusion outputCost outputMass outputScore)

noncomputable def mono {cost' mass' score' : ℝ}
    (hcost : outputCost ≤ cost') (hmass : mass' ≤ outputMass)
    (hscore : score' ≤ outputScore) : P.Conclusion cost' mass' score' where
  ambient := out.ambient
  marked := out.marked
  retained := out.retained
  subset := out.subset
  mass := hmass.trans out.mass
  step := out.step
  step_pos := out.step_pos
  slice := out.slice
  dense z := (out.dense z).mono hcost
  inside := out.inside
  score z := hscore.trans (out.score z)

@[simp] theorem mono_ambient {cost' mass' score' : ℝ}
    (hcost : outputCost ≤ cost') (hmass : mass' ≤ outputMass)
    (hscore : score' ≤ outputScore) :
    (out.mono hcost hmass hscore).ambient = out.ambient := rfl

@[simp] theorem mono_retained {cost' mass' score' : ℝ}
    (hcost : outputCost ≤ cost') (hmass : mass' ≤ outputMass)
    (hscore : score' ≤ outputScore) :
    (out.mono hcost hmass hscore).retained = out.retained := rfl

@[simp] theorem mono_slice {cost' mass' score' : ℝ}
    (hcost : outputCost ≤ cost') (hmass : mass' ≤ outputMass)
    (hscore : score' ≤ outputScore) (z : out.retained) :
    (out.mono hcost hmass hscore).slice z = out.slice z := rfl

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateRefilteredSupportedStep
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

theorem exists_marked_topQuotientOrbit_lift_externalFamily_on
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace E.Space]
    {A : Type*} (K : ℝ≥0) (observable : A → D.RealGroup → ℂ) (allowed : A → Prop)
    (hrecovery : ∀ a, allowed a → ∀ source,
      positiveImageSlice (D.markedTopQuotientDiagram E φ Q) K
        (observable a) (D.markedTopQuotientDiagram E φ Q source).2
          (D.markedTopQuotientDiagram E φ Q source).1 = observable a source)
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (heq : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      ∀ a, allowed a → ∀ z : σ → ℝ,
        positiveImageSlice (D.markedTopQuotientDiagram E φ Q) K (observable a)
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitRealEval w z marked))
          (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitRealEval w z q)) =
        observable a (D.filtration.realification.polynomialOrbitRealEval w z g) := by
  obtain ⟨g, hg, hm, hdiagram⟩ :=
    D.exists_marked_topQuotientOrbit_lift_diagram E φ hφ Q hQ QF hQF hsurj q marked heq
  refine ⟨g, hg, hm, ?_⟩
  intro a ha z
  have h := hrecovery a ha (D.filtration.realification.polynomialOrbitRealEval w z g)
  rw [hdiagram z] at h
  exact h

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateResetSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    {c : Basis κ ℚ M} {ν : κ → ℕ}
    {hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i})}
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    (slow : ℝ) (denominator : ℕ)

structure AllocatedExternalGlobalNativeResetFamily where
  localLeft : (P.withKeep keep hkeep).productive →
    (D.filtration.realification.adaptedPolynomialFiltration (fun _ : {i // keep i} => 1)).Group
  localMiddle : (P.withKeep keep hkeep).productive →
    (D.filtration.realification.adaptedPolynomialFiltration (fun _ : {i // keep i} => 1)).Group
  localRight : (P.withKeep keep hkeep).productive →
    (D.filtration.realification.adaptedPolynomialFiltration (fun _ : {i // keep i} => 1)).Group
  native : (P.withKeep keep hkeep).productive →
    (D.filtration.gradedRefiltration W).realification.PolynomialOrbit (fun _ : {i // keep i} => 1)
  source_factor : ∀ z, localLeft z * localMiddle z * localRight z =
    D.filtration.realification.polynomialOrbitCoordinates _ ((P.withKeep keep hkeep).candidate z).orbit
  projection_left : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
    (fun _ : {i // keep i} => 1) (localLeft z) =
    Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
      (fun _ : {i // keep i} => 1)
      (integerSampledRealChart ((P.withKeep keep hkeep).chart z).integerChart)
      ((P.withKeep keep hkeep).chart z).integerChart_support factors.left
  projection_middle : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
    (fun _ : {i // keep i} => 1) (localMiddle z) =
    Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
      (fun _ : {i // keep i} => 1)
      (integerSampledRealChart ((P.withKeep keep hkeep).chart z).integerChart)
      ((P.withKeep keep hkeep).chart z).integerChart_support factors.middle
  projection_right : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
    (fun _ : {i // keep i} => 1) (localRight z) =
    Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
      (fun _ : {i // keep i} => 1)
      (integerSampledRealChart ((P.withKeep keep hkeep).chart z).integerChart)
      ((P.withKeep keep hkeep).chart z).integerChart_support factors.right
  slow_left : ∀ z, D.filtration.PolynomialSlowBound D.basis
    (fun _ : {i // keep i} => 1) (fun i => (A.sides i.val : ℝ)) slow (localLeft z)
  grid_right : ∀ z, D.filtration.PolynomialRationalGrid D.basis
    (fun _ : {i // keep i} => 1) denominator (localRight z)
  native_log : ∀ z, map
    (realLieHomToRat (realificationLieHom
      (D.filtration.gradedRefiltrationSubalgebra W).incl)).toLinearMap (native z).log =
    ((localMiddle z).coord : VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L))

namespace AllocatedExternalGlobalNativeResetFamily

variable {Fmark φ hφ P keep hkeep W factors slow denominator}

variable (reset : AllocatedExternalGlobalNativeResetFamily
    Fmark φ hφ P keep hkeep W factors slow denominator)

variable {nD nF : ℕ}
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

noncomputable def candidate (z : (P.withKeep keep hkeep).productive) :
    AllocatedExternalLocalCandidate ((P.withKeep keep hkeep).chart z) Dref Fref.filtration
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (factors.markedMiddleOn Fref hFref) :=
  AllocatedExternalLocalCandidate.ofGlobalMarkedNativeMiddle
    ((P.withKeep keep hkeep).chart z) D Fmark φ hφ W Dref hDref Fref hFref factors
    (reset.localMiddle z) (reset.native z) (reset.projection_middle z) (reset.native_log z)

@[simp] theorem candidate_orbit_log (z : (P.withKeep keep hkeep).productive) :
    (reset.candidate Dref hDref Fref hFref z).orbit.log = (reset.native z).log := rfl

end AllocatedExternalGlobalNativeResetFamily
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredDeterminingSlots
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
variable (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)

noncomputable def sortedDeterminingPolynomial
    (i : Fin (Fintype.card (Σ j, E j))) : MvPolynomial X ℝ :=
  L.determiningPolynomial bW hmem (sortedLayerCoordinateEquiv E i)

noncomputable def sortedDeterminingMatrix {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n)
    (a : Fin (Fintype.card (Σ j, E j))) : ℤ :=
  L.determiningMatrix bW (e i) (sortedLayerCoordinateEquiv E a)

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
variable (c : ∀ j, (L j).space)

noncomputable def determiningCenterCoordinate (a : L.DeterminingIndex E) : ℝ :=
  ((L a.1).integralCoordinateBasis (bW a.1)).repr (c a.1) a.2

noncomputable def sortedDeterminingCenter
    (a : Fin (Fintype.card (Σ j, E j))) : ℝ :=
  L.determiningCenterCoordinate bW c (sortedLayerCoordinateEquiv E a)

variable (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)

noncomputable def centeredDeterminingPolynomial
    (a : Fin (Fintype.card (Σ j, E j))) : MvPolynomial X ℝ :=
  L.sortedDeterminingPolynomial bW hmem a - MvPolynomial.C (L.sortedDeterminingCenter bW c a)

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateGeneratedFastTerminal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

theorem ordinarySymbolSubtype_card_le {σ ι : Type*}
    (keep : σ → Prop) (ω : ι → ℕ)
    [Fintype (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)] :
    Fintype.card (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω) ≤
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) := by
  let embed : SymbolBasisIndex (fun _ : {i // keep i} => 1) ω →
      SymbolBasisIndex (fun _ : σ => 1) ω := fun z =>
    ⟨(z.val.1.mapDomain Subtype.val, z.val.2), by
      simpa only [← Finsupp.degree_eq_weight_one, Finsupp.degree_mapDomain] using z.property⟩
  apply Fintype.card_le_of_injective embed
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · exact Finsupp.mapDomain_injective Subtype.val_injective
      (congrArg (fun z => z.val.1) hxy)
  · exact congrArg (fun z => z.val.2) hxy

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedEarlyLateSamplerGeometry
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.basisAxisScale_le_exp
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
      (euclideanSubspace (L j).space)ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (L j).space))
    (hp : 0 ≤ p) (hRp : (R : ℝ) ≤ Real.exp p)
    (hcoord : ∀ j, (Fintype.card (L j).Coord : ℝ) ≤ p)
    (hcols : ∀ j, (Fintype.card (L j).Column : ℝ) ≤ p)
    (hrows : ∀ j, (Fintype.card (L j).Row : ℝ) ≤ p) :
    ∀ j i, (basisAxisScale (b j) i : ℝ) ≤
      Real.exp ((p + 2) ^ preparedIntegralBasisExponent m) := by
  let q := (p + 2) ^ budgetDepthExponent 38 m
  have hpq : p ≤ q := le_power_budget hp (preparationExponent_pos m)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hheight (j : Fin m) :
      (preparationHeight p (m - 1 - j.val) : ℝ) ≤ Real.exp q :=
    (Nat.cast_le.mpr (preparationHeight_mono hp (by omega : m - 1 - j.val ≤ m))).trans
      (preparationHeight_le_exp p m)
  have hRpq : (R : ℝ) ≤ Real.exp q := hRp.trans (Real.exp_le_exp.mpr hpq)
  intro j i
  have haxis := (L j).basisAxisScale_le_exp (hL j) (preparationHeight_pos hp _)
    (b j) (hb j) hq ((hcoord j).trans hpq) ((hcols j).trans hpq)
    ((hrows j).trans hpq) (hheight j) hRpq i
  apply haxis.trans (Real.exp_le_exp.mpr ?_)
  calc
    (q + 2) ^ 28 ≤ (q + 2) ^ 124 :=
      pow_le_pow_right₀ (by linarith : 1 ≤ q + 2) (by decide)
    _ ≤ (p + 2) ^ preparedIntegralBasisExponent m :=
      shifted_power_budget_le hp (budgetDepthExponent 38 m) 124

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction
namespace OAI

section

namespace Erdos3
open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

def PreparedRelativePatchPowerPassage
    (s n₀ stage : ℕ) (discount : ℝ)
    (requiredPower precisionPower preparationPower passagePower : ℕ) : Prop :=
  ∀ (p a Λ : ℝ) (d₀ : ℕ), 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
    RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
    ∀ (nX : ℕ), 0 < nX → (nX : ℝ) ≤ p →
    ∀ (N : Fin nX → ℕ),
      (∀ i, Real.exp ((p + 2) ^ passagePower) ≤ (N i : ℝ)) →
    ∀ (f : (Fin nX → ℤ) → ℝ), (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
    ∀ (D E m : ℕ), 0 < D → 0 < m → m ≤ s →
    ∀ (oldPatch : PolynomialPatch (Fin nX) s (D + E))
      (F : oldPatch.LowestLayerModel m),
      (∀ i : Fin E, m < oldPatch.weight (i.natAdd D)) →
      relativePatchComplexity oldPatch ≤ p →
      relativePatchDistinctWeights oldPatch ≤ stage + 1 →
      Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch →
    ∀ (L : RankPreparationFamily (Fin nX) (Fin D) m),
      L.Sized D (m * D) →
      L.PreparedHeights ((p + 2) ^ preparationPower) (preparedRoundedRank p requiredPower) →
      (∑ j, (L j).rank) ≤ m * D →
      (∀ j, Fintype.card (L j).Coord ≤ preparationCoordinateCap m D (m * D)) →
      (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
        (preparedRoundedRank p requiredPower) (L j).space (L j).poly) →
    ∀ (ip : Fin D → MvPolynomial (Fin nX) ℤ) (c : Fin D → ℝ)
      (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ)),
      (∀ i, (ip i).totalDegree ≤ m) → DegreeLE (fun _ => 1) m err →
      ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
        L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err →
      (∀ x ∈ integerBox N, ∀ i,
        |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ precisionPower))) →
      RelativePatchSliceConclusion s N f ((1 - discount) ^ (stage + 2) * Λ)
        (d₀ + s * (D + E)) ((p + 2) ^ passagePower)

def RelativePatchFinPositivePowerRule
    (s n₀ stage : ℕ) (discount : ℝ) (power : ℕ) : Prop :=
  ∀ (p a Λ : ℝ) (d₀ : ℕ), 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
    RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
    ∀ (nX : ℕ), 0 < nX → (nX : ℝ) ≤ p →
    ∀ (N : Fin nX → ℕ), (∀ i, Real.exp ((p + 2) ^ power) ≤ (N i : ℝ)) →
    ∀ (f : (Fin nX → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
    ∀ (d : ℕ) (A : PolynomialPatch (Fin nX) s d), 0 < d →
      relativePatchComplexity A ≤ p → relativePatchDistinctWeights A ≤ stage + 1 →
      Real.exp (-p) ≤ relativePatchBoxScore N f a A →
      RelativePatchSliceConclusion s N f ((1 - discount) ^ (stage + 2) * Λ)
        (d₀ + s * d) ((p + 2) ^ power)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualFixedSpatialGoodPrimeDeletion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
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
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedReferencePrimeNeZero
attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedReferenceModulusNeZero
omit [Fintype Tsp] in
theorem referenceRetainedModulus_pos (cutoff : ℕ) :
    0 < path.referenceRetainedModulus cutoff := by
  apply Finset.prod_pos
  intro p _
  exact pow_pos (path.prime p.val p.property).pos _

omit [Fintype Tsp] in
theorem referenceRetainedModulus_dvd (cutoff : ℕ) :
    path.referenceRetainedModulus cutoff ∣ path.referenceModulus :=
  Finset.prod_dvd_prod_of_subset (path.referenceRetainedPrimes cutoff) Finset.univ
    (fun p : path.primes => p.val ^ path.exponent p.val) (Finset.subset_univ _)

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedModulusBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

namespace VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped NNReal Matrix

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
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] retainedLabelDecidableEq

omit [Fintype Tsp] in
theorem referenceRetainedCRTModulus_eq (cutoff : ℕ) :
    path.referenceRetainedCRTModulus cutoff = path.referenceRetainedModulus cutoff := by
  exact Finset.prod_coe_sort (path.referenceRetainedPrimes cutoff)
    (fun p : path.primes => p.val ^ path.exponent p.val)

omit [Fintype Tsp] in
theorem referenceRetainedCRTModulus_dvd (cutoff : ℕ) :
    path.referenceRetainedCRTModulus cutoff ∣ path.referenceModulus := by
  rw [path.referenceRetainedCRTModulus_eq]
  exact path.referenceRetainedModulus_dvd cutoff

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.smallReferencePrimeNeZero
local instance smallReferenceModulusNeZero (cutoff : ℕ) :
    NeZero (path.referenceRetainedCRTModulus cutoff) :=
  ⟨by rw [path.referenceRetainedCRTModulus_eq]; exact (path.referenceRetainedModulus_pos cutoff).ne'⟩

noncomputable def referenceRetainedCRTInputLaw (cutoff : ℕ) : FiniteProbabilityWeights
    (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
      ZMod (path.referenceRetainedCRTModulus cutoff)) :=
  crtPolynomialInputLaw (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
    (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
    (fun p : path.referenceRetainedPrimes cutoff => path.prescribed p.val.val)
    (primePower_crt_coprime (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
      (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
      (fun p => path.prime p.val.val p.val.property)
      (Subtype.val_injective.comp Subtype.val_injective)) (fun p => path.origin p.val)

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

def RelativeReturnedFiberLaw {X : Type*} [Fintype X] [DecidableEq X]
    (keep : X → Prop) [DecidablePred keep] (N : X → ℕ) (cost : ℝ)
    (law : FiniteProbabilityWeights (integerBox N)) : Prop :=
  ∃ (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ))
    (q : ℕ), 0 < q ∧
    ∃ (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
      (hlen : ∀ i, 0 < S.length i),
      (∀ i, Real.exp (-cost) * (N i.val : ℝ) ≤ (S.length i : ℝ)) ∧
      law = S.fiberSliceLaw hlen fixed hfixed

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedZeroLayerDegreeScalarConclusion
namespace OAI

section

namespace Erdos3

open scoped NNReal TensorProduct Classical

namespace PolynomialPatch

variable {V : Type*} {s d : ℕ} (P : PolynomialPatch V s d)
  [Fintype (PolynomialShearIndex P.weight)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]

structure ExternalObservableRegularity (M : ℝ≥0) (p : ℝ) : Prop where
  geometry : (polynomialShearNilmanifold P.weight s P.weight_le).GeometryComplexityLE p
  lip_bound : (P.shearObservableLipBound M : ℝ) ≤ Real.exp p
  lipschitz :
    letI : MetricSpace
      ((polynomialShearFiltration P.weight s P.weight_le).realification.Group ⧸
        polynomialShearRealLattice s P.weight_le) :=
      (polynomialShearNilmanifold P.weight s P.weight_le).metricSpace
    LipschitzWith (P.shearObservableLipBound M) (fun y => (P.shearObservable y : ℂ))
  positive : ∀ y, (P.shearObservable y : ℂ).im = 0 ∧
    0 ≤ (P.shearObservable y : ℂ).re ∧ (P.shearObservable y : ℂ).re ≤ 1

theorem externalObservableRegularity_of_niltest_complexity
    (M : ℝ≥0) (hP : ∀ i, realPolynomialMass (P.form.center i) ≤ M)
    {p : ℝ} (h : (P.shearNiltest M hP).ComplexityLE p) :
    P.ExternalObservableRegularity M p := by
  refine ⟨h.1, ?_, (P.shearNiltest M hP).lipschitz, ?_⟩
  · have hbound := RationalFilteredNilmanifold.Niltest.observable_budget h
    change 2 + 1 + (P.shearObservableLipBound M : ℝ) ≤ Real.exp p at hbound
    linarith
  · exact P.shearNiltest_unitInterval M hP

theorem ExternalObservableRegularity.mono {M : ℝ≥0} {p q : ℝ}
    (h : P.ExternalObservableRegularity M p) (hpq : p ≤ q) :
    P.ExternalObservableRegularity M q where
  geometry := RationalFilteredNilmanifold.GeometryComplexityLE.mono _ h.geometry hpq
  lip_bound := h.lip_bound.trans (Real.exp_le_exp.mpr hpq)
  lipschitz := h.lipschitz
  positive := h.positive

omit [Fintype (PolynomialShearIndex P.weight)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)] in

theorem shearObservable_memberNets {X : Type*} [Fintype X]
    (N : X → ℕ) (hN : ∀ x, 0 < N x) {p : ℝ} (hp : 0 ≤ p) (e : ℕ) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖(fun (_ : X → ℤ) y => (P.shearObservable y : ℂ)) x y -
            (fun (_ : X → ℤ) y => (P.shearObservable y : ℂ)) (oc i).val y‖ ≤ η :=
  constantObservable_integerBox_memberNets N hN
    (fun y => (P.shearObservable y : ℂ)) hp e

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

def DegreeGlobalizationAt (weight : (X → ℤ) → ℂ)
    (degree netExponent : ℕ) (p outputCost : ℝ) : Prop :=
  ∀ {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d f : ℕ} (D : RationalFilteredNilmanifold L degree d)
    (Fmark : RationalFilteredNilmanifold M degree f) (φ : L →ₗ⁅ℚ⁆ M),
    (∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j) →
    (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
    D.GeometryComplexityLE p → Fmark.GeometryComplexityLE p →
    (∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p) →
    ∀ (marked : Fmark.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
      (observable : (X → ℤ) → D.Space → ℂ) (ℓ : ℝ≥0),
    (ℓ : ℝ) ≤ Real.exp p →
    (∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x)) →
    (∀ x y, (observable x y).im = 0 ∧ 0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1) →
    (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + netExponent) ^ netExponent) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η) →
    (∀ x, ‖weight x‖ ≤ Real.exp p) →
    ∀ P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight p (Real.exp (-p)) (Real.exp (-p)),
    Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost)))

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateCoveredFamilySuccessor
namespace OAI

section

universe uL uM uX

namespace Erdos3.RationalFilteredNilmanifold

noncomputable def refilteredQuotientNetExponent (s r e : ℕ) : ℕ :=
  Classical.choose (exists_uniform_controlled_native_external_nets.{uL, uM, uX, 0, uL, uL} (s + 1) (s + 1) r e)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateGeneratedFreezingSuccessor
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

noncomputable def frozenMarkedPhysicalExponent (s : ℕ) : ℕ :=
  max (Classical.choose (exists_frozenMarkedLeftOrbit_exp_bound.{0, 0, 0, 0, 0} s))
    (Classical.choose (exists_frozenMarkedRightOrbit_grid_bound.{0, 0, 0, 0, 0} s))

theorem frozenMarkedPhysicalExponent_ge_two (s : ℕ) :
    2 ≤ frozenMarkedPhysicalExponent s :=
  (Classical.choose_spec
    (exists_frozenMarkedLeftOrbit_exp_bound.{0, 0, 0, 0, 0} s)).1.trans
      (le_max_left _ _)

theorem frozenMarkedPhysical_left_bound
    {σ ι κ L M : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ) (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) (H HS : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hdmark : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hHS : (HS : ℝ) ≤ Real.exp p)
    (hb : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hSheight : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) HS)
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (x : σ → ℤ)
    (hmarked : ∀ i, |(c.baseChange ℝ).repr
      (G.realification.polynomialOrbitEval w x marked).coord i| ≤ Real.exp p)
    (hcenter : ∀ i, |(b.baseChange ℝ).repr center.coord i| ≤ Real.exp p) (i : ι) :
    |(b.baseChange ℝ).repr
      (F.realification.polynomialOrbitEval w x
        (F.frozenMarkedLeftOrbit G w S hS marked center)).coord i| ≤
      Real.exp ((p + frozenMarkedPhysicalExponent s) ^ frozenMarkedPhysicalExponent s) := by
  have hleft := Classical.choose_spec
    (exists_frozenMarkedLeftOrbit_exp_bound.{0, 0, 0, 0, 0} s)
  exact (hleft.2 F G b c w S hS H HS p hp hd hdmark hH hHS hb hSheight
    marked center x hmarked hcenter i).trans
      (frozenMarkedPhysical_exp_mono hp hleft.1 (le_max_left _ _))

theorem exists_frozenMarkedPhysical_right_grid
    {σ ι κ L M : Type} [Fintype σ] [Fintype ι] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ) (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) (H : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hb : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hlp : ((matrixDenominator (LinearMap.toMatrix c b S) * q * r : ℕ) : ℝ) ≤
      Real.exp p) :
    ∃ m : ℕ, 0 < m ∧
      (m : ℝ) ≤ Real.exp ((p + frozenMarkedPhysicalExponent s) ^
        frozenMarkedPhysicalExponent s) ∧
      matrixDenominator (LinearMap.toMatrix c b S) * q * r ∣ m ∧
      ∀ marked : G.realification.PolynomialOrbit w,
        CoefficientGrid (c.baseChange ℝ) q marked.log →
        ∀ center : F.realification.Group,
          (b.baseChange ℝ).equivFun center.coord ∈ realDenominatorGrid r →
          ∀ x : σ → ℤ,
            (b.baseChange ℝ).equivFun
              (F.realification.polynomialOrbitEval w x
                (F.frozenMarkedRightOrbit G w S hS marked center)).coord ∈
              realDenominatorGrid m := by
  have hright := Classical.choose_spec
    (exists_frozenMarkedRightOrbit_grid_bound.{0, 0, 0, 0, 0} s)
  obtain ⟨m, hm, hmp, hdiv, hgrid⟩ := hright.2 F G b c w S hS H p hp hd hH hb q r hq hr hlp
  exact ⟨m, hm, hmp.trans
    (frozenMarkedPhysical_exp_mono hp hright.1 (le_max_right _ _)), hdiv, hgrid⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

noncomputable def allocatedRightDictionaryExponent (s : ℕ) : ℕ :=
  Classical.choose (exists_native_grid_right_dictionary.{0} s)

noncomputable def allocatedCoveredLowerExponent (s k : ℕ) : ℕ :=
  Classical.choose (exists_allocated_marked_covered_lower_diagram.{0, 0} s k)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedDilatedDeterminingSlots
namespace OAI

section

namespace Erdos3.RankPreparationFamily
open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
variable (c : ∀ j, (L j).space)
variable (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)

noncomputable def dilatedCenteredDeterminingPolynomial (q : ℕ)
    (a : Fin (Fintype.card (Σ j, E j))) : MvPolynomial X ℝ :=
  (q : ℝ)⁻¹ • L.centeredDeterminingPolynomial bW c hmem a

noncomputable def dilatedSortedDeterminingMatrix (q : ℕ) {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) :
    Fin n → Fin (Fintype.card (Σ j, E j)) → ℤ :=
  dilatedIntegerMatrix q (L.sortedDeterminingMatrix bW e)

@[simp] theorem dilatedCenteredDeterminingPolynomial_eval (q : ℕ)
    (x : X → ℝ) (a : Fin (Fintype.card (Σ j, E j))) :
    MvPolynomial.aeval x (L.dilatedCenteredDeterminingPolynomial bW c hmem q a) =
      MvPolynomial.aeval x (L.centeredDeterminingPolynomial bW c hmem a) / (q : ℝ) := by
  simp [dilatedCenteredDeterminingPolynomial, map_smul, smul_eq_mul, div_eq_mul_inv,
    mul_comm]

end Erdos3.RankPreparationFamily

end

end OAI
end


