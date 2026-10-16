-- Prove2me | Definitions.Def_OAIErdos3B1340
-- name    : OAIErdos3B1340
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T23:07:31.689977+00:00
-- url     : https://prove2.me/theorems/d2ca1bb5-cb10-47b5-b043-6f0c94a20b7b
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1341 of 1374
-- statement:
--   Definitions bundle 1341 of 1374 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1339`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1341 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.actualPathReferenceNeZero`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.referenceInputLaw`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.referenceModulus`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.referenceModulus_pos`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.referencePolynomial`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastNumerics.noConfusion`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.rawTarget`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.slicedBlockEquiv`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.AxisFreezing.realThreshold_long`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.AxisFreezing.realThreshold_strict_long`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.ambientScore_one_eq`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.conclusion_stepZero`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.exists_realThresholdAxisFreezing`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.realThresholdKeep`, `OAI.Erdos3.VectorPolynomial.actualSlicedForecastDecayBudget`, `OAI.Erdos3.VectorPolynomial.actualSlicedForecastDensityBudget`, `OAI.Erdos3.VectorPolynomial.actualSlicedForecastModelCapLog`, `OAI.Erdos3.VectorPolynomial.actualSlicedForecastModelPeriodLog`, `OAI.Erdos3.VectorPolynomial.candidateSideCutoff`, `OAI.Erdos3.VectorPolynomial.candidateSideCutoffCost`, `OAI.Erdos3.VectorPolynomial.candidateSideCutoff_lt_max_add_two`, `OAI.Erdos3.VectorPolynomial.candidateSideCutoff_pos`, `OAI.Erdos3.VectorPolynomial.exists_actualSlicedForecastModelCapLog_budget`, `OAI.Erdos3.VectorPolynomial.lt_candidateSideCutoff`, `OAI.Erdos3.VectorPolynomial.preparedActualSlicedForecastSetup`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastBadLog`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastCapLog`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastJacobianLog`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastSpatialBudget`, `_private.Probability.ActualFixedSpatialSlicedDensityBounds.0.OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.slicedBlock_det_ne_zero`, `_private.Sampling.PreparedActualSlicedForecastSetup.0.OAI.Erdos3.VectorPolynomial.and_rec_projection`, `_private.Sampling.PreparedActualSlicedForecastSetup.0.OAI.Erdos3.VectorPolynomial.preparedSliceWidth_inverse`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1336

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateRealThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable def candidateSideCutoff (bound : ℝ) : ℕ := Nat.ceil bound + 1

theorem candidateSideCutoff_pos (bound : ℝ) : 0 < candidateSideCutoff bound :=
  Nat.succ_pos _

theorem lt_candidateSideCutoff (bound : ℝ) : bound < (candidateSideCutoff bound : ℝ) := by
  have hceil := Nat.le_ceil bound
  simp only [candidateSideCutoff, Nat.cast_add, Nat.cast_one]
  linarith

theorem candidateSideCutoff_lt_max_add_two (bound : ℝ) :
    (candidateSideCutoff bound : ℝ) < max bound 0 + 2 := by
  have hmono : (Nat.ceil bound : ℝ) ≤ Nat.ceil (max bound 0) := by
    exact_mod_cast Nat.ceil_mono (le_max_left bound 0)
  have hceil := Nat.ceil_lt_add_one (le_max_right bound 0)
  simp only [candidateSideCutoff, Nat.cast_add, Nat.cast_one]
  linarith

noncomputable def candidateSideCutoffCost (bound : ℝ) : ℝ :=
  Real.log ((max (candidateSideCutoff bound) 1 : ℕ) : ℝ)

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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def realThresholdKeep (bound : ℝ) :
    P.productive → LayerSamplerVariables G I n B → Prop :=
  P.thresholdKeep (candidateSideCutoff bound)

namespace AxisFreezing

variable {P} {bound : ℝ}
    (freezing : P.AxisFreezing (P.realThresholdKeep bound) (candidateSideCutoffCost bound))

theorem realThreshold_long (z : P.productive) (i : LayerSamplerVariables G I n B)
    (hi : (freezing.problem.chart z).keep i) :
    (candidateSideCutoff bound : ℝ) ≤ layerSamplerBox B U b S i := by
  have hs : candidateSideCutoff bound ≤ A.sides i := hi.2
  have he : layerSamplerBox B U b S i = (A.sides i : ℝ) := by
    cases i <;> rfl
  rw [he]
  exact_mod_cast hs

theorem realThreshold_strict_long (z : P.productive) (i : LayerSamplerVariables G I n B)
    (hi : (freezing.problem.chart z).keep i) :
    bound < layerSamplerBox B U b S i :=
  (lt_candidateSideCutoff bound).trans_le (freezing.realThreshold_long z i hi)

end AxisFreezing

theorem exists_realThresholdAxisFreezing (bound : ℝ) :
    ∃ freezing : P.AxisFreezing (P.realThresholdKeep bound) (candidateSideCutoffCost bound),
      (∀ z : P.productive, ∀ i, (freezing.problem.chart z).keep i →
        (candidateSideCutoff bound : ℝ) ≤ layerSamplerBox B U b S i) ∧
      (∀ z : P.productive, ∀ i, (freezing.problem.chart z).keep i →
        bound < layerSamplerBox B U b S i) := by
  obtain ⟨freezing⟩ := P.exists_thresholdAxisFreezing (candidateSideCutoff bound)
  exact ⟨freezing, freezing.realThreshold_long, freezing.realThreshold_strict_long⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateStepZero
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {d : ℕ}
    (D : RationalFilteredNilmanifold L 0 d) (Fmark : NilpotentLieFiltration M 0)
    (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace AllocatedExternalCandidateProblem

theorem ambientScore_one_eq (z : P.productive) :
    P.ambientScore 1 z (P.chart z).slice.integerPoints =
      (P.candidate z).score observable weight := by
  unfold ambientScore AllocatedExternalLocalCandidate.score AllocatedExternalLocalCandidate.value
  congr 2
  funext u
  congr 2
  apply congrArg QuotientGroup.mk
  exact (D.filtration.realification.externalCandidate_stepZero_group_eq_one _).trans
    (D.filtration.realification.externalCandidate_stepZero_group_eq_one _).symm

theorem conclusion_stepZero : Nonempty (P.Conclusion cost massThreshold scoreThreshold) := by
  classical
  refine ⟨{
    ambient := 1
    marked := ?_
    retained := P.productive
    subset := fun _ h => h
    mass := P.mass
    step := fun z => (P.chart z).step
    step_pos := fun z => (P.chart z).step_pos
    slice := fun z => (P.chart z).slice
    dense := fun z => (P.chart z).dense
    inside := fun _ _ h => h
    score := ?_
  }⟩
  · apply coefficients.injective
    ext α
    rw [coefficients_map]
    exact (Fmark.realification.externalCandidate_stepZero_coord_eq_zero _).trans
      (Fmark.realification.externalCandidate_stepZero_coord_eq_zero _).symm
  · intro z
    rw [P.ambientScore_one_eq]
    exact P.score z

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialSlicedDensityBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem slicedBlock_det_ne_zero (second : Bool) :
    (fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fixedSpatialKernelSliceFrame Wsp Lsp slice.path.normalizedNoise
        slice.kernelLower slice.kernelWidth) second).det ≠ 0 := by
  have hbase : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp slice.path.normalizedNoise second).det ≠ 0 := by
    cases second
    · exact slice.path.detFalse
    · exact slice.path.detTrue
  let w : X → ℝ := fun i => slice.kernelWidth
    (spatialEquiv.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i))
  have hmatrix : fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fixedSpatialKernelSliceFrame Wsp Lsp slice.path.normalizedNoise
        slice.kernelLower slice.kernelWidth) second =
      fixedSpatialKernelBlock spatialEquiv Wsp Lsp slice.path.normalizedNoise second * Matrix.diagonal w := by
    ext x i
    rw [fixedSpatialKernelBlock_slice, Matrix.mul_diagonal]
  rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero hbase (Finset.prod_ne_zero_iff.mpr (fun i _ => slice.kernelWidth_ne_zero _))

noncomputable def slicedBlockEquiv (second : Bool) : (X → ℝ) ≃L[ℝ] (X → ℝ) :=
  fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp
    (fixedSpatialKernelSliceFrame Wsp Lsp slice.path.normalizedNoise
      slice.kernelLower slice.kernelWidth) second (slice.slicedBlock_det_ne_zero second)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup
namespace OAI

section

namespace Erdos3

end Erdos3

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
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

noncomputable def actualSlicedForecastDensityBudget (v : ℝ) : ℝ :=
  Real.exp (forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * v))

noncomputable def actualSlicedForecastDecayBudget : ℝ :=
  Real.exp ((s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m)

structure ActualFixedSpatialSlicedForecastNumerics where
  T : ℕ
  hT : 0 < T
  δ : ℝ
  hδ : 0 < δ
  Hchild : ℕ
  v : ℝ
  hv : 0 ≤ v
  Ptail : ℝ
  Ctail : ℝ
  hPtail : 1 ≤ Ptail
  hprimitive : s.Pcap ≤ Ptail
  hCtail : 0 ≤ Ctail
  Cactual : ℝ
  δout : ℝ
  Q : ℝ
  Nt : ℝ
  Vt : ℝ
  Ct : ℝ
  Ht : ℝ
  Lt : ℝ≥0
  hCactual : 0 ≤ Cactual
  hδout : 0 < δout
  hQ : 0 ≤ Q
  hCt : 0 ≤ Ct
  hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
    forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
      δ (Ptail * T) Cactual δout Q Nt Vt Ct Ht Lt
  htailactual : ∀ a,
    let degree := (selected a).1.val + 1
    let denom := inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := blockTorusFactor (Fintype.card Empty) degree
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := (torus : ℝ) * ((denom : ℝ) * 2 ^ degree) / δ ^ degree
    let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
      (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
    max (cutoff : ℝ)
      (uniformSpectrumAbsoluteCap (selected a).1.val 1 degree Ptail V V) ≤ Ctail
  Pnative : ℝ
  massLog : ℝ
  capLog : ℝ
  E : ℝ
  hPnative : 0 ≤ Pnative
  hperiod : (T : ℝ) * Vt ^ Fintype.card A ≤ Real.exp Pnative
  hfactor : (actualSlicedForecastDensityBudget s v + Fintype.card A * (Lt : ℝ)) *
    max (8 / τ) 1 ≤ Real.exp Pnative
  hcoord : ((s.K * ∑ j, s.forward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Pnative
  hcut : (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
    (2 * s.radius)) * (s.K * ∑ j, s.forward j * Fintype.card (J j)) : ℝ≥0) : ℝ) ≤ Real.exp Pnative
  hmass : s.κ * (2 * actualSlicedForecastDensityBudget s v *
    ((T : ℝ) ^ (Dmod + 1) * Ct ^ Fintype.card A)) ≤ Real.exp massLog
  herror : s.κ * (actualSlicedForecastDensityBudget s v *
    (Ctail ^ Fintype.card A * (actualSlicedForecastDecayBudget s / T) +
      (T : ℝ) ^ (Dmod + 1) * δout)) ≤ Real.exp (-E)
  hcap : s.κ * actualSlicedForecastDensityBudget s v * Ctail ^ Fintype.card A *
    (1 + actualSlicedForecastDecayBudget s) ≤ Real.exp capLog

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
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

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
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

end Erdos3.VectorPolynomial

end

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

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem and_rec_projection_p0 {p q : Prop} {α : Sort*}
    (f : p → q → α) (h : p ∧ q) : And.rec f h = f h.1 h.2 := by
  cases h
  rfl

noncomputable def preparedSlicedForecastSpatialBudget (m M nX Jalloc : ℕ)
    (Pdim cost : ℝ) : ℝ :=
  max (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + nX + 8)
    (max (preparedCenteredForecastSpatialLog Pdim) (cost + 1))

noncomputable def preparedSlicedForecastBadLog (m nX : ℕ) (Qstride gainLog : ℝ) : ℝ :=
  2 * nX * Qstride + (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11

noncomputable def preparedSlicedForecastJacobianLog (m M nX : ℕ)
    (pRadius gainLog Pchart : ℝ) : ℝ :=
  ((nX + m + m * M : ℕ) : ℝ) * (pRadius + gainLog + nX + Pchart + 11)

noncomputable def preparedSlicedForecastCapLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart kernelV p w vchild : ℝ) : ℝ :=
  actualSlicedForecastModelCapLog m (nX + m * M) nX
    (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost)
    (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1)
    (preparedSlicedForecastBadLog m nX Qstride gainLog) (cost + 1)
    (preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart) kernelV p w vchild

theorem preparedSliceWidth_inverse (cost : ℝ) :
    (Real.exp (-cost) / 2)⁻¹ ≤ Real.exp (cost + 1) := by
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg, Real.exp_add]
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  nlinarith only [mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg cost)]

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]
noncomputable def preparedActualSlicedForecastSetup {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4) :
    ActualFixedSpatialForecastSetup («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) (X := Fin nX) (Eout := Eout)
      («G» := (EnlargedPreparedCommonKernel m Jalloc)) («I» := (PreparedSamplerContinuous L)) («n» := (preparedSamplerTransverse L)) (A := PreparedActualForecastShortIndex («I» := (PreparedSamplerContinuous L)) («n» := (preparedSamplerTransverse L)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := (EnlargedPreparedCommonKernel m Jalloc)) (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S)
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S (nX + m * M) (preparedActualForecastShortSelection («I» := (PreparedSamplerContinuous L)) («n» := (preparedSamplerTransverse L)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := (EnlargedPreparedCommonKernel m Jalloc)) (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S)
      (Real.exp (-(gainLog + (nX : ℝ) + 8))) (Real.exp (-cost) / 2) := by
  let Pbad := preparedSlicedForecastBadLog m nX Qstride gainLog
  let Pκ := preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart
  let κ := forecastGeometricJacobian (X := Fin nX) («I» := (PreparedSamplerContinuous L)) U b R S.value
    (preparedForecastGridVolume L Jalloc U b S) (Real.exp (-(gainLog + (nX : ℝ) + 8)))
  have hPbad : 0 ≤ Pbad := by dsimp only [Pbad, preparedSlicedForecastBadLog]; positivity
  obtain ⟨hκ, hPκ, hκcap⟩ := preparedActualForecastJacobian_ratio_budget (nX := nX) L
    (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S
    hCoord hpRadius hGain hChart hR hRinv hratio
  let s := preparedActualForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord
    hpRadius hGain hPbad (show 0 ≤ cost + 1 by linarith) hPF hPκ hκ.le hκcap
    hR hRone hRinv hσone forward hforward hforwardBound radius T hT hradius
    inverse hinverse hchart hsourceBudget
  have hsP : s.P = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + nX + 8 := by
    simp only [s, preparedActualForecastSetup, and_rec_projection_p0]
  have hP : s.P ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost := by
    rw [hsP]
    exact le_max_left _ _
  let s' := s.enlargeP hP
  have hwidth : (Real.exp (-cost) / 2)⁻¹ ≤ Real.exp s'.P :=
    (preparedSliceWidth_inverse cost).trans (Real.exp_le_exp.mpr
      ((le_max_right _ _).trans (le_max_right _ _)))
  exact s'.withSliceWidth (div_pos (Real.exp_pos _) (by norm_num)) hwidth

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal
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
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def referenceModulus : ℕ := ∏ p : path.primes, p.val ^ path.exponent p.val

omit [Fintype Tsp] in
theorem referenceModulus_pos : 0 < path.referenceModulus := by
  apply Finset.prod_pos
  intro p _
  exact pow_pos (path.prime p.val p.property).pos _

local instance actualPathReferenceNeZero : NeZero path.referenceModulus :=
  ⟨path.referenceModulus_pos.ne'⟩

noncomputable def referencePolynomial :=
  allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value) path.base path.noise
    (allocatedReadDeck path.read) (fun j a => allocatedReadProjection path.read ⟨j,a.val⟩)

noncomputable def referenceInputLaw : FiniteProbabilityWeights
    (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
      ZMod path.referenceModulus) := by
  letI := path.primeNeZero
  exact crtPolynomialInputLaw (fun p : path.primes => p.val)
    (fun p : path.primes => path.exponent p.val) (fun p : path.primes => path.prescribed p.val)
    (primePower_crt_coprime (fun p : path.primes => p.val)
      (fun p : path.primes => path.exponent p.val)
      (fun p => path.prime p.val p.property) Subtype.val_injective) path.origin

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

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
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

namespace VectorPolynomial

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
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

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
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

noncomputable def rawTarget (κ : ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ) : ℂ := by
  letI : NeZero slice.path.referenceModulus := ⟨slice.path.referenceModulus_pos.ne'⟩
  exact (κ : ℂ) * forecastLawDensityPhysicalTarget B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceInputLaw)
    (fun y t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (y k.1 k.2 : ℤ)) slice.path.referenceModulus t j)
    slice.path.referenceModulus (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW poly hm u

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

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
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

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
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable (κ : ℝ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

variable {Pnative massLog capLog E : ℝ}

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end


