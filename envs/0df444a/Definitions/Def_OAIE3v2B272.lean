-- Prove2me | Definitions.Def_OAIE3v2B272
-- name    : OAIE3v2B272
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:55:45.661554+00:00
-- url     : https://prove2.me/theorems/fd2e45e3-dcf9-4007-9e5e-e804b0074370
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 283 of 311
-- statement:
--   Definitions bundle 283 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B304`, `OAIE3v2B305`, `OAIE3v2B266`, `OAIE3v2B267` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidatePrecenterPaths.lean`, `Estimates/AllocatedExternalCandidateAdaptedOptionQuotientFactors.lean`, `Estimates/AllocatedExternalCandidateAxisFreezingConclusion.lean`, `Estimates/AllocatedExternalCandidateTaggedPairLongUniformFactors.lean`, `Estimates/AllocatedZeroLayerDetectorReturn.lean`, `Estimates/AllocatedZeroLayerFixedCenterExcess.lean`, `Estimates/MixedPairComparison.lean`, `Estimates/PreparedFiniteScheduleCandidateDetection.lean`, `Estimates/PreparedFiniteScheduleLocalProductiveSource.lean`, `Estimates/PreparedFiniteScheduleLocalScalarConstruction.lean`, `Geometry/AllocatedExternalCandidateAxisChartOrbit.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeBudget.lean`, `Geometry/ScalarReferenceNativeDetectionCoordinateEquiv.lean`, `Lattices/CertifiedAffineCutoffCost.lean`, `Probability/AllocatedExternalCandidateFixedLawSpatialFamily.lean`, `Sampling/PreparedSourceSlicedForecastNumerics.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B304
import Definitions.Def_OAIE3v2B305
import Definitions.Def_OAIE3v2B266
import Definitions.Def_OAIE3v2B267

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairComparison
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_localCoveredInducedBudget_bound (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      localCoveredInducedBudget s hs q p ≤ (p + C) ^ C := by
  obtain ⟨a, _, hsource⟩ := exists_sharedFreeCorrelationBudget_bound s hs
  let c := (NativeRankRelation.CommonData.exists_covered_induced_correlation_family s (by omega)).choose
  let P : Polynomial ℕ := (Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a +
    2 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  obtain ⟨hsize, _, _⟩ := hsource q p hq hqp hp
  have hcorr : 0 ≤ sharedFreeCorrelationBudget s hs p :=
    (show 0 ≤ sharedFreeCorrelationInput s p by
      linarith only [(sharedFreeCorrelationInput_bounds s hp le_rfl hp).1]).trans
        (sharedFreeCorrelationInput_le_budget s hs hp)
  have hbase : 0 ≤ q + (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs p + 2 + c := by positivity
  have hle : q + (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs p + 2 + c ≤ p + (p + a) ^ a + 2 + c := by linarith
  have hb : (p + (p + a) ^ a + 2 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact (pow_le_pow_left₀ hbase hle c).trans hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeBudget
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators Classical

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

theorem exists_spatialNative_slice_tagged_vertical_partners
    {Ω Pivot K X T LG : Type*} [Fintype Ω] [Fintype Pivot] [Fintype K] [DecidableEq K]
    [LieRing LG] [LieAlgebra ℚ LG]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {m s d : ℕ} (J : Fin m → Type*)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (D : RationalFilteredNilmanifold LG s d)
    {pNative : ℝ} (sample : T → X → ℤ)
    (nativeValue : Pivot → T → ℂ)
    (native : ∀ j, NativeSampleModel (fun _ : X => 1) s pNative sample (nativeValue j))
    (P : Ω → Pivot → D.Niltest (fun _ : K => 1))
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    {N : K → ℕ} (stride : Ω → Pivot → ℕ)
    (S : ∀ a j, ResidueBoxSlice N (stride a j))
    (hstride : ∀ a ∈ H, ∀ j, 0 < stride a j)
    (hlen : ∀ a j i, 0 < (S a j).length i)
    (physical : Ω → integerBox N → T)
    (center : Ω → ∀ j, J j → ℝ)
    (twist : Ω → Pivot → integerBox N → ℂ)
    {pLocal r q : ℝ} (hpLocal : 0 ≤ pLocal) (hr : 0 ≤ r) (hpq : pNative ≤ q)
    (hprecision : pLocal + r + 1 ≤ q)
    (hP : ∀ a ∈ H, ∀ j, (P a j).ComplexityLE pLocal)
    (htwist : ∀ a ∈ H, ∀ j t, ‖twist a j t‖ ≤ 1)
    (hcorr : ∀ a ∈ H, ∀ j, Real.exp (-r) ≤
      ‖((S a j).fullSliceLaw (hlen a j)).complexMean (fun t =>
        (star (twist a j t) * nativeValue j (physical a t)) * (P a j).eval t.val)‖) :
    ∃ (freq : ∀ j, (native j).L →ₗ[ℚ] ℚ)
      (V : ∀ j, (native j).model.Niltest (fullTaggedVariableWeight (X := X) J))
      (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card Pivot) * outer.mass H ≤
        outer.mass retained ∧
      (∀ j, (V j).orbit = ((native j).test.fullTaggedSpatial J).orbit ∧
        (V j).ComplexityLE pNative ∧ (V j).normBound ≤ 1) ∧
      (∀ j i, rationalLogHeight (freq j ((native j).model.basis i)) ≤
        verticalDecompositionBudget q) ∧
      (∀ j z, z ∈ (native j).model.filtration.realification.subgroup s → ∀ x,
        (V j).observable (z • x) = character
          ((realifyFunctional (freq j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x) ∧
      ∀ a ∈ retained, ∀ j,
        Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) ≤
          ‖((S a j).fullSliceLaw (hlen a j)).complexMean (fun t =>
            star (twist a j t) * ((P a j).eval t.val *
              (V j).eval (fullTaggedPhysicalIntegerPoint J poly (center a)
                (sample (physical a t)))))‖ := by
  have hnativeCorr (a : Ω) (ha : a ∈ H) (j : Pivot) :
      Real.exp (-r) ≤ ‖((S a j).fullSliceLaw (hlen a j)).complexMean (fun t =>
        ((P a j).eval t.val * star (twist a j t)) *
          (native j).test.eval (sample (physical a t)))‖ := by
    convert hcorr a ha j using 2
    congr 1
    funext t
    rw [(native j).eval]
    ring
  obtain ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, _hint,
      _hpres, hselected⟩ := exists_sliceLaw_localPivot_weighted_native_vertical_partners
    (fun j => (native j).model) (fun _ _ => D) (fun j => (native j).test) P
    outer H hH stride S hstride hlen (fun a t => sample (physical a t)) (fun _ _ t => t.val)
    (fun a j t => star (twist a j t)) hpLocal hr hpq hprecision
    (fun j => (native j).complexity) (fun j => by exact_mod_cast (native j).norm)
    hP (fun a ha j t => by simpa only [norm_star] using htwist a ha j t) hnativeCorr
  refine ⟨freq, (fun j => (V j).fullTaggedSpatial J), retained,
    hsub, hpos, hmass, ?_, hheight, hvert, ?_⟩
  · intro j
    refine ⟨?_, (hcert j).1, ?_⟩
    · simp only [Niltest.fullTaggedSpatial, Niltest.integerChartPullback,
        Niltest.withOrbit, (hcert j).2.1]
    · exact_mod_cast (hcert j).2.2.2.2
  · intro a ha j
    convert hselected a ha j using 2
    congr 1
    funext t
    rw [Niltest.fullTaggedSpatial_eval_physical]
    ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidatePrecenterPaths
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

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
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

theorem AllocatedExternalLocalCandidate.score_of_heq
    {cost : ℝ} {C C' : AllocatedExternalLocalChart (E := E) A cost}
    {candidate : AllocatedExternalLocalCandidate C D Fmark φ marked}
    {candidate' : AllocatedExternalLocalCandidate C' D Fmark φ marked}
    (hC : C = C') (hc : HEq candidate candidate')
    (obs : (X → ℤ) → D.Space → ℂ) (wgt : (X → ℤ) → ℂ) :
    candidate.score obs wgt = candidate'.score obs wgt := by
  subst C'
  cases hc
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion
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

namespace AllocatedExternalLocalChart

variable {cost shortCost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)

variable (fixed : {i : C.Variables // ¬keep i.val} → ℤ)

variable (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
    (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

def axisCoordinateEquiv : ({i // keep i} → ℤ) ≃
    ({i : C.Variables // keep i.val} → ℤ) where
  toFun u i := u ⟨i.val.val, i.property⟩
  invFun v i := v ⟨C.keptInclusion keep hkeep i, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem axisSlice_expect (f : (C.Variables → ℤ) → ℝ) :
    (𝔼 u ∈ (C.axisSlice keep hkeep).integerPoints, f (C.axisPoint keep fixed u)) =
      𝔼 u ∈ (C.slice.coordinateProjection (fun i : C.Variables => keep i.val)).integerPoints,
        f (finiteSplitPoint (fun i : C.Variables => keep i.val) u fixed) := by
  apply Finset.expect_equiv (C.axisCoordinateEquiv keep hkeep)
  · intro u
    rw [ResidueBoxSlice.mem_integerPoints_iff, ResidueBoxSlice.mem_integerPoints_iff]
    constructor
    · intro hu i
      exact hu ⟨i.val.val, i.property⟩
    · intro hu i
      exact hu ⟨C.keptInclusion keep hkeep i, i.property⟩
  · intro u _
    rfl

end AllocatedExternalLocalChart

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable {cost shortCost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

theorem freezeAxes_value (u : {i // keep i} → ℤ) :
    (candidate.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).value u =
      candidate.value (C.axisPoint keep fixed u) := by
  change QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fun _ => 1) u (candidate.axisOrbit keep fixed)) = _
  rw [candidate.axisOrbit_eval]
  rfl

theorem exists_freezeAxes (observable : (X → ℤ) → D.Space → ℂ)
    (weight : (X → ℤ) → ℂ) {a : ℝ} (hscore : a ≤ candidate.score observable weight) :
    ∃ fixed : {i : C.Variables // ¬keep i.val} → ℤ,
      (∀ i, fixed i ∈ integerProgressionSupport
        (C.slice.start i.val : ℤ) C.step (C.slice.length i.val)) ∧
      a ≤ 𝔼 u ∈ (C.axisSlice keep hkeep).integerPoints,
        (weight (C.physical (C.axisPoint keep fixed u)) *
          observable (C.physical (C.axisPoint keep fixed u))
            (candidate.value (C.axisPoint keep fixed u))).re := by
  let f : (C.Variables → ℤ) → ℝ := fun u =>
    (weight (C.physical u) * observable (C.physical u) (candidate.value u)).re
  have hmean : a ≤ 𝔼 u ∈ C.slice.integerPoints, f u := by
    simpa only [score, Complex.re_expect] using hscore
  obtain ⟨fixed, hfixed, _, hmean'⟩ := C.slice.exists_coordinate_fiber_score C.step_pos
    (C.slice.length_pos_of_dense C.dense) (fun i : C.Variables => keep i.val) f hmean
  refine ⟨fixed, hfixed, ?_⟩
  exact (C.axisSlice_expect keep hkeep fixed f).symm ▸ hmean'

end AllocatedExternalLocalCandidate

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] polynomialOrbitRealChart
  integerProgressionSupport IsDenseCommonStrideBox ResidueBoxSlice.integerPoints

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

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

theorem restrictAxes_parameter (u : {i // keep i} → ℤ) :
    (C.restrictAxes keep hkeep fixed hfixed).parameter u =
      C.parameter (C.axisPoint keep fixed u) :=
  C.freezeAxes_parameter (shortCost := cost) keep hkeep fixed hfixed u

theorem restrictAxes_chartValues (u : {i // keep i} → ℤ) :
    (C.restrictAxes keep hkeep fixed hfixed).chartValues u =
      C.chartValues (C.axisPoint keep fixed u) :=
  C.freezeAxes_chartValues (shortCost := cost) keep hkeep fixed hfixed u

theorem axisSlice_complexMean (f : (C.Variables → ℤ) → ℂ) :
    (𝔼 u ∈ (C.axisSlice keep hkeep).integerPoints, f (C.axisPoint keep fixed u)) =
      𝔼 u ∈ (C.slice.coordinateProjection (fun i : C.Variables => keep i.val)).integerPoints,
        f (finiteSplitPoint (fun i : C.Variables => keep i.val) u fixed) := by
  apply Finset.expect_equiv (C.axisCoordinateEquiv keep hkeep)
  · intro u
    rw [ResidueBoxSlice.mem_integerPoints_iff, ResidueBoxSlice.mem_integerPoints_iff]
    constructor
    · intro hu i
      exact hu ⟨i.val.val, i.property⟩
    · intro hu i
      exact hu ⟨C.keptInclusion keep hkeep i, i.property⟩
  · intro u _
    rfl

end AllocatedExternalLocalChart

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

noncomputable def restrictAxes : AllocatedExternalLocalCandidate
    (C.restrictAxes keep hkeep fixed hfixed) D Fmark φ marked where
  orbit := candidate.axisOrbit keep fixed
  mark_on_slice u hu := by
    rw [candidate.axisOrbit_eval, C.restrictAxes_chartValues]
    exact candidate.mark_on_slice _ (C.axisPoint_mem keep hkeep fixed hfixed hu)

theorem restrictAxes_value (u : {i // keep i} → ℤ) :
    (candidate.restrictAxes keep hkeep fixed hfixed).value u =
      candidate.value (C.axisPoint keep fixed u) := by
  change QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fun _ => 1) u
    (candidate.axisOrbit keep fixed)) = _
  rw [candidate.axisOrbit_eval]
  rfl

theorem localLaw_complexMean_parameter_value
    (test : (LayerSamplerVariables G I n B → ℤ) → D.Space → ℂ) :
    C.localLaw.complexMean (fun site => test site.val (candidate.siteValue site)) =
      𝔼 u ∈ C.slice.integerPoints, test (C.parameter u) (candidate.value u) := by
  simpa only [siteValue, C.retainedParameter_parameter] using
    C.localLaw_complexMean_parameter
      (fun x => test x (candidate.value (C.retainedParameter x)))

theorem restrictAxes_complexMean
    (test : (LayerSamplerVariables G I n B → ℤ) → D.Space → ℂ) :
    (C.restrictAxes keep hkeep fixed hfixed).localLaw.complexMean (fun site =>
      test site.val ((candidate.restrictAxes keep hkeep fixed hfixed).siteValue site)) =
      𝔼 u ∈ (C.axisSlice keep hkeep).integerPoints,
        test (C.parameter (C.axisPoint keep fixed u))
          (candidate.value (C.axisPoint keep fixed u)) := by
  rw [(candidate.restrictAxes keep hkeep fixed hfixed).localLaw_complexMean_parameter_value]
  simp only [restrictAxes_value, C.restrictAxes_parameter]

theorem exists_restrictAxes_norm
    (test : (LayerSamplerVariables G I n B → ℤ) → D.Space → ℂ) :
    ∃ fixed : {i : C.Variables // ¬keep i.val} → ℤ,
      ∃ hfixed : ∀ i : {i : C.Variables // ¬keep i.val}, fixed i ∈ integerProgressionSupport
        (C.slice.start i.val : ℤ) C.step (C.slice.length i.val),
      ‖C.localLaw.complexMean (fun site => test site.val (candidate.siteValue site))‖ ≤
        ‖(C.restrictAxes keep hkeep fixed hfixed).localLaw.complexMean (fun site =>
          test site.val ((candidate.restrictAxes keep hkeep fixed hfixed).siteValue site))‖ := by
  let f : (C.Variables → ℤ) → ℂ :=
    fun u => test (C.parameter u) (candidate.value u)
  obtain ⟨fixed, hfixed, _, hnorm⟩ := C.slice.exists_coordinate_fiber_norm C.step_pos
    (C.slice.length_pos_of_dense C.dense) (fun i : C.Variables => keep i.val) f
  refine ⟨fixed, hfixed, ?_⟩
  rw [candidate.localLaw_complexMean_parameter_value,
    candidate.restrictAxes_complexMean keep hkeep fixed hfixed,
    C.axisSlice_complexMean keep hkeep fixed f]
  exact hnorm

theorem exists_restrictAxes_site_norm (test : A.Site → D.Space → ℂ) :
    ∃ fixed : {i : C.Variables // ¬keep i.val} → ℤ,
      ∃ hfixed : ∀ i : {i : C.Variables // ¬keep i.val}, fixed i ∈ integerProgressionSupport
        (C.slice.start i.val : ℤ) C.step (C.slice.length i.val),
      ‖C.localLaw.complexMean (fun site => test site (candidate.siteValue site))‖ ≤
        ‖(C.restrictAxes keep hkeep fixed hfixed).localLaw.complexMean (fun site =>
          test site ((candidate.restrictAxes keep hkeep fixed hfixed).siteValue site))‖ := by
  let extension : (LayerSamplerVariables G I n B → ℤ) → D.Space → ℂ :=
    fun x y => if hx : x ∈ integerBox A.sides then test ⟨x, hx⟩ y else 0
  obtain ⟨fixed, hfixed, hnorm⟩ := candidate.exists_restrictAxes_norm keep hkeep extension
  refine ⟨fixed, hfixed, ?_⟩
  have he (site : A.Site) (y : D.Space) : extension site.val y = test site y := by
    simp only [extension, dif_pos site.property]
  simpa only [he] using hnorm

end AllocatedExternalLocalCandidate

end Erdos3.VectorPolynomial

end

section

universe u

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    {cost : ℝ}

namespace AllocatedExternalLocalChart

variable (C : AllocatedExternalLocalChart (E := Deck) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (fixed fixed' : {i : C.Variables // ¬keep i.val} → ℤ)

theorem axisPolynomial_top_independent (i : C.Variables) :
    weightedHomogeneousComponent (fun _ : {i // keep i} => 1) 1
      (C.axisPolynomial keep fixed i) =
    weightedHomogeneousComponent (fun _ : {i // keep i} => 1) 1
      (C.axisPolynomial keep fixed' i) := by
  by_cases hi : keep i.val
  · simp only [axisPolynomial, dif_pos hi]
  · simp only [axisPolynomial, dif_neg hi]
    rw [(isWeightedHomogeneous_C (fun _ : {i // keep i} => 1)
      (fixed ⟨i, hi⟩ : ℝ)).weightedHomogeneousComponent_ne 1 (by decide),
      (isWeightedHomogeneous_C (fun _ : {i // keep i} => 1)
      (fixed' ⟨i, hi⟩ : ℝ)).weightedHomogeneousComponent_ne 1 (by decide)]

end AllocatedExternalLocalChart

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
    {C : AllocatedExternalLocalChart (E := Deck) A cost}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)

namespace AllocatedExternalLocalChart

theorem pairOrbitSymbol_axisPolynomial_independent
    (C : AllocatedExternalLocalChart (E := Deck) A cost)
    (p : D.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1))
    (q : E.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1))
    (keep : LayerSamplerVariables G I n B → Prop)
    (fixed fixed' : {i : C.Variables // ¬keep i.val} → ℤ)
    {ι : Type*} (pairBasis : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (pairBasis '' {i | k ≤ ω i})) :
    pairOrbitSymbol D E
      (D.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed) p)
      (E.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed) q)
      pairBasis ω hF =
    pairOrbitSymbol D E
      (D.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed') (C.axisPolynomial_support keep fixed') p)
      (E.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed') (C.axisPolynomial_support keep fixed') q)
      pairBasis ω hF := by
  apply pairOrbitSymbol_chart_eq_of_homogeneous_eq D E p q pairBasis ω hF
    (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed)
    (C.axisPolynomial keep fixed') (C.axisPolynomial_support keep fixed')
  funext i
  exact C.axisPolynomial_top_independent keep fixed fixed' i

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

variable {D} {Target : Type*} [LieRing Target] [LieAlgebra ℚ Target] {t : ℕ}
    {Fmark : NilpotentLieFiltration Target t} {φ : L →ₗ⁅ℚ⁆ Target}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

theorem pairOrbitSymbol_axisOrbit_independent
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop)
    (fixed fixed' : {i : C.Variables // ¬keep i.val} → ℤ)
    (partnerOrbit : E.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1))
    {ι : Type*} (pairBasis : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (pairBasis '' {i | k ≤ ω i})) :
    pairOrbitSymbol D E (candidate.axisOrbit keep fixed)
      (E.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed) partnerOrbit)
      pairBasis ω hF =
    pairOrbitSymbol D E (candidate.axisOrbit keep fixed')
      (E.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed') (C.axisPolynomial_support keep fixed') partnerOrbit)
      pairBasis ω hF :=
  C.pairOrbitSymbol_axisPolynomial_independent D E candidate.orbit partnerOrbit
    keep fixed fixed' pairBasis ω hF

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAdaptedOptionQuotientFactors
namespace OAI

section

universe u v

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    {cost : ℝ} {C : AllocatedExternalLocalChart (E := Deck) A cost}
    {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {P : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)]
    {s d dQ : ℕ} {dp : Pivot → ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)
    (partners : ∀ j, RationalFilteredNilmanifold (P j) s (dp j))
    (partnerOrbit : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

theorem optionJoint_lieQuotient_log :
    ((candidate.lieQuotient ideal hI Q hQ hker).optionJoint partners partnerOrbit).orbit.log =
      VectorPolynomial.map
        ((realificationLieHom (optionMarkedLieMap (L := P)
          (lieQuotientMap ideal))).toLinearMap.restrictScalars ℚ)
        (candidate.optionJoint partners partnerOrbit).orbit.log := by
  exact (optionMarkedLieMap_piRealOrbit_log D Q partners (lieQuotientMap ideal)
    (candidate.optionJointLocalOrbits partners partnerOrbit)
    ((candidate.lieQuotient ideal hI Q hQ hker).optionJointLocalOrbits partners partnerOrbit)
    (D.quotientOrbit_log ideal hI Q hQ candidate.orbit).symm (fun _ => rfl)).symm

attribute [local irreducible] NilpotentLieFiltration.realPolynomialGroupMap

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateAxisChartOrbit
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

attribute [local irreducible] polynomialOrbitRealChart realChartSubstitute

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

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

include hkeep in

theorem axisPolynomial_freeze (p : MvPolynomial (LayerSamplerVariables G I n B) ℝ) :
    freezePolynomial keep (fun i => (C.axisFixed keep fixed i : ℝ)) p =
      MvPolynomial.aeval (C.axisPolynomial keep fixed)
        (freezePolynomial C.keep (fun i => (C.fixed i : ℝ)) p) := by
  unfold freezePolynomial
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => MvPolynomial.aeval f p)
  funext i
  by_cases hk : keep i
  · have hc := hkeep i hk
    simp [frozenCoordinate, axisPolynomial, hk, hc]
  · by_cases hc : C.keep i
    · simp [frozenCoordinate, axisPolynomial, axisFixed, hk, hc]
    · simp [frozenCoordinate, axisFixed, hk, hc]

theorem restrictAxes_integerSampledRealChart :
    integerSampledRealChart (C.restrictAxes keep hkeep fixed hfixed).integerChart =
      fun i => MvPolynomial.aeval (C.axisPolynomial keep fixed)
        (integerSampledRealChart C.integerChart i) := by
  funext i
  change integerSampledRealChart
      (fun z => freezePolynomial keep (C.axisFixed keep fixed)
        (allocatedRecoveredIntegerFullChart B U b o poly hm C.centerLift
          C.path.1.val C.path.2.val C.sample z)) i =
    MvPolynomial.aeval (C.axisPolynomial keep fixed)
      (integerSampledRealChart
        (fun z => freezePolynomial C.keep C.fixed
          (allocatedRecoveredIntegerFullChart B U b o poly hm C.centerLift
            C.path.1.val C.path.2.val C.sample z)) i)
  rw [integerSampledRealChart_freeze, integerSampledRealChart_freeze]
  exact C.axisPolynomial_freeze keep hkeep fixed _

theorem restrictAxes_polynomialOrbitRealChart
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (g : F.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)) :
    F.polynomialOrbitRealChart (fullTaggedVariableWeight J) (fun _ => 1)
      (integerSampledRealChart (C.restrictAxes keep hkeep fixed hfixed).integerChart)
      (C.restrictAxes keep hkeep fixed hfixed).integerChart_support g =
    F.polynomialOrbitRealChart (fun _ : C.Variables => 1) (fun _ => 1)
      (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed)
      (F.polynomialOrbitRealChart (fullTaggedVariableWeight J) (fun _ => 1)
        (integerSampledRealChart C.integerChart) C.integerChart_support g) := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (F.polynomialOrbitRealChart _ _ _ _ g).log =
    (F.polynomialOrbitRealChart _ _ _ _ (F.polynomialOrbitRealChart _ _ _ _ g)).log
  simp only [polynomialOrbitRealChart_log]
  rw [C.restrictAxes_integerSampledRealChart keep hkeep fixed hfixed]
  exact (realChartSubstitute_comp (integerSampledRealChart C.integerChart)
    (C.axisPolynomial keep fixed) g.log).symm

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairLongUniformFactors
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)

theorem retainedLength_of_densityBudget {densityBudget p : ℝ}
    (hdense : IsDenseCommonStrideBox
      (fun i : C.Variables => A.sides i.val) densityBudget C.slice.integerPoints)
    (hbudget : densityBudget ≤ p) (i : C.Variables) :
    Real.exp (-p) * (A.sides i.val : ℝ) ≤ C.slice.length i :=
  (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbudget))
    (Nat.cast_nonneg (A.sides i.val))).trans
      (C.slice.length_lower_of_dense C.step_pos hdense i)

end AllocatedExternalLocalChart

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerFixedCenterExcess
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

theorem fixedCenter_excess_zero_layers
    (hξ : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    (hloss : (∑ x, 2 * (spatialTrimMargin τ N x : ℝ) / N x) ≤ 1 / 2) :
    letI : Nonempty A.Site := A.site_nonempty
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξ hmargin)) 2 = 0 := by
  let : Nonempty A.Site := A.site_nonempty
  let : Nonempty A.bases := A.bases_nonempty.to_subtype
  let : Nonempty (integerBox N) := A.integerBox_nonempty.to_subtype
  apply le_antisymm ?_ (FiniteProbabilityWeights.excessMass_nonneg _ _ _)
  apply FiniteProbabilityWeights.siteLaw_excessMass_le_of_test_bound
  intro φ hφ site
  rw [A.law_zero_layers, selectedJointReference, FiniteProbabilityWeights.mean_prod,
    FiniteProbabilityWeights.mean_comm]
  have hcard : (Fintype.card (integerBox N) : ℝ) / Fintype.card A.bases ≤ 2 := by
    simpa only [Fintype.card_coe] using
      trimmedIntegerBox_card_ratio_le_two N _ A.trimMargin_proper hloss
  have hinj (noise : rectangularWeightIndices 0 A.widths 1) :
      Function.Injective (fun a : A.bases => A.physicalBox hξ hmargin (a, noise) site) := by
    intro a a' heq
    apply Subtype.ext
    have hv := congrArg Subtype.val heq
    change a.val + integerPhysicalSite site.val noise.val =
      a'.val + integerPhysicalSite site.val noise.val at hv
    exact add_right_cancel hv
  have hbound (noise : rectangularWeightIndices 0 A.widths 1) :
      (FiniteProbabilityWeights.uniformFinset A.bases A.bases_nonempty).mean
        (fun a => φ (A.physicalBox hξ hmargin (a, noise) site)) ≤
      2 * (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).mean φ := by
    exact (FiniteProbabilityWeights.uniform_injective_mean_le _ (hinj noise) φ
      (fun x => (hφ x).1)).trans
        (mul_le_mul_of_nonneg_right hcard
          ((FiniteProbabilityWeights.uniformFinset (integerBox N)
            A.integerBox_nonempty).mean_nonneg (fun x => (hφ x).1)))
  simpa only [FiniteProbabilityWeights.mean_const, add_zero] using
    (selectedResidueFiniteLaw stride cells A.widths A.widths_pos A.smooth_mass_pos).mean_mono hbound

theorem fixedCenter_excess_zero_layers_of_spatial_cutoff
    (hξ : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ x, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N x : ℝ)) :
    letI : Nonempty A.Site := A.site_nonempty
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξ hmargin)) 2 = 0 := by
  apply A.fixedCenter_excess_zero_layers hξ hmargin
  rw [htrim] at hN ⊢
  obtain ⟨_, _, _, _, _, _, hloss⟩ :=
    unconditionedSpatialWidthBudget (K := LayerSamplerVariables G I n B)
      (allocatedExternalCandidateRootBudget_nonneg B U b S) hsurplus hsurplus1 N hN
  linarith

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarReferenceNativeDetectionCoordinateEquiv
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {K K' X : Type*} [Fintype K] [Fintype K'] [Fintype X]
    (e : K ≃ K') (B τ : ℝ) (N : X → ℕ)

local notation "W" => trimmedSpatialWidths (K := K) B τ N
local notation "W'" => trimmedSpatialWidths (K := K') B τ N

include e in
theorem selectedResidueSmoothMass_scalarCoordinateEquiv :
    (∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W' z) =
      ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z :=
  selectedResidueSmoothMass_one_reindex (scalarNoiseIndexEquiv e) W W'
    (trimmedSpatialWidths_scalarNoiseIndexEquiv e B τ N)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def OrdinarySliceNativeDetection
    {m degree : ℕ} {X K Ω : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K] [Fintype Ω]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sides : K → ℕ) (law : FiniteProbabilityWeights Ω)
    (physical : Ω → integerBox sides → X → ℤ) (pSlice pTest pNative α : ℝ) : Prop :=
  ∀ {Tests : Ω → Type} [∀ z, Nonempty (Tests z)]
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) degree (dims z j))
    (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : K => 1))
    (slices : ∀ z, Tests z → Finset (integerBox sides))
    (origin : ∀ z, Tests z → K → ℤ) (step : ∀ z, Tests z → ℕ)
    (length : ∀ z, Tests z → K → ℕ),
    (∀ z j, 0 < step z j) →
    (∀ z j, (slices z j).image Subtype.val = commonStrideBox (origin z j) (step z j) (length z j)) →
    (∀ z j, IsDenseCommonStrideBox sides pSlice ((slices z j).image Subtype.val)) →
    (∀ z j, (Vdetect z j).ComplexityLE pTest) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    SampledSliceNativeDetection J N hbox poly law physical slices
      (fun z j t => star ((Vdetect z j).eval (commonStrideIndex (origin z j) (step z j) t.val)))
      degree pNative α

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def ScalarReferenceNativeDetection
    {m degree : ℕ} {X K : Type} [Fintype X] [DecidableEq X]
    [Fintype K] [DecidableEq K]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (S : ℕ) (W τ : ℝ)
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hW : ∀ z : Option K × X, 0 < trimmedSpatialWidths W τ N z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K) W τ N) z)
    (pSlice pTest pNative α : ℝ) : Prop :=
  OrdinarySliceNativeDetection (degree := degree) J N hbox poly (fun _ : K => S)
    (selectedJointReference _ hbase (fun _ : X => 1) {0}
      (trimmedSpatialWidths W τ N) hW hZ)
    (fun z t => jointIntegerPhysicalSite t.val (z.1.val, z.2.val))
    pSlice pTest pNative α

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerDetectorReturn
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler
variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
  N poly hm τ ξ (fun _ : X => 1) {0} center)

omit [∀ j, IsEmpty (J j)]
  [∀ j, IsZLattice ℝ
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
include A in
theorem scalarMass_pos_empty_layers :
    0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := LayerSamplerVariables G I n B)
        ((Fintype.card G : ℝ) * S.value) τ N) z := by
  simpa only [allocatedExternalCandidateWidths_empty_layers] using A.smooth_mass_pos

omit [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)] [∀ j, IsEmpty (Fin (n j))]
  [∀ j, IsZLattice ℝ
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
include A in
theorem scalarAxesWidths_pos_empty_layers :
    ∀ z : Option G × X,
      0 < trimmedSpatialWidths ((Fintype.card G : ℝ) * S.value) τ N z :=
  trimmedSpatialWidths_pos (by positivity) A.trim_pos N A.size_pos

omit [∀ j, IsEmpty (J j)]
  [∀ j, IsZLattice ℝ
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
include A in
theorem scalarAxesMass_pos_empty_layers :
    0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := G) ((Fintype.card G : ℝ) * S.value) τ N) z := by
  rw [selectedResidueSmoothMass_scalarCoordinateEquiv (emptyLayerVariablesEquiv B)
    ((Fintype.card G : ℝ) * S.value) τ N]
  exact A.scalarMass_pos_empty_layers

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler
variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
  N poly hm τ ξ (fun _ : X => 1) {0} center)

omit [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
include A in
theorem scalarAxesMass_pos_zero_layers :
    0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := G) ((Fintype.card G : ℝ) * S.value) τ N) z := by
  let : ∀ j, IsEmpty (I j) := fun j => Fin.elim0 j
  let : ∀ j, IsEmpty (Fin (n j)) := fun j => Fin.elim0 j
  exact A.scalarAxesMass_pos_empty_layers

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleCandidateDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def AllocatedNativeSliceDetection
    {m degree : ℕ} {X K Ω : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K] [Fintype Ω]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sides : K → ℕ) (law : FiniteProbabilityWeights Ω)
    (physical : Ω → integerBox sides → X → ℤ) (pSlice pTest pNative α : ℝ) : Prop :=
  ∀ {Tests : Ω → Type} [∀ z, Nonempty (Tests z)]
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) degree (dims z j))
    (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : K => 1))
    (slices : ∀ z, Tests z → Finset (integerBox sides))
    (origin : ∀ z, Tests z → K → ℤ) (step : ∀ z, Tests z → ℕ)
    (length : ∀ z, Tests z → K → ℕ),
    (∀ z j, 0 < step z j) →
    (∀ z j, (slices z j).image Subtype.val = commonStrideBox (origin z j) (step z j) (length z j)) →
    (∀ z j, IsDenseCommonStrideBox sides pSlice ((slices z j).image Subtype.val)) →
    (∀ z j, (Vdetect z j).ComplexityLE pTest) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    SampledSliceNativeDetection J N hbox poly law physical slices
      (fun z j t => star ((Vdetect z j).eval (commonStrideIndex (origin z j) (step z j) t.val)))
      degree pNative α

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

def PreparedFiniteScheduleGeometryPrescribedScaleStatement (m : ℕ) {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
    {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {Bstruct pnum Qstride : ℝ} (nX : ℕ)
    (pDetect aDetect target : K → ℝ)
 : Prop :=
    let Aradius := Classical.choose (exists_preparedUniformEarlyRadius.{0,0,0,0} m)
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let gainLog := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables G I n B)) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K =>
      scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
    let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    pRadius ∈ Set.Icc 0 ((Bstruct + Bstruct + Aradius) ^ Aradius) ∧
    (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧ 0 ≤ D ∧
    (∀ s, 0 ≤ gainLog s ∧ 0 ≤ Pk s ∧ 0 ≤ Prho s ∧ 0 ≤ Ptail s) ∧
    ∃ t : K → ℝ,
      (∀ s, 0 < t s ∧ t s ≤ 1 ∧ (t s)⁻¹ ≤ Real.exp (Ptail s)) ∧
    ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := preparedUniformDegreeTolerance t Qσ
      let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
      let lengthLogs := fun s : K => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
        (target s) (pDetect s + 2) (Tmod s)
      0 < σ ∧ σ ≤ 1 ∧ (∀ s, σ ≤ t s) ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ 0 ≤ Pscale ∧ D ≤ Pscale ∧
      (∀ s, Pk s ≤ Pscale) ∧
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
      ∀ (S : LayerSamplerScale (G := G) B U basis R (fun _ => σ)),
        (∀ s : K, Real.exp (lengthLogs s) ≤ S.value) →
        ∀ s : K, PreparedUniformDegreeGeometryAt B U basis S (degree s) (Cdetect s) nX
          Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (gainLog s)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalProductiveSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

def PreparedFiniteScheduleGeometryStatement (m : ℕ) {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
    {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {Bstruct pnum Qstride : ℝ} (nX : ℕ)
    (pDetect aDetect target : K → ℝ)
 : Prop :=
    let Aradius := Classical.choose (exists_preparedUniformEarlyRadius.{0,0,0,0} m)
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let gainLog := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables G I n B)) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K =>
      scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
    let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    pRadius ∈ Set.Icc 0 ((Bstruct + Bstruct + Aradius) ^ Aradius) ∧
    (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧ 0 ≤ D ∧
    (∀ s, 0 ≤ gainLog s ∧ 0 ≤ Pk s ∧ 0 ≤ Prho s ∧ 0 ≤ Ptail s) ∧
    ∃ t : K → ℝ,
      (∀ s, 0 < t s ∧ t s ≤ 1 ∧ (t s)⁻¹ ≤ Real.exp (Ptail s)) ∧
    ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := preparedUniformDegreeTolerance t Qσ
      let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
      let lengthLogs := fun s : K => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
        (target s) (pDetect s + 2) (Tmod s)
      0 < σ ∧ σ ≤ 1 ∧ (∀ s, σ ≤ t s) ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ 0 ≤ Pscale ∧ D ≤ Pscale ∧
      (∀ s, Pk s ≤ Pscale) ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
      let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
      ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
        Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
        (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
          8 * (probabilityProfileLipschitz : ℝ) * W ≤
            (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
              ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
        ∀ s : K, PreparedUniformDegreeGeometryAt B U basis S (degree s) (Cdetect s) nX
          Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (gainLog s)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedAffineCutoffCost
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem allocatedFrozenIntegerFullChart_anchor_grid
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (j : Fin m) {T : Type*} (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (D : ℝ)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ) (t : T) :
    ∃ z : ℤ, D * Q (fun i => MvPolynomial.eval (0 : {k // keep k} → ℝ)
      (integerSampledRealChart
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed)
          (Sum.inr ⟨j, i⟩))) t = z := by
  have heval (i : J j) : MvPolynomial.eval (0 : {k // keep k} → ℝ)
      (integerSampledRealChart
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed)
          (Sum.inr ⟨j, i⟩)) =
      (MvPolynomial.eval (0 : {k // keep k} → ℤ)
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed
          (Sum.inr ⟨j, i⟩)) : ℝ) := by
    simpa only [Pi.zero_apply, Int.cast_zero, Pi.zero_def] using
      integerSampledRealChart_eval
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed)
        (0 : {k // keep k} → ℤ) (Sum.inr ⟨j, i⟩)
  simp_rw [heval]
  exact hgrid _ t

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateFixedLawSpatialFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {Ω Freq Bin : Type} [Fintype Ω] [Fintype Bin] [Nonempty Bin]
    {LG LM : Type} [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d t rank : ℕ} (D : RationalFilteredNilmanifold LG s d)
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {cost : ℝ} (C : Ω → AllocatedExternalLocalChart (E := Deck) A cost)
    (candidate : ∀ a, AllocatedExternalLocalCandidate (C a) D Fmark φ marked)
    (hξ1 : ξ ≤ 1)

theorem exists_fixedLaw_spatial_native_family
    (external : Freq → integerBox N → D.Niltest (fullTaggedVariableWeight (X := X) J))
    (representative : Bin → integerBox N)
    (eta : Freq → LG →ₗ[ℚ] ℚ)
    {p pLocal pNative r inputBound ε δ coefficientBound termBound : ℝ}
    (hcomplex : ∀ f x, (external f x).ComplexityLE pLocal)
    (hnet : ∀ f x, ∃ i, ∀ y, ‖(external f x).observable y -
      (external f (representative i)).observable y‖ ≤ ε)
    (input : integerBox N → ℂ)
    (models : (Freq × Bin) → CenteredForecastModel (integerBox N))
    (periodCap coverCap : ℝ) (Lip : ℝ≥0)
    (hnativeModels : ∀ branch i, (models branch).models i ∈
      twistedNativeSampleFunctions (fun _ : X => 1) s pNative
        (fun x : integerBox N => x.val)
        (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
          (x : integerBox N) => twist.eval N poly x.val))
    (hmodel : ∀ branch, externalNetMaskFamily (fun f x => (external f x).observable)
        (fun f i => (external f (representative i)).observable) hnet input branch =
      (∑ i, (models branch).coefficient i • (models branch).models i) + (models branch).residual)
    (hcoefficient : ∀ branch, (∑ i, |(models branch).coefficient i|) ≤ coefficientBound)
    (hterms : ∀ branch, ((models branch).nterms : ℝ) ≤ termBound)
    (hM : 0 < coefficientBound) (hterm : 1 ≤ termBound)
    (code : Fin rank → Option Freq)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (hB : 0 ≤ inputBound) (hδ : 0 < δ) (herror : inputBound * ε ≤ δ / 2)
    (hinput : ∀ x, ‖input x‖ ≤ inputBound)
    {Eres sliceBudget testBudget : ℝ}
    (hcost0 : 0 ≤ cost)
    (hshort : ∀ a ∈ H, ∀ i : {i // ¬(C a).keep i},
      (A.sides i.val : ℝ) ≤ Real.exp cost)
    (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : pLocal ≤ testBudget)
    (hUniform : ∀ a ∈ H, ∀ f i,
      ∀ packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget,
        ‖𝔼 site ∈ packet.slice.subtypeSites,
          (models (f, i)).residual (A.boxedPhysical hξ1 (C a).path site) *
            packet.weight site.val‖ ≤ Real.exp (-Eres))
    (hresBudget : Real.exp (pLocal - Eres) ≤ (δ / (2 * Fintype.card Bin)) / 2)
    (hscore : ∀ a ∈ H, ∀ i f, code i = some f → δ ≤
      ‖(C a).localLaw.complexMean (fun site =>
        input (A.boxedPhysical hξ1 (C a).path site) *
          (external f (A.boxedPhysical hξ1 (C a).path site)).observable
            ((candidate a).siteValue site))‖)
    (hcorrBudget : Real.exp (-r) ≤ (δ / (2 * Fintype.card Bin)) / (2 * coefficientBound))
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ a, (C a).keep = keep)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : 0 ≤ p) (hpLocal : 0 ≤ pLocal) (hr : 0 ≤ r)
    (hcost : cost ≤ p) (hlocal : pLocal ≤ p) (hnative : pNative ≤ p)
    (hperiod : periodCap * coverCap ≤ Real.exp p)
    (hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
    (hetaHeight : ∀ f i, rationalLogHeight (eta f (D.basis i)) ≤ p)
    (hvertical : ∀ f x z, z ∈ D.filtration.realification.subgroup s → ∀ y,
      (external f x).observable (z • y) = CircleFourier.character
        ((realifyFunctional (eta f) z.coord : ℝ) : CircleFourier.Circle) *
          (external f x).observable y)
    (hK : (Fintype.card {i // keep i} : ℝ) ≤ p) :
    ∃ (retained : Finset Ω), retained ⊆ H ∧ 0 < outer.mass retained ∧
      outer.mass H / ((Fintype.card Bin : ℝ) ^ rank * termBound ^ rank) ≤ outer.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω
          (KernelProjectionPresentPivot code) D Fmark φ marked keep cost p pLocal pNative r
          periodCap coverCap Lip,
        F.sourceChart = C ∧ (∀ a, HEq (F.sourceCandidate a) (candidate a)) ∧
        F.η = (fun k => eta (kernelProjectionSelectedPivot code k)) ∧
        ∀ a ∈ retained, ∀ k, Real.exp (-r) ≤ ‖F.correlation a k‖ := by
  have hresidual : ∀ a ∈ H, ∀ f i,
      ‖(C a).localLaw.complexMean (fun site =>
        (models (f, i)).residual (A.boxedPhysical hξ1 (C a).path site) *
          (external f (representative i)).observable ((candidate a).siteValue site))‖ ≤
            (δ / (2 * Fintype.card Bin)) / 2 := by
    intro a ha f i
    exact ((candidate a).localLaw_residual_le_exp_of_universal_native_budget
      (external f (representative i)) (hcomplex f _) hcost0 (hshort a ha)
      hSliceBudget hTestBudget
      (fun site => (models (f, i)).residual (A.boxedPhysical hξ1 (C a).path site))
      (hUniform a ha f i)).trans hresBudget
  obtain ⟨chosen, twist, value, native, retained, hsub, hpos, hmass, _, hcorr⟩ :=
    exists_external_kernel_precenter_native_point_partners D external representative hcomplex hnet
      input models (fun _ : X => 1) s pNative (fun x : integerBox N => x.val)
      (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
        (x : integerBox N) => twist.eval N poly x.val)
      hnativeModels hmodel hcoefficient hterms hM hterm code outer H hH
      (fun a => (C a).localLaw) (fun a => (candidate a).siteValue)
      (fun a => A.boxedPhysical hξ1 (C a).path)
      hB hδ herror hinput hresidual hscore
  let F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω
      (KernelProjectionPresentPivot code) D Fmark φ marked keep cost p pLocal pNative r
      periodCap coverCap Lip := {
    hpoly := hpoly
    hτ1 := hτ1
    hξ := hξ1
    hσ1 := hσ1
    Cgeo := Cgeo
    hCgeo := hCgeo
    hchart := hchart
    hsmall := hsmall
    sourceChart := C
    keep_eq := hkeep
    sourceCandidate := candidate
    reference := fun _ k => external (kernelProjectionSelectedPivot code k) (representative (chosen k))
    nativeValue := value
    native := native
    twist := fun _ => twist
    hp := hp
    hpLocal := hpLocal
    hr := hr
    hcost := hcost
    hlocal := hlocal
    hnative := hnative
    hperiod := by
      intro a k
      rw [Nat.cast_mul]
      exact (mul_le_mul (twist k).modulus_bound (twist k).cover_bound
        (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans (twist k).modulus_bound)).trans hperiod
    hvariation := hvariation
    hV := fun _ k => hcomplex _ _
    η := fun k => eta (kernelProjectionSelectedPivot code k)
    hηheight := fun k i => hetaHeight _ i
    hη := fun _ k => hvertical _ _
    hK := hK }
  refine ⟨retained, hsub, hpos, hmass, F, rfl, (fun _ => HEq.rfl), rfl, ?_⟩
  intro a ha k
  apply hcorrBudget.trans
  simpa only [AllocatedExternalCandidateSpatialNativeFamily.correlation,
    AllocatedExternalCandidateSpatialNativeFamily.sitePhysicalBox, F, boxedPhysical, mul_assoc, mul_left_comm, mul_comm]
    using hcorr a ha k

end AllocatedExternalCandidateSampler
end
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSourceSlicedForecastNumerics
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

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
noncomputable def preparedActualSlicedForecastSetupOfSourceGeometry {M nX : ℕ}
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
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)),
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    {Cdetect : ℕ} {Bstruct Pscale Dgeometry target Pk Prho pDetect aDetect detectionGain : ℝ}
    (hInverseBound : ∀ j, inverse j ≤ Real.exp Bstruct)
    (hgeometry : PreparedUniformDegreeGeometryAt
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S 0 Cdetect nX
      Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain) :
    ActualFixedSpatialForecastSetup (X := Fin nX) (Eout := Eout)
      (G := EnlargedPreparedCommonKernel m Jalloc)
      (I := PreparedSamplerContinuous L) (n := preparedSamplerTransverse L)
      (A := PreparedActualForecastShortIndex (G := EnlargedPreparedCommonKernel m Jalloc)
        (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S)
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S (nX + m * M)
      (preparedActualForecastShortSelection (G := EnlargedPreparedCommonKernel m Jalloc)
        (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S)
      (Real.exp (-(gainLog + (nX : ℝ) + 8))) (Real.exp (-cost) / 2) := by
  let geometry := Classical.choice hgeometry.1
  exact preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
    hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound geometry.siteRadius geometry.T
    (fun j => by
      have h := geometry.hsource j
      norm_num only [Fintype.card_fin, Nat.cast_one, pow_one] at h
      exact h) geometry.hradius
    inverse hinverse hchart (fun j => by
      simpa only [mul_assoc] using (geometry.hbudgets inverse hinverse hInverseBound).2.2 j)

end Erdos3.VectorPolynomial

end

end OAI
end


