-- Prove2me | Definitions.Def_OAIE3v2B282
-- name    : OAIE3v2B282
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:37:42.264491+00:00
-- url     : https://prove2.me/theorems/738ad5ac-74c9-484f-9fbd-0fc736a95c25
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 295 of 311
-- statement:
--   Definitions bundle 295 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B308`, `OAIE3v2B275`, `OAIE3v2B276` of this split.
--
--   Modules: `Dynamics/AllocatedCandidateStageScalarBudget.lean`, `Dynamics/AllocatedExternalCandidateSourcePhysicalBudgetBounds.lean`, `Estimates/AllocatedExternalCandidateLocalFixedCenterFront.lean`, `Estimates/AllocatedExternalCandidatePrimitiveFrontDescentData.lean`, `Estimates/AllocatedExternalCandidateSelectedDescentRegularity.lean`, `Estimates/AllocatedFrozenPrefixStageData.lean`, `Estimates/PreparedFiniteNestedSourceArrays.lean`, `Polynomial/AllocatedNestedDegreeInduction.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B308
import Definitions.Def_OAIE3v2B275
import Definitions.Def_OAIE3v2B276

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateStageScalarBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration

attribute [local irreducible] allocatedFrozenCurrentGradeResetConstant
  allocatedCandidateStageResetLog allocatedCandidateStageLocalInput allocatedCandidateStageSliceLog

theorem exists_allocatedCandidateStageSliceLog_budget (s m Cbase : ℕ) :
    ∃ Cslice : ℕ, 2 ≤ Cslice ∧ ∀ b : ℝ, 0 ≤ b →
      allocatedCandidateStageSliceLog s m ((b + Cbase) ^ Cbase) ≤ (b + Cslice) ^ Cslice := by
  let V : Polynomial ℕ := (Polynomial.X + Polynomial.C Cbase) ^ Cbase
  let P : Polynomial ℕ := V + (V + 2) ^ 4 + Polynomial.C (s + 1) +
    Polynomial.C s * (V + 1) + Polynomial.C s *
      (Polynomial.C (m + 1) + Polynomial.C m * (V + 1))
  let Creset := allocatedFrozenCurrentGradeResetConstant s 1
  let R : Polynomial ℕ := (P + Polynomial.C Creset) ^ Creset
  let L : Polynomial ℕ := R + V ^ 2 + 2 * V + 2
  let Q : Polynomial ℕ := (L + Polynomial.C (s + 401)) ^ (s + 401) +
    2 * (V + 2) ^ 9 + V + Polynomial.C s + 4
  obtain ⟨Cslice, hCslice, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨Cslice, hCslice, ?_⟩
  intro b hb
  simpa [Q, L, R, P, V, Creset, allocatedCandidateStageSliceLog,
    allocatedCandidateStageLocalInput, allocatedCandidateStageResetLog,
    allocatedCandidateStageResetInput, Polynomial.eval₂_pow, Nat.cast_add]
    using hbound b hb

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenPrefixStageData
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCandidateStageSliceExponent (s m Cprimitive : ℕ) : ℕ :=
  Classical.choose (exists_allocatedCandidateStageSliceLog_budget s m
    (allocatedCandidateStageBaseExponent s m Cprimitive))

noncomputable def allocatedCandidateStageSlice (s m Cprimitive : ℕ) (b : ℝ) : ℝ :=
  (b + allocatedCandidateStageSliceExponent s m Cprimitive) ^
    allocatedCandidateStageSliceExponent s m Cprimitive

 theorem allocatedCandidateStageSlice_bounds (s m Cprimitive : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    2 ≤ allocatedCandidateStageSliceExponent s m Cprimitive ∧
    allocatedCandidateStageSliceLog s m (allocatedCandidateStageBase s m Cprimitive b) ≤
      allocatedCandidateStageSlice s m Cprimitive b := by
  have h := Classical.choose_spec (exists_allocatedCandidateStageSliceLog_budget s m
    (allocatedCandidateStageBaseExponent s m Cprimitive))
  exact ⟨h.1, h.2 b hb⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateLocalFixedCenterFront
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrecenterKernelSelection
variable {P} {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

theorem exists_fixedCenter_spatialNativeFamily
    {Bin : Type} [Fintype Bin] [Nonempty Bin]
    (representative : Bin → integerBox N)
    (hnet : ∀ x : integerBox N, ∃ i, ∀ y,
      ‖(T x.val).observable y - (T (representative i).val).observable y‖ ≤
        Real.exp (-(p + q + 2)))
    (models : (early.Freq × Bin) → CenteredForecastModel (integerBox N))
    {pNative coefficientLog termLog binLog dimensionLog Eres sliceBudget testBudget : ℝ}
    (periodCap coverCap : ℝ) (Lip : ℝ≥0)
    (hnativeModels : ∀ branch i, (models branch).models i ∈
      twistedNativeSampleFunctions (fun _ : X => 1) s pNative
        (fun x : integerBox N => x.val)
        (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
          (x : integerBox N) => twist.eval N poly x.val))
    (hmodel : ∀ branch, externalNetMaskFamily
        (fun f (x : integerBox N) => (early.U f x.val).observable)
        (fun f i => (early.U f (representative i).val).observable)
        (contracted_member_net (early := early) representative hnet) (fun x => weight x.val) branch =
      (∑ i, (models branch).coefficient i • (models branch).models i) + (models branch).residual)
    (hcoefficientModels : ∀ branch,
      (∑ i, |(models branch).coefficient i|) ≤ Real.exp coefficientLog)
    (hterms : ∀ branch, ((models branch).nterms : ℝ) ≤ Real.exp termLog)
    (hq : 0 ≤ q) (hcoefficient : 0 ≤ coefficientLog)
    (hterm : 0 ≤ termLog) (hbin : 0 ≤ binLog)
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp binLog)
    (hdim : (finrank ℚ top : ℝ) ≤ dimensionLog)
    (hξ1 : ξ ≤ 1)
    (hweight : ∀ x ∈ integerBox N, ‖weight x‖ ≤ Real.exp p)
    (hcost0 : 0 ≤ cost) (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : q ≤ testBudget)
    {u : ℝ}
    (hlocalResidual : ∀ branch, sampledSliceSeminorm A.law (A.boxedPhysical hξ1)
      (fun _ (packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget) =>
        packet.slice.subtypeSites)
      (fun _ packet site => packet.weight site.val) (models branch).residual ≤ Real.exp (-u))
    (hMarkovBudget : (Fintype.card (early.Freq × Bin) : ℝ) * Real.exp (-u) ≤
      Real.exp (-Eres) * A.law.mass selected.retained / 2)
    (hresBudget : q + q + binLog + 4 ≤ Eres)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ a, (P.chart a).keep = keep)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {pFamily : ℝ} (hpFamily : 0 ≤ pFamily)
    (hcost : cost ≤ pFamily) (hlocal : q ≤ pFamily) (hnative : pNative ≤ pFamily)
    (hperiod : periodCap * coverCap ≤ Real.exp pFamily)
    (hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp pFamily)
    (hK : (Fintype.card {i // keep i} : ℝ) ≤ pFamily) :
    ∃ (retained : Finset A.Path), retained ⊆ selected.retained ∧
      0 < A.law.mass retained ∧
      Real.exp (-(dimensionLog * (binLog + termLog))) * (A.law.mass selected.retained / 2) ≤
        A.law.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A E A.Path
          (KernelProjectionPresentPivot selected.code) D Fmark φ marked keep cost pFamily q pNative
          (q + binLog + coefficientLog + 4) periodCap coverCap Lip,
        F.sourceChart = P.precenterChart hpos ∧
        (∀ a, HEq (F.sourceCandidate a) (P.precenterCandidate hpos a)) ∧
        F.η = (fun k => early.eta (kernelProjectionSelectedPivot selected.code k)) ∧
        (∀ a ∈ retained, ∀ k,
          Real.exp (-(q + binLog + coefficientLog + 4)) ≤ ‖F.correlation a k‖) ∧
        (∀ a ∈ retained, (F.sourceChart a).path = a) ∧
        (∀ a, (F.sourceChart a).centerLift = P.centerLift) ∧
        (∀ a ∈ retained, Real.exp (-q) ≤
          (F.sourceCandidate a).score (fun x => (selected.tests x).observable) weight) := by
  let : Nonempty A.Site := A.site_nonempty
  let slices := fun (_ : A.Path)
    (packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget) => packet.slice.subtypeSites
  let tests := fun (_ : A.Path)
    (packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget) (site : A.Site) =>
      packet.weight site.val
  have hDense : ∀ a packet, IsDenseCommonStrideBox A.sides sliceBudget
      ((slices a packet).image Subtype.val) := fun _ packet => packet.slice.subtypeSites_dense packet.dense
  have hsize := preparedCenteredForecast_slice_family_bounds B U b S slices hDense
  obtain ⟨good, hgoodSub, hgoodMass, hgoodPos, hgood⟩ :=
    A.law.exists_uniformSliceResidualGood selected.retained (A.boxedPhysical hξ1) slices tests
      (fun branch => (models branch).residual) hsize.1 hsize.2
      (fun _ packet site => packet.weight_norm site.val) hlocalResidual selected.positive_mass
      (Real.exp_pos (-Eres)) hMarkovBudget
  have hU : ∀ f (i : integerBox N), (early.U f i.val).ComplexityLE q := fun f i => (early.U_bounds f i.val).1
  have hnetU := contracted_member_net (early := early) representative hnet
  have hmodelError := precenter_native_selection_model_error_budget p q
  have hres := precenter_native_selection_residual_budget (rFreq := q) (pLocal := q) hcard hresBudget
  have hcorr := precenter_native_selection_correlation_budget (rFreq := q)
    (c := coefficientLog) hcard
  obtain ⟨retained, hsub, hmassPos, hmass, F, hFC, hFcandidate, hFeta, hFcorr⟩ :=
    A.exists_fixedLaw_spatial_native_family D (P.precenterChart hpos) (P.precenterCandidate hpos)
      hξ1 (fun f x => early.U f x.val) representative early.eta hU hnetU
      (fun x => weight x.val) models periodCap coverCap Lip hnativeModels hmodel hcoefficientModels hterms (Real.exp_pos _) (Real.one_le_exp_iff.mpr hterm)
      selected.code A.law good hgoodPos (Real.exp_nonneg _)
      (Real.exp_pos _) hmodelError (fun x => hweight x.val x.property)
      hcost0 (fun a _ i => P.precenterChart_frozen hpos a i) hSliceBudget hTestBudget
      (by
        intro a ha f i packet
        rw [P.precenterChart_path hpos a (selected.subset (hgoodSub ha))]
        exact hgood a ha (f, i) packet)
      hres (fun a ha i f hif => (selected.pivots a (hgoodSub ha) i f hif).le) hcorr keep
      (P.precenterChart_keep hpos keep hkeep) hpoly hτ1 hσ1 Cgeo hCgeo hchart hsmall
      hpFamily hq (by positivity) hcost hlocal hnative hperiod hvariation
      (fun f i => (early.eta_height f i).trans hlocal) (fun f x => early.vertical f x.val) hK
  refine ⟨retained, fun a ha => hgoodSub (hsub ha), hmassPos, ?_, F, hFC, hFcandidate, hFeta, hFcorr, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hgoodMass (Real.exp_nonneg _)).trans
      ((precenter_native_selection_mass_budget (finrank ℚ top) hbin hterm hdim hcard
        (A.law.mass_nonneg good)).trans hmass)
  · intro a ha
    rw [hFC]
    exact P.precenterChart_path hpos a (selected.subset (hgoodSub (hsub ha)))
  · intro a
    rw [hFC]
    exact P.precenterChart_center hpos a
  · intro a ha
    have hs := selected.scores a (hgoodSub (hsub ha))
    have hchartEq := congrFun hFC a
    have heq : (F.sourceCandidate a).score (fun x => (selected.tests x).observable) weight =
        (P.precenterCandidate hpos a).score (fun x => (selected.tests x).observable) weight := by
      exact AllocatedExternalLocalCandidate.score_of_heq hchartEq (hFcandidate a) _ _
    exact hs.trans_eq heq.symm

end PrecenterKernelSelection
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedNestedDegreeInduction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.degreeSourceProfileSiteNonempty
structure InnerSourceProfile (degree : ℕ) where
  x : ℝ
  scheduleExponent : ℕ
  Cprimitive : ℕ
  Csource : ℕ
  gainLog : ℝ
  stageLog : ℝ
  sourceNative : ℕ → ℝ
  pTest : ℕ → ℝ
  detectionLoss : ℕ → ℝ
  rankThreshold : ℝ
  x_nonneg : 0 ≤ x
  gain_range : gainLog ∈ Set.Icc 0 x
  stage_range : stageLog ∈ Set.Icc 0 x
  primitive_pos : 1 ≤ Cprimitive
  base_exponent : allocatedCandidateStageBaseExponent degree m Cprimitive ≤ scheduleExponent
  slice_exponent : allocatedCandidateStageSliceExponent degree m Cprimitive + 1 ≤ scheduleExponent
  phase_exponent : ∀ r < degree,
    allocatedCandidateCompositePhaseConstant degree m 1
      (allocatedCandidatePromotedMajorConstant Csource) r ≤ scheduleExponent
  source_nonneg : ∀ r < degree, 0 ≤ sourceNative r
  source_bound : ∀ r < degree, sourceNative r ≤
    (preparedFiniteForwardSourcePrecision scheduleExponent degreeSourceCountConstants
        r x gainLog stageLog +
      preparedFiniteForwardWork scheduleExponent degreeSourceCountConstants r x + Csource) ^ Csource
  test_floor : ∀ r < degree, OrdinaryPolynomialPhase.budget r ≤ pTest r
  loss_nonneg : ∀ r < degree, 0 ≤ detectionLoss r
  loss_bound : ∀ r < degree, detectionLoss r ≤ Real.exp (-gainLog) / 2
  detection : ∀ r < degree, A.NativeDetection r
    (allocatedCandidateStageSlice degree m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent degreeSourceCountConstants r x))
    (pTest r) (sourceNative r) (detectionLoss r)
  tags_input : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x
  layers_input : (m : ℝ) ≤ x
  variables_input : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x
  size_floor : ∀ i, Real.exp
    (preparedFiniteForwardCumulative scheduleExponent degreeSourceCountConstants degree x) ≤ (N i : ℝ)
  rank_floor : Real.exp
    (preparedFiniteForwardCumulative scheduleExponent degreeSourceCountConstants degree x) ≤ rankThreshold
  sampling_rank : ∀ j, HasLayerSamplingRank (j.val + 1)
    (fun i => (N i : ℝ)) rankThreshold (U j) (poly j)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateSourcePhysicalBudgetBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler.InnerSourceProfile
variable {s : ℕ} (source : A.InnerSourceProfile (s + 1))

noncomputable def physicalBudget : ℝ :=
  nativePhysicalTerminalFullBudget (s + 1) m source.Cprimitive source.scheduleExponent source.x

noncomputable def ordinaryBudget : ℝ := candidatePhysicalOrdinaryBudget source.physicalBudget

theorem input_le_physicalBudget : source.x ≤ source.physicalBudget := by
  have h := nativePhysicalTerminalBudgets_nonneg (s + 1) m source.Cprimitive
    source.scheduleExponent source.x_nonneg
  exact (allocatedCandidateTerminalFullInput_bounds (s + 1) m source.Cprimitive
    source.x_nonneg h.2.1 h.1).2.2.1

end AllocatedExternalCandidateSampler.InnerSourceProfile
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceArrays
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteNestedSourceSliceExponent
    (m cutoff Cprimitive : ℕ) : ℕ :=
  1 + ∑ d : Fin (cutoff + 1), allocatedCandidateStageSliceExponent d.val m Cprimitive

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateSelectedDescentRegularity
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
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.PrecenterKernelSelection

variable {cost massThreshold scoreThreshold p q : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

theorem exists_native_descent
    (ideal : LieIdeal ℚ L)
    (hkernel : ideal.toSubmodule = frequencyCodeKernel top early.eta selected.code)
    (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    {dQ : ℕ} (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ ideal))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ ideal))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ ideal))] [T2Space (ℝ ⊗[ℚ] (L ⧸ ideal))]
    (hQF : Q.filtration = D.filtration.quotientLie ideal hI)
    (hQL : Q.lattice = D.lattice.map (D.filtration.quotientStepHom ideal hI))
    (pDesc : ℝ) (hpDesc : 0 ≤ pDesc) (hqDesc : q ≤ pDesc)
    (hQ : Q.GeometryComplexityLE pDesc)
    (hmap : ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap ideal (D.basis j)) i) ≤ pDesc) :
    ∃ descended : (X → ℤ) → Q.Niltest (fullTaggedVariableWeight (X := X) J),
      (∀ x, (descended x).orbit =
        D.idealQuotientOrbit ideal hI Q hQF (selected.tests x).orbit) ∧
      (∀ x, (descended x).UnitIntervalValued) ∧
      (∀ x y, ‖(descended x).observable y‖ ≤ 1) ∧
      (∀ x, (descended x).ComplexityLE
        ((pDesc + 2) ^ RationalFilteredNilmanifold.nativeInvariantFamilyDescentExponent s)) ∧
      (∀ x, letI := Q.metricSpace;
        LipschitzWith
          ⟨Real.exp ((pDesc + 2) ^ RationalFilteredNilmanifold.nativeInvariantFamilyDescentExponent s),
            Real.exp_nonneg _⟩ (descended x).observable) ∧
      (∀ x (g : D.RealGroup), (descended x).observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
          (selected.tests x).observable (QuotientGroup.mk g)) ∧
      (∀ x y η, (∀ z, ‖(T x).observable z - (T y).observable z‖ ≤ η) →
        ∀ z, ‖(descended x).observable z - (descended y).observable z‖ ≤ η) ∧
      ∀ entropy : ℝ → ℝ,
        (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ, (n : ℝ) ≤ entropy η ∧
          ∃ rep : Fin n → {x : X → ℤ // x ∈ integerBox N},
            ∀ x ∈ integerBox N, ∃ i, ∀ y,
              ‖(T x).observable y - (T (rep i).val).observable y‖ ≤ η) →
        ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ, (n : ℝ) ≤ entropy η ∧
          ∃ rep : Fin n → {x : X → ℤ // x ∈ integerBox N},
            ∀ x ∈ integerBox N, ∃ i, ∀ y,
              ‖(descended x).observable y - (descended (rep i).val).observable y‖ ≤ η := by
  classical
  have hinvariant (x : X → ℤ) (g : D.RealGroup)
      (hg : g.coord ∈ ideal.toSubmodule.baseChange ℝ) (y : D.Space) :
      (selected.tests x).observable (g • y) = (selected.tests x).observable y := by
    apply selected.invariant x g _ y
    simpa only [hkernel] using hg
  have hex (x : X → ℤ) := (Classical.choose_spec
    (RationalFilteredNilmanifold.exists_idealInvariant_niltest_budget.{0, 0} s)).2
    D ideal hI Q hQF hQL (selected.tests x)
    pDesc hpDesc ((selected.test_bounds x).2.1.mono hqDesc) hQ hmap (hinvariant x)
  choose descended horbit hnorm hcomplex hrecovery heval hunit using hex
  have hpositive (x : X → ℤ) : (descended x).UnitIntervalValued :=
    hunit x (selected.test_bounds x).1
  have htopIdeal : ideal.toSubmodule ≤ D.filtration.layer s := by
    rw [hkernel]
    exact (finiteFrequencyKernel_le top _ _).trans htop
  have hrecOriginal (x : X → ℤ) (g : D.RealGroup) :
      (descended x).observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
        ((T x).kernelProjection ideal.toSubmodule htopIdeal).observable (QuotientGroup.mk g) := by
    rw [hrecovery, selected.identity]
    congr 2
    exact hkernel.symm
  have hcontract (x y : X → ℤ) (η : ℝ)
      (hxy : ∀ z, ‖(T x).observable z - (T y).observable z‖ ≤ η) :
      ∀ z, ‖(descended x).observable z - (descended y).observable z‖ ≤ η :=
    (T x).nativeQuotient_observable_sub_norm_le (T y) ideal htopIdeal Q
      (descended x).observable (descended y).observable (hrecOriginal x) (hrecOriginal y) hxy
  refine ⟨descended, horbit, hpositive, fun x y => (hpositive x).norm_le_one y,
    hcomplex, ?_, hrecovery, hcontract, ?_⟩
  · intro x
    let := Q.metricSpace
    apply (descended x).lipschitz.weaken
    change ((descended x).lipBound : ℝ) ≤
      Real.exp ((pDesc + 2) ^ RationalFilteredNilmanifold.nativeInvariantFamilyDescentExponent s)
    unfold RationalFilteredNilmanifold.nativeInvariantFamilyDescentExponent
    have h := (descended x).observable_budget (hcomplex x)
    linarith [(descended x).normBound.coe_nonneg]
  · intro entropy hnet η hη hη1
    obtain ⟨n, hn, rep, hrep⟩ := hnet η hη hη1
    refine ⟨n, hn, rep, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := hrep x hx
    exact ⟨i, hcontract x (rep i).val η hi⟩

end AllocatedExternalCandidateProblem.PrecenterKernelSelection
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
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.PositiveKernelPreparation

variable {cost massThreshold scoreThreshold p : ℝ} {e : ℕ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    (prep : P.PositiveKernelPreparation p e)

theorem exists_native_descended_quotient
    {nMarkedBasis : ℕ} (markBasis : Basis (Fin nMarkedBasis) ℚ M)
    (pBudget : ℝ) (hs : 1 ≤ s) (hpBudget : 0 ≤ pBudget)
    (hD : D.GeometryComplexityLE pBudget) (hmarkDim : (nMarkedBasis : ℝ) ≤ pBudget)
    (hmark : ∀ i j, rationalLogHeight (markBasis.repr (φ (D.basis j)) i) ≤ pBudget)
    (hqBudget : positiveKernelPreparationParameter p ≤ pBudget) :
    (∀ x ∈ prep.nativeQuotientIdeal, φ x = 0) ∧
    ∃ dQ : ℕ, dQ ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ prep.nativeQuotientIdeal) s dQ,
      Q.filtration = D.filtration.quotientLie prep.nativeQuotientIdeal prep.nativeQuotientIdeal_terminal ∧
      Q.lattice = D.lattice.map (D.filtration.quotientStepHom prep.nativeQuotientIdeal prep.nativeQuotientIdeal_terminal) ∧
      Q.GeometryComplexityLE
        ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s) ∧
      (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap prep.nativeQuotientIdeal (D.basis j)) i) ≤
        (pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s) ∧
      (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ prep.nativeQuotientIdeal))
       letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ prep.nativeQuotientIdeal)) :=
         IsModuleTopology.topologicalAddGroup ℝ _
       letI := realification_moduleTopology_t2 Q.basis
       ∃ descended : (X → ℤ) → Q.Niltest (fullTaggedVariableWeight (X := X) J),
         (∀ x, (descended x).UnitIntervalValued) ∧
         (∀ x y, ‖(descended x).observable y‖ ≤ 1) ∧
         (∀ x, (descended x).ComplexityLE
           ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)) ∧
         (∀ x, letI := Q.metricSpace;
           LipschitzWith
             ⟨Real.exp ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s),
               Real.exp_nonneg _⟩ (descended x).observable) ∧
         (∀ x (g : D.RealGroup), (descended x).observable (QuotientGroup.mk
           (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
             (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap prep.nativeQuotientIdeal) g)) =
             (prep.selected.tests x).observable (QuotientGroup.mk g)) ∧
         (∀ x y η, (∀ z, ‖observable x z - observable y z‖ ≤ η) →
           ∀ z, ‖(descended x).observable z - (descended y).observable z‖ ≤ η) ∧
         ∀ entropy : ℝ → ℝ,
           (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ, (n : ℝ) ≤ entropy η ∧
             ∃ rep : Fin n → {x : X → ℤ // x ∈ integerBox N},
               ∀ x ∈ integerBox N, ∃ i, ∀ y,
                 ‖observable x y - observable (rep i).val y‖ ≤ η) →
           ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ, (n : ℝ) ≤ entropy η ∧
             ∃ rep : Fin n → {x : X → ℤ // x ∈ integerBox N},
               ∀ x ∈ integerBox N, ∃ i, ∀ y,
                 ‖(descended x).observable y - (descended (rep i).val).observable y‖ ≤ η) := by
  classical
  let ideal := prep.nativeQuotientIdeal
  let hI := prep.nativeQuotientIdeal_terminal
  have hcode : (finrank ℚ ↥(D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap) : ℝ) ≤ pBudget := by
    let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
    have hdim := Submodule.finrank_le (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap)
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at hdim
    exact (Nat.cast_le.mpr hdim).trans hD.1
  have hkernel : ideal.toSubmodule = frequencyCodeKernel
      (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap) prep.early.eta prep.selected.code :=
    D.filtration.pivotAnnihilatorIdeal_presentPivots_toSubmodule φ prep.early.eta prep.selected.code
  have hker (x : L) (hx : x ∈ ideal) : φ x = 0 := by
    have hx' : x ∈ frequencyCodeKernel
        (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap) prep.early.eta prep.selected.code := by
      rw [← hkernel]
      exact hx
    exact ((mem_frequencyCodeKernel _ _ _ x).mp hx').1.2
  obtain ⟨dQ, hdQ, Q, hQF, hQL, hQ, hmap⟩ :=
    (Classical.choose_spec
      (RationalFilteredNilmanifold.exists_nativePresentPivotQuotient_budget.{0, 0, 0})).2
      D markBasis φ prep.early.eta prep.selected.code pBudget hs hpBudget hD hmarkDim hcode
      hmark (fun i j => (prep.early.eta_height i j).trans hqBudget)
  let pDesc := pBudget + (pBudget + 2) ^
    RationalFilteredNilmanifold.nativePresentPivotQuotientExponent + 1
  have hb := RationalFilteredNilmanifold.positiveKernelNativeDescentBudget_bounds s hpBudget
  refine ⟨hker, dQ, hdQ, Q, hQF, hQL, hQ.mono Q (hb.2.2.1.trans hb.2.2.2.1),
    fun i j => (hmap i j).trans (hb.2.2.1.trans hb.2.2.2.1), ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ ideal))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ ideal)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (L ⧸ ideal)) := realification_moduleTopology_t2 Q.basis
  obtain ⟨descended, _, hunit, hnorm, hcomplex, hLip, hrec, hcontract, hnets⟩ :=
    prep.selected.exists_native_descent ideal hkernel hI Q hQF hQL pDesc hb.2.1
      (hqBudget.trans hb.1) (hQ.mono Q hb.2.2.1)
      (fun i j => (hmap i j).trans hb.2.2.1)
  refine ⟨descended, hunit, hnorm, fun x => (hcomplex x).mono hb.2.2.2.2,
    ?_, hrec, ?_, ?_⟩
  · intro x
    let := Q.metricSpace
    exact (hLip x).weaken (show
      Real.exp ((pDesc + 2) ^ RationalFilteredNilmanifold.nativeInvariantFamilyDescentExponent s) ≤
        Real.exp ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)
      from Real.exp_le_exp.mpr hb.2.2.2.2)
  · intro x y η hxy
    apply hcontract x y η
    simpa only [prep.tests_observable] using hxy
  · intro entropy hnet
    apply hnets entropy
    simpa only [prep.tests_observable] using hnet

end AllocatedExternalCandidateProblem.PositiveKernelPreparation
end Erdos3.VectorPolynomial

end

end OAI
end


