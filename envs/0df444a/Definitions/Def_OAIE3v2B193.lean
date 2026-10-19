-- Prove2me | Definitions.Def_OAIE3v2B193
-- name    : OAIE3v2B193
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:52:37.82963+00:00
-- url     : https://prove2.me/theorems/189f093a-a861-449d-8820-43eb779f3a38
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 196 of 311
-- statement:
--   Definitions bundle 196 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B164`, `OAIE3v2B171`, `OAIE3v2B172`, `OAIE3v2B173`, `OAIE3v2B174`, `OAIE3v2B175`, `OAIE3v2B176` of this split.
--
--   Modules: `Estimates/AllocatedMarkedDictionaryRecovery.lean`, `Estimates/ControlledRefilteredRecoveredExpansion.lean`, `Estimates/ExternalPhysicalMemberPivotMasks.lean`, `Estimates/LowerRefilteredCyclicExpansion.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/NativeFrozenMarkedLocalMark.lean`, `Estimates/NativeMarkedDiagramOrbitLift.lean`, `Estimates/NativeModelOrbit.lean`, `Estimates/NativeOptionFixedSourceQuotientMarkStrong.lean`, `Estimates/NativeSharedFrozenCorrelations.lean`, `Estimates/NativeTwoVariableSplitFreezing.lean`, `Estimates/NormalizedTwistSliceVariationPairCorrelation.lean`, `Estimates/PositiveShiftProductData.lean`, `Estimates/PrescribedPartitionExpansionCore.lean`, `Estimates/PrescribedSquareImagePartition.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Estimates/StrongRefiltrationReconstruction.lean`, `Estimates/UniformFrozenDescent.lean`, `Estimates/UnitVerticalMeanRowCorrelation.lean`, `Lattices/AllocatedOriginalSampleResidueMixtureForecast.lean`, `Lattices/BoundedPrimeResidual.lean`, `Lattices/DenseResidueScalarScoreNet.lean`, `Lattices/RefilteredResidueExpansionSpec.lean`, `Lattices/RelativeSliceAffineThreeFactorLaw.lean`, `Lattices/ResiduePrimeDensityError.lean`, `Lattices/SpatialAffineFullMass.lean`, `Linear/ActualCandidateSlowProjectionMass.lean`, `Linear/FrozenDiagramKernelInvariance.lean`, `Linear/SplitCoverProjection.lean`, `Nilpotent/FrozenComplexNiltest.lean`, `Polynomial/MeasureDegreeZeroTwistTransfer.lean`, `Sampling/ForecastNativePullbackBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B164
import Definitions.Def_OAIE3v2B171
import Definitions.Def_OAIE3v2B172
import Definitions.Def_OAIE3v2B173
import Definitions.Def_OAIE3v2B174
import Definitions.Def_OAIE3v2B175
import Definitions.Def_OAIE3v2B176

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {J : Type v} [Fintype J] {L : Type u} {M : J → Type u} {Y : Type*}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ dQ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  (Q : RationalFilteredNilmanifold
    (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) s dQ)
  (hQ : Q.filtration = D.filtration.quotientLie
    (D.filtration.pivotAnnihilatorIdeal π eta js)
    (by rw [D.filtration.terminal]; exact bot_le))

include hQ

variable (U : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)

variable {κ κQ : Type*}
  (e : Basis κ ℚ (∀ i : Option J, optionLieSpace L M i)) (μ : κ → ℕ)
  (hSource : ∀ k, (optionProduct D E).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (c : Basis κQ ℚ (∀ i : Option J,
    optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i))
  (ν : κQ → ℕ)
  (hTarget : ∀ k, (optionProduct Q E).filtration.layer k =
    Submodule.span ℚ (c '' {i | k ≤ ν i}))
  (hU : BasisGradedSubmodule
    ((optionProduct D E).filtration.associatedGradedBasis e μ hSource) μ U.toSubmodule)

include e μ hSource c ν hTarget hU in

theorem optionNativeCommonPivotQuotientFast_layer_eq (k : ℕ) :
    (optionProduct Q E).filtration.gradedRefiltrationLayer
      (optionNativeCommonPivotQuotientFast D E π eta js Q hQ U) k =
    ((optionProduct D E).filtration.gradedRefiltrationLayer U k).map
      (optionMarkedLieMap (L := M)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js))).toLinearMap := by
  symm
  exact (optionProduct D E).filtration.gradedRefiltrationLayer_map
    (optionProduct Q E).filtration e μ hSource c ν hTarget
    (optionMarkedLieMap (L := M)
      (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)))
    (optionNativePivotQuotientMap_mem_layer D E π eta js Q hQ) U hU
    (optionNativePivotQuotientMap_layer_surjective D E π eta js Q hQ) k

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ExternalPhysicalMemberPivotMasks
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {L σ I : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d)

theorem externalNetNiltest_complexity
    (f : D.Space → ℂ) (K : ℝ≥0)
    (hcap : ∀ x, ‖f x‖ ≤ 1) (hLip : letI := D.metricSpace; LipschitzWith K f)
    {w : σ → ℕ} (orbit : D.filtration.realification.PolynomialOrbit w)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hK : (K : ℝ) ≤ Real.exp p) :
    (D.externalNetNiltest f K hcap hLip orbit).ComplexityLE (p + 3) := by
  refine ⟨hD.mono D (by linarith), ?_⟩
  change Real.log (2 + (1 : ℝ) + (K : ℝ)) ≤ p + 3
  apply (Real.log_le_iff_le_exp (by positivity)).2
  have he : 1 ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
  have hthree : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    2 + 1 + (K : ℝ) ≤ 4 * Real.exp p := by linarith
    _ ≤ Real.exp 3 * Real.exp p := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg p)
    _ = Real.exp (p + 3) := by rw [← Real.exp_add, add_comm]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedDiagramOrbitLift
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)

variable (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

theorem topQuotientMarkedOrbit_eq_iff (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w) :
    D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked ↔
      map (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (D.filtration.layerIdeal (s + 1))
          (E.filtration.layerIdeal (s + 1)) φ (hφ (s + 1))))).toLinearMap q.log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (E.filtration.layerIdeal (s + 1))))).toLinearMap marked.log := by
  constructor
  · intro h
    exact congrArg (fun p => p.log) h
  · intro h
    exact Subtype.ext (NilpotentLieBCHGroup.ext h)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SplitCoverProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : Option ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (V : RationalFilteredNilmanifold (∀ i, L i) s (Fintype.card (Σ i, Fin (d i))))
  (hsub : (pi D).lattice ≤ V.lattice)

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [T2Space (ℝ ⊗[ℚ] (∀ i, L (some i)))]

theorem splitCoverProjection_lipschitz (hb : (pi D).basis = V.basis) :
    letI := (D none).metricSpace
    letI := (pi (fun i => D (some i))).metricSpace
    letI := V.metricSpace
    LipschitzWith ((1 + productMetricBound (fun i => d (some i))) * productMetricBound d)
      (splitCoverProjection D V hsub) := by
  let := (D none).metricSpace
  let := (pi (fun i => D (some i))).metricSpace
  let := (pi D).metricSpace
  let := V.metricSpace
  simpa only [one_mul, splitCoverProjection] using
    (sublatticeProjection_lipschitz V (pi D) hsub hb).comp (optionProductSpaceEquiv_symm_lipschitz D)

theorem splitCoverProjection_pullback (hb : (pi D).basis = V.basis)
    (u : V.Space → ℂ) {K : ℝ≥0} (hu : letI := V.metricSpace; LipschitzWith K u)
    (hpositive : ∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) :
    letI := (D none).metricSpace
    letI := (pi (fun i => D (some i))).metricSpace
    let v := u ∘ splitCoverProjection D V hsub
    LipschitzWith (K * ((1 + productMetricBound (fun i => d (some i))) * productMetricBound d)) v ∧
      (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
      ∀ x : (pi D).RealGroup, v (optionProductSpaceEquiv D (QuotientGroup.mk x)) =
        u (QuotientGroup.mk x) := by
  let := (D none).metricSpace
  let := (pi (fun i => D (some i))).metricSpace
  let := V.metricSpace
  exact ⟨hu.comp (splitCoverProjection_lipschitz D V hsub hb),
    fun x => hpositive _, fun x => congrArg u (splitCoverProjection_mk D V hsub x)⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionFixedSourceQuotientMarkStrong
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

theorem exists_adapted_model_data (D : RationalFilteredNilmanifold L s d)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ F : D.AdaptedModelData, F.model.GeometryComplexityLE ((p + 3) ^ 11) ∧
      ∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ p + 1 := by
  obtain ⟨b, w, N, _, _, hlayers, hb, _, hc, hN, hNp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let F : D.AdaptedModelData := ⟨b, w, hlayers, N, hN, hin, hout⟩
  have hp1 : 1 ≤ p + 3 := by linarith
  have hpow : p ≤ (p + 3) ^ 11 := by
    calc
      p ≤ p + 3 := by linarith
      _ = (p + 3) ^ 1 := (pow_one _).symm
      _ ≤ (p + 3) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have hdim : (finrank ℚ L : ℝ) ≤ (p + 3) ^ 11 := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hD.1.trans hpow
  refine ⟨F, ?_, hb⟩
  exact D.filtration.ofAdaptedBasis_geometry b w hlayers D.lattice N hN hin hout
    (by positivity) hdim
    (hNp.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hp1 (by decide : 9 ≤ 11)))) hc

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_prescribed_adapted_model {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d n : ℕ} (D : RationalFilteredNilmanifold L s d)
    (b : Basis (Fin n) ℚ L) (ω : Fin n → ℕ)
    (hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hb : ∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) :
    ∃ (M : ℕ) (hM : 0 < M)
      (hin : scaledIntegerGrid M ⊆ bchSubgroupCoordinates b D.lattice)
      (hout : bchSubgroupCoordinates b D.lattice ⊆ denominatorGrid M),
      (D.filtration.ofAdaptedBasis b ω hF D.lattice M hM hin hout).GeometryComplexityLE
        ((p + 4) ^ 11) := by
  obtain ⟨hdim, _hinverse, hstructure⟩ := D.basis_geometry_of_forward_height b hp hD hb
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp (p + 1)
  have hHp : (H : ℝ) ≤ Real.exp (p + 2) := by
    simpa only [show p + 1 + 1 = p + 2 by ring] using
      ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)
  have hentries : ∀ i j, RationalHeightLE (D.basis.repr (b i) j) H :=
    fun i j => rationalHeightLE_ceil_exp (hb i j)
  have hd : (Fintype.card (Fin d) : ℝ) ≤ p + 2 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 2 by linarith)
  obtain ⟨M, hM, hMp, hin, hout⟩ := exists_basis_change_grid_exp_bound D.basis b D.lattice
    hH D.grid_pos hentries D.inner_grid D.outer_grid (by linarith : 0 ≤ p + 2) hd
    (hdim.trans (by linarith)) hHp (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hbase : 1 ≤ p + 4 := by linarith
  have hpbig : p ≤ (p + 4) ^ 11 := by
    apply (show p ≤ p + 4 by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 11)
  have hgrid : (M : ℝ) ≤ Real.exp ((p + 4) ^ 11) := by
    have hsmall : (M : ℝ) ≤ Real.exp ((p + 4) ^ 9) := by
      simpa only [show p + 2 + 2 = p + 4 by ring] using hMp
    exact hsmall.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 9 ≤ 11)))
  refine ⟨M, hM, hin, hout, ?_⟩
  exact D.filtration.ofAdaptedBasis_geometry b ω hF D.lattice M hM hin hout
    (by positivity) (by simpa only [Fintype.card_fin] using hdim.trans hpbig) hgrid hstructure

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {Partner : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ a, LieRing (Partner a)] [∀ a, LieAlgebra ℚ (Partner a)]
    {s d f dQ : ℕ} {dp : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (Mmark : RationalFilteredNilmanifold M s f)
    (ideal : LieIdeal ℚ L)
    (hkill : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hkill)
    (atoms : ∀ a, RationalFilteredNilmanifold (Partner a) s (dp a))
    (φ : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ ideal, φ x = 0)
    (hφ : ∀ k, ∀ x ∈ D.filtration.layer k, φ x ∈ Mmark.filtration.layer k)
    (source : (optionProduct Q atoms).AdaptedModelData)

include hQ hφ in

theorem nativeOptionFixedSourceQuotientMark_mem_layer
    (k : ℕ) (x : ∀ i : Option Pivot, optionLieSpace (L ⧸ ideal) Partner i)
    (hx : x ∈ source.model.filtration.layer k) :
    optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker) x ∈
      (NilpotentLieFiltration.pi
        (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration))).layer k := by
  have hinduced : ∀ k, ∀ y ∈ Q.filtration.layer k,
      quotientInducedMark ideal φ hker y ∈ Mmark.filtration.layer k := by
    intro k y hy
    rw [hQ] at hy
    exact D.filtration.quotientInducedMark_mem_layer Mmark.filtration
      ideal hkill φ hker hφ k y hy
  have hfiltration : (fun i => (optionFactors Q atoms i).filtration) =
      optionFiltrations Q.filtration (fun a => (atoms a).filtration) := by
    funext i
    cases i <;> rfl
  change x ∈ (NilpotentLieFiltration.pi (fun i => (optionFactors Q atoms i).filtration)).layer k at hx
  rw [hfiltration] at hx
  exact optionMarkedLieMap_mem_layer Q.filtration Mmark.filtration
    (fun a => (atoms a).filtration) (quotientInducedMark ideal φ hker) hinduced k x hx

theorem optionAdaptedModel_layers
    (target : (optionProduct Mmark atoms).AdaptedModelData) (k : ℕ) :
    (NilpotentLieFiltration.pi
      (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration))).layer k =
      Submodule.span ℚ (target.basis '' {i | k ≤ target.weight i}) := by
  have hfiltration : (fun i => (optionFactors Mmark atoms i).filtration) =
      optionFiltrations Mmark.filtration (fun a => (atoms a).filtration) := by
    funext i
    cases i <;> rfl
  have hlayers := target.layers k
  change (NilpotentLieFiltration.pi (fun i => (optionFactors Mmark atoms i).filtration)).layer k =
    Submodule.span ℚ (target.basis '' {i | k ≤ target.weight i}) at hlayers
  rw [hfiltration] at hlayers
  exact hlayers

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {Partner : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ a, LieRing (Partner a)] [∀ a, LieAlgebra ℚ (Partner a)]
    {s d f dQ : ℕ} {dp : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (Mmark : RationalFilteredNilmanifold M s f)
    (ideal : LieIdeal ℚ L)
    (hkill : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hkill)
    (atoms : ∀ a, RationalFilteredNilmanifold (Partner a) s (dp a))
    (φ : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ ideal, φ x = 0)
    (source : (optionProduct Q atoms).AdaptedModelData)
    (hsurj : ∀ k, ∀ y ∈ Mmark.filtration.layer k,
      ∃ x ∈ D.filtration.layer k, φ x = y)

include hQ hsurj in

theorem nativeOptionFixedSourceQuotientMark_layer_surjective
    (k : ℕ) (y : ∀ i : Option Pivot, optionLieSpace M Partner i)
    (hy : y ∈ (NilpotentLieFiltration.pi
      (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration))).layer k) :
    ∃ x ∈ source.model.filtration.layer k,
      optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker) x = y := by
  have hcoord := (mem_pi_layer
    (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration)) k y).mp hy
  obtain ⟨x₀, hx₀, hxy₀⟩ := hsurj k (y none) (hcoord none)
  let x : ∀ i : Option Pivot, optionLieSpace (L ⧸ ideal) Partner i
    | none => lieQuotientMap ideal x₀
    | some a => y (some a)
  refine ⟨x, ?_, ?_⟩
  · change x ∈ (NilpotentLieFiltration.pi
      (fun i => (optionFactors Q atoms i).filtration)).layer k
    apply (mem_pi_layer (fun i => (optionFactors Q atoms i).filtration) k x).mpr
    intro i
    cases i with
    | none =>
      change lieQuotientMap ideal x₀ ∈ Q.filtration.layer k
      rw [hQ]
      exact ⟨x₀, hx₀, rfl⟩
    | some a => exact hcoord (some a)
  · funext i
    cases i with
    | none => exact hxy₀
    | some a => rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSharedFrozenCorrelations
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
  (φ : L →ₗ⁅ℚ⁆ M) (a r : E.RealGroup)
  (h : ∀ γ ∈ D.realLattice,
    r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)

include h in
theorem exists_positive_frozen_observable {A C ℓ : ℝ≥0}
    (hφ : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith C (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    (ha : letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith A (fun x => a * x))
    (u : E.Space → ℂ) (hu : letI := E.metricSpace; LipschitzWith ℓ u)
    (hunit : ∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) :
    ∃ v : D.Space → ℂ,
      (letI := D.metricSpace; LipschitzWith (ℓ * (A * C)) v) ∧
      (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
      ∀ x : D.RealGroup, v (QuotientGroup.mk x) = u (QuotientGroup.mk
        (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r)) := by
  let := D.metricSpace
  let := E.metricSpace
  let f := frozenCosetMap D.realLattice E.realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h
  have hf : LipschitzWith (A * C) f := D.lipschitz_native_frozenCosetMap E φ a r h hφ ha
  refine ⟨u ∘ f, hu.comp hf, fun x => hunit (f x), ?_, fun _ => rfl⟩
  intro x
  change ‖u (f x)‖ ≤ 1
  rw [← positiveClip_eq_self (u (f x)) (hunit (f x))]
  exact norm_positiveClip_le_one _

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FrozenComplexNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
  (φ : L →ₗ⁅ℚ⁆ M) (a r : E.RealGroup)
  (h : ∀ γ ∈ D.realLattice,
    r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)
  {w : σ → ℕ} (T : E.Niltest w) (g : D.filtration.realification.PolynomialOrbit w)
  (K : ℝ≥0)
  (hK : letI := D.metricSpace
    letI := E.metricSpace
    LipschitzWith K (frozenCosetMap D.realLattice E.realLattice
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h))

theorem frozenComplexNiltest_complexity {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hD : D.GeometryComplexityLE q) (hT : T.ComplexityLE p)
    (hbound : (K : ℝ) ≤ Real.exp q) :
    (D.frozenComplexNiltest E φ a r h T g K hK).ComplexityLE (p + q + 4) := by
  have hb := T.observable_budget hT
  have hnorm : (T.normBound : ℝ) ≤ Real.exp (p + q) :=
    (by linarith [T.lipBound.coe_nonneg] : (T.normBound : ℝ) ≤ Real.exp p).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hlip : (T.lipBound : ℝ) * K ≤ Real.exp (p + q) := by
    rw [Real.exp_add]
    exact mul_le_mul (by linarith [T.normBound.coe_nonneg]) hbound K.coe_nonneg (Real.exp_pos _).le
  refine ⟨hD.mono D (by linarith), ?_⟩
  change Real.log (2 + (T.normBound : ℝ) + ((T.lipBound * K : ℝ≥0) : ℝ)) ≤ p + q + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    _ ≤ 4 * Real.exp (p + q) := by
      simp only [NNReal.coe_mul]
      linarith [Real.one_le_exp (show 0 ≤ p + q by linarith)]
    _ ≤ Real.exp 4 * Real.exp (p + q) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem frozenComplexNiltest_top_invariant
    (hinv : ∀ z ∈ D.filtration.realification.subgroup s, ∀ x : D.RealGroup,
      T.observable (QuotientGroup.mk
        (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r)) =
      T.observable (QuotientGroup.mk
        (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r)))
    (z : D.RealGroup) (hz : z ∈ D.filtration.realification.subgroup s) (x : D.Space) :
    (D.frozenComplexNiltest E φ a r h T g K hK).observable (z • x) =
      (D.frozenComplexNiltest E φ a r h T g K hK).observable x := by
  induction x using Quotient.inductionOn with
  | h x => exact hinv z hz x

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFrozenDescent
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem exists_controlled_top_subspace_quotient
    {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (vK : κ → K) (hspanK : Submodule.span ℚ (Set.range vK) = ⊤)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hvK : ∀ j i, rationalLogHeight (D.basis.repr (vK j : L) i) ≤ p) :
    let I := D.filtration.topSubspaceIdeal K hK
    let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by rw [D.filtration.terminal]; exact bot_le
    ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
      Q.filtration = D.filtration.quotientLie I hI ∧
      Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
      Q.GeometryComplexityLE ((p + 3) ^ 11) ∧
      ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis i)) j) ≤ (p + 3) ^ 5 := by
  classical
  intro I hI
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  obtain ⟨b, w, S, hw, hcentral, hb, hlayers, hKS⟩ :=
    D.filtration.exists_bounded_adapted_basis_with_top_subspace hs D.basis
      (fun i => D.layerBasis i) (fun i => (D.layerBasis i).span_eq) K hK vK hspanK
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.2 i j k))
      (fun j i => rationalHeightLE_ceil_exp (hvK j i))
  have hdim : finrank ℚ L = d := by simpa only [Fintype.card_fin] using finrank_eq_card_basis D.basis
  have hd : (Fintype.card (Fin d) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith)
  have hr : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p + 1 := by simpa only [hdim] using hd
  obtain ⟨N, hN, hNp, hin, hout⟩ := exists_basis_change_grid_exp_bound D.basis b D.lattice
    hH D.grid_pos hb D.inner_grid D.outer_grid (by linarith : 0 ≤ p + 1) hd hr hHp
    (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hbinv := inverse_basis_entries_height D.basis b hH hb
  have hc := basis_change_structure_height D.basis b hH hb
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
  have hcb := rationalLieStructureHeight_inverse_budget (Fintype.card (Fin d))
    (Fintype.card (Fin (finrank ℚ L))) H (by linarith : 0 ≤ p + 1) hd hr hHp
  have hsolve := rationalSolveHeight_le_budget (Fintype.card (Fin (finrank ℚ L))) H
    (by linarith : 0 ≤ p + 1) hr hHp
  have hspanI : I.toSubmodule = Submodule.span ℚ (b '' S) := hKS
  let Q := D.filtration.coordinateQuotientModel b w hlayers I hI S hspanI D.lattice N hN hin hout
  have hbig : p + 1 ≤ (p + 3) ^ 11 := by
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      le_power_budget (by linarith : 0 ≤ p + 1) (by decide : 1 ≤ 11)
  have hgeometry : Q.GeometryComplexityLE ((p + 3) ^ 11) := by
    apply D.filtration.coordinateQuotientModel_geometry b w hlayers I hI S hspanI
      D.lattice N hN hin hout (by positivity) (hr.trans hbig)
    · apply hNp.trans (Real.exp_le_exp.mpr ?_)
      rw [show p + 1 + 2 = p + 3 by ring]
      exact pow_le_pow_right₀ (by linarith : 1 ≤ p + 3) (by decide : 9 ≤ 11)
    · intro i j k
      apply rationalLogHeight_le_of_height (hc i j k)
      simpa only [show p + 1 + 2 = p + 3 by ring] using hcb
  refine ⟨_, ?_, Q, rfl, rfl, hgeometry, ?_⟩
  · simpa only [Fintype.card_fin, hdim] using Fintype.card_subtype_le (fun i => i ∉ S)
  · intro i j
    have hcoord := quotientFinBasis_repr_mk b I S hspanI (D.basis i) j
    change rationalLogHeight ((quotientFinBasis b I S hspanI).repr (lieQuotientMap I (D.basis i)) j) ≤ _
    rw [hcoord]
    apply rationalLogHeight_le_of_height (hbinv i _)
    simpa only [show p + 1 + 2 = p + 3 by ring] using hsolve

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeModelOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s d)

noncomputable def nativeModelEquivOfCoordinates
    (h : D.rationalModelCoordinates = E.rationalModelCoordinates) (B : ℕ)
    (hD : bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B)
    (hE : bchSubgroupCoordinates E.basis E.lattice = scaledIntegerGrid B) : NativeModelEquiv D E where
  toLieEquiv := D.rationalModelEquiv E h
  map_basis := D.rationalModelEquiv_basis E h
  mem_layer n x := D.rationalModelGroupEquiv_mem_layer E h n ⟨x⟩
  mem_lattice := D.rationalModelGroupEquiv_mem_integral_lattice E h D.lattice E.lattice B hD hE

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftProductData
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold

variable {J σ : Type*} {L : Option (Option J ⊕ J) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : Option (Option J ⊕ J) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)} {w : σ → ℕ}

noncomputable def anchoredOptionObservableData
    (U : J → (D none).Niltest w) (V : J → (D (some (.inl none))).Niltest w)
    (A : ∀ j, (D (some (.inl (some j)))).Niltest w) (B : ∀ j, (D (some (.inr j))).Niltest w)
    (j : J) : ∀ i, (D i).Niltest w
  | none => U j
  | some (.inl none) => (V j).conjugate
  | some (.inl (some k)) => A k
  | some (.inr k) => B k

noncomputable def anchoredOptionFrequencyData
    (eta : J → L none →ₗ[ℚ] ℚ) (theta : J → L (some (.inl none)) →ₗ[ℚ] ℚ)
    (alpha : ∀ j, L (some (.inl (some j))) →ₗ[ℚ] ℚ)
    (beta : ∀ j, L (some (.inr j)) →ₗ[ℚ] ℚ) (j : J) : ∀ i, L i →ₗ[ℚ] ℚ
  | none => eta j
  | some (.inl none) => -theta j
  | some (.inl (some k)) => alpha k
  | some (.inr k) => beta k

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerRefilteredCyclicExpansion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_native_positive_reconstruction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (E.realLattice ⊓ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ).range ≤
        D.realLattice.map (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ)) →
      ∀ (u : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
      (letI := D.metricSpace; LipschitzWith ℓ u) →
      (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
      (∀ k ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ).ker, ∀ x,
        u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x)) →
      ∃ (v : E.Space → ℂ) (K : ℝ≥0),
        (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := E.metricSpace; LipschitzWith K v) ∧
        (∀ y, (v y).im = 0 ∧ 0 ≤ (v y).re ∧ (v y).re ≤ 1) ∧ (∀ y, ‖v y‖ ≤ 1) ∧
        ∀ x, v (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨c, _, hrec⟩ := exists_controlled_rational_image_reconstruction s
  let P : Polynomial ℕ := (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ hcover u ℓ hℓ hu hunit hker
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHt : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have ht : 0 ≤ p + 1 := add_nonneg hp zero_le_one
  have hpt : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have hexp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr hpt
  have hub : ∀ x, ‖u x‖ ≤ (1 : ℝ≥0) := by
    intro x
    rw [← positiveClip_eq_self (u x) (hunit x)]
    exact norm_positiveClip_le_one _
  let := E.metricSpace
  obtain ⟨v, K, hK, hv, _, heval⟩ := hrec D.filtration.lowerCentralSeries_eq_bot
    E.filtration.lowerCentralSeries_eq_bot D.basis E.basis φ D.lattice E.lattice
    D.grid E.grid H D.grid_pos E.grid_pos hH D.outer_grid E.inner_grid E.outer_grid
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
    (fun i j => rationalHeightLE_ceil_exp (hφ i j)) hcover u hker ℓ 1 hu hub
    (p + 1) ht
    (by simpa only [Fintype.card_fin] using hD.1.trans hpt)
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt)
    hHt (hE.2.1.trans hexp) (hℓ.trans hexp) (by simpa only [NNReal.coe_one] using Real.one_le_exp ht)
  obtain ⟨v', hv', hunit', hcap', heval'⟩ := exists_positive_lipschitz_reconstruction
    (fun x : D.RealGroup => u (QuotientGroup.mk x)) (fun x => hunit (QuotientGroup.mk x))
    (fun x => (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ x) : E.Space)) v hv heval
  have hcost : (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨v', K, hK.trans (Real.exp_le_exp.mpr hcost), hv', hunit', hcap', heval'⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_uniform_native_positive_reconstruction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup E.filtration.Group,
        Λ ≤ E.lattice ∧ (Λ.subgroupOf E.lattice).Characteristic ∧
        (Λ.subgroupOf E.lattice).Normal ∧ (Λ.subgroupOf E.lattice).FiniteIndex ∧
        (Λ.relIndex E.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates E.basis Λ)
          (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid N),
          let Q := E.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ (u : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
            (letI := D.metricSpace; LipschitzWith ℓ u) →
            (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
            (∀ k ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := E.filtration.lowerCentralSeries_eq_bot) φ).ker, ∀ x,
              u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x)) →
            ∃ (v : Q.Space → ℂ) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := Q.metricSpace; LipschitzWith K v) ∧
              (∀ y, (v y).im = 0 ∧ 0 ≤ (v y).re ∧ (v y).re ≤ 1) ∧ (∀ y, ‖v y‖ ≤ 1) ∧
              ∀ x, v (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨a, _, hcover⟩ := exists_native_image_cover s
  obtain ⟨b, _, hrec⟩ := exists_native_positive_reconstruction s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C a) ^ a
  let P := Q + (Q + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hidx, N, hN, hin, hout, hQ, hLift⟩ :=
    hcover D E φ hp hD hE hφ
  let q := p + (p + a) ^ a
  have hpq : p ≤ q := le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg a)) _)
  have hq : 0 ≤ q := hp.trans hpq
  have hBq : (p + a) ^ a ≤ q := le_add_of_nonneg_left hp
  have hbound : q + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hq (Nat.cast_nonneg b)) _)).trans hbound
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans hbound
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite,
    hidx.trans (Real.exp_le_exp.mpr (hBq.trans hqC)), N, hN, hin, hout,
    hQ.mono _ (hBq.trans hqC), ?_⟩
  intro u ℓ hℓ hu hunit hker
  obtain ⟨v, K, hK, hv, hunit', hcap, heval⟩ := hrec D (E.withLattice Λ N hN hin hout) φ hq
    (hD.mono D hpq) (hQ.mono _ hBq) (fun i j => (hφ i j).trans hpq) hLift
    u ℓ (hℓ.trans (Real.exp_le_exp.mpr hpq)) hu hunit hker
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv, hunit', hcap, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RefilteredResidueExpansionSpec
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def RefilteredResidueExpansionSpec
    (p : ℝ) (q r P : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
    Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
    Q'.GeometryComplexityLE cost ∧
    ∃ Z : RationalFilteredNilmanifold (∀ i : I₀, L i.val) (s + 1)
        (Fintype.card (Σ i : I₀, Fin (d i.val))),
      Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
      Z.GeometryComplexityLE cost ∧
      letI := Z.metricSpace
      let w := fun _ : Unit => 1
      let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
      let ψ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := Z.filtration.lowerCentralSeries_eq_bot)
        (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
      ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
        (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
          realifyFunctional (piFrequency (freq j)) x = 0) →
        ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
          (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (label : I → ZMod P) {ρ η : ℝ},
          0 < ρ → 0 ≤ η →
          (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
          (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
          (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
          (∀ i x y, 0 < A i x → 0 < A i y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
          ∀ (S : ZMod N → (D a).Niltest w),
            (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
            (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
              (∀ j, realifyFunctional (freq j a) z.coord = 0) →
              ∀ x, (S h).observable (z • x) = (S h).observable x) →
            ∀ (slow middle rat : ZMod N → ((D a).filtration.realification.adaptedPolynomialFiltration w).Group)
              (κ : ZMod N → (D a).RealGroup)
              (g : ZMod N → E.filtration.realification.PolynomialOrbit w),
              (∀ h, κ h ∈ (D a).realLattice) →
              (∀ h, slow h * middle h * rat h * (D a).filtration.realification.adaptedConstantGroupHom w (κ h) =
                ⟨⟨(S h).orbit.log, (S h).orbit.property⟩⟩) →
              (∀ h, (D a).filtration.PolynomialSlowBound (D a).basis w
                (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
              (∀ h, (D a).filtration.PolynomialRationalGrid (D a).basis w q (rat h)) →
              (∀ h x, (D a).filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (middle h) =
                φ (E.filtration.realification.polynomialOrbitEval w x (g h))) →
              (∀ i j h x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                dist (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
                  (fun _ => (x.val : ℤ)) (g h))) : Z.Space)
                  (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
                    (fun _ => (y.val : ℤ)) (g h)))) ≤ η) →
              ∃ U : I → J → ZMod N → Q'.Niltest w,
                (∀ i j h, (U i j h).UnitIntervalValued) ∧
                (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                  ∀ x, (U i j h).eval x = 0) ∧
                ∃ err : ZMod N → ZMod N → ℝ,
                  (∀ h x, ((S h).evalCyclic N (fun _ => x)).re =
                    (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                  ∀ h, (𝔼 x, |err h x|) ≤ Real.exp cost * (ρ + η) + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FrozenDiagramKernelInvariance
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold

open NilpotentLieBCHGroup

theorem frozenDiagramKernelInvariance_of_injective
    {H L M : Type*} [LieRing H] [LieAlgebra ℚ H]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t r d e f : ℕ}
    (D : RationalFilteredNilmanifold H s d)
    (E : RationalFilteredNilmanifold L t e)
    (T : RationalFilteredNilmanifold M r f)
    (φ : H →ₗ⁅ℚ⁆ L) (ψ : H →ₗ⁅ℚ⁆ M) (hψ : Function.Injective ψ)
    (u : E.Space → ℂ) (a b : E.RealGroup) :
    ∀ z ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := T.filtration.lowerCentralSeries_eq_bot) ψ).ker, ∀ x : D.RealGroup,
      u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * b)) =
      u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * b)) := by
  intro z hz x
  have hz1 : z = 1 := realificationMap_injective ψ hψ
    ((MonoidHom.mem_ker.mp hz).trans (map_one _).symm)
  rw [hz1, one_mul]

end RationalFilteredNilmanifold

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedMarkedDictionaryRecovery
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)
  (Λ : Subgroup (D.raiseStep hst).filtration.Group) (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)

theorem loweredCoverMap_mk (x : (D.loweredCover hst Λ N hN hin hout).RealGroup) :
    D.loweredCoverMap hst Λ N hN hin hout (QuotientGroup.mk x) =
      QuotientGroup.mk (changeStep D.filtration.realification.lowerCentralSeries_eq_bot
        (D.raiseStep hst).filtration.realification.lowerCentralSeries_eq_bot x) := by
  change QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L) x) = _
  rw [realificationMap_id_eq_changeStep]

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem loweredCoverMap_lipschitz :
    letI := (D.loweredCover hst Λ N hN hin hout).metricSpace
    letI := ((D.raiseStep hst).withLattice Λ N hN hin hout).metricSpace
    LipschitzWith 1 (D.loweredCoverMap hst Λ N hN hin hout) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := (D.raiseStep hst).filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := (D.raiseStep hst).filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have hLip : LipschitzWith 1
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
    rw [realificationMap_id_eq_changeStep]
    exact lipschitz_changeStep (D.basis.baseChange ℝ) _ _
  exact lipschitz_cosetMap (D.loweredCover hst Λ N hN hin hout).realLattice
    ((D.raiseStep hst).withLattice Λ N hN hin hout).realLattice
    (D.loweredCover hst Λ N hN hin hout).realLattice_closed_discrete.1
    ((D.raiseStep hst).withLattice Λ N hN hin hout).realLattice_closed_discrete.1
    _ _ hLip

end Metric

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L Z : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)
  (Λ : Subgroup (D.raiseStep hst).filtration.Group) (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
  (v : ((D.raiseStep hst).withLattice Λ N hN hin hout).Space × Z → ℂ)

theorem loweredCoverPullback_mk (x : D.RealGroup) (z : Z) :
    D.loweredCoverPullback hst Λ N hN hin hout v (QuotientGroup.mk x, z) =
      v (QuotientGroup.mk (changeStep D.filtration.realification.lowerCentralSeries_eq_bot
        (D.raiseStep hst).filtration.realification.lowerCentralSeries_eq_bot x), z) := by
  unfold loweredCoverPullback
  rw [D.loweredCoverMap_mk]

theorem loweredCoverPullback_bounds
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] [PseudoMetricSpace Z]
    {K : ℝ≥0}
    (hv : letI := ((D.raiseStep hst).withLattice Λ N hN hin hout).metricSpace; LipschitzWith K v)
    (hpositive : ∀ y, (v y).im = 0 ∧ 0 ≤ (v y).re ∧ (v y).re ≤ 1) :
    letI := (D.loweredCover hst Λ N hN hin hout).metricSpace
    LipschitzWith K (D.loweredCoverPullback hst Λ N hN hin hout v) ∧
      ∀ y, (D.loweredCoverPullback hst Λ N hN hin hout v y).im = 0 ∧
        0 ≤ (D.loweredCoverPullback hst Λ N hN hin hout v y).re ∧
        (D.loweredCoverPullback hst Λ N hN hin hout v y).re ≤ 1 := by
  let := (D.loweredCover hst Λ N hN hin hout).metricSpace
  let := ((D.raiseStep hst).withLattice Λ N hN hin hout).metricSpace
  have hm := ((D.loweredCoverMap_lipschitz hst Λ N hN hin hout).comp
    (LipschitzWith.prod_fst (β := Z))).prodMk
      (LipschitzWith.prod_snd (α := (D.loweredCover hst Λ N hN hin hout).Space))
  have hpair : LipschitzWith 1 (fun y : (D.loweredCover hst Λ N hN hin hout).Space × Z =>
      (D.loweredCoverMap hst Λ N hN hin hout y.1, y.2)) := by
    simpa only [mul_one, max_self, Function.comp_def] using hm
  refine ⟨?_, fun y => hpositive _⟩
  unfold loweredCoverPullback
  simpa only [mul_one, Function.comp_def] using hv.comp hpair

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_split_reconstruction_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L (some i)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L (some i)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L (some i)))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, L (some i)))]
      {s : ℕ} {d : Option ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (Λ : Subgroup (pi D).filtration.Group) (m : ℕ) (hm : 0 < m)
      (hΛin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (pi D).basis Λ)
      (hΛout : bchSubgroupCoordinates (pi D).basis Λ ⊆ denominatorGrid m)
      {p : ℝ}, 0 ≤ p → (Fintype.card (Option ι) : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (m : ℝ) ≤ Real.exp p →
      ∃ (Δ : ∀ i, Subgroup (D i).filtration.Group) (N : Option ι → ℕ)
        (hN : ∀ i, 0 < N i)
        (hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (D i).basis (Δ i))
        (hout : ∀ i, bchSubgroupCoordinates (D i).basis (Δ i) ⊆ denominatorGrid (N i)),
        let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
        ∃ _hsub : (pi E).lattice ≤ Λ,
          (∀ i, Δ i ≤ (D i).lattice ∧ ((Δ i).subgroupOf (D i).lattice).Characteristic ∧
            ((Δ i).subgroupOf (D i).lattice).Normal ∧ ((Δ i).subgroupOf (D i).lattice).FiniteIndex ∧
            ((Δ i).relIndex (D i).lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
          (pi E).GeometryComplexityLE ((p + C) ^ C) ∧
          (pi (fun i => E (some i))).GeometryComplexityLE ((p + C) ^ C) ∧
          let V := (pi D).withLattice Λ m hm hΛin hΛout
          ∀ (u : V.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
            (letI := V.metricSpace; LipschitzWith ℓ u) →
            (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
            ∃ (v : (E none).Space × (pi (fun i => E (some i))).Space → ℂ) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (letI := (E none).metricSpace
               letI := (pi (fun i => E (some i))).metricSpace
               LipschitzWith K v) ∧
              (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
              ∀ x : (pi E).RealGroup,
                v (optionProductSpaceEquiv E (QuotientGroup.mk x)) = u (QuotientGroup.mk x) := by
  obtain ⟨A, _, hcover⟩ := exists_native_factorwise_covers
  obtain ⟨B, _, hmetric⟩ := exists_optionProductMetric_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  let P := T + (T + 2) ^ 2 + X + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ s d D Λ m hm hΛin hΛout p hp hι hD hmp
  obtain ⟨Δ, N, hN, hin, hout, hindex, hE, hprod, hsub⟩ :=
    hcover D Λ m hm hΛin hp hι hD hmp
  let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  let V := (pi D).withLattice Λ m hm hΛin hΛout
  let t := p + (p + A) ^ A
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hsum : t + (t + 2) ^ 2 + p + (p + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htc : t ≤ (p + C) ^ C := by
    nlinarith [sq_nonneg (t + 2), pow_nonneg (show 0 ≤ p + B by positivity) B]
  have hrestc : (t + 2) ^ 2 ≤ (p + C) ^ C := by
    nlinarith [pow_nonneg (show 0 ≤ p + B by positivity) B]
  have hlipc : p + (p + B) ^ B ≤ (p + C) ^ C := by
    nlinarith [sq_nonneg (t + 2)]
  have hι' : (Fintype.card ι : ℝ) ≤ t := by
    simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one] at hι
    linarith
  have hrest := pi_geometry (fun i => E (some i)) (hp.trans hpt) hι'
    (fun i => (hE (some i)).mono _ hAt)
  refine ⟨Δ, N, hN, hin, hout, hsub, ?_, fun i => (hE i).mono _ (hAt.trans htc),
    hprod.mono _ (hAt.trans htc), hrest.mono _ hrestc, ?_⟩
  · intro i
    obtain ⟨hle, hc, hn, hf, hi⟩ := hindex i
    exact ⟨hle, hc, hn, hf, hi.trans (Real.exp_le_exp.mpr (hAt.trans htc))⟩
  · dsimp only
    intro u ℓ hℓ hu hpositive
    let M := (1 + productMetricBound (fun i => d (some i))) * productMetricBound d
    have hM : (M : ℝ) ≤ Real.exp ((p + B) ^ B) := hmetric d hp hι (fun i => (hD i).1)
    have hK : ((ℓ * M : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
      calc
        _ ≤ Real.exp p * Real.exp ((p + B) ^ B) := by push_cast; gcongr
        _ = Real.exp (p + (p + B) ^ B) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlipc
    obtain ⟨hLip, hunit, heval⟩ := splitCoverProjection_pullback E V hsub rfl u hu hpositive
    exact ⟨u ∘ splitCoverProjection E V hsub, ℓ * M, hK, hLip, hunit, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

theorem exists_lowered_split_reconstruction_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type v} [Fintype ι] [DecidableEq ι]
      {L₀ : Type u} {L : ι → Type u}
      [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, optionLieSpace L₀ L i))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, optionLieSpace L₀ L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, optionLieSpace L₀ L i))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, optionLieSpace L₀ L i))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {s t d₀ : ℕ} {d : ι → ℕ} (Q : RationalFilteredNilmanifold L₀ s d₀) (hst : s ≤ t)
      (D : ∀ i, RationalFilteredNilmanifold (L i) t (d i)),
      let F := optionFactors (Q.raiseStep hst) D
      ∀ (Λ : Subgroup (pi F).filtration.Group) (m : ℕ) (hm : 0 < m)
        (hΛin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (pi F).basis Λ)
        (hΛout : bchSubgroupCoordinates (pi F).basis Λ ⊆ denominatorGrid m) {p : ℝ},
        0 ≤ p → (Fintype.card ι : ℝ) ≤ p → Q.GeometryComplexityLE p →
        (∀ i, (D i).GeometryComplexityLE p) → (m : ℝ) ≤ Real.exp p →
        ∃ (Δ : ∀ i, Subgroup (F i).filtration.Group) (N : Option ι → ℕ)
          (hN : ∀ i, 0 < N i)
          (hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (F i).basis (Δ i))
          (hout : ∀ i, bchSubgroupCoordinates (F i).basis (Δ i) ⊆ denominatorGrid (N i)),
          let E := fun i => (F i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
          let Q' := Q.loweredCover hst (Δ none) (N none) (hN none) (hin none) (hout none)
          ∃ _hsub : (pi E).lattice ≤ Λ,
            (∀ i, Δ i ≤ (F i).lattice ∧ ((Δ i).subgroupOf (F i).lattice).Characteristic ∧
              ((Δ i).subgroupOf (F i).lattice).Normal ∧ ((Δ i).subgroupOf (F i).lattice).FiniteIndex ∧
              ((Δ i).relIndex (F i).lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
            Q'.filtration = Q.filtration ∧ Q'.lattice ≤ Q.lattice ∧
            Q'.GeometryComplexityLE ((p + C) ^ C) ∧
            (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
            (pi (fun i => E (some i))).GeometryComplexityLE ((p + C) ^ C) ∧
            let V := (pi F).withLattice Λ m hm hΛin hΛout
            ∀ (u : V.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (letI := V.metricSpace; LipschitzWith ℓ u) →
              (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
              ∃ (v : Q'.Space × (pi (fun i => E (some i))).Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                (letI := Q'.metricSpace
                 letI := (pi (fun i => E (some i))).metricSpace
                 LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
                ∀ x : (pi E).RealGroup,
                  v (QuotientGroup.mk (changeStep (E none).filtration.realification.lowerCentralSeries_eq_bot
                      Q.filtration.realification.lowerCentralSeries_eq_bot (productProjectionHom E none x)),
                    (optionProductSpaceEquiv E (QuotientGroup.mk x)).2) = u (QuotientGroup.mk x) := by
  obtain ⟨A, _, hsplit⟩ := exists_split_reconstruction_cover
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + 1 + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L₀ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    s t d₀ d Q hst D F Λ m hm hΛin hΛout p hp hι hQ hD hmp
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := fun i =>
    match i with
    | none => inferInstance
    | some i => inferInstance
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
    intro i
    cases i <;> infer_instance
  let : ∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
    intro i
    cases i <;> infer_instance
  let : ∀ i, T2Space (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
    intro i
    cases i <;> infer_instance
  have hpp : p ≤ p + 1 := by linarith
  have hF : ∀ i, (F i).GeometryComplexityLE (p + 1) := by
    intro i
    cases i with
    | none => exact (Q.raiseStep_geometry hst hQ).mono _ hpp
    | some i => exact (hD i).mono _ hpp
  obtain ⟨Δ, N, hN, hin, hout, hsub, hindex, hE, _, hrest, hrec⟩ :=
    hsplit F Λ m hm hΛin hΛout (by linarith : 0 ≤ p + 1)
      (by simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one]; linarith)
      hF (hmp.trans (Real.exp_le_exp.mpr hpp))
  let E := fun i => (F i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  let Q' := Q.loweredCover hst (Δ none) (N none) (hN none) (hin none) (hout none)
  have hsum : p + (p + 1 + A) ^ A ≤ (p + C) ^ C := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) A)).trans hsum
  have hcost : (p + 1 + A) ^ A ≤ (p + C) ^ C := (le_add_of_nonneg_left hp).trans hsum
  have hlow : Q'.GeometryComplexityLE ((p + C) ^ C) :=
    Q.loweredCover_geometry hst (Δ none) (N none) (hN none) (hin none) (hout none) hQ hpC
      ((hE none).2.1.trans (Real.exp_le_exp.mpr hcost))
  refine ⟨Δ, N, hN, hin, hout, hsub, ?_, rfl,
    Q.lowerCoverLattice_le hst (Δ none) (hindex none).1, hlow,
    fun i => (hE i).mono _ hcost, hrest.mono _ hcost, ?_⟩
  · intro i
    obtain ⟨hle, hc, hn, hf, hi⟩ := hindex i
    exact ⟨hle, hc, hn, hf, hi.trans (Real.exp_le_exp.mpr hcost)⟩
  · dsimp only
    intro u ℓ hℓ hu hpositive
    obtain ⟨v, K, hK, hv, hunit, heval⟩ := hrec u ℓ
      (hℓ.trans (Real.exp_le_exp.mpr hpp)) hu hpositive
    let := (pi (fun i => E (some i))).metricSpace
    obtain ⟨hLip, hpos⟩ := Q.loweredCoverPullback_bounds hst (Δ none) (N none)
      (hN none) (hin none) (hout none) v hv hunit
    refine ⟨Q.loweredCoverPullback hst (Δ none) (N none) (hN none) (hin none) (hout none) v,
      K, hK.trans (Real.exp_le_exp.mpr hcost), hLip, hpos, ?_⟩
    intro x
    have h := Q.loweredCoverPullback_mk hst (Δ none) (N none) (hN none) (hin none) (hout none) v
      (changeStep (E none).filtration.realification.lowerCentralSeries_eq_bot
        Q.filtration.realification.lowerCentralSeries_eq_bot (productProjectionHom E none x))
      (optionProductSpaceEquiv E (QuotientGroup.mk x)).2
    apply h.trans
    change v ((optionProductSpaceEquiv E (QuotientGroup.mk x)).1,
      (optionProductSpaceEquiv E (QuotientGroup.mk x)).2) = u (QuotientGroup.mk x)
    simpa only [Prod.mk.eta] using heval x

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

theorem exists_controlled_basepoint_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∃ U : D.Niltest w, U.normBound = T.normBound ∧ U.ComplexityLE ((p + C) ^ C) ∧
        D.filtration.realification.polynomialOrbitEval w 0 U.orbit = 1 ∧
        ∀ x : σ → ℤ, U.eval x = T.eval x := by
  obtain ⟨a, _, hrep⟩ := Erdos3.exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + Polynomial.C a + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w T p hp hT
  have hcost : p + normalizedSquareLeftBudget a b p ≤ (p + C) ^ C := by
    simpa [X, normalizedSquareLeftBudget, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨A, _, hA, hLip⟩ := hleft D p hp hT.1
  obtain ⟨ε, hε, γ, hγ, hfactor⟩ :=
    hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
      ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hT.1.2.2.1 i j k))
      (by linarith) (by simpa only [Fintype.card_fin] using hT.1.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp) (hT.1.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
      (D.filtration.realification.polynomialOrbitEval w 0 T.orbit)
  let U := T.normalizeBasepoint ε γ A (hLip ε hε)
  refine ⟨U, rfl, ?_, ?_, ?_⟩
  · exact (T.normalizeBasepoint_complexity ε γ A (hLip ε hε) hT
      (normalizedSquareLeftBudget_nonneg a b hp) hA).mono hcost
  · exact T.normalizeBasepoint_zero ε γ A (hLip ε hε) hfactor
  · intro x
    exact T.normalizeBasepoint_eval ε γ A (hLip ε hε) hγ x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_normalized_common_correlators (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      (∀ h, (T h).ComplexityLE p) → (∀ h ∈ H, (T h).normBound ≤ 1) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ (H' : Finset G) (S : G → D.Niltest (fun _ : Unit => 1)),
        H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        (∀ h, (S h).normBound ≤ 1 ∧ (S h).UnitIntervalValued ∧
          (S h).ComplexityLE ((p + C) ^ C) ∧
          D.filtration.realification.polynomialOrbitEval (fun _ => 1) 0 (S h).orbit = 1) ∧
        (∀ h k, (S h).observable = (S k).observable) ∧
        ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))‖ := by
  obtain ⟨a, _, hnormalize⟩ := exists_controlled_basepoint_normalization s
  obtain ⟨b, _, hfixed⟩ := exists_fixed_observable_correlators s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C a) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C b) ^ b + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hD hT hcap N _ weight hweight hcorr
  let q := p + (p + a) ^ a + 2
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hnormq : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hcost : q + (q + b) ^ b + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hfixedC : (q + b) ^ b ≤ (p + C) ^ C := by linarith
  choose R hRn hRc hRzero hRvalue using fun h => hnormalize D (T h) hp (hT h)
  have hReval (h : G) (x : ZMod N) :
      (R h).evalCyclic N (fun _ => x) = (T h).evalCyclic N (fun _ => x) := hRvalue h _
  obtain ⟨H', S, hsub, hnonempty, hdense, hS, hsame, hcS⟩ :=
    hfixed D R H hH hq (hD.mono D hpq) (fun h _ => (hRc h).mono hnormq)
      (fun h hh => by rw [hRn h]; exact hcap h hh) weight hweight
      (fun h hh => by
        simp_rw [hReval h]
        exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hcorr h hh))
  refine ⟨H', S, hsub, hnonempty, ?_, ?_, hsame, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hfixedC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h
    refine ⟨(hS h).2.1, (hS h).2.2.1, (hS h).2.2.2.mono hfixedC, ?_⟩
    rw [(hS h).1]
    exact hRzero h
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hfixedC)).trans (hcS h hh)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledRefilteredRecoveredExpansion
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def RefilteredRecoveredExpansionSpec (p : ℝ) (q r : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp cost ∧
    ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
      Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
      Q'.GeometryComplexityLE cost ∧
      ∃ Z : RationalFilteredNilmanifold (∀ i : I₀, L i.val) (s + 1)
          (Fintype.card (Σ i : I₀, Fin (d i.val))),
        Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
        Z.GeometryComplexityLE cost ∧
        ∃ Λ : Subgroup Z₀.filtration.Group, Λ ≤ Z₀.lattice ∧
          (Λ.subgroupOf Z₀.lattice).Characteristic ∧ (Λ.subgroupOf Z₀.lattice).Normal ∧
          (Λ.subgroupOf Z₀.lattice).FiniteIndex ∧ (Λ.relIndex Z₀.lattice : ℝ) ≤ Real.exp cost ∧
          ∃ (l : ℕ) (hl : 0 < l)
            (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates Z₀.basis Λ)
            (hout : bchSubgroupCoordinates Z₀.basis Λ ⊆ denominatorGrid l),
            let V := Z₀.withLattice Λ l hl hin hout
            V.GeometryComplexityLE cost ∧
            letI := V.metricSpace
            let w := fun _ : Unit => 1
            let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
              (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
            let ψ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
              (hM := Z.filtration.lowerCentralSeries_eq_bot)
              (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
            ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
                (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (label : I → ZMod P) {ρ K : ℝ},
                0 < ρ → 0 ≤ K →
                (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
                (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
                (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
                (∀ i x y, 0 < A i x → 0 < A i y →
                  dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
                ∀ (S : ZMod N → (D a).Niltest w),
                  (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                  (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
                    (∀ j, realifyFunctional (freq j a) z.coord = 0) →
                    ∀ x, (S h).observable (z • x) = (S h).observable x) →
                  ∀ (slow middle rat : ZMod N → ((D a).filtration.realification.adaptedPolynomialFiltration w).Group)
                    (κ : ZMod N → (D a).RealGroup)
                    (g : ZMod N → E.filtration.realification.PolynomialOrbit w),
                    (∀ h, κ h ∈ (D a).realLattice) →
                    (∀ h, slow h * middle h * rat h * (D a).filtration.realification.adaptedConstantGroupHom w (κ h) =
                      ⟨⟨(S h).orbit.log, (S h).orbit.property⟩⟩) →
                    (∀ h, (D a).filtration.PolynomialSlowBound (D a).basis w
                      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                    (∀ h, (D a).filtration.PolynomialRationalGrid (D a).basis w q (rat h)) →
                    (∀ h x, (D a).filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (middle h) =
                      φ (E.filtration.realification.polynomialOrbitEval w x (g h))) →
                    ∀ (slowZ ratZ : ZMod N → (Z.filtration.realification.adaptedPolynomialFiltration w).Group)
                      (κZ : ZMod N → Z₀.RealGroup) (fZ : ZMod N → (Unit → ℤ) → Z₀.RealGroup),
                      (∀ h, κZ h ∈ Z₀.realLattice) →
                      (∀ h x, Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (slowZ h) *
                        ψ (E.filtration.realification.polynomialOrbitEval w x (g h)) *
                        Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (ratZ h) * κZ h = fZ h x) →
                      (∀ h, Z.filtration.PolynomialSlowBound Z.basis w (fun _ => (N : ℝ))
                        (Real.exp ((p + 2) ^ r)) (slowZ h)) →
                      (∀ h, Z.filtration.PolynomialRationalGrid Z.basis w q (ratZ h)) →
                      (∀ i j h x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                        0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                        dist (QuotientGroup.mk (fZ h (fun _ => (x.val : ℤ))) : V.Space)
                          (QuotientGroup.mk (fZ h (fun _ => (y.val : ℤ)))) ≤ K * ρ) →
                      ∃ U : I → J → ZMod N → Q'.Niltest w,
                        (∀ i j h, (U i j h).UnitIntervalValued) ∧
                        (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                        (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                          ∀ x, (U i j h).eval x = 0) ∧
                        ∃ err : ZMod N → ZMod N → ℝ,
                          (∀ h x, ((S h).evalCyclic N (fun _ => x)).re =
                            (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                          ∀ h, (𝔼 x, |err h x|) ≤ Real.exp cost * (K + 2) * ρ + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalMeanRowCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct NNReal

variable {σ L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {S : Subgroup D.RealGroup} {p : ℝ} {w : σ → ℕ}

theorem test_complexity (V : D.UnitVerticalObservable S I p)
    (g : D.filtration.realification.PolynomialOrbit w) (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (i : I) : (V.test g i).ComplexityLE (p + 4) := by
  refine ⟨hD.mono D (by linarith), ?_⟩
  have ht := niltest_log_bound_of_exp (1 : ℝ≥0) V.lipBound (a := 0) (b := p)
    (by norm_num) hp (by simp) V.lip_bound
  simpa only [test, zero_add] using ht

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootLosses
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixedSwapSample_input {s : ℕ} (π : Fin (s + 3) → Fin 2) (x : Fin 2 → ℤ) :
    mixedSampledInput (mixedSwapSample π) x =
      mixedSlotInput (x (π 1)) (x (π 0)) (fun j => x (π j.succ.succ)) := by
  rw [mixedSampledInput_slots]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFrozenMarkedLocalMark
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

variable {L M σ κ Ω J X : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d n t : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) s n)
    (hEF : E.filtration = D.filtration.gradedRefiltration W)

theorem includedRefilteredOrbit_realEval (w : σ → ℕ)
    (g : E.filtration.realification.PolynomialOrbit w) (x : σ → ℝ) :
    D.filtration.realification.polynomialOrbitRealEval w x
        (D.includedRefilteredOrbit W E hEF w g) =
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl
        (E.filtration.realification.polynomialOrbitRealEval w x g) := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_map (realificationLieHom
    (D.filtration.gradedRefiltrationSubalgebra W).incl).toLinearMap x g.log

theorem externalCandidateOrbit_realEval (w : σ → ℕ)
    (left right : D.filtration.realification.PolynomialOrbit w)
    (middle : E.filtration.realification.PolynomialOrbit w) (x : σ → ℝ) :
    D.filtration.realification.polynomialOrbitRealEval w x
        (D.externalCandidateOrbit W E hEF w left right middle) =
      D.filtration.realification.polynomialOrbitRealEval w x left *
        realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (E.filtration.realification.polynomialOrbitRealEval w x middle) *
      D.filtration.realification.polynomialOrbitRealEval w x right := by
  simp only [externalCandidateOrbit, map_mul, includedRefilteredOrbit_realEval]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical NNReal

namespace NormalizedPolynomialTwist
variable {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem norm_eval_le (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    ‖W.eval N p u‖ ≤ 1 := by
  unfold eval
  rw [norm_mul]
  exact (mul_le_mul (W.mask_bound _) (W.smooth_bound _) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedSquareImagePartition
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

def SquareImageRecoverySpec (s t k C : ℕ) : Prop :=
    ∀ {L : Type u} {M : Type v} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d dV dQ : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      (V : RationalFilteredNilmanifold D.filtration.squareLieSubalgebra s dV)
      (Q : RationalFilteredNilmanifold M t dQ)
      (φ : D.filtration.squareLieSubalgebra →ₗ⁅ℚ⁆ M) {p : ℝ},
      2 ≤ p → D.GeometryComplexityLE p → V.GeometryComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((pi (fun _ : Bool => D)).basis.repr
        (D.filtration.squarePairMap (V.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr (φ (V.basis j)) i) ≤ p) →
      ∃ (Δ : Bool → Subgroup D.filtration.Group) (l : Bool → ℕ)
        (hl : ∀ i, 0 < l i)
        (hlin : ∀ i, scaledIntegerGrid (l i) ⊆ bchSubgroupCoordinates D.basis (Δ i))
        (hlout : ∀ i, bchSubgroupCoordinates D.basis (Δ i) ⊆ denominatorGrid (l i)),
        let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
        (∀ i, Δ i ≤ D.lattice ∧ ((Δ i).subgroupOf D.lattice).Characteristic ∧
          ((Δ i).subgroupOf D.lattice).Normal ∧ ((Δ i).subgroupOf D.lattice).FiniteIndex ∧
          ((Δ i).relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
        letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
        letI := Q.metricSpace
        let ψ := realificationMap (hnil := D.filtration.squareFiltration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) φ
        ∀ ε γ : D.RealGroup, γ ∈ D.realLattice →
          (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 2) ^ k)) →
          ∀ a b c d : D.RealGroup, ∀ u v : D.filtration.squareFiltration.realification.Group,
            D.filtration.realSquareFstHom u = ε⁻¹ * a * γ⁻¹ →
            D.filtration.realSquareSndHom u = b →
            D.filtration.realSquareFstHom v = ε⁻¹ * c * γ⁻¹ →
            D.filtration.realSquareSndHom v = d →
            ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ Real.exp (-((p + C) ^ C)) →
              dist (QuotientGroup.mk a : (E true).Space) (QuotientGroup.mk c) ≤ ρ →
              dist (QuotientGroup.mk b : (E false).Space) (QuotientGroup.mk d) ≤ ρ →
              dist (QuotientGroup.mk (ψ u) : Q.Space) (QuotientGroup.mk (ψ v)) ≤
                Real.exp ((p + C) ^ C) * ρ

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedPartitionExpansionCore
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def SelectedRefilteredProductExpansionSpec (p : ℝ) (q r : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp cost ∧
    ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
      Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
      Q'.GeometryComplexityLE cost ∧
        ∃ Λ : Subgroup Z₀.filtration.Group, Λ ≤ Z₀.lattice ∧
          (Λ.subgroupOf Z₀.lattice).Characteristic ∧ (Λ.subgroupOf Z₀.lattice).Normal ∧
          (Λ.subgroupOf Z₀.lattice).FiniteIndex ∧ (Λ.relIndex Z₀.lattice : ℝ) ≤ Real.exp cost ∧
          ∃ (l : ℕ) (hl : 0 < l)
            (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates Z₀.basis Λ)
            (hout : bchSubgroupCoordinates Z₀.basis Λ ⊆ denominatorGrid l),
            let V := Z₀.withLattice Λ l hl hin hout
            V.GeometryComplexityLE cost ∧
            letI := V.metricSpace
            let w := fun _ : Unit => 1
            ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
                (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (label : I → ZMod P) {ρ K : ℝ},
                0 < ρ → 0 ≤ K →
                (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
                (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
                (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
                (∀ i x y, 0 < A i x → 0 < A i y →
                  dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
                ∀ (S : ZMod N → (D a).Niltest w),
                  (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                  (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
                    (∀ j, realifyFunctional (freq j a) z.coord = 0) →
                    ∀ x, (S h).observable (z • x) = (S h).observable x) →
                  ∀ (Hsh : Set (ZMod N)) (g : ZMod N → ∀ i, (D i).filtration.realification.PolynomialOrbit w),
                    (∀ h ∈ Hsh, g h a = (S h).orbit) →
                    ∀ (slow middle rat : ZMod N → ((pi D).filtration.realification.adaptedPolynomialFiltration w).Group)
                      (κ : ZMod N → (pi D).RealGroup),
                      (∀ h ∈ Hsh, κ h ∈ (pi D).realLattice) →
                      (∀ h ∈ Hsh, slow h * middle h * rat h * (pi D).filtration.realification.adaptedConstantGroupHom w (κ h) =
                        ⟨⟨(NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (g h)).log,
                          (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (g h)).property⟩⟩) →
                      (∀ h ∈ Hsh, (pi D).filtration.PolynomialSlowBound (pi D).basis w
                        (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                      (∀ h ∈ Hsh, (pi D).filtration.PolynomialRationalGrid (pi D).basis w q (rat h)) →
                      (∀ h ∈ Hsh, ∀ α, VectorPolynomial.coefficients
                        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
                          (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight w α)) →
                      (∀ h ∈ Hsh, VectorPolynomial.coefficients
                        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0) →
                      (∀ i j h, h ∈ Hsh → ∀ x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                        0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                        dist (V.cyclicOrbitPoint
                          (NilpotentLieFiltration.piRealOrbit (fun i : I₀ => (D i.val).filtration)
                            (fun i : I₀ => g h i.val)) N (fun _ : Unit => x))
                          (V.cyclicOrbitPoint
                            (NilpotentLieFiltration.piRealOrbit (fun i : I₀ => (D i.val).filtration)
                              (fun i : I₀ => g h i.val)) N (fun _ : Unit => y)) ≤ K * ρ) →
                      ∃ U : I → J → ZMod N → Q'.Niltest w,
                        (∀ i j h, (U i j h).UnitIntervalValued) ∧
                        (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                        (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                          ∀ x, (U i j h).eval x = 0) ∧
                        ∃ err : ZMod N → ZMod N → ℝ,
                          (∀ h ∈ Hsh, ∀ x, ((S h).evalCyclic N (fun _ => x)).re =
                            (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                          ∀ h, (𝔼 x, |err h x|) ≤ Real.exp cost * (K + 2) * ρ + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)

variable (hH : ∀ j, 0 < H j)

noncomputable def principalAffineIntervalAxisLaw (P : D → Prop) :
    FiniteProbabilityWeights (PrincipalAxisTuples (α := Empty) P L) :=
  (principalAffineIntervalLaw B h L H step start hinside hH).finitePushforward
    (principalAxisRestrict P)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistSliceVariationPairCorrelation
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

namespace ResidueBoxSlice

theorem fullSlicePoint_normalized_distance_le
    {K : Type*} [Fintype K] [DecidableEq K] {P : K → ℕ} {q : ℕ}
    (S : ResidueBoxSlice P q) (htwo : ∀ k, 2 ≤ S.length k)
    (u v : ∀ k, Fin (S.length k)) {η : ℝ}
    (hnear : ∀ k, |((u k).val : ℝ) / S.length k -
      ((v k).val : ℝ) / S.length k| ≤ η) (k : K) :
    |((S.fullSlicePointInIntegerBox u).val k : ℝ) / P k -
      ((S.fullSlicePointInIntegerBox v).val k : ℝ) / P k| ≤ 2 * η := by
  have htwoK := htwo k
  have hlen : (0 : ℝ) < S.length k := by exact_mod_cast (by omega : 0 < S.length k)
  have hP : (0 : ℝ) < P k := by
    have h := S.inside k 0 (by omega)
    exact_mod_cast (show 0 < P k by omega)
  have hspan : (q : ℝ) * S.length k ≤ 2 * (P k : ℝ) := by
    exact_mod_cast S.stride_mul_length_le_twice k (htwo k)
  have hfac : (q : ℝ) * S.length k / P k ≤ 2 := (div_le_iff₀ hP).mpr hspan
  have hfac0 : 0 ≤ (q : ℝ) * S.length k / P k := by positivity
  have heq : ((S.fullSlicePointInIntegerBox u).val k : ℝ) / P k -
      ((S.fullSlicePointInIntegerBox v).val k : ℝ) / P k =
      ((q : ℝ) * S.length k / P k) *
        (((u k).val : ℝ) / S.length k - ((v k).val : ℝ) / S.length k) := by
    simp only [fullSlicePointInIntegerBox, point, Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    field_simp
    ring
  rw [heq, abs_mul, abs_of_nonneg hfac0]
  exact mul_le_mul hfac (hnear k) (abs_nonneg _) (by norm_num)

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3
open scoped TensorProduct BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

namespace UniversalLocalMajorSliceTest

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {N : I → ℕ} {degree : ℕ} {cost budget : ℝ}

noncomputable def nativeModel (packet : UniversalLocalMajorSliceTest N degree cost budget) :
    NativeSampleModel (fun _ : I => 1) degree budget id packet.value :=
  Classical.choice packet.native

theorem value_eq_native_eval (packet : UniversalLocalMajorSliceTest N degree cost budget)
    (x : I → ℤ) : packet.value x = packet.nativeModel.test.eval x :=
  packet.nativeModel.eval x

theorem weight_eq_native_eval (packet : UniversalLocalMajorSliceTest N degree cost budget)
    (x : I → ℤ) :
    packet.weight x = star (packet.nativeModel.test.eval
      (commonStrideIndex (fun i => (packet.slice.start i : ℤ)) packet.stride x)) := by
  rw [weight, packet.value_eq_native_eval]

end UniversalLocalMajorSliceTest
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedOriginalSampleResidueMixtureForecast
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

local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "ActiveInput" => PrincipalTupleIndex activeB activeDegree
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides

noncomputable def allocatedPrincipalResidueJoin (q : ℕ) (u : ShortTuple)
    (r : ActiveInput → ZMod q) : FullInput → Option Empty → ZMod q :=
  principalAxisResidueJoin short u q (fun j _ => r j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResiduePrimeDensityError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def residuePrimeCoordinateDensity {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f : (σ → ℤ) → ℝ) : (∀ i, σ → ZMod (q i)) → ℝ := by
  let := hne
  exact observedProductDensity (primeCoordinateReference (σ := σ) q)
    (FiniteProbabilityWeights.uniform
      (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (fun z => primeCoordinateObservation q (fun j => (z j).val)) (fun z => f (fun j => (z j).val))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
  (q : ι → ℕ) [∀ i, NeZero (q i)]

noncomputable def residuePhysicalTruncation (b : ℕ) (f : (σ → ℤ) → ℝ) (u : σ → ℤ) : ℝ :=
  productANOVATruncation (primeCoordinateReference (σ := σ) q) (lowDegreeCoordinateSets ι b)
    (residuePrimeCoordinateDensity lo N M a hne q f) (primeCoordinateObservation q u)

def ResiduePhysicalTruncationControl (b : ℕ) (f : (σ → ℤ) → ℝ) (eta : ℝ) : Prop :=
  let low := residuePhysicalTruncation lo N M a hne q b f
  let cap := residueTruncationCap ι b eta
  (𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
    low (fun k => (z k).val) ^ 2) ≤ 2 + 3 * eta * cap ^ 2 ∧
  (𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
    (f (fun k => (z k).val) - low (fun k => (z k).val)) ^ 2) ≤ 1 + eta * cap ^ 2 ∧
  ∀ (I : Finset ι), I.card ≤ b → ∀ test : (∀ i, σ → ZMod (q i)) → ℝ, ProductDependsOn I test →
    |𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
      (f (fun k => (z k).val) - low (fun k => (z k).val)) *
        test (primeCoordinateObservation q (fun k => (z k).val))| ≤
      eta * cap * (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).mean
        (fun x => |test x|)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DenseResidueScalarScoreNet
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

noncomputable def fullSliceSupport (S : ResidueBoxSlice N q) : Finset (integerBox N) :=
  Finset.univ.image S.fullSlicePointInIntegerBox

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SpatialAffineFullMass
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {K X : Type*} [Fintype K]

theorem spatialAffineFull_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k) (x : X) :
    realPolynomialMass (scaleMvPolynomialAxes T (affineFramePolynomial frame x)) ≤
      |frame none x| + ∑ k, |frame (some k) x| * T k := by
  rw [scaleMvPolynomialAxes_affineFrame_eq_const_add_top]
  exact (realPolynomialMass_add_le _ _).trans
    (add_le_add (le_of_eq (realPolynomialMass_C _))
      (spatialAffineTop_mass_le frame T hT x))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualCandidateSlowProjectionMass
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

theorem normalizedMass_neg_linearCombination_le {K I : Type*} [Fintype I]
    (T : K → ℝ) (a : I → ℝ) (p : I → MvPolynomial K ℝ) {M : ℝ}
    (hp : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T (p i)) ≤ M) :
    realPolynomialMass (scaleMvPolynomialAxes T (-(∑ i, a i • p i))) ≤
      (∑ i, |a i|) * M := by
  simp only [scaleMvPolynomialAxes_eq_aeval, map_neg, map_sum, map_smul,
    normalizedPolynomialMass_neg]
  apply (realPolynomialMass_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [realPolynomialMass_smul]
  simpa only [scaleMvPolynomialAxes_eq_aeval] using
    mul_le_mul_of_nonneg_left (hp i) (abs_nonneg (a i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal BigOperators

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R : Fin m → ℝ)

noncomputable def forecastNativeMixedRow (j : Fin m) :
    (LayerSamplerAxis I n → ℝ) →ₗ[ℝ] ((I j → ℝ) × (Fin (n j) → ℝ)) :=
  ((R j) • LinearMap.pi (fun i : I j => LinearMap.proj ⟨j, Sum.inl i⟩)).prod
    ((R j) • LinearMap.pi (fun i : Fin (n j) => LinearMap.proj ⟨j, Sum.inr i⟩))

noncomputable def forecastNativeAmbientLinear :
    (LayerSamplerAxis I n → ℝ) →ₗ[ℝ] ((Σ j, J j) → ℝ) :=
  LinearMap.pi (fun a => (LinearMap.proj a.2).comp
    ((EuclideanSpace.equiv (J a.1) ℝ).toLinearMap.comp
      ((mixedRealPoint (euclideanSubspace (U a.1)) (b a.1) (o a.1)).comp
        (forecastNativeMixedRow (I := I) (n := n) R a.1))))

noncomputable def forecastNativeAmbientLip : ℝ≥0 :=
  ‖(forecastNativeAmbientLinear U b o R).toContinuousLinearMap‖₊

variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
local notation "Active" => {a : LayerSamplerAxis I n // ¬P a}
local notation "Output" => (Σ _a : Active, Unit)

def forecastNativeFillAxes (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (v : Output → ℝ) : LayerSamplerAxis I n → ℝ :=
  fun a => if ha : P a then frozen ⟨a, ha⟩ else v ⟨⟨a, ha⟩, ()⟩

variable {X : Type*} [Fintype X]
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))

noncomputable def forecastNativeSpatialInverse (center : X → ℝ) (τ : ℝ) (z : Spatial → ℝ) : X → ℝ :=
  fun x => center x + τ / 8 * z ⟨x, Sum.inl ()⟩

noncomputable def forecastNativeTorusInverse (d : ℕ) [NeZero d]
    (deck : (Σ j, J j) → ZMod d)
    (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) (v : Output → ℝ) :
    (Σ j, J j) → UnitAddCircle :=
  fun a => ((forecastNativeAmbientLinear U b o R (forecastNativeFillAxes P frozen v) a /
    d : ℝ) : UnitAddCircle) + ZMod.toAddCircle (deck a)

namespace NormalizedPolynomialTwist

variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def forecastPullback
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (deck : (Σ j, J j) → ZMod W.cover)
    (center : X → ℝ) (τ : ℝ) (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (y : Domain) : ℂ := by
  letI : NeZero W.cover := ⟨W.cover_pos.ne'⟩
  exact W.mask residue * W.smooth (forecastNativeSpatialInverse center τ y.1,
    forecastNativeTorusInverse U b o R P W.cover deck frozen y.2)

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end


