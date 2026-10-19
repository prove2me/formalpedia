-- Prove2me | Definitions.Def_OAIE3v2B213
-- name    : OAIE3v2B213
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:11:39.371296+00:00
-- url     : https://prove2.me/theorems/2c507785-4272-4dd9-87f3-49f92cbc050d
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 217 of 311
-- statement:
--   Definitions bundle 217 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B299`, `OAIE3v2B180`, `OAIE3v2B181`, `OAIE3v2B182`, `OAIE3v2B186`, `OAIE3v2B191`, `OAIE3v2B192`, `OAIE3v2B193`, `OAIE3v2B194` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidateCoveredBudget.lean`, `Dynamics/AllocatedExternalCandidateExponentialFreezingBudget.lean`, `Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`, `Estimates/AllocatedActiveContainedTupleMap.lean`, `Estimates/AllocatedCenteredNarrowPrescribedMarginal.lean`, `Estimates/AllocatedExternalCandidateRealThreshold.lean`, `Estimates/AllocatedOriginalSampleCongruenceOutput.lean`, `Estimates/AllocatedProfileDimensions.lean`, `Estimates/NativeOptionFixedSourceQuotientMarkStrong.lean`, `Estimates/NativeSharedFrozenCorrelations.lean`, `Estimates/UniformFrozenDescent.lean`, `Geometry/ActualCandidateSpatialCenter.lean`, `Lattices/AllocatedAffineCanonicalBackendBudget.lean`, `Lattices/AllocatedAffineWholeProfileComparison.lean`, `Lattices/AllocatedModularRankAffineFullWitness.lean`, `Lattices/AllocatedModularRankIntegerDecay.lean`, `Lattices/CertifiedAffineCutoffCost.lean`, `Lattices/ForecastNativeResidueTest.lean`, `Lattices/RetainedAffineResidueEpoch.lean`, `Lattices/SpatialAffineFullMass.lean`, `Linear/AllocatedCenteredMeasurableFramedBadTail.lean`, `Linear/AllocatedModularRankActualRead.lean`, `Linear/AllocatedShortRankWitnessWidth.lean`, `Nilpotent/NativeSquareNiltest.lean`, `Sampling/ForecastLawRecoveredRationalCardinalityCap.lean`, `Sampling/ForecastNativeJointTestBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B181
import Definitions.Def_OAIE3v2B182
import Definitions.Def_OAIE3v2B186
import Definitions.Def_OAIE3v2B191
import Definitions.Def_OAIE3v2B192
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B194

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionFixedSourceQuotientMarkStrong
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}

theorem exists_native_adapted_map_geometry :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
        (E : RationalFilteredNilmanifold M t e) (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ},
        0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
        (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis i)) j) ≤ p) →
        Nonempty (D.AdaptedMapGeometryData E φ p ((p + 2) ^ C)) := by
  obtain ⟨C, hC, hbudget⟩ := exists_adaptedMapGeometryBudget_fixed_power
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s t d e D E φ p hp hD hE hφ
  obtain ⟨source, hsource, hsourceForward⟩ := D.exists_adapted_model_data hp hD
  obtain ⟨target, htarget, htargetForward⟩ := E.exists_adapted_model_data hp hE
  obtain ⟨hsourceDim, hsourceInverse, _⟩ :=
    D.basis_geometry_of_forward_height source.basis hp hD hsourceForward
  obtain ⟨htargetDim, htargetInverse, _⟩ :=
    E.basis_geometry_of_forward_height target.basis hp hE htargetForward
  have hp1 : 0 ≤ p + 1 := by linarith
  have hmap := D.markedMap_basisChange_logHeight E source.basis target.basis φ.toLinearMap
    hp1 (hD.mono D (by linarith)) (hE.mono E (by linarith))
    hsourceForward htargetForward (fun i j => (hφ i j).trans (by linarith))
  let r := adaptedMapGeometryBudget p
  have hr : 0 ≤ r := adaptedMapGeometryBudget_nonneg hp
  have hgeomr : (p + 3) ^ 11 ≤ r := adaptedMapGeometryBudget_geometry hp
  have hinverser : (p + 4) ^ 5 ≤ r := by
    have hpow : (p + 4) ^ 5 ≤ (p + 4) ^ 11 :=
      pow_le_pow_right₀ (by linarith) (by decide)
    exact hpow.trans (adaptedMapGeometryBudget_inverse hp)
  have hmapr : adaptedMarkedMapHeightBudget (p + 1) ≤ r :=
    adaptedMapGeometryBudget_markedMap hp
  have hforwardr : p + 1 ≤ r := by
    exact (show p + 1 ≤ p + 2 by linarith).trans (adaptedMapGeometryBudget_parameter hp)
  have hrq : r ≤ (p + 2) ^ C := (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
    (hbudget p hp)
  have hsourceq := hsource.mono source.model (hgeomr.trans hrq)
  have htargetq := htarget.mono target.model (hgeomr.trans hrq)
  let H := ⌈Real.exp r⌉₊
  refine ⟨{
    source := source
    target := target
    budget_nonneg := hr.trans hrq
    forward_budget := hforwardr.trans hrq
    source_dimension := ?_
    target_dimension := ?_
    source_geometry := hsourceq
    target_geometry := htargetq
    source_forward := hsourceForward
    target_forward := htargetForward
    source_inverse := fun i j => (hsourceInverse i j).trans (hinverser.trans hrq)
    target_inverse := fun i j => (htargetInverse i j).trans (hinverser.trans hrq)
    source_structure := hsourceq.2.2.1
    target_structure := htargetq.2.2.1
    entries_height := H
    entries_height_pos := lt_of_lt_of_le Nat.zero_lt_one (one_le_ceil_exp r)
    entries_bound := (ceil_exp_le_exp_add_one hr).trans (Real.exp_le_exp.mpr (hbudget p hp))
    entries := fun i j => rationalHeightLE_ceil_exp ((hmap j i).trans hmapr)
    entries_logHeight := fun i j => (hmap j i).trans (hmapr.trans hrq)
  }⟩
  · simpa only [Fintype.card_fin] using hsourceDim
  · simpa only [Fintype.card_fin] using htargetDim

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

theorem exists_uniform_frozen_map (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : E.RealGroup,
            (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∃ h : ∀ γ ∈ Q.realLattice,
                r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice,
              ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                (letI := Q.metricSpace
                 letI := E.metricSpace
                 LipschitzWith K (frozenCosetMap Q.realLattice E.realLattice
                   (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                     (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h)) := by
  obtain ⟨c₀, _, hcover⟩ := exists_uniform_conjugated_source_cover s
  obtain ⟨c₁, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s k
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c₀) ^ c₀ + X +
    (X + 1 + Polynomial.C c₁) ^ c₁ + (X + 1 + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ⟩ :=
    hcover D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right zero_le_one
  have hsum : (p + c₀) ^ c₀ + p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcovC : (p + c₀) ^ c₀ ≤ (p + C) ^ C := by
    exact (((le_add_of_nonneg_right hp).trans
      (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg c₁)) _))).trans
      (le_add_of_nonneg_right (sq_nonneg (t + 2)))).trans hsum
  have hcostC : p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    have hc : 0 ≤ (p + c₀) ^ c₀ := pow_nonneg (add_nonneg hp (Nat.cast_nonneg c₀)) _
    linarith
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp t := ceil_exp_le_exp_add_one hp
  have hd : (Fintype.card (Fin d) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hD.1.trans hpt
  have he : (Fintype.card (Fin e) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hE.1.trans hpt
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  obtain ⟨A, _, hA, hALip⟩ := hleft (E.basis.baseChange ℝ) (lieStructureConstants E.basis) H t
    E.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure E.basis i j k).symm) ht he hH
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  obtain ⟨B, _, hB, hBLip⟩ := exists_realificationMap_lipschitz_exp_bound
    (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot)
    D.basis E.basis φ H ht hd he hH (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcovC),
    N, hN, hin, hout, hQ.mono Q hcovC, ?_⟩
  intro a r ha hr
  have hconj := D.real_conjugationPullback_property E φ q hq Λ htarget r hr
  have ha' : LipschitzWith A (fun x => a * x) := hALip a (fun i =>
    (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by dsimp [t]; linarith) _)))
  refine ⟨hconj, A * B, ?_, Q.lipschitz_native_frozenCosetMap E φ a r hconj hBLip ha'⟩
  calc
    _ = (A : ℝ) * B := by simp only [NNReal.coe_mul]
    _ ≤ Real.exp ((t + c₁) ^ c₁) * Real.exp ((t + 2) ^ 2) :=
      mul_le_mul hA hB B.coe_nonneg (Real.exp_pos _).le
    _ = Real.exp ((t + c₁) ^ c₁ + (t + 2) ^ 2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFrozenDescent
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_frozen_descent (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (E : RationalFilteredNilmanifold M (s + 1) e) (φ : L →ₗ⁅ℚ⁆ M)
      {w : σ → ℕ} (T : E.Niltest w)
      (g : D.filtration.realification.PolynomialOrbit w) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → T.ComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧
        (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ d ∧
          ∃ Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n,
            ∃ hQF : Q.filtration = D.filtration.quotientTop,
              Q.lattice = Λ.map
                (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl) ∧
              Q.GeometryComplexityLE ((p + C) ^ C) ∧
              (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
               letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
                 IsModuleTopology.topologicalAddGroup ℝ _
               letI := realification_moduleTopology_t2 Q.basis
               ∀ a r : E.RealGroup,
                 (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
                 (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
                 (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x : D.RealGroup,
                   T.observable (QuotientGroup.mk
                     (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                       (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r)) =
                   T.observable (QuotientGroup.mk
                     (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                       (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r))) →
                 ∃ S : Q.Niltest w, S.orbit = D.topQuotientOrbit Q hQF g ∧
                   S.normBound = T.normBound ∧ S.ComplexityLE ((p + C) ^ C) ∧
                   ∀ x : σ → ℤ, S.eval x = T.observable (QuotientGroup.mk
                     (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                       (hM := E.filtration.lowerCentralSeries_eq_bot) φ
                       (D.filtration.realification.polynomialOrbitEval w x g) * r))) := by
  obtain ⟨A, _, hmaps⟩ := exists_uniform_frozen_map (s + 1) k
  obtain ⟨B, _, hdesc⟩ := exists_topInvariant_niltest_budget s
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let P := X + U + 4
  let R := P + (P + 3) ^ 11 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L M σ _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ w T g p hp hD hT hφ q hq hqp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hF, hmap⟩ :=
    hmaps D E φ p hp hD hT.1 hφ q hq hqp
  let F := D.withLattice Λ N hN hin hout
  let u := (p + A) ^ A
  let t := p + u + 4
  let r := t + (t + 3) ^ 11 + 4
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hut : u ≤ t := by dsimp [t]; linarith
  have htr : t ≤ r := by dsimp [r]; linarith [pow_nonneg (by linarith : 0 ≤ t + 3) 11]
  have hr : 0 ≤ r := ht.trans htr
  have hQr : (t + 3) ^ 11 ≤ r := by dsimp [r]; linarith
  have hsum : r + (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [R, P, U, X, r, t, u, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (r + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans hsum
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hproj, _⟩ :=
    F.exists_controlled_top_quotient ht (hF.mono F hut)
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr ((hut.trans htr).trans hrC)),
    n, hn, Q, hQF, hQL, hQ.mono Q (hQr.trans hrC), ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ F.filtration.layerIdeal (s + 1))) :=
    moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ F.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  intro a b ha hb hinvariant
  obtain ⟨hconj, K, hK, hKlip⟩ := hmap a b ha hb
  let T' := F.frozenComplexNiltest E φ a b hconj T g K hKlip
  have hT' : T'.ComplexityLE t :=
    F.frozenComplexNiltest_complexity E φ a b hconj T g K hKlip hp hu hF hT hK
  have h5 : (t + 3) ^ 5 ≤ (t + 3) ^ 11 := pow_le_pow_right₀ (by linarith) (by decide)
  obtain ⟨S, hSo, hSn, hSc, hSe⟩ := hdesc F Q hQF hQL T' r hr (hT'.mono htr)
    (hQ.mono Q hQr) (fun i j => (hproj j i).trans (h5.trans hQr))
    (F.frozenComplexNiltest_top_invariant E φ a b hconj T g K hKlip hinvariant)
  refine ⟨S, hSo, hSn, hSc.mono hcost, ?_⟩
  intro x
  exact (hSe x).trans (F.frozenComplexNiltest_eval E φ a b hconj T g K hKlip x)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeSquareNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

theorem exists_square_niltest_with_budget_and_orbit {w : σ → ℕ} (T : D.Niltest w)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (a b c : ℕ)
    (hrec : ∀ (m n H : ℕ) (ℓ B : ℝ≥0) (r : ℝ),
      0 ≤ r → (m : ℝ) ≤ r → (n : ℝ) ≤ r → (H : ℝ) ≤ Real.exp r →
      (ℓ : ℝ) ≤ Real.exp r → (B : ℝ) ≤ Real.exp r →
      (rationalReconstructionLipschitzBound s m n H ℓ B : ℝ) ≤ Real.exp ((r + c) ^ c))
    (ε : D.RealGroup) (q : D.filtration.squareFiltration.realification.PolynomialOrbit w)
    (χ : D.RealGroup → CircleFourier.Circle)
    (hvert : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = character (χ z) * T.observable x)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp (normalizedSquareLeftBudget a b p))
    (hALip : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    ∃ (m : ℕ) (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
      (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
        (D.filtration.squareLattice D.lattice) N hN hin hout
      ∃ S : Q.Niltest w,
        S.orbit = D.filtration.squareFiltration.realQuotientPolynomialOrbit
          (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q ∧
        (∀ z : D.filtration.squareFiltration.realification.Group,
          S.observable (QuotientGroup.mk (D.filtration.squareFiltration.realQuotientStepHom
            (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
            D.filtration.realSquareObservable D.lattice ε T.observable (QuotientGroup.mk z)) ∧
        S.normBound = T.normBound ^ 2 ∧
        S.ComplexityLE (normalizedSquareComplexityBudget a b c p) ∧
        ∀ x : σ → ℤ, S.eval x = D.filtration.realSquareObservable D.lattice ε T.observable
          (QuotientGroup.mk (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  obtain ⟨e, ω, hF, N, hN, hin, hout, _, _, hconstruct⟩ :=
    D.exists_uniform_square_niltest_with_budget T hp hT a b c hrec
  obtain ⟨S, hS⟩ := hconstruct ε q χ hvert A hA hALip
  exact ⟨_, D.filtration.squareFinBasis e ω (hF 2), squareFinWeight ω,
    D.filtration.squareFinBasis_layers e ω hF, N, hN, hin, hout, S, hS⟩

theorem exists_square_niltest_with_budget {w : σ → ℕ} (T : D.Niltest w)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (a b c : ℕ)
    (hrec : ∀ (m n H : ℕ) (ℓ B : ℝ≥0) (r : ℝ),
      0 ≤ r → (m : ℝ) ≤ r → (n : ℝ) ≤ r → (H : ℝ) ≤ Real.exp r →
      (ℓ : ℝ) ≤ Real.exp r → (B : ℝ) ≤ Real.exp r →
      (rationalReconstructionLipschitzBound s m n H ℓ B : ℝ) ≤ Real.exp ((r + c) ^ c))
    (ε : D.RealGroup) (q : D.filtration.squareFiltration.realification.PolynomialOrbit w)
    (χ : D.RealGroup → CircleFourier.Circle)
    (hvert : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = character (χ z) * T.observable x)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp (normalizedSquareLeftBudget a b p))
    (hALip : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    ∃ (m : ℕ) (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
      (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
        (D.filtration.squareLattice D.lattice) N hN hin hout
      ∃ S : Q.Niltest w, S.normBound = T.normBound ^ 2 ∧
        S.ComplexityLE (normalizedSquareComplexityBudget a b c p) ∧
        ∀ x : σ → ℤ, S.eval x = D.filtration.realSquareObservable D.lattice ε T.observable
          (QuotientGroup.mk (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  obtain ⟨m, bs, v, hls, N, hN, hin, hout, S, _, _, hS⟩ :=
    D.exists_square_niltest_with_budget_and_orbit T hp hT a b c hrec ε q χ hvert A hA hALip
  exact ⟨m, bs, v, hls, N, hN, hin, hout, S, hS⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)] {D : ℝ}

theorem AllocatedComparisonDimensions.layer_degree
    (h : AllocatedComparisonDimensions (G := G) B α O D) (j : Fin m) :
    ((j.val+1 : ℕ) : ℝ) ≤ D :=
  (Nat.cast_le.mpr (Nat.succ_le_of_lt j.isLt)).trans h.degree

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredNarrowPrescribedMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def AllocatedCenteredNarrowPrescribedMarginalStatement (m A : ℕ) : Prop :=
    ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    let Z := fun center => selectedJointDensityMass bases stride T widths (density center)
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z)
      (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x),
    ∃ hnormalizer : ∀ center, |Z center - 1| ≤ Real.exp (-E) ∧
      Z center ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z center ∧ (Z center)⁻¹ ≤ 2,
    let law := fun center => selectedJointFiniteLaw bases hbases stride T widths
      (narrowTrimmedSpatialWidths_pos _hW _hτ _hξ N hN) hmass (density center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
      (hnormalizer center).2.2.1
    ∃ hweight : ∀ z, Measurable (fun center => (law center).weight z),
    ∀ {Sites : Type*} [Fintype Sites] [Nonempty Sites]
      (root : Sites → LayerSamplerVariables G I n B → ℤ)
      (_hroot : ∀ t k, |(root t k : ℝ)| ≤ Real.exp P)
      (hrootSum : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W),
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        ((centeredFiniteMarginal μ law hweight).siteLaw
          (narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
            _hW _hτ _hξ1 N hN hmargin root hrootSum))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) ≤
          6 * positiveProjectionAccuracy E

def AllocatedCenteredNarrowPrescribedMarginalPointwiseStatement (m A : ℕ) : Prop :=
    ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    let Z := fun center => selectedJointDensityMass bases stride T widths (density center)
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z)
      (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x),
    ∃ hnormalizer : ∀ center, |Z center - 1| ≤ Real.exp (-E) ∧
      Z center ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z center ∧ (Z center)⁻¹ ≤ 2,
    let law := fun center => selectedJointFiniteLaw bases hbases stride T widths
      (narrowTrimmedSpatialWidths_pos _hW _hτ _hξ N hN) hmass (density center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
      (hnormalizer center).2.2.1
    ∀ {Sites : Type*} [Fintype Sites] [Nonempty Sites]
      (root : Sites → LayerSamplerVariables G I n B → ℤ)
      (_hroot : ∀ t k, |(root t k : ℝ)| ≤ Real.exp P)
      (hrootSum : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W),
      ∀ center,
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        ((law center).siteLaw
          (narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
            _hW _hτ _hξ1 N hN hmargin root hrootSum))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) ≤
          6 * positiveProjectionAccuracy E

def AllocatedCenteredNarrowPrescribedMarginalOneCenterStatement (m A : ℕ) : Prop :=
    ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm center
    let Z := selectedJointDensityMass bases stride T widths density
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z)
      (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x),
    ∃ hnormalizer : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ (Z)⁻¹ ≤ 2,
    let law := selectedJointFiniteLaw bases hbases stride T widths
      (narrowTrimmedSpatialWidths_pos _hW _hτ _hξ N hN) hmass density
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
      hnormalizer.2.2.1
    ∀ {Sites : Type*} [Fintype Sites] [Nonempty Sites]
      (root : Sites → LayerSamplerVariables G I n B → ℤ)
      (_hroot : ∀ t k, |(root t k : ℝ)| ≤ Real.exp P)
      (hrootSum : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W),
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        (law.siteLaw
          (narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
            _hW _hτ _hξ1 N hN hmargin root hrootSum))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) ≤
          6 * positiveProjectionAccuracy E

end Erdos3.VectorPolynomial

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

theorem spatialAffineFull_inv_mul_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k)
    (x : X) (N : ℝ) (hN : 0 < N) :
    realPolynomialMass (C N⁻¹ *
      scaleMvPolynomialAxes T (affineFramePolynomial frame x)) ≤
        |frame none x| / N + N⁻¹ * ∑ k, |frame (some k) x| * T k := by
  apply (realPolynomialMass_C_mul_le _ _).trans
  rw [abs_of_pos (inv_pos.mpr hN)]
  calc
    _ ≤ N⁻¹ * (|frame none x| + ∑ k, |frame (some k) x| * T k) :=
      mul_le_mul_of_nonneg_left (spatialAffineFull_mass_le frame T hT x)
        (inv_nonneg.mpr hN.le)
    _ = _ := by ring

theorem spatialAffineFull_scaled_inv_mul_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k)
    (x : X) (N : ℝ) (hN : 0 < N) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (C N⁻¹ * affineFramePolynomial frame x)) ≤
        |frame none x| / N + N⁻¹ * ∑ k, |frame (some k) x| * T k := by
  rw [scaleMvPolynomialAxes_C_mul]
  exact spatialAffineFull_inv_mul_mass_le frame T hT x N hN

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankActualRead
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial
variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedOriginalTaggedTop
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) :
    AllocatedTaggedRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl x => homogeneousComponent 1
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (spatialRankPolynomial (fun d => noise (d,x.val))))
  | .inr (.inl i) => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v (modularDeckPolynomial r j i))
  | .inr (.inr a) => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1) (projection a)))

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankIntegerDecay
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedCongruenceIntegerPolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ) :
    AllocatedCongruenceRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) ℤ
  | .inl x => conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v
      (C (base x.val) + spatialRankPolynomial (fun d => noise (d, x.val)))
  | .inr (.inl i) => conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v
      (modularBoundedCoefficientPolynomial (j.val + 1) (fun q => r j q i))
  | .inr (.inr a) => conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v
      (modularBoundedCoefficientPolynomial (j.val + 1)
        (projection (allocatedCongruenceIntegerEmbedding inactive j a)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

def allocatedResidueModulusBad
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ) (M : ℕ) [NeZero M]
    (f : AllocatedActualCoefficientIndex G X I E n B → ZMod M) : Prop :=
  ∃ v : LayerSamplerVariables G I n B → ZMod M, ∃ j : Fin m,
    ∃ w : AllocatedCongruenceRankOutput X E inactive j → ZMod M,
      (∃ o, IsUnit (w o)) ∧ (M : ℝ) ^ (-C) <
        (𝔼 u : Fin j.val → LayerSamplerLongVariables inactive G B → ZMod M,
          if polynomialLinearRow (polynomialIterDifference j.val
            (∑ o, w o • allocatedOriginalTaggedTop inactive j
              (allocatedReadNoise f) (allocatedReadDeck f)
              (fun a => allocatedReadProjection f ⟨j,a.val⟩) v
              (allocatedCongruenceOutputEmbedding inactive j o)) u) = 0 then 1 else 0)

def allocatedResiduePrimePowerWitness
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (fM : AllocatedActualCoefficientIndex G X I E n B → ZMod M) : Prop :=
  ∀ p : P, allocatedResidueModulusBad inactive C (p.val ^ A p.val)
    (fun i => ZMod.castHom (hdiv p) (ZMod (p.val ^ A p.val)) (fM i))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

def allocatedChartResiduePrimePowerWitness
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M) : Prop :=
  allocatedResiduePrimePowerWitness inactive C P A M hdiv
    (allocatedChartActualResidues noise chart)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCenteredMeasurableFramedBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

theorem allocatedJointFrameRead_noise (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedReadNoise (allocatedJointFrameRead a f) =
      fun t => BooleanCubeKernel.jointIntegerFrame (a, allocatedReadNoise f) t.1 t.2 := by
  funext t
  rcases t with ⟨k,x⟩
  cases k <;> rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateExponentialFreezingBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem finiteFreezing_cost_le_uniform
    {cost densityCost budget θ : ℝ} {modulus Q k : ℕ}
    (hθ : 0 < θ) (hmodulus : 0 < modulus) (hQpos : 0 < Q)
    (hmodulusBound : (modulus : ℝ) ≤ budget) (hQbound : (Q : ℝ) ≤ max 1 budget) :
    max cost (densityCost + Real.log ((4 * modulus * Q * (k + 1 : ℝ)) / θ)) ≤
      max cost (densityCost + Real.log ((4 * budget * max 1 budget * (k + 1 : ℝ)) / θ)) := by
  apply max_le_max le_rfl
  apply add_le_add le_rfl
  apply Real.log_le_log
  · have hm : (0 : ℝ) < modulus := Nat.cast_pos.mpr hmodulus
    have hQ : (0 : ℝ) < Q := Nat.cast_pos.mpr hQpos
    positivity
  · apply div_le_div_of_nonneg_right _ hθ.le
    apply mul_le_mul_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ k + 1)
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hmodulusBound (by norm_num)) hQbound
      (Nat.cast_nonneg _) (mul_nonneg (by norm_num) ((Nat.cast_nonneg _).trans hmodulusBound))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateCoveredBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem finiteFreezing_initial_precision_exponent {p : ℝ} (hp : 0 ≤ p) :
    3 * p + Real.log 8 ≤ (p + 2) ^ 3 := by
  have hlog : Real.log (8 : ℝ) ≤ 8 := Real.log_le_self (by norm_num)
  nlinarith [sq_nonneg p, pow_nonneg hp 3]

theorem finiteFreezing_initial_discard_exponent {p : ℝ} (hp : 0 ≤ p) :
    3 * p + Real.log 8 ≤ 4 * p + 8 := by
  have hlog : Real.log (8 : ℝ) ≤ 8 := Real.log_le_self (by norm_num)
  linarith

theorem finiteFreezing_uniform_recursive_exponents (k : ℕ) {p b a : ℝ}
    (hp : 0 ≤ p) {C : ℕ} (hC : 2 ≤ C)
    (hb : b ≤ (p + C) ^ C) (hk : (k : ℝ) ≤ (p + C) ^ C)
    (ha : a ≤ (p + C) ^ C) :
    (p + C) ^ C + Real.log 4 + 2 * b + Real.log (k + 1 : ℝ) + (4 * p + 8) ≤
        finiteFreezingRecursiveParameter C p ∧
      a + 2 * b ≤ finiteFreezingRecursiveParameter C p ∧
      p + Real.log 2 ≤ finiteFreezingRecursiveParameter C p := by
  have hS : 0 ≤ (p + C) ^ C := pow_nonneg (by positivity) _
  have hpS := finiteFreezing_initial_le_polynomial hp hC
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hklog : Real.log (k + 1 : ℝ) ≤ (k : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < k + 1)
    linarith
  unfold finiteFreezingRecursiveParameter
  constructor
  · linarith
  constructor <;> linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastNativeResidueTest
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical Matrix

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable (inactive : LayerSamplerAxis I n → Prop)

def forecastNativeSpatialResidue (hm : 0 < m) {R : Type*}
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → R) : X → R :=
  fun x => out ⟨⟨0, hm⟩, .inl ⟨x, rfl⟩⟩

noncomputable def forecastNativeSheetResidue (q : ℕ)
    (frozen : ∀ j, {i : Fin (n j) // inactive ⟨j, .inr i⟩} → ℤ)
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod q)
    (j : Fin m) (i : Fin (n j)) : ZMod q :=
  if hi : inactive ⟨j, .inr i⟩ then (frozen j ⟨i, hi⟩ : ZMod q)
  else out ⟨j, .inr (.inr ⟨i, hi⟩)⟩

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

noncomputable def forecastNativeDeckResidueMatrix (q : ℕ) [NeZero q] (j : Fin m) :
    Matrix (J j) (Fin (n j) ⊕ E j) ℤ :=
  Classical.choose (exists_bounded_integerMap_residue_matrix
    (standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (b j) (hb j)).symm.toLinearMap q)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativeJointTestBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {A : Type*}

noncomputable def forecastInactiveShortGrid
    (selected : A → Σ j : Fin m, Fin (n j))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (u : PrincipalAxisTuples (α := Empty) (allocatedShortAxis U basis S.value)
      (allocatedPrincipalSides B U basis S)) :
    A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ :=
  forecastInactiveFixedOutput B U basis S selected c
    (fun _ => integerScalarCubeBoxZero Empty S.value S.positive)
    (principalAxisJoin (allocatedShortAxis U basis S.value) u
      (fun j => integerScalarCubeBoxZero Empty
        (allocatedPrincipalSides B U basis S ⟨j.1.val, j.2⟩)
        (allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ)
local notation "short" => allocatedShortAxis (I := I) U b Lsize
local notation "Grid" => AllocatedShortIntegerAxis U b Lsize →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

noncomputable def forecastShortGridNormalized (R : Fin m → ℝ) (grid : Grid) :
    {a : LayerSamplerAxis I n // short a} → ℝ := fun a =>
  let i := (allocatedShortIntegerAxisEquiv (I := I) U b Lsize).symm a
  (grid i ⟨∅, Finset.mem_univ _⟩ : ℝ) / basisAxisScale (b i.val.1) i.val.2 / R i.val.1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleCongruenceOutput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical
open BooleanCubeKernel

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value

def allocatedOriginalSampleCongruenceProjection
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (j : Fin m) (a : AllocatedDegreeActiveAxis short j) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ :=
  match a.val with
  | .inl _ => fun _ => 0
  | .inr i => (sample j).2 i

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local instance slicedPhysicalDensityCRTNeZero : NeZero Ncrt :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateRealThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable def candidateSideCutoffCost (bound : ℝ) : ℝ :=
  Real.log ((max (candidateSideCutoff bound) 1 : ℕ) : ℝ)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualCandidateSpatialCenter
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
  N poly hm τ ξ stride cells center)

theorem path_base_abs_le (z : A.Path) (x : X) : |(z.1.val x : ℝ)| ≤ N x := by
  have hz := z.1.property
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hz
  have hax := (mem_integerBox _ _).mp ha x
  have hx := congrFun he x
  simp only [Pi.add_apply] at hx
  have hi : |z.1.val x| ≤ (N x : ℤ) := by
    rw [abs_of_nonneg (by omega : 0 ≤ z.1.val x)]
    omega
  exact_mod_cast hi

theorem path_spatial_center_mass_le_trim (z : A.Path) (x : X) :
    |(jointIntegerFrame (z.1.val, z.2.val) none x : ℝ)| / (N x : ℝ) + τ / 8 ≤
      1 + τ / 4 := by
  have hN : (0 : ℝ) < N x := by exact_mod_cast A.size_pos x
  have hnoise := rectangularWeightIndices_zero_bound
    (allocatedExternalCandidateWidths B U b S N τ ξ) z.2.property (none, x)
  have hnoise' : |(z.2.val (none, x) : ℝ)| ≤ τ * (N x : ℝ) / 8 := by
    simpa only [allocatedExternalCandidateWidths, narrowTrimmedSpatialWidths,
      trimmedSpatialWidths, centeredSpatialWidths, one_mul, mul_div_assoc] using hnoise
  have hcenter : |(jointIntegerFrame (z.1.val, z.2.val) none x : ℝ)| ≤
      (N x : ℝ) + τ * (N x : ℝ) / 8 := by
    simp only [jointIntegerFrame, Int.cast_add]
    exact (abs_add_le _ _).trans (add_le_add (A.path_base_abs_le z x) hnoise')
  have hnorm : |(jointIntegerFrame (z.1.val, z.2.val) none x : ℝ)| / (N x : ℝ) ≤
      1 + τ / 8 := by
    apply (div_le_iff₀ hN).mpr
    nlinarith
  linarith

theorem path_spatial_center_mass_le (hτ1 : τ ≤ 1) (z : A.Path) (x : X) :
    |(jointIntegerFrame (z.1.val, z.2.val) none x : ℝ)| / (N x : ℝ) + τ / 8 ≤ 2 := by
  have h := A.path_spatial_center_mass_le_trim z x
  linarith

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineResidueEpoch
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

noncomputable def RetainedAffineResidueEpoch {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ) (p cost : ℝ) (C : ℕ) : Prop :=
  ∃ (v : Fin d → D.filtration.AssociatedGraded) (q P : ℕ) (hP : 0 < P)
      (κ : D.RealGroup)
      (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω W.toSubmodule ∧
    (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (v i) j) ≤ p) ∧
    0 < q ∧ (q : ℝ) ≤ Real.exp p ∧ (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ κ ∈ D.realLattice ∧
    E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩ ∧
    D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A (Real.exp (p + 2)) E ∧
    (∀ B : σ → ℝ, (∀ i, 0 < B i) → ∀ (r : ℚ) (h : σ → ℚ),
      (∀ i, |(h i : ℝ)| ≤ A i) → (∀ i, |(r : ℝ)| * B i ≤ A i) →
      D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) B (Real.exp (p + 2))
        (D.filtration.realification.scalarAffineAdaptedHom r h E)) ∧
    D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) q R ∧
    coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
    coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
    (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      D.filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
    HasFixedAffineResidueChild D W b p q P hP C 1 cost

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineWholeProfileComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (α : Type*) [Fintype α] [DecidableEq α] (O : Fin m → Type*) [∀ j, Fintype (O j)]

noncomputable def allocatedAffineSourceReferenceError (ρ : ℝ≥0) (P η : ℝ)
    (M H : PrincipalTupleIndex
      (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val)
      (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) → ℕ)
    (ε mesh Cmask : ℝ) : ℝ :=
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), Real.exp_nonneg _⟩
      let cap := bound ^ Fintype.card (LayerSamplerAxis I n)
      let lip := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap
      let sourceError := η +
        ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
          (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε) *
          (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1)
      let radius := max (Real.exp P * (partitionedIdealRadius α m + 1)) (Real.exp (allocatedJetSupportLog (G := G) B α O P))
      let Ki : ℝ≥0 := ‖(∏ o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1), |R o.1.val.1|)⁻¹‖₊ *
        (affineProductProfileLip (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) ρ * ⟨Real.exp P, Real.exp_nonneg _⟩)
      let select := allocatedLongIntegerSelect B U basis S (O := O)
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
          (sourceError + (2 * radius) ^ Fintype.card (UnselectedColumn select) *
            ((2 * radius + 2) ^ Fintype.card {o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) // allocatedLongIntegerCoordinate B U basis S (O := O) o} *
              ((Ki : ℝ) + lip) * mesh))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

def AllocatedAffineReferenceComparison
    (δ η : ℝ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) : Prop :=
      ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (_hR : ∀ j, 0 < R j) (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (hMk : 0 < Mk)
        (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
        (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      ∀ (L step H M : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
        (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
        (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
        (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
        (outputModulus : ℕ)
        (outputResidue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod outputModulus))
        {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
        (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (hCmask : 1 ≤ Cmask)
        (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j outputModulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j outputModulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let discrete := fun z : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) → ℝ =>
        (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
          (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
          (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
            (principalTupleFlatten (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) α
              (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z)
      (∫ z, |allocatedLongProfileDensity B U basis S x rows outputModulus outputResidue ideal z -
          allocatedLongProfileDensity B U basis S x rows outputModulus outputResidue discrete z|
        ∂allocatedLongJetReference B U basis S O) ≤
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η M H ε mesh Cmask

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

def AllocatedAffineCoefficientComparison
    (δ η : ℝ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1) : Prop :=
  ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      ∀ (hσsmall : ∀ j, σ j ≤ t),
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (hMk : 0 < Mk)
        (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
        (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      let L := principalAxisLength (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S)
      let hL := fun j : PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) => allocatedPrincipalSides_pos B U basis S
        (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j))
      ∀ (H step : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : ℕ) (hm : 0 < modulus)
        (residue : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ZMod modulus)
        (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
        (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
        (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
        (hq : Fintype.card α ≤ m + 1)
        {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
        (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
        (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S))
        (hv₀ : (containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
          (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0),
      let outputResidue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
      ∀ {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
        (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (hCmask : 1 ≤ Cmask)
        (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let law := containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
        (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize
      (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA
            (fun j => (hσsmall j).trans htone) z) -
          allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z|
        ∂allocatedLongJetReference B U basis S O) ≤
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
          (Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} * εcoef *
            (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
              Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}) +
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

def AllocatedAffineCoveredComparison
    (δ η : ℝ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (_ : t ≤ 1) : Prop :=
  ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      ∀ (hσsmall : ∀ j, σ j ≤ t),
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (hMk : 0 < Mk)
        (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
        (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      let L := principalAxisLength (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S)
      let hL := fun j : PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) => allocatedPrincipalSides_pos B U basis S
        (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j))
      ∀ (H step : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : ℕ) (hm : 0 < modulus)
        (residue : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ZMod modulus)
        (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
        (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
        (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
        (hq : Fintype.card α ≤ m + 1)
        {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
        (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
        (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S))
        (hv₀ : (containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
          (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0),
      let outputResidue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
      ∀ {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
        (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (hCmask : 1 ≤ Cmask)
        (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let law := containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
        (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize
      ∀ (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
        (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d]
        (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)
        (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1),
      ‖(∫ p, law.complexMean (fun v => F (((allocatedCoefficientSplit B U basis S) p.1).1,
          euclideanCoefficientJetMap U
            (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v))
            (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v)) rows
            (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
          ∂(allocatedCoefficientSource B U basis hR hσ S).prod
            (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).toMeasure) -
        ∫ a₀, ∫ z, (allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z : ℂ) *
          allocatedCoveredFixedTest B U basis S x u v₀ rows Q hb o bW d F a₀ z
          ∂allocatedLongJetReference B U basis S O ∂allocatedFrozenCoefficientSource B U basis hR hσ S‖ ≤
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
          (Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} * εcoef *
            (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
              Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}) +
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawRecoveredRationalCardinalityCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators NNReal Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

noncomputable def forecastFrozenIntegerMixedValue
    (z : ∀ j, Fin (n j) → ℤ) (v : (Σ j, J j) → ℝ) :
    ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
  fun j => ((mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
    ((EuclideanSpace.equiv (J j) ℝ).symm (fun i => v ⟨j,i⟩))).1, z j)

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

variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
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

noncomputable def forecastRecoveredIntegerLabels (β : (Σ j, J j) → ℤ) :
    ∀ j, Fin (n j) ⊕ Eout j → ℤ :=
  fun j => standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (basis j) (hb j)
    (fun i => β ⟨j,i⟩)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedAffineCutoffCost
namespace OAI

section

namespace Erdos3

theorem le_monomialScale_of_coordinate {A : Type*} (T : A → ℝ)
    (hT : ∀ i, 1 ≤ T i) {α : A →₀ ℕ} (i : A) (hi : α i ≠ 0) :
    T i ≤ monomialScale T α := by
  classical
  have hp : T i ≤ T i ^ α i := by
    simpa only [pow_one] using pow_le_pow_right₀ (hT i) (Nat.one_le_iff_ne_zero.mpr hi)
  have hs : ({i} : Finset A) ⊆ α.support :=
    Finset.singleton_subset_iff.mpr (Finsupp.mem_support_iff.mpr hi)
  have hprod := Finset.prod_le_prod_of_subset_of_one_le hs
    (fun j _ => pow_nonneg (zero_le_one.trans (hT j)) (α j))
    (fun j _ _ => one_le_pow₀ (hT j))
  exact hp.trans (by
    simpa only [Finset.prod_singleton, monomialScale, Finsupp.prod] using hprod)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineCanonicalBackendBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration

noncomputable def canonicalSectionPolynomial (s : ℕ) (P : Polynomial ℕ) : Polynomial ℕ :=
  2 * (P + Polynomial.C (s + 3)) ^ (s + 3) +
    ((P + Polynomial.C (s + 3)) ^ (s + 3)) ^ 2 + P

end Erdos3.VectorPolynomial

end

end OAI
end


