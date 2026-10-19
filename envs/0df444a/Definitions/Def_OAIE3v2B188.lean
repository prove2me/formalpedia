-- Prove2me | Definitions.Def_OAIE3v2B188
-- name    : OAIE3v2B188
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:50:12.861014+00:00
-- url     : https://prove2.me/theorems/a83d59ee-58aa-4c97-b043-6ffc808a90c5
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 191 of 311
-- statement:
--   Definitions bundle 191 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B164`, `OAIE3v2B165`, `OAIE3v2B169`, `OAIE3v2B170`, `OAIE3v2B171`, `OAIE3v2B172` of this split.
--
--   Modules: `Estimates/CommonCoefficientFourAnnihilators.lean`, `Estimates/CommonDependentIntegralModel.lean`, `Estimates/CommonMarkedMultidegree.lean`, `Estimates/CubeSignalAlgebra.lean`, `Estimates/DiagonalWrapComparison.lean`, `Estimates/MarkedEvaluationJointBounds.lean`, `Estimates/MarkedLocalCoefficientValue.lean`, `Estimates/MarkedPureEvaluation.lean`, `Estimates/MarkedShiftGeneratorBounds.lean`, `Estimates/MixedAnchorExpansion.lean`, `Estimates/MixedFrozenMiddleRows.lean`, `Estimates/MixedPermutationTensor.lean`, `Estimates/MixedRootCyclicComparison.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/NativeMixedReflectionBridge.lean`, `Estimates/NativeOrbitOuterControl.lean`, `Estimates/NativeSubspaceFreeModel.lean`, `Estimates/OriginalMixedRootEquivalence.lean`, `Estimates/RealAnnihilatorCorrections.lean`, `Estimates/SampledNativeModel.lean`, `Estimates/SharedFreeComparisonLift.lean`, `Estimates/SourceUnitCover.lean`, `Estimates/TensorSquarePairComparison.lean`, `Estimates/UniformControlledNativeExternalNetsOfRecovery.lean`, `Estimates/UnitVerticalCyclicDifference.lean`, `Estimates/VectorSubspaceCorrectionRepresentatives.lean`, `Fourier/BohrNiltestBudget.lean`, `Geometry/MarkedLocalObservableMetric.lean`, `Geometry/MixedCoordinateTransfer.lean`, `Geometry/NormalizedMarkedChart.lean`, `Lattices/NativeIntegerHalving.lean`, `Linear/CommonFreeSpanBounds.lean`, `Linear/MarkedProjectionBounds.lean`, `Linear/RealFourBalancedDual.lean`, `Linear/SharedFreeComparisonBasis.lean`, `Nilpotent/MissingCoordinateNiltestApproximation.lean`, `Nilpotent/NativeMultidegreeNiltest.lean`, `Nilpotent/NativeRankZeroNiltest.lean`, `Polynomial/LocalPhaseMarkedObservable.lean`, `Polynomial/MarkedPolynomialGenerators.lean`, `Polynomial/NativePolynomialOrbitConstruction.lean`, `Polynomial/NormalizedMarkedPhase.lean`, `Polynomial/OrdinaryPolynomialPhaseAffineInverse.lean`, `Polynomial/PositiveDegreeCyclicDifference.lean`, `Sampling/MixedAssignmentSampling.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B164
import Definitions.Def_OAIE3v2B165
import Definitions.Def_OAIE3v2B169
import Definitions.Def_OAIE3v2B170
import Definitions.Def_OAIE3v2B171
import Definitions.Def_OAIE3v2B172

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold CircleFourier
open scoped TensorProduct NNReal

theorem exists_cyclic_character_niltest {N : ℕ} [NeZero N] (χ : AddChar (ZMod N) ℂ) :
    ∃ T : (RationalTorus.nilmanifold 1).Niltest (fun _ : Unit => 1),
      T.normBound ≤ 1 ∧ T.ComplexityLE 12 ∧
      ∀ x : ZMod N, T.evalCyclic N (fun _ => x) = χ x := by
  obtain ⟨r, hr⟩ := AddChar.zmodAddEquiv.surjective χ
  obtain ⟨theta, htheta⟩ := CyclicBohr.exists_real_frequency_phase r
  have hphase (x : ZMod N) :
      character (((x.val : ℝ) * theta : ℝ) : CircleFourier.Circle) = χ x := by
    rw [htheta]
    exact congrArg (fun ψ : AddChar (ZMod N) ℂ => ψ x) hr
  let Ψ : (Fin 1 → CircleFourier.Circle) → ℂ := fun v => character (v 0)
  have hΨ (v) : ‖Ψ v‖ ≤ (1 : ℝ≥0) := by
    exact le_of_eq (norm_character (v 0))
  have hLip : LipschitzWith characterLipConstant Ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (character_lipschitz.dist_le_mul (x 0) (y 0)).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y 0) characterLipConstant.coe_nonneg)
  let T := RationalTorus.affineNiltest 1 0 (fun _ : Unit => fun _ => theta)
    Ψ 1 characterLipConstant hΨ hLip
  have hT : T.ComplexityLE 12 := by
    apply RationalTorus.affineNiltest_complexity 1 0 (fun _ : Unit => fun _ => theta)
      Ψ 1 characterLipConstant hΨ hLip (by norm_num) (by norm_num)
    change Real.log (2 + 1 + 2 * Real.pi) ≤ 12
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + 1 + 2 * Real.pi)
    linarith [Real.pi_lt_four]
  refine ⟨T, le_rfl, hT, ?_⟩
  intro x
  simpa [T, Ψ, RationalTorus.affineNiltest_evalCyclic] using hphase x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem adaptedPolynomialRealValueHom_constant (t : σ → ℝ) (κ : F.realification.Group) :
    F.adaptedPolynomialRealValueHom w t (F.realification.adaptedConstantGroupHom w κ) = κ := by
  apply NilpotentLieBCHGroup.ext
  rw [adaptedPolynomialRealValueHom_coord, F.realification.adaptedConstantGroupHom_log,
    eval₂_monomial, Finsupp.prod_zero_index, one_smul]

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ)

theorem lattice_factorization_quotient
    (g E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ = g)
    (t : σ → ℝ) :
    (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w t g) : D.Space) =
      QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w t E *
        D.filtration.adaptedPolynomialRealValueHom w t b *
        D.filtration.adaptedPolynomialRealValueHom w t R) := by
  have h := congrArg (D.filtration.adaptedPolynomialRealValueHom w t) hprod
  simp only [map_mul, NilpotentLieFiltration.adaptedPolynomialRealValueHom_constant] at h
  rw [← h]
  exact QuotientGroup.mk_mul_of_mem _ hκ

namespace Niltest

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem evalReal_of_lattice_factorization (T : D.Niltest w)
    (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (t : σ → ℝ) :
    T.evalReal t = T.observable (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom w t E *
        D.filtration.adaptedPolynomialRealValueHom w t b *
        D.filtration.adaptedPolynomialRealValueHom w t R)) := by
  exact congrArg T.observable (lattice_factorization_quotient D w _ E b R κ hκ hprod t)

theorem eval_of_lattice_factorization (T : D.Niltest w)
    (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (x : σ → ℤ) :
    T.eval x = T.observable (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) E *
        D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b *
        D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) R)) := by
  rw [← T.evalReal_integer]
  exact evalReal_of_lattice_factorization D w T E b R κ hκ hprod _

end Niltest
end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SourceUnitCover
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

namespace NativeMultidegreeNilcharacter

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

theorem mono_eval (hpq : p ≤ q) (i : Fin W.outputDim) (x : σ → ℤ) :
    (W.mono hpq).eval i x = W.eval i x := rfl

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r) {p : ℝ}
  (V : D.UnitVerticalObservable (R.realSubgroup s r) I p)
  (Λ : Subgroup D.filtration.Group) (hΛ : Λ ≤ D.lattice)
  (m : ℕ) (hm : 0 < m)
  (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid m)

noncomputable def onSublattice :
    (D.withLattice Λ m hm hin hout).UnitVerticalObservable
      ((R.withLattice Λ m hm hin hout).realSubgroup s r) I p where
  observable i := V.observable i ∘ sublatticeProjection D (D.withLattice Λ m hm hin hout) hΛ
  unit x := V.unit _
  norm i x := V.norm i _
  lipBound := V.lipBound
  lip_bound := V.lip_bound
  lipschitz := fun i => sublattice_pullback_lipschitz D (D.withLattice Λ m hm hin hout)
    hΛ rfl (V.observable i) (V.lipschitz i)
  frequency := V.frequency
  height := V.height
  vertical i z hz x := by
    induction x using Quotient.inductionOn with
    | h x => exact V.vertical i z hz (QuotientGroup.mk x)
  integral z hz hlat := V.integral z hz (Subgroup.map_mono hΛ hlat)

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_source_unit_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M I : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s t d e r : ℕ}
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (E : RationalFilteredNilmanifold M t e) (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ},
      0 ≤ p → R.ComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup D.filtration.Group,
        Λ ≤ D.lattice ∧ (Λ.subgroupOf D.lattice).Characteristic ∧
        (Λ.subgroupOf D.lattice).Normal ∧ (Λ.subgroupOf D.lattice).FiniteIndex ∧
        (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          (R.withLattice Λ N hN hin hout).ComplexityLE ((p + C) ^ C) ∧
          Λ ≤ E.lattice.comap (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ) ∧
          ∀ V : D.UnitVerticalObservable (R.realSubgroup s r) I p,
            ∃ U : (D.withLattice Λ N hN hin hout).UnitVerticalObservable
                ((R.withLattice Λ N hN hin hout).realSubgroup s r) I ((p + C) ^ C),
              U.frequency = V.frequency ∧ U.lipBound = V.lipBound ∧
              ∀ i x, U.observable i (QuotientGroup.mk x) = V.observable i (QuotientGroup.mk x) := by
  obtain ⟨C, hC, hcover⟩ := exists_native_source_cover
  refine ⟨C, hC, ?_⟩
  intro L M I _ _ _ _ _ _ _ _ _ s t d e r D R E φ p hp hR hE hentries
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast (show 1 ≤ C by omega)
  have hpC : p ≤ (p + C) ^ C := by
    calc
      p ≤ p + C := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (p + C) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ C)
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hgeometry, hmap⟩ :=
    hcover D E φ hp hR.1 hE hentries
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout,
    R.withLattice_complexity Λ N hN hin hout hR hpC hgeometry, hmap, ?_⟩
  intro V
  exact ⟨(V.onSublattice R Λ hΛ N hN hin hout).mono hpC, rfl, rfl, fun _ _ => rfl⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativePolynomialOrbitConstruction
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

namespace NativePolynomialOrbitFactors

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
  {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p q : ℝ}
  (R : NativePolynomialOrbitFactors D g eta A p)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem eval_niltest (T : D.Niltest (fun _ : σ => 1))
    (hT : g = ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (x : σ → ℤ) :
    T.eval x = T.observable (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.slow *
        D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.middle *
        D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.rational)) :=
  Niltest.eval_of_lattice_factorization D (fun _ : σ => 1) T R.slow R.middle R.rational
    R.latticeConstant R.latticeConstant_mem (R.product.trans hT) x

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOrbitOuterControl
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold

namespace NativePolynomialOrbitFactors

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
  {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
  (R : NativePolynomialOrbitFactors D g eta A p)

def HasOuterValueControl (b : ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp b ∧
    (∀ x : σ → ℤ, (D.basis.baseChange ℝ).equivFun (R.rationalValue x).coord ∈
      realDenominatorGrid m) ∧
    ∀ x : σ → ℤ, (∀ i, |(x i : ℝ)| ≤ A i) → ∀ i,
      |(D.basis.baseChange ℝ).repr (R.slowValue x).coord i| ≤ Real.exp b

theorem hasOuterValueControl_mono {a b : ℝ} (h : R.HasOuterValueControl a) (hab : a ≤ b) :
    R.HasOuterValueControl b := by
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := h
  exact ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hab), hrat,
    fun x hx i => (hslow x hx i).trans (Real.exp_le_exp.mpr hab)⟩

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeModel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeSampleCorrelation

variable {σ X : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ}
  {S : Finset X} {sample : X → σ → ℤ} {f : X → ℂ}

theorem exists_of_expansion {eta : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p eta) (hq : 0 ≤ q)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 x ∈ S, f x * star (eta (sample x))‖) :
    Nonempty (NativeSampleCorrelation w s (q + p) S sample f) := by
  obtain ⟨i, hi⟩ := E.select_sample_correlation S sample f hcorr
  exact ⟨{
    L := E.L i
    dim := E.dim i
    model := E.model i
    test := E.test i
    complexity := (E.complexity i).mono (le_add_of_nonneg_left hq)
    correlation := hi }⟩

end NativeSampleCorrelation

end Erdos3

end

section

namespace Erdos3.NativeSampleModel

open CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [instance] VerticalExpansion.finite

end Erdos3.NativeSampleModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerHalving
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem RationalTorus.residueNiltest_eval {q : ℕ} [NeZero q] (j : ZMod q) (n : ℤ) :
    (residueNiltest j).eval (fun _ : Unit => n) = if (n : ZMod q) = j then 1 else 0 := by
  classical
  unfold residueNiltest realAffineNiltest
  rw [affineNiltest_eval]
  simp only [reindexedRealObservable, Equiv.refl_apply,
    Finset.univ_unique, Finset.sum_singleton, Pi.add_apply, Pi.smul_apply,
    zero_add, smul_eq_mul, mul_one_div]
  rw [← ZMod.toAddCircle_intCast, CircleFourier.residueCutoff_at_grid]
  split_ifs <;> rfl

theorem exists_coordinate_residue_expansion {σ : Type*} [Fintype σ]
    {q : ℕ} [NeZero q] (k : σ) (j : ZMod q) {p : ℝ}
    (hp : 0 ≤ p) (hq : (q : ℝ) ≤ Real.exp p) :
    Nonempty (NativeIntegerExpansion (fun _ : σ => 1) 1 (p + 2)
      (fun x => if (x k : ZMod q) = j then 1 else 0)) := by
  let T := RationalTorus.residueNiltest j
  let a : (σ → ℤ) →+ ℤ := { toFun := fun x => x k, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let U := T.linearPullbackHom (fun _ : Unit => a)
  refine ⟨NativeIntegerExpansion.ofTest U (RationalTorus.residueNiltest_complexity j hp hq) ?_⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom]
  exact (RationalTorus.residueNiltest_eval j (x k)).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.MissingCoordinateNiltestApproximation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct

theorem niltest_eval_eq_of_zero_coordinate {σ L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
    (M : D.MultidegreeStructure bound) (i : σ) (hi : bound i = 0)
    (T : D.Niltest (fun _ : σ => 1)) (g : M.filtration.realification.PolynomialOrbit)
    (hT : T.orbit = M.orbitToOrdinary g) (x y : σ → ℤ)
    (hxy : ∀ j, j ≠ i → x j = y j) : T.eval x = T.eval y := by
  unfold RationalFilteredNilmanifold.Niltest.eval
  rw [hT, M.orbitToOrdinary_eval, M.orbitToOrdinary_eval]
  apply congrArg T.observable
  apply congrArg QuotientGroup.mk
  exact M.filtration.realification.polynomialOrbitEval_eq_of_zero_coordinate i hi g x y hxy

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeMultidegreeNiltest
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {σ τ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

theorem component_eval (i : Fin W.outputDim) (x : σ → ℤ) : (W.component i).eval x = W.eval i x := by
  exact congrArg (fun z : W.model.RealGroup => W.vertical.observable i (QuotientGroup.mk z))
    (W.multi.orbitToOrdinary_eval W.orbit x)

theorem exists_linear_niltest [Fintype τ] (i : Fin W.outputDim) (f : σ → ((τ → ℤ) →+ ℤ)) :
    ∃ T : W.model.Niltest (fun _ : τ => 1), T.normBound = 1 ∧ T.ComplexityLE (p + 4) ∧
      ∀ x, T.eval x = W.eval i (fun j => f j x) := by
  refine ⟨(W.component i).linearPullbackHom f, rfl, W.component_complexity i, ?_⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom, W.component_eval]

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoordinateTransfer
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem antisymmetricKernel_cyclic {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (N : ℕ) [NeZero N] (i j : Fin W.outputDim) (x y : ZMod N) :
    W.antisymmetricKernel i j (x.val : ℤ) (y.val : ℤ) =
      star (W.evalCyclic N i (correlationInput x y)) * W.evalCyclic N j (correlationInput y x) := by
  have he (k : Fin W.outputDim) (x y : ZMod N) :
      W.eval k (correlationInput (x.val : ℤ) (y.val : ℤ)) =
        W.evalCyclic N k (correlationInput x y) := by
    apply congrArg (W.eval k)
    funext l
    fin_cases l <;> rfl
  simp only [antisymmetricKernel, he]

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TensorSquarePairComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def halfDilationExchangeCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ ij : Fin W.outputDim × Fin W.outputDim,
    (star ((W.rationalDilation (1 / 2)).eval a x * star (W.eval ij.1 (fun k => x k / 2))) *
      ((W.rationalDilation (1 / 2)).eval b (fun k => x k.rev) *
        star (W.eval ij.2 (fun k => x k.rev / 2)))) * G ij.1 ij.2 (fun k => x k / 2)

end NativeMultidegreeNilcharacter
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeRankZeroNiltest
namespace OAI

section

namespace Erdos3.NativeDegreeRankFamily

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily (s + 1) 0 A p)

noncomputable def lowerComponent (i : Fin W.outputDim) (a : A) :
    (W.model.dropTop W.rankZero_top_eq_bot).Niltest (fun _ : Unit => 1) :=
  (W.component i a).dropTop W.rankZero_top_eq_bot

end Erdos3.NativeDegreeRankFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
namespace OAI

section

namespace Erdos3

open Module

theorem exists_submodule_basis_of_spanning_logHeight
    {V ι κ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι]
    (e : Basis ι ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) {p : ℝ}
    (hv : ∀ a i, rationalLogHeight (e.repr (v a) i) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ U)) ℚ U,
      ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p := by
  classical
  let : FiniteDimensional ℚ V := e.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  refine ⟨(Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan), ?_⟩
  intro a i
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  obtain ⟨k, hk⟩ := hz a
  rw [← hk]
  exact hv k i

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_petalComparisonSpace_basis_logHeight
    {V μ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype μ]
    (e : Basis μ ℚ V) (C P K : Submodule ℚ V)
    (c : Basis (Fin (finrank ℚ C)) ℚ C) (p : Basis (Fin (finrank ℚ P)) ℚ P)
    (k : Basis (Fin (finrank ℚ K)) ℚ K) {q : ℝ} (hq : 0 ≤ q)
    (hc : ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ q)
    (hp : ∀ a i, rationalLogHeight (e.repr (p a : V) i) ≤ q)
    (hk : ∀ a i, rationalLogHeight (e.repr (k a : V) i) ≤ q) :
    ∃ b : Basis (Fin (finrank ℚ (petalComparisonSpace C P K))) ℚ (petalComparisonSpace C P K),
      ∀ a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => e)).repr (b a : Fin 2 → V) i) ≤ q := by
  classical
  let Δ : V →ₗ[ℚ] (Fin 2 → V) := LinearMap.pi (fun _ => LinearMap.id)
  let S₀ : V →ₗ[ℚ] (Fin 2 → V) := LinearMap.single ℚ (fun _ : Fin 2 => V) 0
  let S₁ : V →ₗ[ℚ] (Fin 2 → V) := LinearMap.single ℚ (fun _ : Fin 2 => V) 1
  have hspace : petalComparisonSpace C P K =
      (C.map Δ ⊔ P.map S₀) ⊔ (K.map S₀ ⊔ K.map S₁) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, u, hu, v, hv, h₀, h₁⟩ := petalComparisonSpace_decompose C P K x hx
      have hh : (Δ a + S₀ b) + (S₀ u + S₁ v) ∈
          (C.map Δ ⊔ P.map S₀) ⊔ (K.map S₀ ⊔ K.map S₁) :=
        Submodule.add_mem_sup (Submodule.add_mem_sup ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
          (Submodule.add_mem_sup ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩)
      convert hh using 1
      ext i
      fin_cases i <;> simp [Δ, S₀, S₁, LinearMap.single_apply, h₀, h₁]
    · apply sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [Δ] using And.intro (Submodule.mem_sup_left ha)
          ((P ⊔ K).zero_mem)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [S₀, LinearMap.single_apply] using
          And.intro ((C ⊔ K).zero_mem) (Submodule.mem_sup_left ha)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [S₀, LinearMap.single_apply] using
          And.intro ((C ⊔ K).zero_mem) (Submodule.mem_sup_right ha)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [S₁, LinearMap.single_apply] using
          And.intro (Submodule.mem_sup_right ha) (Submodule.mem_sup_right (K.neg_mem ha))
  have hspan (U : Submodule ℚ V) (b : Basis (Fin (finrank ℚ U)) ℚ U) :
      Submodule.span ℚ (Set.range (fun j => (b j : V))) = U := by
    change Submodule.span ℚ (Set.range (U.subtype ∘ b)) = U
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hmap (U : Submodule ℚ V) (b : Basis (Fin (finrank ℚ U)) ℚ U)
      (φ : V →ₗ[ℚ] (Fin 2 → V)) :
      Submodule.span ℚ (Set.range (fun j => φ (b j : V))) = U.map φ := by
    change Submodule.span ℚ (Set.range (φ ∘ fun j => (b j : V))) = _
    rw [Set.range_comp, ← Submodule.map_span, hspan]
  let v := Sum.elim (Sum.elim (fun j => Δ (c j : V)) (fun j => S₀ (p j : V)))
    (Sum.elim (fun j => S₀ (k j : V)) (fun j => S₁ (k j : V)))
  have hv : Submodule.span ℚ (Set.range v) = petalComparisonSpace C P K := by
    dsimp only [v]
    rw [span_range_sumElim, span_range_sumElim, span_range_sumElim,
      hmap, hmap, hmap, hmap, hspace]
  have hsingle (j : Fin 2) (x : V) (hx : ∀ i, rationalLogHeight (e.repr x i) ≤ q)
      (i : Σ _ : Fin 2, μ) :
      rationalLogHeight ((Pi.basis (fun _ : Fin 2 => e)).repr
        (LinearMap.single ℚ (fun _ : Fin 2 => V) j x) i) ≤ q := by
    rcases i with ⟨i, a⟩
    by_cases hji : j = i
    · subst i
      simpa [Pi.basis_repr, LinearMap.single_apply] using hx a
    · simpa [Pi.basis_repr, LinearMap.single_apply, hji, Ne.symm hji, rationalLogHeight] using hq
  apply exists_submodule_basis_of_spanning_logHeight (Pi.basis (fun _ : Fin 2 => e)) _ v hv
  intro j i
  cases j with
  | inl j =>
    cases j with
    | inl j => simpa [v, Δ, Pi.basis_repr] using hc j i.2
    | inr j => exact hsingle 0 (p j) (hp j) i
  | inr j =>
    cases j with
    | inl j => exact hsingle 0 (k j) (hk j) i
    | inr j => exact hsingle 1 (k j) (hk j) i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
namespace OAI

section

namespace Erdos3.SubspaceFreeLift

open Module VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (S : Fin s → Submodule ℚ L)

noncomputable def generatorSpan (r : ℕ) (d : Fin s) : Submodule ℚ (Algebra S r) :=
  Submodule.span ℚ (Set.range (fun i => generator S r ⟨d, i⟩))

theorem generatorSpan_le_layer (hr : r ≤ s) (d : Fin s) :
    generatorSpan S r d ≤ (filtration S hr).layer (d.val + 1) 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact FreeDegreeRankLieAlgebra.of_mem_layer (Alphabet S) s r (weight S) (weight_pos S) hr ⟨d, i⟩

variable (B : ∀ d, Basis (Fin (finrank ℚ (S d))) ℚ (S d))

theorem coefficientLift_range (r : ℕ) (d : Fin s) :
    LinearMap.range (coefficientLift S B r d) = generatorSpan S r d :=
  (B d).constr_range ℚ

variable (F : DegreeRankLieFiltration L s r)
  (hS : ∀ d, S d ≤ F.layer (d.val + 1) 0)

theorem realCoefficientLift_mem (d : Fin s) (x : (S d).baseChange ℝ) :
    realCoefficientLift S B (r := r) d x ∈ (generatorSpan S r d).baseChange ℝ := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [realCoefficientLift_baseChange]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem a
      ((coefficientLift_range S B r d).le ⟨v, rfl⟩)
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

theorem realEvaluation_coefficientLift (d : Fin s) (x : (S d).baseChange ℝ) :
    realificationLieHom (evaluation S B F hS) (realCoefficientLift S B d x) = x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [realCoefficientLift_baseChange, realificationSubmoduleEquiv_coe]
  change (evaluation S B F hS).toLinearMap.baseChange ℝ
    ((coefficientLift S B r d).baseChange ℝ v) = _
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    change a ⊗ₜ[ℚ] evaluation S B F hS (coefficientLift S B r d v) = a ⊗ₜ[ℚ] v.val
    rw [evaluation_coefficientLift]
  | add v w hv hw => simp only [map_add, hv, hw]

end Erdos3.SubspaceFreeLift

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators
namespace OAI

section

namespace Erdos3

open Module

variable {R V ι κ : Type*} [Field R] [AddCommGroup V] [Module R V]

theorem fourBasisVectors_span (D : Submodule R V) (b : Basis κ R D) :
    Submodule.span R (Set.range (fourBasisVectors D b)) =
      Submodule.pi Set.univ (fun _ : Fin 4 => D) := by
  classical
  rw [fourBasisVectors, Set.range_comp, ← Submodule.map_span,
    (Pi.basis (fun _ : Fin 4 => b)).span_eq, Submodule.map_top]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Submodule.mem_pi.mpr (fun k _ => (y k).property)
  · intro hx
    exact ⟨fun k => ⟨x k, (Submodule.mem_pi.mp hx) k (Set.mem_univ k)⟩, rfl⟩

theorem fourCommonGenerators_span (C D : Submodule R V) (hDC : D ≤ C)
    (c : Basis ι R C) (b : Basis κ R D) :
    Submodule.span R (Set.range (Sum.elim (fun i => fourDiagonalMap (R := R) (c i : V))
      (fourBasisVectors D b))) = fourCommonModulo C D := by
  rw [span_range_sumElim, fourBasisVectors_span, fourCommonModulo_eq_sup C D hDC]
  congr 1
  change Submodule.span R (Set.range ((fourDiagonalMap (R := R)).comp C.subtype ∘ c)) = _
  rw [Set.range_comp, ← Submodule.map_span, c.span_eq, Submodule.map_top,
    LinearMap.range_comp, Submodule.range_subtype]

end Erdos3

end

section

namespace Erdos3

open Module

variable {R V κ : Type*} [Field R] [AddCommGroup V] [Module R V]

theorem fourBalancedGenerators_span (D : Submodule R V) (b : Basis κ R D) :
    Submodule.span R (Set.range ((fourBalanceProjection (R := R)) ∘ fourBasisVectors D b)) =
      fourBalancedDependent D := by
  rw [Set.range_comp, ← Submodule.map_span, fourBasisVectors_span]
  exact fourBalanceProjection_image D

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_bounded_four_annihilator
    {V ι κ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]
    (e : Basis ι ℚ V) (K : Submodule ℚ (Fin 4 → V)) (v : κ → Fin 4 → V)
    (hspan : Submodule.span ℚ (Set.range v) = K) {p : ℝ} (hp : 0 ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hv : ∀ a k i, rationalLogHeight (e.repr (v a k) i) ≤ p) :
    ∃ m : ℕ, m ≤ 4 * Fintype.card ι ∧ ∃ ℓ : (Fin 4 → V) →ₗ[ℚ] (Fin m → ℚ),
      Function.Surjective ℓ ∧ LinearMap.ker ℓ = K ∧
      ∀ k i j, rationalLogHeight (ℓ (LinearMap.single ℚ (fun _ : Fin 4 => V) k (e i)) j) ≤
        (p + 3) ^ 7 := by
  classical
  let b := Pi.basis (fun _ : Fin 4 => e)
  obtain ⟨H, _, hH, m, hm, f, hf⟩ := exists_submodule_quotient_basis_exp b K v hspan
    (one_le_ceil_exp p) (fun a i => rationalHeightLE_ceil_exp (hv a i.1 i.2))
    (by linarith : 0 ≤ p + 1) (hκ.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
  let ℓ : (Fin 4 → V) →ₗ[ℚ] (Fin m → ℚ) := f.equivFun.toLinearMap.comp K.mkQ
  have hker : LinearMap.ker ℓ = K := by
    ext x
    change f.equivFun (K.mkQ x) = 0 ↔ x ∈ K
    rw [f.equivFun.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero K
  refine ⟨m, ?_, ℓ, f.equivFun.surjective.comp K.mkQ_surjective, hker, ?_⟩
  · simpa only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] using hm
  · intro k i j
    have he : b ⟨k, i⟩ = LinearMap.single ℚ (fun _ : Fin 4 => V) k (e i) := by
      simp only [b, Pi.basis_apply, LinearMap.single_apply]
    rw [← he]
    change rationalLogHeight (f.repr (K.mkQ (b ⟨k, i⟩)) j) ≤ _
    have h := rationalLogHeight_le_of_height (hf j ⟨k, i⟩) hH
    simpa only [show p + 1 + 2 = p + 3 by ring] using h

theorem exists_bounded_refined_four_annihilator
    {V ι κ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]
    (e : Basis ι ℚ V) (C D : Submodule ℚ V) (hDC : D ≤ C)
    (K : Submodule ℚ (Fin 4 → V)) (v : κ → Fin 4 → V)
    (hspan : Submodule.span ℚ (Set.range v) = fourRefinedRelation C D K)
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hv : ∀ a k i, rationalLogHeight (e.repr (v a k) i) ≤ p) :
    ∃ m : ℕ, m ≤ 4 * Fintype.card ι ∧ ∃ ℓ : (Fin 4 → V) →ₗ[ℚ] (Fin m → ℚ),
      Function.Surjective ℓ ∧ LinearMap.ker ℓ = fourRefinedRelation C D K ∧
      (∀ k i j, rationalLogHeight (ℓ (LinearMap.single ℚ (fun _ : Fin 4 => V) k (e i)) j) ≤
        (p + 3) ^ 7) ∧
      (∀ x ∈ D, ℓ (fourDiagonalMap (R := ℚ) x) = 0) ∧
      (∀ z ∈ fourRefinedRelation C D K,
        ℓ (fourDiagonalMap (R := ℚ) (z 0)) +
          ℓ (LinearMap.single ℚ (fun _ : Fin 4 => V) 0 (z 0 + z 1 - z 2 - z 3)) = 0) ∧
      fourPetalSpace D (fourRefinedRelation C D K) =
        D ⊓ LinearMap.ker (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) := by
  obtain ⟨m, hm, ℓ, hsurj, hker, hheight⟩ :=
    exists_bounded_four_annihilator e _ v hspan hp hκ hv
  have hzero (z) (hz : z ∈ fourRefinedRelation C D K) : ℓ z = 0 := by
    exact LinearMap.mem_ker.mp (hker.symm ▸ hz)
  refine ⟨m, hm, ℓ, hsurj, hker, hheight, ?_, ?_, fourPetalSpace_eq_inf_ker D _ ℓ hker⟩
  · exact fun x hx => four_annihilator_common_zero D ℓ
      (fun z hz => hzero z (fourBalancedDependent_le_refined C D K hz)) x hx
  · exact fun z hz => four_refined_annihilator_identity C D hDC K ℓ hzero z hz

end Erdos3

end

section

namespace Erdos3

open Module

variable {V μ ι κ : Type*} [AddCommGroup V] [Module ℚ V]

theorem exists_fourCommonModulo_basis_logHeight [Fintype μ]
    (e : Basis μ ℚ V) (C D : Submodule ℚ V) (hDC : D ≤ C)
    (c : Basis ι ℚ C) (b : Basis κ ℚ D) {p : ℝ} (hp : 0 ≤ p)
    (hc : ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p) :
    ∃ a : Basis (Fin (finrank ℚ (fourCommonModulo C D))) ℚ (fourCommonModulo C D),
      ∀ j i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (a j : Fin 4 → V) i) ≤ p := by
  apply exists_submodule_basis_of_spanning_logHeight (Pi.basis (fun _ : Fin 4 => e)) _
    (Sum.elim (fun i => fourDiagonalMap (R := ℚ) (c i : V)) (fourBasisVectors D b))
    (fourCommonGenerators_span C D hDC c b)
  intro a i
  cases a with
  | inl a => exact hc a i.2
  | inr a => exact fourBasisVectors_logHeight e D b hp hb a i.1 i.2

theorem exists_fourBalancedDependent_basis_logHeight [Fintype μ]
    (e : Basis μ ℚ V) (D : Submodule ℚ V) (b : Basis κ ℚ D) {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p) :
    ∃ a : Basis (Fin (finrank ℚ (fourBalancedDependent D))) ℚ (fourBalancedDependent D),
      ∀ j i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (a j : Fin 4 → V) i) ≤ p := by
  apply exists_submodule_basis_of_spanning_logHeight (Pi.basis (fun _ : Fin 4 => e)) _
    ((fourBalanceProjection (R := ℚ)) ∘ fourBasisVectors D b) (fourBalancedGenerators_span D b)
  intro a i
  exact fourBalancedGenerators_logHeight e D b hp hb a i.1 i.2

end Erdos3

end

section

namespace Erdos3

open Module

variable {V μ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype μ]

theorem exists_fourRefinedRelation_basis_logHeight
    (e : Basis μ ℚ V) (C D : Submodule ℚ V) (hDC : D ≤ C)
    (K : Submodule ℚ (Fin 4 → V))
    (c : Basis (Fin (finrank ℚ C)) ℚ C) (b : Basis (Fin (finrank ℚ D)) ℚ D)
    (k : Basis (Fin (finrank ℚ K)) ℚ K) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card μ : ℝ) ≤ p)
    (hc : ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p)
    (hk : ∀ a i,
      rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (k a : Fin 4 → V) i) ≤ p) :
    ∃ a : Basis (Fin (finrank ℚ (fourRefinedRelation C D K))) ℚ (fourRefinedRelation C D K),
      ∀ j i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr
        (a j : Fin 4 → V) i) ≤ fourRefinementBasisBudget p := by
  classical
  let e4 := Pi.basis (fun _ : Fin 4 => e)
  have hspan (U : Submodule ℚ (Fin 4 → V)) (a : Basis (Fin (finrank ℚ U)) ℚ U) :
      Submodule.span ℚ (Set.range (fun j => (a j : Fin 4 → V))) = U := by
    change Submodule.span ℚ (Set.range (U.subtype ∘ a)) = U
    rw [Set.range_comp, ← Submodule.map_span, a.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hdim4 : (Fintype.card (Σ _ : Fin 4, μ) : ℝ) ≤ 4 * p := by
    simpa using mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4)
  have hcard (U : Submodule ℚ (Fin 4 → V)) :
      (Fintype.card (Fin (finrank ℚ U)) : ℝ) ≤ 4 * p := by
    have h := (Nat.cast_le (α := ℝ)).mpr (four_submodule_finrank_le e U)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    simpa using h.trans (mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4))
  have hp4 : p ≤ 4 * p := by linarith
  obtain ⟨s, hs⟩ := exists_fourCommonModulo_basis_logHeight e C D hDC c b hp hc hb
  have hu := exists_preimage_basis_logHeight e4 e4 K (fourCommonModulo C D)
    LinearMap.id (fun j => (k j : Fin 4 → V)) (fun j => (s j : Fin 4 → V))
    (hspan K k) (hspan _ s) (by positivity : 0 ≤ 4 * p) hdim4 (hcard K) (hcard _)
    (fun a i => (hk a i).trans hp4) (fun a i => (hs a i).trans hp4)
    (fun a i => (hk a i).trans hp4)
  obtain ⟨u, hu⟩ := hu
  obtain ⟨v, hv⟩ := exists_fourBalancedDependent_basis_logHeight e D b hp hb
  have hsum : Submodule.span ℚ (Set.range (Sum.elim
      (fun j => (u j : Fin 4 → V)) (fun j => (v j : Fin 4 → V)))) =
      fourRefinedRelation C D K := by
    rw [span_range_sumElim, hspan _ u, hspan _ v]
    rfl
  apply exists_submodule_basis_of_spanning_logHeight e4 _ _ hsum
  intro a i
  cases a with
  | inl a => exact (hu a i).trans (le_add_of_nonneg_left hp)
  | inr a =>
    exact (hv a i).trans
      (le_add_of_nonneg_right (preimageBasisBudget_nonneg (by positivity)))

theorem exists_fourRefinedRelation_annihilator
    (e : Basis μ ℚ V) (C D : Submodule ℚ V) (hDC : D ≤ C)
    (K : Submodule ℚ (Fin 4 → V))
    (c : Basis (Fin (finrank ℚ C)) ℚ C) (b : Basis (Fin (finrank ℚ D)) ℚ D)
    (k : Basis (Fin (finrank ℚ K)) ℚ K) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card μ : ℝ) ≤ p)
    (hc : ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p)
    (hk : ∀ a i,
      rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (k a : Fin 4 → V) i) ≤ p) :
    ∃ m : ℕ, m ≤ 4 * Fintype.card μ ∧ ∃ ℓ : (Fin 4 → V) →ₗ[ℚ] (Fin m → ℚ),
      Function.Surjective ℓ ∧ LinearMap.ker ℓ = fourRefinedRelation C D K ∧
      (∀ k i j, rationalLogHeight (ℓ (LinearMap.single ℚ (fun _ : Fin 4 => V) k (e i)) j) ≤
        fourRefinementAnnihilatorBudget p) ∧
      (∀ x ∈ D, ℓ (fourDiagonalMap (R := ℚ) x) = 0) ∧
      (∀ z ∈ fourRefinedRelation C D K,
        ℓ (fourDiagonalMap (R := ℚ) (z 0)) +
          ℓ (LinearMap.single ℚ (fun _ : Fin 4 => V) 0 (z 0 + z 1 - z 2 - z 3)) = 0) ∧
      fourPetalSpace D (fourRefinedRelation C D K) =
        D ⊓ LinearMap.ker (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) := by
  obtain ⟨a, ha⟩ := exists_fourRefinedRelation_basis_logHeight e C D hDC K c b k hp hdim hc hb hk
  have hspan : Submodule.span ℚ (Set.range (fun j => (a j : Fin 4 → V))) =
      fourRefinedRelation C D K := by
    change Submodule.span ℚ (Set.range ((fourRefinedRelation C D K).subtype ∘ a)) = _
    rw [Set.range_comp, ← Submodule.map_span, a.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hB := fourRefinementBasisBudget_nonneg hp
  have hcard : (Fintype.card (Fin (finrank ℚ (fourRefinedRelation C D K))) : ℝ) ≤
      4 * p + fourRefinementBasisBudget p := by
    have h := (Nat.cast_le (α := ℝ)).mpr (four_submodule_finrank_le e (fourRefinedRelation C D K))
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    simpa using (h.trans (mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4))).trans
      (le_add_of_nonneg_right hB)
  exact exists_bounded_refined_four_annihilator e C D hDC K (fun j => (a j : Fin 4 → V))
    hspan (by positivity) hcard
    (fun j k i => (ha j ⟨k, i⟩).trans (le_add_of_nonneg_left (by positivity)))

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_fourRefinedRelation_correction
    {L μ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype μ]
    (e : Basis μ ℚ L) (C D : Submodule ℚ L) (hDC : D ≤ C)
    (K : Submodule ℚ (Fin 4 → L))
    (c : Basis (Fin (finrank ℚ C)) ℚ C) (b : Basis (Fin (finrank ℚ D)) ℚ D)
    (k : Basis (Fin (finrank ℚ K)) ℚ K) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card μ : ℝ) ≤ p)
    (hc : ∀ a i, rationalLogHeight (e.repr (c a : L) i) ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : L) i) ≤ p)
    (hk : ∀ a i, rationalLogHeight
      ((Pi.basis (fun _ : Fin 4 => e)).repr (k a : Fin 4 → L) i) ≤ p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget (8 * p + 1)) ≤ T i) :
    let q := 8 * p + 1
    let B := ((Pi.basis (fun _ : Fin 4 => e)).baseChange ℝ).equivFun
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (q + ((q + 2) ^ 3 + (q + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (x u v : ℝ ⊗[ℚ] (Fin 4 → L)),
        x - u - v ∈ K.baseChange ℝ → x ∈ (fourCommonModulo C D).baseChange ℝ →
        ‖B u‖ ≤ Real.exp q / monomialScale T α → B v ∈ realDenominatorGrid l →
        ∃ E Q : ℝ ⊗[ℚ] (Fin 4 → L),
          ‖B E‖ ≤ (Real.exp q + Real.exp ((q + 2) ^ 3 + (q + 2) ^ 18 + q)) /
            monomialScale T α ∧ B Q ∈ realDenominatorGrid m ∧
          x - E - Q ∈ (fourRefinedRelation C D K).baseChange ℝ := by
  intro q B
  classical
  let e4 := Pi.basis (fun _ : Fin 4 => e)
  obtain ⟨a, ha⟩ := exists_fourCommonModulo_basis_logHeight e C D hDC c b hp hc hb
  have hdim4 : (Fintype.card (Σ _ : Fin 4, μ) : ℝ) ≤ 4 * p := by
    simpa using mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4)
  have hcard (U : Submodule ℚ (Fin 4 → L)) :
      (finrank ℚ U : ℝ) ≤ 4 * p := by
    have h := (Nat.cast_le (α := ℝ)).mpr (four_submodule_finrank_le e U)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4))
  have hcols : (Fintype.card
      (Fin (finrank ℚ K) ⊕ Fin (finrank ℚ (fourCommonModulo C D))) : ℝ) ≤ q := by
    simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
    have hK := hcard K
    have hS := hcard (fourCommonModulo C D)
    dsimp only [q]
    linarith
  have hpq : p ≤ q := by dsimp only [q]; linarith
  have hHp : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr (by dsimp only [q]; linarith))
  have hkspan : Submodule.span ℚ (Set.range (fun j => (k j : Fin 4 → L))) = K := by
    change Submodule.span ℚ (Set.range (K.subtype ∘ k)) = K
    rw [Set.range_comp, ← Submodule.map_span, k.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have haspan : Submodule.span ℚ (Set.range (fun j => (a j : Fin 4 → L))) =
      fourCommonModulo C D := by
    change Submodule.span ℚ (Set.range ((fourCommonModulo C D).subtype ∘ a)) = _
    rw [Set.range_comp, ← Submodule.map_span, a.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hkH : ∀ j i, RationalHeightLE (e4.repr (k j : Fin 4 → L) i) ⌈Real.exp p⌉₊ :=
    fun j i => rationalHeightLE_ceil_exp (hk j i)
  have haH : ∀ j i, RationalHeightLE (e4.repr (a j : Fin 4 → L) i) ⌈Real.exp p⌉₊ :=
    fun j i => rationalHeightLE_ceil_exp (ha j i)
  have hdimq : (Fintype.card (Σ _ : Fin 4, μ) : ℝ) ≤ q :=
    hdim4.trans (by dsimp only [q]; linarith)
  have hlq : (l : ℝ) ≤ Real.exp q := hlp.trans (Real.exp_le_exp.mpr hpq)
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_basis_intersection_correction
    (μ := Σ _ : Fin 4, μ) (κ := Fin (finrank ℚ K))
    (ν := Fin (finrank ℚ (fourCommonModulo C D))) (σ := σ) (L := Fin 4 → L)
    (H := ⌈Real.exp p⌉₊) (p := q) (l := l) e4 K
    (fourCommonModulo C D) (fun j => (k j : Fin 4 → L)) (fun j => (a j : Fin 4 → L))
    hkspan haspan (one_le_ceil_exp p) hl hkH haH
    (hp.trans hpq) hdimq hcols hHp hlq T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α hα x u v hx hS hu hv
  obtain ⟨E, Q, hE, hQ, hmem⟩ := hsolve α hα x u v hx hS hu hv
  exact ⟨E, Q, hE, hQ, Submodule.baseChange_mono ℝ
    (show K ⊓ fourCommonModulo C D ≤ fourRefinedRelation C D K from le_sup_left) hmem⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentIntegralModel
namespace OAI

section

namespace Erdos3

open Module

variable {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L]

theorem markedLieSpan_eq_finite_span {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d k l : ℕ) :
    markedLieSpan v w marked d k l =
      Submodule.span ℚ (finiteMarkedLieValues v w marked s d k l : Set L) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, hd, hk, hl, rfl⟩
    by_cases ha : a.length ≤ s
    · exact Submodule.subset_span (Finset.mem_image.mpr ⟨a,
        Finset.mem_filter.mpr ⟨mem_finiteLieTrees_of_length_le I a ha, hd, hk, hl⟩, rfl⟩)
    · have hweight := lieTree_length_le_weight w hw a
      have hzero := F.lieTreeEval_mem_length v w hv a
      rw [F.layer_eq_bot_of_past_top (Or.inl (by omega)), Submodule.mem_bot] at hzero
      rw [hzero]
      exact Submodule.zero_mem _
  · exact Submodule.span_le.mpr (fun _ hx => finiteMarkedLieValues_mem v w marked s d k l hx)

theorem exists_markedLieSpan_bounded_basis {ι : Type*} [Fintype ι] {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H) (d k l : ℕ) :
    ∃ e : Basis (Fin (finrank ℚ (markedLieSpan v w marked d k l))) ℚ
      (markedLieSpan v w marked d k l),
      ∀ i j, RationalHeightLE (b.repr (e i : L) j) (lieTreeHeight (Fintype.card ι) H s) := by
  let S := finiteMarkedLieValues v w marked s d k l
  have hspan : Submodule.span ℚ (Set.range (Subtype.val : S → L)) =
      markedLieSpan v w marked d k l := by
    rw [markedLieSpan_eq_finite_span F v w marked hw hv]
    congr 1
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  exact exists_bounded_submodule_basis_from_spanning b _ (Subtype.val : S → L) hspan
    (fun x j => finiteMarkedLieValues_coordinate_height b v w marked hc hgen s d k l x.property j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MarkedPolynomialGenerators
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedPolynomialLayer_eval_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d k l : ℕ} {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l)
    (t : σ → ℚ) : eval t p ∈ markedLieSpan v w marked d k l := by
  apply (eval_mem_iff_coefficients (markedLieSpan v w marked d k l) p).mpr _ t
  intro α
  exact markedLieSpan_antitone v w marked le_rfl (Nat.le_add_right k _) le_rfl (hp α)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (v : I → L) (w : I → ℕ) (marked : I → Bool)

theorem markedPolynomialLayer_translate (h : σ → ℚ) {d k l : ℕ}
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l) :
    translate h p ∈ markedPolynomialLayer v w marked d k l := by
  intro α
  rw [coefficients_translate]
  apply Submodule.sum_mem
  intro β _
  by_cases hc : (polynomialTranslate h (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    have hd := polynomialDegreeGap_translate_monomial h β (MvPolynomial.mem_support_iff.mpr hc)
    change Finsupp.weight (fun _ : σ => 1) α + 0 ≤ Finsupp.weight (fun _ : σ => 1) β at hd
    exact markedLieSpan_antitone v w marked le_rfl (by omega) le_rfl (hp β)

theorem markedPolynomialLayer_taylorRemainder [Fintype σ] (h : σ → ℚ) {d k l : ℕ}
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l) :
    translate h p - p - directionalDerivative h p ∈
      markedPolynomialLayer v w marked d (k + 2) l := by
  rw [← taylorRemainder_apply]
  intro α
  rw [coefficients_taylorRemainder]
  apply Submodule.sum_mem
  intro β _
  by_cases hc : (scalarTaylorRemainder h (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    have hd := scalarTaylorRemainder_monomial h β (MvPolynomial.mem_support_iff.mpr hc)
    change Finsupp.weight (fun _ : σ => 1) α + 2 ≤ Finsupp.weight (fun _ : σ => 1) β at hd
    exact markedLieSpan_antitone v w marked le_rfl (by omega) le_rfl (hp β)

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {I σ L : Type*} [Fintype I] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

omit [Fintype I] [Fintype σ] in
theorem markedPolynomialLayer_degreeLE {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) {d k l : ℕ} {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ markedPolynomialLayer v w marked d k l) : DegreeLE (fun _ : σ => 1) s p := by
  intro α hα
  have hm := markedLieSpan_antitone v w marked le_rfl
    (by omega : s + 1 ≤ k + Finsupp.weight (fun _ : σ => 1) α) le_rfl (hp α)
  simpa only [markedLieSpan_marked_terminal F v w marked hw hv, Submodule.mem_bot] using hm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

noncomputable def markedShiftEval (t : ℕ) (a : Fin t → ℚ) :
    markedShiftSubalgebra F v w marked t →ₗ[ℚ] L where
  toFun x := eval a x.val.left.val
  map_add' x y := (eval a).map_add x.val.left.val y.val.left.val
  map_smul' c x := (eval a).map_smul c x.val.left.val

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

noncomputable def markedShiftDirectionMap (t : ℕ) :
    RationalTorus.Algebra t →ₗ[ℚ] markedShiftSubalgebra F v w marked t where
  toFun u := ⟨⟨0, u⟩, (markedPolynomialLayer v w marked 0 0 0).zero_mem⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NormalizedMarkedPhase
namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)

noncomputable def markedShiftPhase :
    markedShiftSubalgebra F v w marked t →ₗ⁅ℚ⁆ RationalTorus.Algebra t where
  toFun x := x.val.right
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

noncomputable def markedQuotientPhase :
    MarkedShiftQuotient F v w marked t →ₗ⁅ℚ⁆ RationalTorus.Algebra t :=
  lieQuotientDescend (markedShiftSecondIdeal F v w marked t)
    (markedShiftPhase F v w marked t) (fun _ hx => hx.1)

noncomputable def markedQuotientPolynomialAlgebra :
    LieSubalgebra ℚ (MarkedShiftQuotient F v w marked t) :=
  (markedQuotientPhase F v w marked t).ker.toLieSubalgebra

theorem exists_zero_phase_lift (x : MarkedShiftQuotient F v w marked t)
    (hx : markedQuotientPhase F v w marked t x = 0) :
    ∃ p : markedShiftSubalgebra F v w marked t,
      p.val.right = 0 ∧ lieQuotientMap (markedShiftSecondIdeal F v w marked t) p = x := by
  obtain ⟨p, rfl⟩ := lieQuotientMap_surjective (markedShiftSecondIdeal F v w marked t) x
  exact ⟨p, hx, rfl⟩

end Erdos3

end

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t m : ℕ)

noncomputable def normalizedMarkedPhase :
    MarkedShiftQuotient F v w marked t →ₗ⁅ℚ⁆ RationalTorus.Algebra t where
  toLinearMap := (m : ℚ)⁻¹ • (markedQuotientPhase F v w marked t).toLinearMap
  map_lie' {x y} := by
    change (m : ℚ)⁻¹ • markedQuotientPhase F v w marked t ⁅x, y⁆ = 0
    rw [(markedQuotientPhase F v w marked t).map_lie, RationalTorus.lie_eq_zero, smul_zero]

theorem normalizedMarkedPhase_apply (x : MarkedShiftQuotient F v w marked t) :
    normalizedMarkedPhase F v w marked t m x =
      (m : ℚ)⁻¹ • markedQuotientPhase F v w marked t x := rfl

theorem normalizedMarkedPhase_height {p : ℝ} (hm : 0 < m) (hp : 0 ≤ p)
    (hmp : (m : ℝ) ≤ Real.exp p) (x : MarkedShiftQuotient F v w marked t) (i : Fin t)
    (hx : rationalLogHeight (markedQuotientPhase F v w marked t x i) ≤ p) :
    rationalLogHeight (normalizedMarkedPhase F v w marked t m x i) ≤ 2 * p + 1 :=
  rationalLogHeight_nat_inv_mul_exp_bound m hm hp hmp hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedPureEvaluation
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)

theorem markedShiftEval_lie_of_zero_phase (a : Fin t → ℚ)
    (p q : markedShiftSubalgebra F v w marked t)
    (hp : p.val.right = 0) (hq : q.val.right = 0) :
    markedShiftEval F v w marked t a ⁅p, q⁆ =
      ⁅markedShiftEval F v w marked t a p, markedShiftEval F v w marked t a q⁆ := by
  have hz (p : VectorPolynomial (Fin t) ℚ L) : directionalDerivative (0 : Fin t → ℚ) p = 0 := by
    simp only [directionalDerivative, Pi.zero_apply, zero_smul, Finset.sum_const_zero, LinearMap.zero_apply]
  change eval a (⁅p.val.left.val, q.val.left.val⁆ + directionalDerivative p.val.right q.val.left.val -
    directionalDerivative q.val.right p.val.left.val) = ⁅eval a p.val.left.val, eval a q.val.left.val⁆
  rw [hp, hq]
  change eval a (⁅p.val.left.val, q.val.left.val⁆ +
    directionalDerivative (0 : Fin t → ℚ) q.val.left.val -
    directionalDerivative (0 : Fin t → ℚ) p.val.left.val) = _
  rw [hz, hz, add_zero, sub_zero]
  exact (evalLie a).map_lie _ _

variable (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)

noncomputable def markedBaseEvaluation (a : Fin t → ℚ) :
    MarkedShiftQuotient F v w marked t →ₗ[ℚ] (L ⧸ J) :=
  (markedShiftSecondIdeal F v w marked t).toSubmodule.liftQ
    ((lieQuotientMap J).toLinearMap.comp (markedShiftEval F v w marked t a)) (by
      intro p hp
      exact (lieQuotientMap_eq_zero J _).mpr (hJ (markedPolynomialLayer_eval_mem v w marked hp.2 a)))

theorem markedBaseEvaluation_map (a : Fin t → ℚ) (p : markedShiftSubalgebra F v w marked t) :
    markedBaseEvaluation F v w marked t J hJ a (lieQuotientMap (markedShiftSecondIdeal F v w marked t) p) =
      lieQuotientMap J (markedShiftEval F v w marked t a p) := rfl

theorem markedBaseEvaluation_lie (a : Fin t → ℚ) (x y : MarkedShiftQuotient F v w marked t)
    (hx : markedQuotientPhase F v w marked t x = 0) (hy : markedQuotientPhase F v w marked t y = 0) :
    markedBaseEvaluation F v w marked t J hJ a ⁅x, y⁆ =
      ⁅markedBaseEvaluation F v w marked t J hJ a x, markedBaseEvaluation F v w marked t J hJ a y⁆ := by
  obtain ⟨p, hp, rfl⟩ := exists_zero_phase_lift F v w marked t x hx
  obtain ⟨q, hq, rfl⟩ := exists_zero_phase_lift F v w marked t y hy
  rw [← (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).map_lie]
  change lieQuotientMap J (markedShiftEval F v w marked t a ⁅p, q⁆) =
    ⁅lieQuotientMap J (markedShiftEval F v w marked t a p),
      lieQuotientMap J (markedShiftEval F v w marked t a q)⁆
  rw [markedShiftEval_lie_of_zero_phase F v w marked t a p q hp hq]
  exact (lieQuotientMap J).map_lie _ _

noncomputable def markedBaseEvaluationLie (a : Fin t → ℚ) :
    markedQuotientPolynomialAlgebra F v w marked t →ₗ⁅ℚ⁆ (L ⧸ J) where
  toLinearMap := (markedBaseEvaluation F v w marked t J hJ a).comp
    (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule.subtype
  map_lie' {x y} := markedBaseEvaluation_lie F v w marked t J hJ a x.val y.val x.property y.property

theorem markedBaseEvaluation_real_map (a : Fin t → ℚ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedBaseEvaluation F v w marked t J hJ a).baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ p) =
      (lieQuotientMap J).toLinearMap.baseChange ℝ ((markedShiftEval F v w marked t a).baseChange ℝ p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul c p =>
    simp only [LinearMap.baseChange_tmul]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e u : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
  (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (E : RationalFilteredNilmanifold (L ⧸ J) u e) (a : Fin t → ℚ)

theorem markedBaseEvaluation_real_incl
    (z : ℝ ⊗[ℚ] markedQuotientPolynomialAlgebra F v w marked t) :
    (markedBaseEvaluation F v w marked t J hJ a).baseChange ℝ
      ((markedQuotientPolynomialAlgebra F v w marked t).incl.toLinearMap.baseChange ℝ z) =
      (markedBaseEvaluationLie F v w marked t J hJ a).toLinearMap.baseChange ℝ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c z => simp only [LinearMap.baseChange_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MarkedProjectionBounds
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r d q : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (e : Basis (Fin d) ℚ (markedShiftSubalgebra F v w marked t))
  {H : ℕ} (he : ∀ i j, RationalHeightLE
    ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr (e i).val j) H)

include he

omit [Fintype ι] in
theorem markedShiftPhase_coordinate_height (i : Fin t) (j : Fin d) :
    RationalHeightLE ((RationalTorus.basis t).repr (markedShiftPhase F v w marked t (e j)) i) H := by
  have h := he j (Sum.inr i)
  rw [F.associatedDegree.polynomialShiftBasis_repr_inr] at h
  exact h

omit [Fintype ι] in
theorem markedShiftEval_zero_coordinate_height (i : ι) (j : Fin d) :
    RationalHeightLE (b.repr (markedShiftEval F v w marked t 0 (e j)) i) H := by
  let z : NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω :=
    ⟨(0, i), by simp⟩
  have h := he j (Sum.inl z)
  rw [F.associatedDegree.polynomialShiftBasis_repr_inl] at h
  change RationalHeightLE (b.repr (eval (fun _ => 0) (e j).val.left.val) i) H
  rw [eval_zero_eq_coefficient]
  exact h

variable (f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t))
  {Q : ℕ} (hQ : 1 ≤ Q)
  (hf : ∀ i j, RationalHeightLE
    (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q)

include hQ hf

omit [Fintype ι] in
theorem markedQuotientPhase_coordinate_height (i : Fin t) (j : Fin q) :
    RationalHeightLE ((RationalTorus.basis t).repr (markedQuotientPhase F v w marked t (f j)) i)
      ((d + 1) * (rationalSolveHeight q Q * H) ^ d) := by
  have h := descended_linear_map_coordinate_height e f (RationalTorus.basis t)
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap
    (lieQuotientMap_surjective _) (markedQuotientPhase F v w marked t).toLinearMap hQ hf
    (fun i j => markedShiftPhase_coordinate_height F v w marked t b ω hF e he i j) i j
  change RationalHeightLE ((RationalTorus.basis t).repr
    (markedQuotientPhase F v w marked t (f j)) i)
    ((Fintype.card (Fin d) + 1) * (rationalSolveHeight (Fintype.card (Fin q)) Q * H) ^
      Fintype.card (Fin d)) at h
  simpa only [Fintype.card_fin] using h

variable {ν : Type*} (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (c : Basis ν ℚ (L ⧸ J)) {K : ℕ}
  (hc : ∀ i j, RationalHeightLE (c.repr (lieQuotientMap J (b j)) i) K)

include hc

theorem markedBaseEvaluation_zero_coordinate_height (i : ν) (j : Fin q) :
    RationalHeightLE (c.repr (markedBaseEvaluation F v w marked t J hJ 0 (f j)) i)
      ((d + 1) * (rationalSolveHeight q Q * ((Fintype.card ι + 1) * (H * K) ^ Fintype.card ι)) ^ d) := by
  have hcomp (i j) : RationalHeightLE
      (c.repr (markedBaseEvaluation F v w marked t J hJ 0
        (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j))) i)
      ((Fintype.card ι + 1) * (H * K) ^ Fintype.card ι) := by
    rw [markedBaseEvaluation_map]
    exact linearMap_coordinate_height b c (lieQuotientMap J).toLinearMap
      (fun j i => hc i j) (markedShiftEval F v w marked t 0 (e j))
      (fun i => markedShiftEval_zero_coordinate_height F v w marked t b ω hF e he i j) i
  have h := descended_linear_map_coordinate_height e f c
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap
    (lieQuotientMap_surjective _) (markedBaseEvaluation F v w marked t J hJ 0)
    hQ hf hcomp i j
  simpa only [Fintype.card_fin] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonMarkedMultidegree
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

theorem marked_first_layer_bracket_zero
    {x y : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t}
    (hx : x ∈ (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput 1 0))
    (hy : y ∈ (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput 1 0)) :
    ⁅x, y⁆ = 0 := by
  let M := (markedShiftMultidegree F v w marked hw hv t).realification
  have h := M.lie_mem hx hy
  have he : correlationInput (1 : ℕ) 0 + correlationInput 1 0 = correlationInput 2 0 := by
    funext i
    fin_cases i <;> rfl
  have ht : M.layer (correlationInput 2 0) = ⊥ := M.terminal _ (by
    intro hle
    have hh := hle 0
    exact Nat.not_succ_le_self 1 hh)
  rw [he, ht] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubeSignalAlgebra
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

theorem mixedCubeWithShift_diagonal {s d : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (c : (Fin d → Bool) → ℤ) (i : Fin M.outputDim) (h n : ℤ) (k : Fin d → ℤ) :
    M.mixedCubeWithShift c (fun _ => i) (Fin.cons h (Fin.cons n k)) =
      integerCubeProductWithShift (fun z => M.eval i (correlationInput h z)) k c n := by
  have hinput (ω : Fin d → Bool) :
      mixedCubeInput ω (Fin.cons h (Fin.cons n k)) + ![0, c ω] =
        correlationInput h (n + cubeShift k ω + c ω) := by
    funext j
    fin_cases j <;> simp [mixedCubeInput, correlationInput, cubeShift]
    rfl
  simp only [mixedCubeWithShift, integerCubeProductWithShift, hinput]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem NativeMultidegreeNilcharacter.mixedCubeWithShift_zero_eq {s d : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p) :
    M.mixedCubeWithShift (d := d) 0 = mixedCubeObservable M.eval := by
  funext a x
  have hzero : (![0, 0] : Fin 2 → ℤ) = 0 := by ext i; fin_cases i <;> rfl
  simp only [NativeMultidegreeNilcharacter.mixedCubeWithShift, mixedCubeObservable,
    Pi.zero_apply, hzero, add_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalWrapComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem smoothCyclicCarry_eq_of_outside {N : ℕ} [NeZero N]
    (δ : ℝ≥0) (hδ : 0 < δ) (h n : ZMod N)
    (hn : n ∉ cyclicCutNeighborhood N ((N : ℤ) - h.val) (3 * N * (δ : ℝ))) :
    smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)] = cyclicCarry h n := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  let s : ℝ := h.val + n.val
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s < 2 * N := by
    have hh : (h.val : ℝ) < N := Nat.cast_lt.mpr h.val_lt
    have hn' : (n.val : ℝ) < N := Nat.cast_lt.mpr n.val_lt
    dsimp [s]
    linarith
  have ht0 : 0 ≤ s / (3 * N) := by positivity
  have ht2 : s / (3 * N) ≤ 2 / 3 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hdist := circle_dist_half_of_unit_interval ⟨ht0, ht2.trans (by norm_num)⟩
  change linearCutoff (1 / 6) δ (dist ((s / (3 * N) : ℝ) : CircleFourier.Circle)
    ((1 / 2 : ℝ) : CircleFourier.Circle)) = cyclicCarry h n
  rw [hdist]
  by_cases hw : N ≤ h.val + n.val
  · have hsN : (N : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hw
    have ht1 : 1 / 3 ≤ s / (3 * N) := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    rw [linearCutoff_eq_one _ _ hδ (abs_le.mpr ⟨by linarith, by linarith⟩)]
    simp only [cyclicCarry, hw, ite_true]
  · have hsN : s < (N : ℝ) := by dsimp [s]; exact_mod_cast Nat.lt_of_not_ge hw
    have hgap := lt_of_not_ge (fun hh => hn ((mem_cyclicCutNeighborhood _ _ _ _).mpr hh))
    simp only [Int.cast_sub, Int.cast_natCast] at hgap
    rw [abs_of_neg (by dsimp [s] at hsN; linarith)] at hgap
    have hfar : 1 / 6 + (δ : ℝ) ≤ |s / (3 * N) - 1 / 2| := by
      rw [abs_of_neg (by
        have : s / (3 * N) < 1 / 3 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
        linarith)]
      have ht : s / (3 * N) ≤ 1 / 3 - (δ : ℝ) := by
        apply (div_le_iff₀ (by positivity)).mpr
        dsimp [s]
        nlinarith
      linarith
    rw [linearCutoff_eq_zero _ _ hfar]
    simp only [cyclicCarry, hw, ite_false]

theorem smoothCyclicCarry_mean_error {N : ℕ} [NeZero N] (δ : ℝ≥0) (hδ : 0 < δ) :
    (𝔼 x : Fin 2 → ZMod N,
      |cyclicCarry (x 0) (x 1) - smoothCyclicCarry N δ (fun j => ((x j).val : ℤ))|) ≤
      6 * (δ : ℝ) + 1 / N := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hrow (h : ZMod N) :
      (𝔼 n : ZMod N, |cyclicCarry h n - smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)]|) ≤
        6 * (δ : ℝ) + 1 / N := by
    let E := cyclicCutNeighborhood N ((N : ℤ) - h.val) (3 * N * (δ : ℝ))
    have hcard : (E.card : ℝ) ≤ 6 * N * (δ : ℝ) + 1 := by
      simpa only [show 2 * (3 * (N : ℝ) * (δ : ℝ)) = 6 * N * (δ : ℝ) by ring] using
        cyclicCutNeighborhood_card_le N ((N : ℤ) - h.val) (by positivity : 0 ≤ 3 * N * (δ : ℝ))
    have hcap (n : ZMod N) :
        |cyclicCarry h n - smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)]| ≤ 1 := by
      have hr := circleCarryCutoff_range δ
        (((((h.val : ℤ) : ℝ) + ((n.val : ℤ) : ℝ)) / (3 * N) : ℝ) : CircleFourier.Circle)
      change 0 ≤ smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)] ∧
        smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)] ≤ 1 at hr
      unfold cyclicCarry
      split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hh := expect_abs_le_of_exceptional_set E
      (fun n => cyclicCarry h n - smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)])
      (by norm_num : (0 : ℝ) ≤ 0) hcap (fun n hn => by
        rw [smoothCyclicCarry_eq_of_outside δ hδ h n hn, sub_self, abs_zero])
    simp only [zero_add, one_mul, ZMod.card] at hh
    apply hh.trans
    apply (div_le_iff₀ hN).mpr
    calc
      _ ≤ 6 * N * (δ : ℝ) + 1 := hcard
      _ = (6 * (δ : ℝ) + 1 / N) * N := by field_simp
  rw [expect_fin_two]
  exact (Finset.expect_le_expect (fun h _ => hrow h)).trans_eq (Fintype.expect_const _)

theorem exists_smoothCyclicCarry_expansion (N : ℕ) (δ : ℝ≥0) (hδ : 0 < δ)
    {p : ℝ} (hp : 0 ≤ p) (hinv : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 (p + 4)
      (fun x => (smoothCyclicCarry N δ x : ℂ))) := by
  let Ψ : (Fin 1 → CircleFourier.Circle) → ℂ := fun v => (circleCarryCutoff δ (v 0) : ℂ)
  have hΨ (v : Fin 1 → CircleFourier.Circle) : ‖Ψ v‖ ≤ (1 : ℝ≥0) := by
    change ‖(circleCarryCutoff δ (v 0) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (circleCarryCutoff_range δ _).1]
    exact (circleCarryCutoff_range δ _).2
  have hcoord : LipschitzWith 1 (fun v : Fin 1 → CircleFourier.Circle => v 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [NNReal.coe_one, one_mul] using dist_le_pi_dist v w 0
  have hLip : LipschitzWith δ⁻¹ Ψ := by
    simpa only [mul_one, one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitz.comp ((circleCarryCutoff_lipschitz δ hδ).comp hcoord)
  let T := RationalTorus.affineNiltest 1 0
    (fun _ : Fin 2 => fun _ : Fin 1 => 1 / (3 * (N : ℝ))) Ψ 1 δ⁻¹ hΨ hLip
  have hlog : Real.log (3 + (δ : ℝ)⁻¹) ≤ p + 4 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have h1 := Real.one_le_exp hp
    have h4 : 4 ≤ Real.exp (4 : ℝ) := by linarith [Real.add_one_le_exp (4 : ℝ)]
    rw [Real.exp_add]
    nlinarith
  have hT : T.ComplexityLE (p + 4) :=
    RationalTorus.affineNiltest_complexity 1 0
      (fun _ : Fin 2 => fun _ : Fin 1 => 1 / (3 * (N : ℝ))) Ψ 1 δ⁻¹ hΨ hLip
      (by linarith) (by norm_num; linarith)
      (by simpa only [NNReal.coe_one, NNReal.coe_inv, show (2 : ℝ) + 1 = 3 by norm_num] using hlog)
  refine ⟨NativeIntegerExpansion.ofTest T hT ?_⟩
  intro x
  simp only [T, RationalTorus.affineNiltest_eval, smoothCyclicCarry, Ψ,
    Fin.sum_univ_two,
    Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, zero_add]
  apply congrArg (fun t : ℝ => (circleCarryCutoff δ (t : CircleFourier.Circle) : ℂ))
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem smoothCyclicCarry_fixed_shift_mean_error {N : ℕ} [NeZero N]
    (δ : ℝ≥0) (hδ : 0 < δ) (k : ZMod N) :
    (𝔼 n : ZMod N, |cyclicCarry k n -
      smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]|) ≤ 6 * (δ : ℝ) + 1 / N := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  let E := cyclicCutNeighborhood N ((N : ℤ) - k.val) (3 * N * (δ : ℝ))
  have hcard : (E.card : ℝ) ≤ 6 * N * (δ : ℝ) + 1 := by
    simpa only [show 2 * (3 * (N : ℝ) * (δ : ℝ)) = 6 * N * (δ : ℝ) by ring] using
      cyclicCutNeighborhood_card_le N ((N : ℤ) - k.val) (by positivity : 0 ≤ 3 * N * (δ : ℝ))
  have hcap (n : ZMod N) :
      |cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]| ≤ 1 := by
    have hr := circleCarryCutoff_range δ
      (((((k.val : ℤ) : ℝ) + ((n.val : ℤ) : ℝ)) / (3 * N) : ℝ) : CircleFourier.Circle)
    change 0 ≤ smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)] ∧
      smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)] ≤ 1 at hr
    unfold cyclicCarry
    split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hh := expect_abs_le_of_exceptional_set E
    (fun n => cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)])
    (by norm_num : (0 : ℝ) ≤ 0) hcap (fun n hn => by
      rw [smoothCyclicCarry_eq_of_outside δ hδ k n hn, sub_self, abs_zero])
  simp only [zero_add, one_mul, ZMod.card] at hh
  apply hh.trans
  apply (div_le_iff₀ hN).mpr
  calc
    _ ≤ 6 * N * (δ : ℝ) + 1 := hcard
    _ = (6 * (δ : ℝ) + 1 / N) * N := by field_simp

theorem exists_fixed_shift_smoothCyclicCarry_expansion (N : ℕ) (δ : ℝ≥0)
    (hδ : 0 < δ) {p : ℝ} (hp : 0 ≤ p) (hinv : (δ : ℝ)⁻¹ ≤ Real.exp p) (k : ℤ) :
    Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 (p + 4)
      (fun x => (smoothCyclicCarry N δ ![k, x 1] : ℂ))) := by
  obtain ⟨E⟩ := exists_smoothCyclicCarry_expansion N δ hδ hp hinv
  let A : Fin 2 → Fin 2 → ℤ := ![![0, 0], ![0, 1]]
  let b : Fin 2 → ℤ := ![k, 0]
  have hinput (x : Fin 2 → ℤ) : integerAffineMap A b x = ![k, x 1] := by
    funext i
    fin_cases i <;> simp [integerAffineMap, A, b, Fin.sum_univ_two]
  simpa only [hinput] using
    (show Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 (p + 4)
      (fun x => (smoothCyclicCarry N δ (integerAffineMap A b x) : ℂ))) from
        ⟨E.affinePullback A b⟩)

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def quadraticDiagonalDerivative (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0))

noncomputable def quadraticMixedTriple (a : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star ((W.eval a.1 (correlationInput (x 1) (x 0)) *
    W.eval a.2.1 (correlationInput (x 0) (x 1))) * W.eval a.2.2 (fun _ => x 0))

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def cyclicDiagonalDerivative {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) : ℂ :=
  W.eval a.1 (fun _ => ((x 1).val : ℤ)) *
    star (W.eval a.2 (fun _ => ((x 0 + x 1).val : ℤ)))

noncomputable def wrappedDiagonalDerivative (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0 - N))

noncomputable def diagonalWrapCoefficient (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval k (fun _ => x 1 + x 0) * star (W.eval j (fun _ => x 1 + x 0 - N))

theorem cyclicDiagonalDerivative_branches {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    W.cyclicDiagonalDerivative a x =
      (1 - (cyclicCarry (x 0) (x 1) : ℂ)) *
          W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) +
        (cyclicCarry (x 0) (x 1) : ℂ) *
          W.wrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) := by
  have hval := cyclic_representative_add (x 0) (x 1)
  have hlt := (x 0).val_lt
  by_cases hw : N ≤ (x 0).val + (x 1).val
  · have hcut : N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_true, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add,
      cyclicDiagonalDerivative, wrappedDiagonalDerivative]
    rw [hval, if_pos hcut]
  · have hcut : ¬N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_false, Complex.ofReal_zero, sub_zero, zero_mul, one_mul, add_zero,
      cyclicDiagonalDerivative, quadraticDiagonalDerivative]
    rw [hval, if_neg hcut, sub_zero]

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedEvaluationJointBounds
namespace OAI

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)

include hω hH hc in
theorem markedShiftBasis_structure_height (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s)) :
    let U := max (lieTreeHeight (Fintype.card ι) H s) (s + 1)
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    ∀ i j k, RationalHeightLE (lieStructureConstants e i j k)
      (rationalLieStructureHeight a (max U (rationalSolveHeight d U))) := by
  classical
  let U := max (lieTreeHeight (Fintype.card ι) H s) (s + 1)
  have hHU : H ≤ U := (lieTreeHeight_ge_input _ _ _).trans (Nat.le_max_left _ _)
  have hU : 1 ≤ U := hH.trans hHU
  let _ : Fintype (NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω) :=
    NilpotentLieFiltration.adaptedBasisIndexFintype (fun _ : Fin t => 1) ω s (by simp) hω
  let E := F.associatedDegree.polynomialShiftBasis b ω hF t
  have hCE (i j k) : RationalHeightLE (lieStructureConstants E i j k) U :=
    (F.associatedDegree.polynomialShiftBasis_structure_height b ω hF hω hH hc t i j k).mono
      (max_le hHU (Nat.le_max_right _ _))
  have hmatrix (i j) : RationalHeightLE
      (LinearMap.toMatrix e E (markedShiftSubalgebra F v w marked t).incl.toLinearMap i j) U := by
    rw [LinearMap.toMatrix_apply]
    exact (he j i).mono (Nat.le_max_left _ _)
  obtain ⟨_, _, _, hstructure⟩ := exists_bounded_lie_embedding_retraction e E
    (markedShiftSubalgebra F v w marked t).incl (fun _ _ h => Subtype.ext h) hU hCE hmatrix
  dsimp only
  intro i j k
  simpa only [Fintype.card_fin, ← finrank_eq_card_basis E] using hstructure i j k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LocalPhaseMarkedObservable
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

theorem markedQuotientPhase_real_map (z : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedQuotientPhase F v w marked t).toLinearMap.baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ z) =
      (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c z => simp only [LinearMap.baseChange_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedMarkedChart
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t m : ℕ)

theorem normalizedMarkedPhase_real_pure
    (z : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
    (hz : z ∈ (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule.baseChange ℝ) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m) z = 0 := by
  have hker : (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule ≤
      LinearMap.ker (normalizedMarkedPhase F v w marked t m).toLinearMap := by
    intro x hx
    change markedQuotientPhase F v w marked t x = 0 at hx
    change normalizedMarkedPhase F v w marked t m x = 0
    rw [normalizedMarkedPhase_apply, hx, smul_zero]
  have h := Submodule.baseChange_mono ℝ hker hz
  rw [realification_ker, LinearMap.mem_ker] at h
  change ((RationalTorus.basis t).baseChange ℝ).equivFun
    ((normalizedMarkedPhase F v w marked t m).toLinearMap.baseChange ℝ z) = 0
  rw [h, map_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedLocalCoefficientValue
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ)
  (E : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

theorem normalizedMarkedPhase_real_eq_zero_iff (hm : 0 < m)
    (z : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m) z = 0 ↔
      z ∈ (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule.baseChange ℝ := by
  have hker : LinearMap.ker (normalizedMarkedPhase F v w marked t m).toLinearMap =
      LinearMap.ker (markedQuotientPhase F v w marked t).toLinearMap := by
    ext x
    change normalizedMarkedPhase F v w marked t m x = 0 ↔ markedQuotientPhase F v w marked t x = 0
    rw [normalizedMarkedPhase_apply]
    simp [show (m : ℚ) ≠ 0 by exact_mod_cast hm.ne']
  let e := ((RationalTorus.basis t).baseChange ℝ).equivFun
  change e ((normalizedMarkedPhase F v w marked t m).toLinearMap.baseChange ℝ z) = 0 ↔
    z ∈ (LinearMap.ker (markedQuotientPhase F v w marked t).toLinearMap).baseChange ℝ
  rw [← hker, realification_ker, LinearMap.mem_ker]
  constructor
  · intro hz
    exact e.injective (hz.trans (e.map_zero).symm)
  · intro hz
    rw [hz, map_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealAnnihilatorCorrections
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V] [Fintype I] [Fintype J]

theorem exists_real_annihilator_correction
    (b : Basis I ℚ V) (ℓ : V →ₗ[ℚ] (J → ℚ)) {H l : ℕ} {p : ℝ}
    (hℓ : ∀ j i, RationalHeightLE (ℓ (b i) j) H) (hp : 0 ≤ p)
    (hI : (Fintype.card I : ℝ) ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ (x E Q : ℝ ⊗[ℚ] V) (ε : ℝ),
        x - E - Q ∈ (LinearMap.ker ℓ).baseChange ℝ →
        ‖(b.baseChange ℝ).equivFun E‖ ≤ ε →
        (b.baseChange ℝ).equivFun Q ∈ realDenominatorGrid l →
        ∃ q ∈ realDenominatorGrid m,
          ‖realifyCoordinateMap ℓ x - q‖ ≤ Real.exp ((p + 2) ^ 3) * ε := by
  let A := coordinateFunctionalMatrix b ℓ
  have hm := matrixDenominator_allowance_le_exp A l H hℓ hp hJ hI hH hlp
  rw [Nat.mul_comm l] at hm
  refine ⟨matrixDenominator A * l, Nat.mul_pos (matrixDenominator_pos A) hl, hm,
    ⟨matrixDenominator A, Nat.mul_comm _ _⟩, ?_⟩
  intro x E Q ε hker hE hQ
  refine ⟨realifyCoordinateMap ℓ Q, realifyCoordinateMap_grid b ℓ l Q hQ, ?_⟩
  have hz := (mem_realified_coordinate_kernel_iff_eq_zero ℓ _).mp hker
  rw [map_sub, map_sub] at hz
  have heq : realifyCoordinateMap ℓ x - realifyCoordinateMap ℓ Q =
      realifyCoordinateMap ℓ E := by
    calc
      _ = (realifyCoordinateMap ℓ x - realifyCoordinateMap ℓ E -
          realifyCoordinateMap ℓ Q) + realifyCoordinateMap ℓ E := by abel
      _ = _ := by rw [hz, zero_add]
  rw [heq]
  have hfac : ((Fintype.card I : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    calc
      _ ≤ ((Fintype.card I : ℝ) + 1) * (Real.exp ((p + 2) ^ 1) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hHp : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) :=
          hH.trans (Real.exp_le_exp.mpr (by rw [pow_one]; linarith))
        linarith
      _ ≤ _ := matrix_weighted_factor_le_exp_power (Fintype.card I) hp hI 1 (by decide)
  exact (realifyCoordinateMap_norm_bound b ℓ hℓ E).trans
    ((mul_le_mul_of_nonneg_right hfac (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hE (Real.exp_nonneg _)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFourBalancedDual
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

variable [Fintype J]

theorem realFourCoordinateMap_decomposition (C D : Submodule ℚ V)
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ))
    (hℓ : fourBalancedDependent D ≤ LinearMap.ker ℓ)
    (v : Fin 4 → ℝ ⊗[ℚ] V) (hv : v ∈ fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ)) :
    realFourCoordinateMap ℓ v =
      realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) (v 0) +
        realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0))
          (v 0 + v 1 - v 2 - v 3) := by
  have hzero (z) (hz : z ∈ fourBalancedDependent (D.baseChange ℝ)) :
      realFourCoordinateMap ℓ z = 0 := by
    rw [← realification_fourBalancedDependent] at hz
    have hmem := (Submodule.mem_map_equiv _).mp hz
    exact (mem_realified_coordinate_kernel_iff_eq_zero ℓ _).mp
      (Submodule.baseChange_mono ℝ hℓ hmem)
  have h := four_annihilator_decomposition (C.baseChange ℝ) (D.baseChange ℝ)
    (realFourCoordinateMap ℓ) hzero v hv
  simpa only [realFourCoordinateMap_diagonal, realFourCoordinateMap_single,
    fourAlternatingMap_apply] using h

theorem realFourCoordinateMap_shared_decomposition (C D : Submodule ℚ V) (hDC : D ≤ C)
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ))
    (hℓ : fourBalancedDependent D ≤ LinearMap.ker ℓ)
    (c : ℝ ⊗[ℚ] V) (hc : c ∈ C.baseChange ℝ)
    (v : Fin 4 → ℝ ⊗[ℚ] V) (hv : ∀ k, v k ∈ D.baseChange ℝ) :
    realFourCoordinateMap ℓ (fun k => c + v k) =
      realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) c +
        realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0))
          (v 0 + v 1 - v 2 - v 3) := by
  have hmem : (fun k => c + v k) ∈ fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ) := by
    apply (mem_fourCommonModulo _ _ _).mpr
    refine ⟨fun k => (C.baseChange ℝ).add_mem hc
      (Submodule.baseChange_mono ℝ hDC (hv k)), ?_⟩
    intro k
    rw [add_sub_add_left_eq_sub]
    exact (D.baseChange ℝ).sub_mem (hv k) (hv 0)
  have hdiag : D ≤ LinearMap.ker (ℓ.comp (fourDiagonalMap (R := ℚ))) := by
    intro x hx
    exact four_annihilator_common_zero D ℓ (fun z hz => hℓ hz) x hx
  have hz := (mem_realified_coordinate_kernel_iff_eq_zero
    (ℓ.comp (fourDiagonalMap (R := ℚ))) (v 0)).mp
      (Submodule.baseChange_mono ℝ hdiag (hv 0))
  have halt : (c + v 0) + (c + v 1) - (c + v 2) - (c + v 3) =
      v 0 + v 1 - v 2 - v 3 := by abel
  have h := realFourCoordinateMap_decomposition C D ℓ hℓ (fun k => c + v k) hmem
  rw [halt, map_add, hz, add_zero] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MixedAssignmentSampling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixedChoiceSample_sum {s n : ℕ} (h : ℤ) (y : Fin (n + 1) → ℤ) :
    finiteChoiceCoordinateInput (mixedRepeatedCoordinates s) (mixedChoiceSample h y) =
      mixedReplicatedInput h (fun _ : Fin s => ∑ a, y a) := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rw [mixedReplicatedInput_head]
    simp [finiteChoiceCoordinateInput, mem_mixedRepeatedCoordinates, mixedHead,
      mixedChoiceSample, correlationInput]
  · rw [mixedReplicatedInput_replica]
    have hi : mixedReplica i ∈ mixedRepeatedCoordinates s :=
      (mem_mixedRepeatedCoordinates s _).mpr rfl
    simp only [finiteChoiceCoordinateInput, hi, ite_true, mixedChoiceSample_replica]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPermutationTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p)

theorem mixed_permutation_eval
    (hsym : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
      W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) = W.eval k x)
    (e : Equiv.Perm (Fin s)) (k : Fin W.outputDim) (h : ℤ) (v : Fin s → ℤ) :
    W.eval k (mixedReplicatedInput h (fun j => v (e j))) = W.eval k (mixedReplicatedInput h v) := by
  have H := hsym (mixedPermutationFamily e.symm) k (mixedReplicatedInput h v)
  simpa only [mixedReplicatedInput_permuted, Equiv.symm_symm] using H

theorem mixed_assignment_product_grouped
    (hsym : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
      W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) = W.eval k x)
    (h : ℤ) (x : Fin s → ℤ) (a : Equiv.Perm (Fin s) ⊕ MissingAssignment s → Fin W.outputDim) :
    (∏ v : Fin s → Fin s, W.eval (a ((assignmentSplitEquiv s).symm v))
      (mixedReplicatedInput h (fun j => x (v j)))) =
      (∏ e : Equiv.Perm (Fin s), W.eval (a (Sum.inl e)) (mixedReplicatedInput h x)) *
        ∏ v : MissingAssignment s, W.eval (a (Sum.inr v))
          (mixedReplicatedInput h (fun j => x (v.val j))) := by
  classical
  rw [assignment_product_split (fun v k => W.eval k (mixedReplicatedInput h (fun j => x (v j)))) a]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  exact W.mixed_permutation_eval hsym e _ h x

theorem mixed_missing_assignment_independent (v : MissingAssignment s) :
    ∃ j : Fin s, ∀ (k : Fin W.outputDim) (x y : Fin (s + 1) → ℤ),
      (∀ a, a ≠ j.succ → x a = y a) →
      W.eval k (mixedReplicatedInput (x 0) (fun i => x (v.val i).succ)) =
        W.eval k (mixedReplicatedInput (y 0) (fun i => y (v.val i).succ)) := by
  obtain ⟨j, hj⟩ := missingAssignment_coordinate v
  refine ⟨j, ?_⟩
  intro k x y hxy
  congr 1
  funext a
  rcases mixedReplicated_cases a with rfl | ⟨i, rfl⟩
  · rw [mixedReplicatedInput_head, mixedReplicatedInput_head]
    apply hxy
    exact (Fin.succ_ne_zero j).symm
  · rw [mixedReplicatedInput_replica, mixedReplicatedInput_replica]
    apply hxy
    exact fun heq => hj i (Fin.succ_injective s heq)

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMixedReflectionBridge
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def mixedReflectionSource {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (c : ℤ) (a : Fin W.outputDim × Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ℂ :=
  W.eval a.1 (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)) *
    star (W.eval a.2 (mixedSlotInput (x 1) (c - x 0 - x 1) (fun j => x j.succ.succ)))

noncomputable def mixedReflectionTarget {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (c : ℤ) (a : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim))
    (x : Fin (n + 2) → ℤ) : ℂ :=
  W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)) *
    star (W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) (fun j => x j.succ.succ))) *
    star (W.eval a.1.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ))) *
    W.eval a.2.2 (mixedSlotInput (x 1) (x 0) (fun j => x j.succ.succ))

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedAnchorExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def NativeIntegerExpansion.boxCornerPullback {n s : ℕ} {p : ℝ}
    {F : (Fin n → ℤ) → ℂ} (E : NativeIntegerExpansion (fun _ : Fin n => 1) s p F)
    (a : Fin n → ℤ) (ω : Fin n → Bool) :
    NativeIntegerExpansion (fun _ : Fin n => 1) s p (fun x => F (boxCorner x a ω)) := by
  let A : Fin n → Fin n → ℤ := fun i j => if ω i then 0 else if j = i then 1 else 0
  let b : Fin n → ℤ := fun i => if ω i then a i else 0
  have hmap (x : Fin n → ℤ) : integerAffineMap A b x = boxCorner x a ω := by
    funext i
    cases h : ω i <;> simp [integerAffineMap, A, b, boxCorner, h, ite_mul]
  simpa only [hmap] using E.affinePullback A b

noncomputable def NativeIntegerExpansion.conjugationPower {σ : Type*} {w : σ → ℕ}
    {s : ℕ} {p : ℝ} {F : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p F) (n : ℕ) :
    NativeIntegerExpansion w s p (fun x => Erdos3.conjugationPower n (F x)) := by
  by_cases h : n % 2 = 0
  · simpa only [conjugationPower_eq_if_mod, h, ite_true] using E
  · simpa only [conjugationPower_eq_if_mod, h, ite_false] using E.conjugate

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalCyclicDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def quadraticSquareTriple (a : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star ((W.eval a.1 (correlationInput (x 0) (x 1)) *
    W.eval a.2.1 (correlationInput (x 0) (x 1))) * W.eval a.2.2 (fun _ => x 0))

noncomputable def diagonalSquareCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ j, (W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple (j, b.2) x)) *
    star (G b.1 j x)

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def wrappedDiagonalCorrection (N : ℕ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ k, W.diagonalWrapCoefficient N a.2 k x * F (a.1, k) b x

noncomputable def cyclicDiagonalCorrection (N : ℕ) (δ : ℝ≥0)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  (1 - (smoothCyclicCarry N δ x : ℂ)) * F a b x +
    (smoothCyclicCarry N δ x : ℂ) * W.wrappedDiagonalCorrection N F a b x

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem smoothedSecondDifference_mean_error {N : ℕ} [NeZero N]
    (δ : ℝ≥0) (hδ : 0 < δ) (u v : (Fin 2 → ℤ) → ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1) (k : ZMod N) (h : ℤ) :
    (𝔼 n : ZMod N, ‖cyclicSecondDifference u v k h n -
      smoothedSecondDifference N δ u v k.val ![h, (n.val : ℤ)]‖) ≤
        12 * (δ : ℝ) + 2 / N := by
  have hp (n : ZMod N) : ‖cyclicSecondDifference u v k h n -
      smoothedSecondDifference N δ u v k.val ![h, (n.val : ℤ)]‖ ≤
        2 * |cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]| := by
    have hh := norm_smoothed_branch_error (cyclicCarry k n)
      (smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]) (circleCarryCutoff_range δ _)
      (integerSecondDifference u v k.val ![h, (n.val : ℤ)])
      (integerSecondDifference u v ((k.val : ℤ) - N) ![h, (n.val : ℤ)])
      (integerSecondDifference u v k.val ![h, (n.val : ℤ)])
      (integerSecondDifference u v ((k.val : ℤ) - N) ![h, (n.val : ℤ)])
      (integerSecondDifference_norm u v hu hv _ _)
      (integerSecondDifference_norm u v hu hv _ _)
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, sub_self, norm_zero, zero_add,
      ← cyclicSecondDifference_branches, smoothedSecondDifference, Matrix.cons_val_one,
      Matrix.cons_val_zero] using hh
  calc
    _ ≤ 𝔼 n : ZMod N,
        2 * |cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]| :=
      Finset.expect_le_expect (fun n _ => hp n)
    _ = 2 * (𝔼 n : ZMod N,
        |cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]|) :=
      (Finset.mul_expect _ _ _).symm
    _ ≤ 2 * (6 * (δ : ℝ) + 1 / N) :=
      mul_le_mul_of_nonneg_left (smoothCyclicCarry_fixed_shift_mean_error δ hδ k) (by norm_num)
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def rootExchangeCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  (W.rationalDilation (1 / 2)).tensorSquareExchangeCorrection (W.halfDilationExchangeCorrection G)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositiveDegreeCyclicDifference
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def raiseStep {σ : Type*} {w : σ → ℕ} {s t : ℕ} {p : ℝ}
    {f : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p f) (hst : s ≤ t) (hp : 0 ≤ p) :
    NativeIntegerExpansion w t (raisedNiltestBudget p) f :=
  { E with
    count_bound := E.count_bound.trans (Real.exp_le_exp.mpr (le_raisedNiltestBudget p))
    model := fun i => (E.model i).raiseStep hst
    test := fun i => (E.test i).raiseStep hst
    complexity := fun i => (E.test i).raiseStep_complexity hst hp (E.complexity i)
    cost := E.cost.trans (Real.exp_le_exp.mpr (le_raisedNiltestBudget p))
    eval := fun x => by
      simpa only [RationalFilteredNilmanifold.Niltest.raiseStep_eval] using E.eval x }

end Erdos3.NativeIntegerExpansion

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixedDiagonalChoice_sum (s : ℕ) (x : Fin 2 → ℤ) :
    finiteChoiceCoordinateInput (mixedAllCoordinates s) (mixedDiagonalChoiceInput x) =
      fun _ => x 1 + x 0 := by
  funext j
  simp only [finiteChoiceCoordinateInput, mem_mixedAllCoordinates, ite_true,
    mixedDiagonalChoiceInput]
  change (∑ a : Fin 2, x a.rev) = x 1 + x 0
  exact Fin.sum_univ_two (fun a : Fin 2 => x a.rev)

theorem mixedDiagonalChoice_leaf (s : ℕ) (x : Fin 2 → ℤ)
    (v : Fin (mixedAllCoordinates s).length → Fin 2) :
    finiteChoiceLeafInput (mixedAllCoordinates s) v (mixedDiagonalChoiceInput x) =
      mixedDiagonalCorner (mixedCornerAssignmentEquiv s v) x := by
  rw [mixedDiagonalCorner, ← mixedSampledInput_coordinates]
  funext j
  let k : Fin (mixedAllCoordinates s).length :=
    Fin.cast (mixedAllCoordinates_length s).symm (mixedInputCoordinate (s + 1) j)
  have H := finiteChoiceLeafInput_get (mixedAllCoordinates s)
    (mixedAllCoordinates_nodup s) v (mixedDiagonalChoiceInput x) k
  rw [mixedAllCoordinates_get] at H
  have hk : mixedCoordinateIndex (s + 1) (Fin.cast (mixedAllCoordinates_length s) k) = j :=
    mixedCoordinateIndex_coordinate (s + 1) j
  rw [hk] at H
  exact H

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedDiagonalTensor
    (a : (Fin (s + 3) → Fin 2) → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∏ v, W.eval (a v) (mixedDiagonalCorner v x)

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedDiagonalDerivative (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0))

noncomputable def mixedNonconstantTensor (a : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star (∏ v, W.eval (a v) (mixedDiagonalCorner v.val x))

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def mixedIntegrationRoot {d : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p) :
    NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1)
      (tensorPowerBudget ((d + 3) ^ (d + 2)) p) :=
  (W.rationalDilation (((d + 3 : ℕ) : ℚ)⁻¹)).tensorPower ((d + 3) ^ (d + 2))

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedCyclicDiagonalDerivative {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) : ℂ :=
  W.eval a.1 (fun _ => ((x 1).val : ℤ)) *
    star (W.eval a.2 (fun _ => ((x 0 + x 1).val : ℤ)))

noncomputable def mixedWrappedDiagonalDerivative (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0 - N))

noncomputable def mixedDiagonalWrapCoefficient (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval k (fun _ => x 1 + x 0) * star (W.eval j (fun _ => x 1 + x 0 - N))

theorem mixedCyclicDiagonalDerivative_branches {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    W.mixedCyclicDiagonalDerivative a x =
      (1 - (cyclicCarry (x 0) (x 1) : ℂ)) *
          W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) +
        (cyclicCarry (x 0) (x 1) : ℂ) *
          W.mixedWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) := by
  have hval := cyclic_representative_add (x 0) (x 1)
  have hlt := (x 0).val_lt
  by_cases hw : N ≤ (x 0).val + (x 1).val
  · have hcut : N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_true, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add,
      mixedCyclicDiagonalDerivative, mixedWrappedDiagonalDerivative]
    rw [hval, if_pos hcut]
  · have hcut : ¬N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_false, Complex.ofReal_zero, sub_zero, zero_mul, one_mul, add_zero,
      mixedCyclicDiagonalDerivative, mixedDiagonalDerivative]
    rw [hval, if_neg hcut, sub_zero]

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootLosses
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def divisionMixedExchangeCorrection (d : ℕ)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  complexCrossContraction
    ((W.rationalDilation ((d : ℚ)⁻¹)).eval a (mixedSampledInput π x))
    ((W.rationalDilation ((d : ℚ)⁻¹)).eval b (mixedSampledInput (mixedSwapSample π) x))
    (fun i => W.eval i (mixedSampledInput π (fun k => x k / (d : ℤ))))
    (fun j => W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => x k / (d : ℤ))))
    (fun i j => G π i j (fun k => x k / (d : ℤ)))

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedTensorExchangeCorrection (n : ℕ)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (π : Fin (s + 3) → Fin 2) (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ℤ) : ℂ :=
  ∏ k : Fin n, G π ((tensorIndexEquiv W.outputDim n).symm a k)
    ((tensorIndexEquiv W.outputDim n).symm b k) x

theorem mixedTensorExchangeCorrection_norm (n : ℕ) {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (π : Fin (s + 3) → Fin 2) (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ZMod N) :
    ‖W.mixedTensorExchangeCorrection n G π a b (fun k => ((x k).val : ℤ))‖ ≤ B ^ n := by
  rw [mixedTensorExchangeCorrection, norm_prod]
  calc
    _ ≤ ∏ _ : Fin n, B := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hG _ _ _ x)
    _ = _ := by simp

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedRootExchangeCorrection
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  (W.rationalDilation (((s + 3 : ℕ) : ℚ)⁻¹)).mixedTensorExchangeCorrection ((s + 3) ^ (s + 2)) (W.divisionMixedExchangeCorrection (s + 3) G)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

namespace NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedRawCornerFactor (a b : MixedNonconstantCorner s → Fin W.outputDim)
    (v : MixedNonconstantCorner s) (x : Fin 2 → ℤ) : ℂ :=
  W.eval (a v) (mixedDiagonalCorner v.val x) *
    star (W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) x))

noncomputable def mixedCornerExchangeFactor
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : MixedNonconstantCorner s → Fin W.outputDim)
    (v : MixedNonconstantCorner s) (x : Fin 2 → ℤ) : ℂ :=
  if v.val 0 = 1 then W.mixedRawCornerFactor a b v x else
    complexCrossContraction
      (W.eval (a v) (mixedDiagonalCorner v.val x))
      (W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) x))
      (fun i => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) x))
      (fun j => W.eval j (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val)) x))
      (fun i j => G (mixedPreExchangeSample v.val) i j x)

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedCornerExchangeProduct
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : MixedNonconstantCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  star (∏ v, W.mixedCornerExchangeFactor G a b v x)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedPermutedDiagonalCorrection
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim) (b : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
    (W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor c x)) *
      W.mixedCornerExchangeProduct G c b x

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedRootCornerCorrection
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  W.mixedIntegrationRoot.mixedPermutedDiagonalCorrection (W.mixedRootExchangeCorrection G)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedIntegrationRoot_outputDim :
    W.mixedIntegrationRoot.outputDim = W.outputDim ^ mixedRootTensorExponent s := rfl

end NativeMultidegreeNilcharacter
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedFrozenMiddleRows
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedWeightTensor (k : Fin (s + 3))
    (a : MixedWeightCorner s (k.val + 1) → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∏ v, W.eval (a v) (mixedSampledInput (mixedWeightSample s k) x)

noncomputable def mixedFirstTensor (a : Fin (s + 3) → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  tensorVector W.eval (s + 3) a (fun j => x j.1)

theorem mixedWeightTensor_first (a : Fin (s + 3) → Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.mixedWeightTensor 0 (fun v => a ((mixedWeightOneEquiv s).symm v)) x = W.mixedFirstTensor a x := by
  unfold mixedWeightTensor mixedFirstTensor tensorVector
  rw [mixedWeightSample_first_input]
  exact (mixedWeightOneEquiv s).symm.prod_comp
    (fun d : Fin (s + 3) => W.eval (a d) (fun j => x j.1))

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedHigherTensor (b : MixedHigherCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∏ z, W.eval (b z) (mixedSampledInput (mixedWeightSample s z.1.succ) x)

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedMiddleTensor (b : MixedMiddleCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∏ z, W.eval (b z) (mixedSampledInput (mixedWeightSample s z.1.castSucc.succ) x)

theorem mixedHigherTensor_split (b : MixedMiddleCorner s → Fin W.outputDim)
    (c : Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.mixedHigherTensor (mixedSplitHigherMerge b c) x =
      W.mixedMiddleTensor b x * W.eval c (fun _ => x 0) := by
  unfold mixedHigherTensor
  rw [Fintype.prod_sigma, Fin.prod_univ_castSucc]
  congr 1
  · simp only [mixedSplitHigherMerge_castSucc]
    exact (Fintype.prod_sigma (fun z : MixedMiddleCorner s =>
      W.eval (b z) (mixedSampledInput (mixedWeightSample s z.1.castSucc.succ) x))).symm
  · simp only [Fin.val_last, mixedSplitHigherMerge_last, mixedWeightSample_last_input,
      Finset.prod_const, Finset.card_univ, mixedWeightCorner_card, Nat.choose_self, pow_one]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedOriginalWeightCorrection
    (F : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (i : Fin M.outputDim) (b : MixedHigherCorner s → Fin W.mixedIntegrationRoot.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∑ d : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim,
    (M.eval i x * star (W.mixedIntegrationRoot.mixedFirstTensor d x)) *
      F a (mixedGroupedWeightMerge d b) x

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootCyclicComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedWrappedDiagonalCorrection (N : ℕ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : MixedNonconstantCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ k, W.mixedDiagonalWrapCoefficient N a.2 k x * F (a.1, k) b x

noncomputable def mixedCyclicDiagonalCorrection (N : ℕ) (δ : ℝ≥0)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : MixedNonconstantCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  (1 - (smoothCyclicCarry N δ x : ℂ)) * F a b x +
    (smoothCyclicCarry N δ x : ℂ) * W.mixedWrappedDiagonalCorrection N F a b x

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedRootCyclicCorrection (N : ℕ) (δ : ℝ≥0)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  W.mixedIntegrationRoot.mixedCyclicDiagonalCorrection N δ (W.mixedRootCornerCorrection G)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SharedFreeComparisonBasis
namespace OAI

section

namespace Erdos3

open Module

variable {V μ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype μ]

theorem exists_firstProjection_basis_logHeight
    (e : Basis μ ℚ V) (K : Submodule ℚ (Fin 4 → V))
    (k : Basis (Fin (finrank ℚ K)) ℚ K) {p : ℝ}
    (hk : ∀ a i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (k a : Fin 4 → V) i) ≤ p) :
    ∃ c : Basis (Fin (finrank ℚ (K.map (LinearMap.proj 0)))) ℚ (K.map (LinearMap.proj 0)),
      ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ p := by
  have hspan : Submodule.span ℚ (Set.range (fun a => (k a : Fin 4 → V))) = K := by
    change Submodule.span ℚ (Set.range (K.subtype ∘ k)) = K
    rw [Set.range_comp, ← Submodule.map_span, k.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hproj : Submodule.span ℚ (Set.range (fun a => (k a : Fin 4 → V) 0)) =
      K.map (LinearMap.proj 0) := by
    change Submodule.span ℚ (Set.range
      ((LinearMap.proj (0 : Fin 4) : (Fin 4 → V) →ₗ[ℚ] V) ∘ fun a => (k a : Fin 4 → V))) = _
    rw [Set.range_comp, ← Submodule.map_span, hspan]
  apply exists_submodule_basis_of_spanning_logHeight e _ (fun a => (k a : Fin 4 → V) 0) hproj
  intro a i
  simpa only [Pi.basis_repr] using hk a ⟨0, i⟩

theorem exists_fourPetalSpace_basis_logHeight
    (e : Basis μ ℚ V) (D : Submodule ℚ V) (K : Submodule ℚ (Fin 4 → V))
    (b : Basis (Fin (finrank ℚ D)) ℚ D) (k : Basis (Fin (finrank ℚ K)) ℚ K)
    {p : ℝ} (hp : 0 ≤ p) (hdim : (Fintype.card μ : ℝ) ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p)
    (hk : ∀ a i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (k a : Fin 4 → V) i) ≤ p) :
    ∃ c : Basis (Fin (finrank ℚ (fourPetalSpace D K))) ℚ (fourPetalSpace D K),
      ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ preimageBasisBudget (4 * p) := by
  let : FiniteDimensional ℚ V := e.finiteDimensional_of_finite
  have hp4 : p ≤ 4 * p := by linarith only [hp]
  have hspan (U : Submodule ℚ V) (a : Basis (Fin (finrank ℚ U)) ℚ U) :
      Submodule.span ℚ (Set.range (fun j => (a j : V))) = U := by
    change Submodule.span ℚ (Set.range (U.subtype ∘ a)) = U
    rw [Set.range_comp, ← Submodule.map_span, a.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hkspan : Submodule.span ℚ (Set.range (fun j => (k j : Fin 4 → V))) = K := by
    change Submodule.span ℚ (Set.range (K.subtype ∘ k)) = K
    rw [Set.range_comp, ← Submodule.map_span, k.span_eq, Submodule.map_top, Submodule.range_subtype]
  apply exists_preimage_basis_logHeight e (Pi.basis (fun _ : Fin 4 => e)) D K
    (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)
    (fun j => (b j : V)) (fun j => (k j : Fin 4 → V)) (hspan D b) hkspan
    (mul_nonneg (by norm_num) hp)
  · simpa using mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4)
  · have hD : (finrank ℚ D : ℝ) ≤ Fintype.card μ := by
      exact_mod_cast D.finrank_le.trans_eq (finrank_eq_card_basis e)
    simpa only [Fintype.card_fin] using (hD.trans hdim).trans hp4
  · have hK : (finrank ℚ K : ℝ) ≤ 4 * Fintype.card μ := by
      exact_mod_cast four_submodule_finrank_le e K
    simpa only [Fintype.card_fin] using hK.trans
      (mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4))
  · exact fun a i => (hb a i).trans hp4
  · exact fun a i => (hk a i).trans hp4
  · rintro a ⟨j, i⟩
    by_cases hj : j = 0
    · subst j
      simpa [Pi.basis_repr, LinearMap.single_apply] using (hb a i).trans hp4
    · simpa [Pi.basis_repr, LinearMap.single_apply, hj, Ne.symm hj, rationalLogHeight] using
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hp)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix NNReal

theorem realifyCoordinateMap_eq_coordinates
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι]
    (φ : V →ₗ[ℚ] (ι → ℚ)) (x : ℝ ⊗[ℚ] V) :
    realifyCoordinateMap φ x = realRationalCoordinateEquiv (φ.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    funext i
    rw [realifyCoordinateMap_tmul, LinearMap.baseChange_tmul, realRationalCoordinateEquiv_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realify_basis_coordinates
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι]
    (b : Basis ι ℚ V) (x : ℝ ⊗[ℚ] V) :
    realifyCoordinateMap b.equivFun.toLinearMap x = (b.baseChange ℝ).equivFun x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    funext i
    rw [realifyCoordinateMap_tmul]
    change a * (b.repr v i : ℝ) = (b.baseChange ℝ).repr (a ⊗ₜ[ℚ] v) i
    rw [Basis.baseChange_repr_tmul]
    simp only [Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MarkedLocalObservableMetric
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t m : ℕ) (e : Basis (Fin d) ℚ (MarkedShiftQuotient F v w marked t))

theorem normalizedMarkedPhase_coordinate_norm_le {p : ℝ}
    (hd : (d : ℝ) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (e j) i) ≤ p)
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    ‖torusPhaseLinear (normalizedMarkedPhase F v w marked t m) x‖ ≤
      Real.exp (2 * p) * ‖(e.baseChange ℝ).equivFun x‖ := by
  exact scalarExtension_coordinate_norm_le e (RationalTorus.basis t)
    (normalizedMarkedPhase F v w marked t m).toLinearMap
    (by simpa only [Fintype.card_fin] using hd)
    (fun i j => by
      change rationalLogHeight (normalizedMarkedPhase F v w marked t m (e j) i) ≤ p
      exact hphase i j) x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

theorem factorizationInputBudget_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ p + factorizationInputOffset s :=
  hp.trans (le_factorizationInputBudget s hp)

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorSubspaceCorrectionRepresentatives
namespace OAI

section

namespace Erdos3

theorem support_subset_boundedExponentWindow {K R : Type*} [Fintype K] [CommSemiring R]
    (p : MvPolynomial K R) {s : ℕ} (hp : p.totalDegree ≤ s) :
    p.support ⊆ boundedExponentWindow K s := by
  intro m hm
  exact (boundedExponentWindow_mem_iff s m).mpr ((MvPolynomial.le_totalDegree hm).trans hp)

end Erdos3

end

end OAI
end


