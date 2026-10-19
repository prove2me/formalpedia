-- Prove2me | Definitions.Def_OAIE3v2B171
-- name    : OAIE3v2B171
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:30:01.991215+00:00
-- url     : https://prove2.me/theorems/30573304-f240-4d5c-b251-2d14d2066444
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 173 of 311
-- statement:
--   Definitions bundle 173 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152`, `OAIE3v2B153`, `OAIE3v2B156`, `OAIE3v2B157` of this split.
--
--   Modules: `Estimates/AllocatedMarkedDictionaryRecovery.lean`, `Estimates/DiagonalWrapComparison.lean`, `Estimates/LinearMapIntegralCover.lean`, `Estimates/MixedFrozenMiddleRows.lean`, `Estimates/MixedPermutationTensor.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/NativeBoundedVariablePatchExpansion.lean`, `Estimates/NativeCrossFactorization.lean`, `Estimates/NativeMixedReflectionBridge.lean`, `Estimates/NativeSpaceMap.lean`, `Estimates/OriginalMixedRootEquivalence.lean`, `Estimates/TensorSquarePairComparison.lean`, `Estimates/UniformControlledNativeExternalNetsOfRecovery.lean`, `Estimates/UnitVerticalCyclicDifference.lean`, `Estimates/UnitVerticalMeanRowCorrelation.lean`, `Fourier/BohrNiltestBudget.lean`, `Fourier/NativeMixedFourierProfiles.lean`, `Geometry/MixedReplicatedCoordinates.lean`, `Geometry/NativeCoordinateFiber.lean`, `Geometry/NativeCoordinateSplitFreezing.lean`, `Geometry/NativeMixedCoordinateSlices.lean`, `Linear/RankSparseFamilies.lean`, `Linear/SplitCoverProjection.lean`, `Nilpotent/NativeRankZeroNiltest.lean`, `Nilpotent/PolarizedVerticalNiltest.lean`, `Polynomial/NativeDegreeRankFamily.lean`, `Polynomial/NativeZeroDegreeCorrelation.lean`, `Polynomial/NormalizedMarkedPhase.lean`, `Polynomial/PolynomialShiftStructure.lean`, `Polynomial/PositivePolynomialVectorOrbit.lean`, `Polynomial/RaisedDegreeRank.lean`, `Sampling/MixedAssignmentSampling.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152
import Definitions.Def_OAIE3v2B153
import Definitions.Def_OAIE3v2B156
import Definitions.Def_OAIE3v2B157

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSpaceMap
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))

theorem nativeSpaceMap_mk (x : D.RealGroup) :
    D.nativeSpaceMap E φ hφ (QuotientGroup.mk x) =
      QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ x) := rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d t : ℕ}

theorem torusPhaseLinear_tmul (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)
    (a : ℝ) (x : L) (i : Fin t) :
    torusPhaseLinear φ (a ⊗ₜ[ℚ] x) i = a * (φ x i : ℝ) := by
  change ((RationalTorus.basis t).baseChange ℝ).repr
    (φ.toLinearMap.baseChange ℝ (a ⊗ₜ[ℚ] x)) i = _
  rw [LinearMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul, RationalTorus.basis_repr]
  simpa [Algebra.smul_def] using mul_comm (φ x i : ℝ) a

variable (D : RationalFilteredNilmanifold L s d) (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)

theorem torusPhaseLinear_mul (g h : D.RealGroup) :
    torusPhaseLinear φ (g * h).coord = torusPhaseLinear φ g.coord + torusPhaseLinear φ h.coord := by
  let f := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := (RationalTorus.nilmanifold t).filtration.lowerCentralSeries_eq_bot) φ
  change ((RationalTorus.basis t).baseChange ℝ).equivFun (f (g * h)).coord =
    ((RationalTorus.basis t).baseChange ℝ).equivFun (f g).coord +
      ((RationalTorus.basis t).baseChange ℝ).equivFun (f h).coord
  rw [f.map_mul, (RationalTorus.nilmanifold t).filtration.realification.stepOne_coord_mul, map_add]

variable (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))

noncomputable def nativeTorusProjection : D.Space → (Fin t → CircleFourier.Circle) :=
  (RationalTorus.phaseProjection t) ∘
    D.nativeSpaceMap (RationalTorus.nilmanifold t) φ (torusPhase_lattice_map D φ hphase)

noncomputable def nativeTorusLocalLift : D.Space → (Fin t → ℝ) :=
  centeredTorusLift ∘ nativeTorusProjection D φ hphase

theorem nativeTorusLocalLift_mk (g : D.RealGroup)
    (hg : ∀ i, |torusPhaseLinear φ g.coord i| ≤ 1 / 4) :
    nativeTorusLocalLift D φ hphase (QuotientGroup.mk g) = torusPhaseLinear φ g.coord := by
  funext i
  exact centeredCircleLift_coe (hg i)

include hphase in
theorem torusPhaseLinear_eq_of_small (g h : D.RealGroup)
    (hg : ∀ i, |torusPhaseLinear φ g.coord i| ≤ 1 / 4)
    (hh : ∀ i, |torusPhaseLinear φ h.coord i| ≤ 1 / 4)
    (heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h) :
    torusPhaseLinear φ g.coord = torusPhaseLinear φ h.coord := by
  rw [← nativeTorusLocalLift_mk D φ hphase g hg, ← nativeTorusLocalLift_mk D φ hphase h hh, heq]

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

theorem adaptedPolynomialRealValueHom_coord (t : σ → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    (F.adaptedPolynomialRealValueHom w t g).coord =
      eval₂ t (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCrossFactorization
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

namespace NativeVectorCorrelation

theorem exists_of_mean {I : Type*} (degree N : ℕ) [NeZero N] {p : ℝ}
    (f : I → ZMod N → ℂ) (hp : 2 ≤ p) (h : ∃ i, Real.exp (-p) ≤ ‖𝔼 x, f i x‖) :
    Nonempty (NativeVectorCorrelation degree N p f) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨{
    L := RationalTorus.Algebra 0
    dim := 0
    model := RationalTorus.trivialNilmanifold degree
    test := RationalFilteredNilmanifold.Niltest.const _ (fun _ : Unit => 1) 1
    complexity := RationalTorus.trivialNilmanifold_const_one_complexity degree _ hp
    coordinate := i
    correlation := ?_
  }⟩
  simpa only [RationalFilteredNilmanifold.Niltest.evalCyclic,
    RationalFilteredNilmanifold.Niltest.eval, RationalFilteredNilmanifold.Niltest.const,
    star_one, mul_one] using hi

end NativeVectorCorrelation

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_native_two_unit_comparison {A I J : Type*} [Fintype I] [Fintype J]
    {degree N : ℕ} [NeZero N] {p q r : ℝ}
    (f : A → ZMod N → ℂ) (v a : I → ZMod N → ℂ) (b : J → ZMod N → ℂ)
    (ha : ∀ x, ∑ i, ‖a i x‖ ^ 2 = 1) (hb : ∀ x, ∑ j, ‖b j x‖ ^ 2 = 1)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp q) (hJ : (Fintype.card J : ℝ) ≤ Real.exp r)
    (W : NativeVectorCorrelation degree N p (fun ai : A × I => fun x => f ai.1 x * star (v ai.2 x))) :
    Nonempty (NativeVectorCorrelation degree N (p + q + r)
      (fun aij : A × ((I × I) × (I × J)) => fun x =>
        f aij.1 x * star (b aij.2.2.2 x) *
          star (v aij.2.1.1 x * star (a aij.2.1.2 x)) *
          star (a aij.2.2.1 x * star (b aij.2.2.2 x)))) := by
  classical
  let F (x : ZMod N) := f W.coordinate.1 x * star (W.test.evalCyclic N (fun _ => x))
  let P (j : I) (x : ZMod N) := star (a j x)
  let ψ (j : I) (_ : Unit) (x : ZMod N) := star (v W.coordinate.2 x * star (a j x))
  have hcorr : Real.exp (-p) ≤ ‖𝔼 x ∈ (Finset.univ : Finset (ZMod N)), F x * star (v W.coordinate.2 x)‖ := by
    simpa only [F, mul_assoc, mul_left_comm, mul_comm] using W.correlation
  obtain ⟨j, _, hj⟩ := exists_unit_expansion_correlation Finset.univ F
    (fun x => star (v W.coordinate.2 x)) P (fun (_ : I) (_ : Unit) => (1 : ℂ)) ψ
    (fun x _ => by simpa only [P, norm_star] using ha x)
    (fun j x _ => by simp only [P, ψ, star_star, star_mul, Fintype.sum_unique, one_mul, mul_comm])
    (Real.exp_pos (-p)) (Real.exp_pos q) (by norm_num : (0 : ℝ) < 1) hI (fun _ => by simp) hcorr
  have hfrac : Real.exp (-p) / (Real.exp q * 1) = Real.exp (-(p + q)) := by
    rw [mul_one, ← Real.exp_sub]
    congr 1
    ring
  rw [hfrac] at hj
  let F' (x : ZMod N) := F x * ψ j () x
  let P' (k : J) (x : ZMod N) := star (b k x)
  let ψ' (k : J) (_ : Unit) (x : ZMod N) := star (a j x * star (b k x))
  have hj' : Real.exp (-(p + q)) ≤
      ‖𝔼 x ∈ (Finset.univ : Finset (ZMod N)), F' x * star (a j x)‖ := by
    simpa only [F', P, mul_assoc, mul_left_comm, mul_comm] using hj
  obtain ⟨k, _, hk⟩ := exists_unit_expansion_correlation Finset.univ F'
    (fun x => star (a j x)) P' (fun (_ : J) (_ : Unit) => (1 : ℂ)) ψ'
    (fun x _ => by simpa only [P', norm_star] using hb x)
    (fun k x _ => by simp only [P', ψ', star_star, star_mul, Fintype.sum_unique, one_mul, mul_comm])
    (Real.exp_pos (-(p + q))) (Real.exp_pos r) (by norm_num : (0 : ℝ) < 1) hJ (fun _ => by simp) hj'
  have hfrac' : Real.exp (-(p + q)) / (Real.exp r * 1) = Real.exp (-(p + q + r)) := by
    rw [mul_one, ← Real.exp_sub]
    congr 1
    ring
  rw [hfrac'] at hk
  exact ⟨{
    L := W.L
    dim := W.dim
    model := W.model
    test := W.test
    complexity := W.complexity.mono (by linarith)
    coordinate := (W.coordinate.1, (W.coordinate.2, j), (j, k))
    correlation := by simpa only [F, F', P', ψ, ψ', mul_assoc, mul_left_comm, mul_comm] using hk
  }⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SplitCoverProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D E : RationalFilteredNilmanifold L s d)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem sublatticeProjection_lipschitz (h : E.lattice ≤ D.lattice) (hb : E.basis = D.basis) :
    letI := E.metricSpace
    letI := D.metricSpace
    LipschitzWith 1 (sublatticeProjection D E h) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hLip : LipschitzWith 1 (MonoidHom.id D.RealGroup) := LipschitzWith.id
  have hc := lipschitz_cosetMap E.realLattice D.realLattice E.realLattice_closed_discrete.1
    D.realLattice_closed_discrete.1 (MonoidHom.id _) (Subgroup.map_mono h) hLip
  change @LipschitzWith E.Space D.Space
    (quotientMetricSpace (E.basis.baseChange ℝ) E.realLattice
      E.realLattice_closed_discrete.1).toEMetricSpace.toPseudoEMetricSpace
    (quotientMetricSpace (D.basis.baseChange ℝ) D.realLattice
      D.realLattice_closed_discrete.1).toEMetricSpace.toPseudoEMetricSpace
    1 (sublatticeProjection D E h)
  rw [hb]
  exact hc

theorem sublattice_pullback_lipschitz (h : E.lattice ≤ D.lattice) (hb : E.basis = D.basis)
    (u : D.Space → ℂ) {K : ℝ≥0} (hu : letI := D.metricSpace; LipschitzWith K u) :
    letI := E.metricSpace
    LipschitzWith K (u ∘ sublatticeProjection D E h) := by
  let := E.metricSpace
  let := D.metricSpace
  simpa only [mul_one] using hu.comp (sublatticeProjection_lipschitz D E h hb)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RaisedDegreeRank
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}

namespace DegreeRankStructure

variable {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

noncomputable def orbitEquiv {σ : Type*} (w : σ → ℕ) :
    D.filtration.realification.PolynomialOrbit w ≃*
      R.filtration.realification.associatedDegree.PolynomialOrbit w :=
  D.filtration.realification.orbitEquivOfEq R.real_associated.symm w

theorem orbitEquiv_eval {σ : Type*} (w : σ → ℕ)
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    R.filtration.realification.associatedDegree.polynomialOrbitEval w x (R.orbitEquiv w g) =
      D.filtration.realification.polynomialOrbitEval w x g :=
  D.filtration.realification.orbitEquivOfEq_eval R.real_associated.symm w g x

end DegreeRankStructure

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeDegreeRankFamily
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

namespace NativeDegreeRankFamily

variable {s r : ℕ} {A : Type*} {p q : ℝ} (W : NativeDegreeRankFamily s r A p)

theorem orbit_rank_normalized (a : A) :
    W.rank.filtration.realification.associatedDegree.polynomialOrbitEval (fun _ : Unit => 1) 0
      (W.rank.orbitEquiv (fun _ : Unit => 1) (W.orbit a)) = 1 := by
  rw [W.rank.orbitEquiv_eval]
  exact W.normalized a

end NativeDegreeRankFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearMapIntegralCover
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct

namespace RationalFilteredNilmanifold

theorem linearMap_real_lattice {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
    (φ : L →ₗ[ℚ] M)
    (hφ : ∀ z : D.filtration.Group, z ∈ D.lattice →
      (⟨φ z.coord⟩ : E.filtration.Group) ∈ E.lattice)
    (z : D.RealGroup) (hz : z ∈ D.realLattice) :
    (⟨φ.baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice := by
  obtain ⟨x, hx, rfl⟩ := hz
  refine ⟨⟨φ x.coord⟩, hφ x hx, ?_⟩
  apply NilpotentLieBCHGroup.ext
  change (1 : ℝ) ⊗ₜ[ℚ] φ x.coord = φ.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] x.coord)
  exact (LinearMap.baseChange_tmul _ _ _).symm

theorem exists_native_linear_target_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] {t d e k : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (φ : L →ₗ[ℚ] M) (ψ : L →ₗ[ℚ] (Fin k → ℚ)) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p → (k : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (ψ (D.basis j) i) ≤ p) →
      ∃ (B : ℕ) (Λ : Subgroup D.filtration.Group) (hB : 0 < B)
        (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ)
        (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B),
        (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ Λ ≤ D.lattice ∧
        bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B ∧
        (D.withLattice Λ B hB hin hout).GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ z : D.filtration.Group, z ∈ Λ → (⟨φ z.coord⟩ : E.filtration.Group) ∈ E.lattice) ∧
        ∀ z : D.filtration.Group, z ∈ Λ → IntegralVector (ψ z.coord) := by
  obtain ⟨a, _, hcover⟩ := exists_integral_grid_subgroup_exp s
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := 2 * X + 2 * (X + 2) ^ 3 + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (P₀ + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ t d e k D E φ ψ p hp hD hE hk hφ hψ
  classical
  let A := LinearMap.toMatrix D.basis E.basis φ
  let Z := LinearMap.toMatrix D.basis (Pi.basisFun ℚ (Fin k)) ψ
  let l := D.grid * ((E.grid * matrixDenominator A) * matrixDenominator Z)
  let P := 2 * p + 2 * (p + 2) ^ 3 + 1
  have hp1 : p + 1 ≤ P := by dsimp [P]; nlinarith [pow_nonneg (by linarith : 0 ≤ p + 2) 3]
  have hpP : p ≤ P := (by linarith : p ≤ p + 1).trans hp1
  have hP : 0 ≤ P := hp.trans hpP
  have hA : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp 1
      (by simpa only [Fintype.card_fin] using hE.1)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    have h := ((rationalLogHeight_le_iff _ p).mp (hφ i j)).2
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact h.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  have hZ : (matrixDenominator Z : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power Z hp 1
      (by simpa only [Fintype.card_fin] using hk)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    have h := ((rationalLogHeight_le_iff _ p).mp (hψ i j)).2
    dsimp only [Z]
    rw [LinearMap.toMatrix_apply]
    simp only [Pi.basisFun_repr]
    exact h.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  have hl : 0 < l := Nat.mul_pos D.grid_pos
    (Nat.mul_pos (Nat.mul_pos E.grid_pos (matrixDenominator_pos A)) (matrixDenominator_pos Z))
  have hDl : D.grid ∣ l := dvd_mul_right _ _
  have hAl : E.grid * matrixDenominator A ∣ l :=
    dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  have hZl : matrixDenominator Z ∣ l :=
    dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  have hlP : (l : ℝ) ≤ Real.exp P := by
    have h := mul_le_mul hD.2.1
      (mul_le_mul (mul_le_mul hE.2.1 hA (Nat.cast_nonneg _) (Real.exp_nonneg _)) hZ
        (Nat.cast_nonneg _) (by positivity)) (by positivity) (Real.exp_nonneg _)
    change (D.grid : ℝ) * ((E.grid : ℝ) * matrixDenominator A * matrixDenominator Z) ≤ _ at h
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add] at h
    have h' : (l : ℝ) ≤ Real.exp (p + (p + (p + 2) ^ 3 + (p + 2) ^ 3)) := by
      simpa only [l, Nat.cast_mul] using h
    apply h'.trans
    apply Real.exp_le_exp.mpr
    dsimp only [P]
    ring_nf
    linarith
  have hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates D.basis D.lattice :=
    fun _ hx => D.inner_grid (scaledIntegerGrid_subset_of_dvd hDl hx)
  obtain ⟨B, Λ, hB, hlB, hBP, hΛ, hcoords⟩ :=
    hcover D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice l ⌈Real.exp p⌉₊ P hl
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) hinner hP
      (by simpa only [Fintype.card_fin] using hD.1.trans hpP)
      ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1)) hlP
  have hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ := hcoords.symm.le
  have hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B := by
    rw [hcoords]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx
  have htotal : P + (P + a) ^ a ≤ (p + C) ^ C := by
    simpa [P₀, X, P, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (P + a) ^ a ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  have hpC : p ≤ (p + C) ^ C := hpP.trans
    ((le_add_of_nonneg_right (by positivity : 0 ≤ (P + a) ^ a)).trans htotal)
  have hBC : (B : ℝ) ≤ Real.exp ((p + C) ^ C) := hBP.trans (Real.exp_le_exp.mpr haC)
  refine ⟨B, Λ, hB, hin, hout, hBC, hΛ, hcoords,
    D.withLattice_geometry Λ B hB hin hout hD hpC hBC, ?_, ?_⟩
  · intro z hz
    apply (bchSubgroupCoordinates_repr E.basis E.lattice ⟨φ z.coord⟩).mp
    apply E.inner_grid
    apply linearMap_mem_scaledGrid D.basis E.basis φ (hAl.trans hlB)
    rw [← hcoords]
    exact (bchSubgroupCoordinates_repr D.basis Λ z).mpr hz
  · intro z hz
    have hgrid : D.basis.equivFun z.coord ∈ scaledIntegerGrid B := by
      rw [← hcoords]
      exact (bchSubgroupCoordinates_repr D.basis Λ z).mpr hz
    have h := linearMap_mem_scaledGrid D.basis (Pi.basisFun ℚ (Fin k)) ψ (b := 1)
      (by simpa only [one_mul] using hZl.trans hlB) hgrid
    obtain ⟨v, hv⟩ := h
    exact ⟨v, fun i => by simpa only [Nat.cast_one, one_smul, Basis.equivFun_apply,
      Pi.basisFun_repr] using congrFun hv i⟩

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedMarkedDictionaryRecovery
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open scoped TensorProduct

theorem realificationMap_id_eq_changeStep {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s t : ℕ} (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥) :
    (realificationMap (hnil := hs) (hM := ht) (LieHom.id : L →ₗ⁅ℚ⁆ L) : _ → _) =
      (changeStep (realification_lowerCentralSeries_eq_bot hs)
        (realification_lowerCentralSeries_eq_bot ht) : _ → _) := by
  funext x
  apply ext
  exact realificationLieHom_id_apply x.coord

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

theorem exists_native_product_partition_approximation (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} [Fintype α] [DecidableEq α]
      {L : α → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : α → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {p rho : ℝ},
      0 ≤ p → (Fintype.card α : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < rho → 1 / rho ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
      letI := (pi D).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (D i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (v : (pi D).Space → ℂ) (ell : ℝ≥0), LipschitzWith ell v → (∀ x, ‖v x‖ ≤ 2) →
              ∃ c : (∀ i, Fin (n i)) → ℂ, (∀ j, ‖c j‖ ≤ 2) ∧
                ∀ x, ‖v x - ∑ j, (∏ i, (ψ i (j i) (productProjection D i x) : ℂ)) * c j‖ ≤
                  (ell : ℝ) * (productMetricBound d : ℝ) * rho := by
  obtain ⟨C, hC, hpart⟩ := exists_native_factor_partitions s a
  refine ⟨C, hC, ?_⟩
  intro α _ _ L _ _ _ _ _ _ _ _ _ _ d D p rho hp hα hD hrho hscale
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, hdiam⟩ :=
    hpart D hp hα hD hrho hscale
  refine ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, ?_⟩
  intro v ell hv hbound
  let F := v ∘ (productSpaceEquiv D).symm
  have hF : LipschitzWith (ell * productMetricBound d) F :=
    hv.comp (productSpaceEquiv_symm_lipschitz D)
  obtain ⟨c, hc, herr⟩ := exists_bounded_complex_partition_approximation
    (productPartitionWeight ψ) (productPartitionWeight_nonneg ψ (fun i j x => (hunit i j x).1))
    (sum_productPartitionWeight ψ hsum)
    (productPartitionWeight_diameter ψ hrho.le (fun i j x => (hunit i j x).1) hdiam)
    F 2 (fun x => hbound _) hF
  refine ⟨c, hc, fun x => ?_⟩
  have h := herr (productSpaceEquiv D x)
  simp only [F, Function.comp_apply, Equiv.symm_apply_apply, productPartitionWeight,
    productSpaceEquiv_apply, NNReal.coe_mul] at h
  push_cast at h
  exact h

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositivePolynomialVectorOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial NilpotentLieBCHGroup

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {bound : σ → ℕ} (M : D.MultidegreeStructure bound)
  (J : α → Set (σ →₀ ℕ)) [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))

omit [DecidableEq σ] [∀ a, DecidablePred (· ∈ J a)] in
theorem positivePolynomialQuotientProductModel_map_injective (p : ℝ)
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → M.filtration.layer (fun i => c i) = ⊥) :
    Function.Injective (M.filtration.positivePolynomialQuotientProductRealMap J hJ) :=
  M.filtration.positivePolynomialQuotientProductRealMap_injective J hJ (M.positiveCoefficientBasis p) hcover

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalMeanRowCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_unit_bounded_vertical_mean_row :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ H X L : Type*}
      [Fintype H] [Nonempty H] [Fintype X] [Nonempty X]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {s d : ℕ} (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ}
      (T : D.Niltest w) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ (sample : H → X → σ → ℤ) (f : H → X → ℂ), (∀ h x, ‖f h x‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 x, f h x * star (T.eval (sample h x))‖) →
      ∃ (η : L →ₗ[ℚ] ℚ) (U : D.Niltest w),
        U.ComplexityLE ((p + C) ^ C) ∧ U.normBound ≤ 1 ∧ U.orbit = T.orbit ∧
        (∀ i, rationalLogHeight (η (D.basis i)) ≤ (p + C) ^ C) ∧
        (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          U.observable (z • x) =
            character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * U.observable x) ∧
        (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional η z.coord = n) ∧
        Real.exp (-((p + C) ^ C)) ≤
          (𝔼 h, ‖𝔼 x, f h x * star (U.eval (sample h x))‖) := by
  obtain ⟨A, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (2 * X + 2 + Polynomial.C A) ^ A + (2 * X + 2) + 2)
  refine ⟨C, hC, ?_⟩
  intro σ H Y L _ _ _ _ _ _ _ _ _ _ s d D w T p hp hT sample f hf hcorr
  let r := 2 * p + 2
  let δ := Real.exp (-(p + 2))
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hδ : 0 < δ := Real.exp_pos _
  have hδr : δ⁻¹ ≤ Real.exp r := by
    dsimp [δ]
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr (by dsimp [r]; linarith)
  obtain ⟨J, inst, η, U, hcard, hheight, hU, hchar, hint, _, _, herr⟩ :=
    T.exists_controlled_vertical_decomposition hr (hT.mono hpr) δ hδ hδr
  let := inst
  have hrow (h : H) : ‖𝔼 x, f h x * star (T.eval (sample h x))‖ ≤
      (∑ j : J, ‖𝔼 x, f h x * star ((U j).eval (sample h x))‖) + δ := by
    apply (norm_correlation_partition_bound (f h)
      (fun x => T.eval (sample h x)) (fun j x => (U j).eval (sample h x)) (hf h)).trans
    apply add_le_add le_rfl
    apply Finset.expect_le Finset.univ_nonempty
    intro x _
    simpa only [norm_sub_rev] using herr (sample h x)
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun h _ => hrow h)
  simp only [Finset.expect_add_distrib, Finset.expect_sum_comm, Fintype.expect_const] at hm
  have htwo : 2 * δ ≤ Real.exp (-p) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hs : δ ≤ ∑ j : J, (𝔼 h, ‖𝔼 x, f h x * star ((U j).eval (sample h x))‖) := by
    linarith
  obtain ⟨j, hj⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ))
    (fun j => 𝔼 h, ‖𝔼 x, f h x * star ((U j).eval (sample h x))‖)
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hs)
  have hne : ∃ x, (U j).observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, (U j).eval x = 0 := fun x => hzero _
    simp only [heval, star_zero, mul_zero, Finset.expect_const_zero, norm_zero] at hj
    exact (not_le_of_gt (div_pos hδ (Real.exp_pos _))) hj
  let q := p + verticalDecompositionBudget r + r + 2
  have hq : q ≤ (p + C) ^ C := by
    have hb : p + (r + A) ^ A + r + 2 ≤ (p + C) ^ C := by
      simpa [X, r, Polynomial.eval₂_pow] using hbudget p hp
    dsimp [q]
    linarith [hvertical r hr]
  have hrq : r ≤ (p + C) ^ C := by
    have hv := verticalDecompositionBudget_nonneg hr
    dsimp [q] at hq
    linarith
  have hvq : verticalDecompositionBudget r ≤ (p + C) ^ C := by
    dsimp [q] at hq
    linarith
  have hnormcorr : Real.exp (-q) ≤
      (𝔼 h, ‖𝔼 x, f h x * star (((U j).expNormalize r).eval (sample h x))‖) := by
    simp only [expNormalize_eval]
    rw [mean_row_correlation_scale f (fun h x => (U j).eval (sample h x)) (Real.exp_nonneg _)]
    have heq : Real.exp (-r) * (δ / Real.exp (verticalDecompositionBudget r)) =
        Real.exp (-q) := by
      dsimp [δ, q]
      rw [← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hj (Real.exp_nonneg _)
  refine ⟨η j, (U j).expNormalize r,
    ((U j).expNormalize_complexity (hU j).1).mono hrq,
    (U j).expNormalize_norm (hU j).1, (hU j).2,
    fun i => (hheight j i).trans hvq, ?_, hint j hne,
    (Real.exp_le_exp.mpr (neg_le_neg hq)).trans hnormcorr⟩
  intro z hz x
  change (Real.exp (-r) : ℂ) * (U j).observable (z • x) =
    _ * ((Real.exp (-r) : ℂ) * (U j).observable x)
  rw [hchar j z hz]
  ring

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct NNReal

variable {σ L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {S : Subgroup D.RealGroup} {p : ℝ} {w : σ → ℕ}

noncomputable def test (V : D.UnitVerticalObservable S I p)
    (g : D.filtration.realification.PolynomialOrbit w) (i : I) : D.Niltest w where
  orbit := g
  observable := V.observable i
  normBound := 1
  lipBound := V.lipBound
  norm_le := V.norm i
  lipschitz := V.lipschitz i

theorem test_eval (V : D.UnitVerticalObservable S I p)
    (g : D.filtration.realification.PolynomialOrbit w) (i : I) (x : σ → ℤ) :
    (V.test g i).eval x = V.observable i
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)) := rfl

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolarizedVerticalNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct NNReal

variable {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p)

noncomputable def coordinateCombination (i j : I) (c : ℂ) (x : D.Space) : ℂ :=
  V.observable i x + c * V.observable j x

theorem coordinateCombination_norm (i j : I) (c : ℂ) (hc : ‖c‖ ≤ 1) (x : D.Space) :
    ‖V.coordinateCombination i j c x‖ ≤ 2 := by
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have hmul := mul_le_mul hc (V.norm j x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  linarith [V.norm i x]

theorem coordinateCombination_lipschitz (i j : I) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    letI := D.metricSpace
    LipschitzWith (2 * V.lipBound) (V.coordinateCombination i j c) := by
  let := D.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hi := (V.lipschitz i).dist_le_mul x y
  have hj := (V.lipschitz j).dist_le_mul x y
  rw [dist_eq_norm] at hi hj ⊢
  have he : V.coordinateCombination i j c x - V.coordinateCombination i j c y =
      (V.observable i x - V.observable i y) + c * (V.observable j x - V.observable j y) := by
    unfold coordinateCombination
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have hm := mul_le_mul_of_nonneg_right hc (norm_nonneg (V.observable j x - V.observable j y))
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  nlinarith

theorem coordinateCombination_vertical (i j : I) (c : ℂ) (z : D.RealGroup) (hz : z ∈ T)
    (x : D.Space) : V.coordinateCombination i j c (z • x) =
      CircleFourier.character ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle) *
        V.coordinateCombination i j c x := by
  unfold coordinateCombination
  rw [V.vertical i z hz, V.vertical j z hz]
  ring

noncomputable def combinationNiltest {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i j : I) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    D.Niltest w where
  orbit := g
  observable := V.coordinateCombination i j c
  normBound := 2
  lipBound := 2 * V.lipBound
  norm_le := V.coordinateCombination_norm i j c hc
  lipschitz := V.coordinateCombination_lipschitz i j c hc

theorem combinationNiltest_complexity {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i j : I) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    (V.combinationNiltest g i j c hc).ComplexityLE (p + 5) := by
  refine ⟨hD.mono D (by linarith), ?_⟩
  change Real.log (2 + (2 : ℝ) + ((2 * V.lipBound : ℝ≥0) : ℝ)) ≤ p + 5
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  calc
    _ ≤ 6 * Real.exp p := by nlinarith [V.lip_bound, Real.one_le_exp hp]
    _ ≤ Real.exp 5 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (5 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalWrapComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def circleCarryCutoff (δ : ℝ≥0) (x : CircleFourier.Circle) : ℝ :=
  linearCutoff (1 / 6) δ (dist x ((1 / 2 : ℝ) : CircleFourier.Circle))

noncomputable def smoothCyclicCarry (N : ℕ) (δ : ℝ≥0) (x : Fin 2 → ℤ) : ℝ :=
  circleCarryCutoff δ ((((x 0 : ℝ) + (x 1 : ℝ)) / (3 * N) : ℝ) : CircleFourier.Circle)

theorem circleCarryCutoff_range (δ : ℝ≥0) (x : CircleFourier.Circle) :
    0 ≤ circleCarryCutoff δ x ∧ circleCarryCutoff δ x ≤ 1 := linearCutoff_range _ _ _

theorem circleCarryCutoff_lipschitz (δ : ℝ≥0) (hδ : 0 < δ) :
    LipschitzWith δ⁻¹ (circleCarryCutoff δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply ((linearCutoff_lipschitz (1 / 6) δ hδ).dist_le_mul _ _).trans
  apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
  rw [Real.dist_eq]
  exact abs_dist_sub_le _ _ _

theorem circle_dist_half_of_unit_interval {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    dist (t : CircleFourier.Circle) ((1 / 2 : ℝ) : CircleFourier.Circle) = |t - 1 / 2| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  apply (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (by norm_num)).mpr
  norm_num only [abs_one]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateSplitFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

theorem coordinateSplitDownset_terminal [Fintype σ] [Nonempty σ]
    {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (i : σ) (a : σ →₀ ℕ)
    (ha : a ∉ coordinateSplitDownset s i false ∪ coordinateSplitDownset s i true) :
    (F.totalDegreeMultifiltration σ).layer (fun j => a j) = ⊥ := by
  apply F.layer_eq_bot_above_step
  exact Nat.lt_of_not_ge (fun h => ha (coordinateSplitDownset_covers s i a h))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TensorSquarePairComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def tensorSquareExchangeCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin (W.outputDim ^ 2)) (x : Fin 2 → ℤ) : ℂ :=
  G ((tensorIndexEquiv W.outputDim 2).symm a 0) ((tensorIndexEquiv W.outputDim 2).symm b 0) x *
    G ((tensorIndexEquiv W.outputDim 2).symm a 1) ((tensorIndexEquiv W.outputDim 2).symm b 1) x

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedReplicatedCoordinates
namespace OAI

section

namespace Erdos3

def mixedHead (s : ℕ) : MixedReplicatedIndex s := ⟨0, ⟨0, by change 0 < 1; omega⟩⟩

def mixedReplica {s : ℕ} (j : Fin s) : MixedReplicatedIndex s := ⟨1, ⟨j.val, j.isLt⟩⟩

theorem mixedReplica_injective (s : ℕ) : Function.Injective (mixedReplica (s := s)) := by
  intro i j h
  exact Fin.ext (congrArg (fun a : MixedReplicatedIndex s => a.2.val) h)

theorem mixedReplicated_cases {s : ℕ} (j : MixedReplicatedIndex s) :
    j = mixedHead s ∨ ∃ i : Fin s, j = mixedReplica i := by
  rcases j with ⟨b, j⟩
  fin_cases b
  · left
    change Fin 1 at j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  · exact Or.inr ⟨⟨j.val, j.isLt⟩, rfl⟩

def mixedRepeatedCoordinates (s : ℕ) : List (MixedReplicatedIndex s) :=
  List.ofFn (mixedReplica (s := s))

theorem mixedRepeatedCoordinates_length (s : ℕ) : (mixedRepeatedCoordinates s).length = s := by
  simp only [mixedRepeatedCoordinates, List.length_ofFn]

theorem mixedRepeatedCoordinates_nodup (s : ℕ) : (mixedRepeatedCoordinates s).Nodup :=
  List.nodup_ofFn.mpr (mixedReplica_injective s)

theorem mixedRepeatedCoordinates_get (s : ℕ) (j : Fin (mixedRepeatedCoordinates s).length) :
    (mixedRepeatedCoordinates s).get j = mixedReplica (Fin.cast (mixedRepeatedCoordinates_length s) j) := by
  exact List.get_ofFn (mixedReplica (s := s)) j

theorem mem_mixedRepeatedCoordinates (s : ℕ) (j : MixedReplicatedIndex s) :
    j ∈ mixedRepeatedCoordinates s ↔ j.1 = 1 := by
  change j ∈ List.ofFn (mixedReplica (s := s)) ↔ j.1 = 1
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    rfl
  · intro h
    rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
    · norm_num [mixedHead] at h
    · exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem mixedReplicatedInput_head {s : ℕ} {α : Type*} (h : α) (v : Fin s → α) :
    mixedReplicatedInput h v (mixedHead s) = h := rfl

theorem mixedReplicatedInput_replica {s : ℕ} {α : Type*} (h : α) (v : Fin s → α) (j : Fin s) :
    mixedReplicatedInput h v (mixedReplica j) = v j := rfl

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

def mixedChoiceAssignmentEquiv (s n : ℕ) :
    (Fin (mixedRepeatedCoordinates s).length → Fin (n + 1)) ≃ (Fin s → Fin (n + 1)) where
  toFun v j := v (Fin.cast (mixedRepeatedCoordinates_length s).symm j)
  invFun v j := v (Fin.cast (mixedRepeatedCoordinates_length s) j)
  left_inv v := by funext j; rfl
  right_inv v := by funext j; rfl

def mixedChoiceSample {s n : ℕ} (h : ℤ) (y : Fin (n + 1) → ℤ)
    (j : Fin (n + 1) × MixedReplicatedIndex s) : ℤ :=
  correlationInput h (y j.1) j.2.1

theorem mixedChoiceSample_replica {s n : ℕ} (h : ℤ) (y : Fin (n + 1) → ℤ)
    (a : Fin (n + 1)) (j : Fin s) : mixedChoiceSample h y (a, mixedReplica j) = y a := rfl

theorem mixedChoiceSample_leaf {s n : ℕ} (h : ℤ) (y : Fin (n + 1) → ℤ)
    (v : Fin (mixedRepeatedCoordinates s).length → Fin (n + 1)) :
    finiteChoiceLeafInput (mixedRepeatedCoordinates s) v (mixedChoiceSample h y) =
      mixedReplicatedInput h (fun j => y (mixedChoiceAssignmentEquiv s n v j)) := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rw [mixedReplicatedInput_head]
    have hnot : mixedHead s ∉ mixedRepeatedCoordinates s := by
      simp [mem_mixedRepeatedCoordinates, mixedHead]
    rw [finiteChoiceLeafInput_of_not_mem _ v _ _ hnot]
    rfl
  · rw [mixedReplicatedInput_replica]
    let k : Fin (mixedRepeatedCoordinates s).length := Fin.cast (mixedRepeatedCoordinates_length s).symm i
    have H := finiteChoiceLeafInput_get (mixedRepeatedCoordinates s)
      (mixedRepeatedCoordinates_nodup s) v (mixedChoiceSample h y) k
    rw [mixedRepeatedCoordinates_get] at H
    have hk : Fin.cast (mixedRepeatedCoordinates_length s) k = i := rfl
    rw [hk, mixedChoiceSample_replica] at H
    exact H

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

def mixedPermutationFamily {s : ℕ} (e : Equiv.Perm (Fin s)) :
    ReplicatedPermutation (mixedCorrelationDegree s) :=
  Fin.cases (motive := fun b : Fin 2 => Equiv.Perm (Fin (mixedCorrelationDegree s b)))
    (Equiv.refl _) (fun _ => e)

theorem mixedPermutation_head {s : ℕ} (e : Equiv.Perm (Fin s)) :
    replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e) (mixedHead s) =
      mixedHead s := rfl

theorem mixedPermutation_replica {s : ℕ} (e : Equiv.Perm (Fin s)) (j : Fin s) :
    replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e) (mixedReplica j) =
      mixedReplica (e j) := rfl

theorem mixedPermutation_symm_head {s : ℕ} (e : Equiv.Perm (Fin s)) :
    (replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm (mixedHead s) =
      mixedHead s := by
  have H := (replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm_apply_apply
    (mixedHead s)
  simpa only [mixedPermutation_head] using H

theorem mixedPermutation_symm_replica {s : ℕ} (e : Equiv.Perm (Fin s)) (j : Fin s) :
    (replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm (mixedReplica j) =
      mixedReplica (e.symm j) := by
  have H := (replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm_apply_apply
    (mixedReplica (e.symm j))
  simpa only [mixedPermutation_replica, Equiv.apply_symm_apply] using H

theorem mixedReplicatedInput_permuted {s : ℕ} {α : Type*} (e : Equiv.Perm (Fin s))
    (h : α) (v : Fin s → α) :
    (fun j => mixedReplicatedInput h v
      ((replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm j)) =
      mixedReplicatedInput h (fun i => v (e.symm i)) := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rw [mixedPermutation_symm_head, mixedReplicatedInput_head, mixedReplicatedInput_head]
  · rw [mixedPermutation_symm_replica, mixedReplicatedInput_replica, mixedReplicatedInput_replica]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def mixedPermutationProduct {s : ℕ} {I : Type*}
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ)
    (a : Equiv.Perm (Fin s) → I) (x : Fin (s + 1) → ℤ) : ℂ :=
  ∏ e, f (a e) (mixedReplicatedInput (x 0) (fun j => x j.succ))

noncomputable def mixedMissingProduct {s : ℕ} {I : Type*}
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ)
    (a : MissingAssignment s → I) (x : Fin (s + 1) → ℤ) : ℂ := by
  classical
  exact ∏ v, f (a v) (mixedReplicatedInput (x 0) (fun j => x (v.val j).succ))

noncomputable def mixedAssignmentPartitionVector {s : ℕ} {I : Type*}
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ)
    (a : Equiv.Perm (Fin s) ⊕ MissingAssignment s → I) (x : Fin (s + 1) → ℤ) : ℂ :=
  mixedPermutationProduct f (fun e => a (Sum.inl e)) x *
    mixedMissingProduct f (fun v => a (Sum.inr v)) x

theorem mixedAssignmentPartitionVector_unit {s : ℕ} {I : Type*} [Fintype I]
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ) (hf : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1)
    (x : Fin (s + 1) → ℤ) :
    ∑ a, ‖mixedAssignmentPartitionVector f a x‖ ^ 2 = 1 := by
  classical
  let F (r : Equiv.Perm (Fin s) ⊕ MissingAssignment s) (i : I) :=
    match r with
    | Sum.inl _ => f i (mixedReplicatedInput (x 0) (fun j => x j.succ))
    | Sum.inr v => f i (mixedReplicatedInput (x 0) (fun j => x (v.val j).succ))
  have hF : ∀ r, ∑ i, ‖F r i‖ ^ 2 = 1 := by
    intro r
    cases r <;> exact hf _
  simpa only [mixedAssignmentPartitionVector, mixedPermutationProduct, mixedMissingProduct,
    Fintype.prod_sum_type, F] using finite_product_unit_vector F hF

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalCyclicDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def smoothedSecondDifference (N : ℕ) (δ : ℝ≥0)
    (u v : (Fin 2 → ℤ) → ℂ) (k : ℤ) (x : Fin 2 → ℤ) : ℂ :=
  (1 - (smoothCyclicCarry N δ ![k, x 1] : ℂ)) * integerSecondDifference u v k x +
    (smoothCyclicCarry N δ ![k, x 1] : ℂ) * integerSecondDifference u v (k - N) x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeRankZeroNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (hD : D.filtration.layer (s + 1) = ⊥)

noncomputable def dropTopMap : (D.dropTop hD).Space → D.Space :=
  cosetMap (D.dropTop hD).realLattice D.realLattice
    (realificationMap (hnil := (D.dropTop hD).filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L))
    (realificationMap_subgroup (LieHom.id : L →ₗ⁅ℚ⁆ L) (D.dropTop hD).lattice D.lattice
      (D.dropTop_lattice_back hD))

theorem dropTopMap_mk (x : (D.dropTop hD).RealGroup) :
    D.dropTopMap hD (QuotientGroup.mk x) =
      QuotientGroup.mk (changeStep (D.dropTop hD).filtration.realification.lowerCentralSeries_eq_bot
        D.filtration.realification.lowerCentralSeries_eq_bot x) := by
  change QuotientGroup.mk (realificationMap
    (hnil := (D.dropTop hD).filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L) x) = _
  rw [realificationMap_id_eq_changeStep]

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem dropTopMap_lipschitz :
    letI := (D.dropTop hD).metricSpace
    letI := D.metricSpace
    LipschitzWith 1 (D.dropTopMap hD) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := (D.dropTop hD).filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := (D.dropTop hD).filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hLip : LipschitzWith 1
      (realificationMap (hnil := (D.dropTop hD).filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
    rw [realificationMap_id_eq_changeStep]
    exact lipschitz_changeStep (D.basis.baseChange ℝ) _ _
  exact lipschitz_cosetMap (D.dropTop hD).realLattice D.realLattice
    (D.dropTop hD).realLattice_closed_discrete.1 D.realLattice_closed_discrete.1 _ _ hLip

end Metric

noncomputable def dropTopRealOrbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) :
    (D.dropTop hD).filtration.realification.PolynomialOrbit w :=
  NilpotentLieFiltration.polynomialOrbitOfLog g.log g.adapted

theorem dropTopMap_orbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    D.dropTopMap hD (QuotientGroup.mk
      ((D.dropTop hD).filtration.realification.polynomialOrbitEval w x (D.dropTopRealOrbit hD g))) =
      QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g) := by
  rw [D.dropTopMap_mk]
  rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L (s + 1) d} {w : σ → ℕ}

noncomputable def dropTop (T : D.Niltest w) (hD : D.filtration.layer (s + 1) = ⊥) :
    (D.dropTop hD).Niltest w where
  orbit := D.dropTopRealOrbit hD T.orbit
  observable := T.observable ∘ D.dropTopMap hD
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le _ := T.norm_le _
  lipschitz := by
    let := D.metricSpace
    let := (D.dropTop hD).metricSpace
    simpa only [mul_one] using T.lipschitz.comp (D.dropTopMap_lipschitz hD)

theorem dropTop_eval (T : D.Niltest w) (hD : D.filtration.layer (s + 1) = ⊥) (x : σ → ℤ) :
    (T.dropTop hD).eval x = T.eval x :=
  congrArg T.observable (D.dropTopMap_orbit hD T.orbit x)

theorem dropTop_complexity (T : D.Niltest w) (hD : D.filtration.layer (s + 1) = ⊥)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.dropTop hD).ComplexityLE p :=
  ⟨D.dropTop_geometry hD hT.1, hT.2⟩

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.NativeDegreeRankFamily

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily (s + 1) 0 A p)

theorem rankZero_top_eq_bot : W.model.filtration.layer (s + 1) = ⊥ := by
  rw [← W.rank.associated]
  exact W.rank.filtration.rank_zero_top_eq_bot

end Erdos3.NativeDegreeRankFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankSparseFamilies
namespace OAI

section

namespace Erdos3

theorem exists_rank_sparse_family
    {ι κ σ : Type*} [Fintype ι] [Fintype κ] {N : ℕ}
    (S : Finset (ZMod N)) (h₀ : ZMod N) (hh₀ : h₀ ∈ S)
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (v : κ → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p) (hfour : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ p)
    (hcols : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (2 * (p + ((p + 2) ^ 3 + (p + 2) ^ 36))) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (β : ZMod N → ι → ℝ) (a b c d : ZMod N) (M : ℝ),
        2 * M ≤ Real.exp p →
        (∀ h ∈ S, ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
          ‖E‖ ≤ M / monomialScale T α ∧ Q ∈ realDenominatorGrid l ∧
          rankCoordinateTuple β (b - h, b, a) - E - Q ∈ realFourCoordinateSpan J) →
        (∀ h ∈ S, ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
          ‖E‖ ≤ M / monomialScale T α ∧ Q ∈ realDenominatorGrid l ∧
          rankCoordinateTuple β (c - d, h + (c - d), c) - E - Q ∈ realFourCoordinateSpan J) →
        ∀ h ∈ S, ∃ e₁₂ q₁₂ e₁₃ q₁₃ : ι → ℝ,
          ‖e₁₂‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) / monomialScale T α ∧
          ‖e₁₃‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) / monomialScale T α ∧
          q₁₂ ∈ realDenominatorGrid m ∧ q₁₃ ∈ realDenominatorGrid m ∧
          β h - β h₀ - e₁₂ - q₁₂ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 2}) ∧
          β h - β h₀ - e₁₃ - q₁₃ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 3}) := by
  have hselected (K : Finset (Fin 4)) : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (card_selected_four_le K)).trans hfour
  obtain ⟨m₁₂, hm₁₂, hmp₁₂, hlm₁₂, hsolve₁₂⟩ :=
    exists_anchored_sparse_family (η := S) J {1, 2} v hv hH hl hvH hp hfour
      (hselected _) hcols hHp hlp T hT
  obtain ⟨m₁₃, hm₁₃, hmp₁₃, _, hsolve₁₃⟩ :=
    exists_anchored_sparse_family (η := S) J {1, 3} v hv hH hl hvH hp hfour
      (hselected _) hcols hHp hlp T hT
  refine ⟨m₁₂ * m₁₃, Nat.mul_pos hm₁₂ hm₁₃, ?_,
    hlm₁₂.trans (dvd_mul_right m₁₂ m₁₃), ?_⟩
  · rw [Nat.cast_mul]
    calc
      (m₁₂ : ℝ) * m₁₃ ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) *
          Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) :=
        mul_le_mul hmp₁₂ hmp₁₃ (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · intro α hα β a b c d M hM hcorrect₁₂ hcorrect₁₃ h hh
    obtain ⟨e₁₂, q₁₂, he₁₂, hq₁₂, hrem₁₂⟩ := hsolve₁₂ α hα
      (fun h : S => rankCoordinateTuple β (b - h, b, a)) (fun h : S => β h)
      ⟨h₀, hh₀⟩ M hM (fun h i => rankCoordinateTuple_first12 β a b h i)
      (fun h j => rankCoordinateTuple_fixed12 β a b h h₀ j)
      (fun h => hcorrect₁₂ h h.property) ⟨h, hh⟩
    obtain ⟨e₁₃, q₁₃, he₁₃, hq₁₃, hrem₁₃⟩ := hsolve₁₃ α hα
      (fun h : S => rankCoordinateTuple β (c - d, h + (c - d), c)) (fun h : S => β h)
      ⟨h₀, hh₀⟩ M hM (fun h i => rankCoordinateTuple_first13 β c d h i)
      (fun h j => rankCoordinateTuple_fixed13 β c d h h₀ j)
      (fun h => hcorrect₁₃ h h.property) ⟨h, hh⟩
    exact ⟨e₁₂, q₁₂, e₁₃, q₁₃, he₁₂, he₁₃,
      realDenominatorGrid_subset_of_dvd hm₁₂ (dvd_mul_right m₁₂ m₁₃) hq₁₂,
      realDenominatorGrid_subset_of_dvd hm₁₃ (dvd_mul_left m₁₃ m₁₂) hq₁₃, hrem₁₂, hrem₁₃⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMixedReflectionBridge
namespace OAI

section

namespace Erdos3

theorem mixedSlotInput_update {n : ℕ} {α : Type*} (h t u : α) (v : Fin n → α) :
    Function.update (mixedSlotInput h t v) (mixedReplica 0) u = mixedSlotInput h u v := by
  classical
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · have hne : mixedHead (n + 1) ≠ mixedReplica (0 : Fin (n + 1)) := by
      intro heq
      have hf := congrArg (fun a : MixedReplicatedIndex (n + 1) => a.1) heq
      norm_num [mixedHead, mixedReplica] at hf
    simp only [Function.update_of_ne hne, mixedSlotInput, mixedReplicatedInput_head]
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Function.update_self, mixedSlotInput, mixedReplicatedInput_replica, Fin.cons_zero]
    · have hne : mixedReplica i.succ ≠ mixedReplica (0 : Fin (n + 1)) :=
        fun heq => Fin.succ_ne_zero i (mixedReplica_injective (n + 1) heq)
      simp only [Function.update_of_ne hne, mixedSlotInput, mixedReplicatedInput_replica, Fin.cons_succ]

def mixedReflectionLinear (n : ℕ) (j : Option (MixedReplicatedIndex (n + 1))) :
    (Fin (n + 2) → ℤ) →+ ℤ :=
  let ev (i : Fin (n + 2)) : (Fin (n + 2) → ℤ) →+ ℤ :=
    ⟨⟨fun x => x i, rfl⟩, fun _ _ => rfl⟩
  match j with
  | none => ev 1
  | some a => mixedSlotInput (ev 0) (-ev 0 - ev 1) (fun i => ev i.succ.succ) a

def mixedReflectionOffset (n : ℕ) (c : ℤ) : Option (MixedReplicatedIndex (n + 1)) → ℤ
  | none => 0
  | some j => mixedSlotInput 0 c (fun _ : Fin n => 0) j

def mixedReflectionAffineInput (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ)
    (j : Option (MixedReplicatedIndex (n + 1))) : ℤ :=
  mixedReflectionOffset n c j + mixedReflectionLinear n j x

theorem mixedReflectionAffineInput_none (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ) :
    mixedReflectionAffineInput n c x none = x 1 := by
  simp [mixedReflectionAffineInput, mixedReflectionOffset, mixedReflectionLinear]

theorem mixedReflectionAffineInput_some (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ)
    (j : MixedReplicatedIndex (n + 1)) :
    mixedReflectionAffineInput n c x (some j) =
      mixedSlotInput (x 0) (c - x 0 - x 1) (fun i => x i.succ.succ) j := by
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · simp [mixedReflectionAffineInput, mixedReflectionOffset, mixedReflectionLinear,
      mixedSlotInput, mixedReplicatedInput_head]
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp [mixedReflectionAffineInput, mixedReflectionOffset, mixedReflectionLinear,
        mixedSlotInput, mixedReplicatedInput_replica, sub_eq_add_neg, add_assoc]
    · simp [mixedReflectionAffineInput, mixedReflectionOffset, mixedReflectionLinear,
        mixedSlotInput, mixedReplicatedInput_replica]

theorem mixedReflectionInput_sum (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ) :
    coordinateAdditionInputs (mixedReplica 0) (mixedReflectionAffineInput n c x) 0 =
      mixedSlotInput (x 0) (c - x 0) (fun i => x i.succ.succ) := by
  rw [coordinateAdditionInputs_sum]
  simp only [mixedReflectionAffineInput_some, mixedReflectionAffineInput_none]
  rw [show mixedSlotInput (x 0) (c - x 0 - x 1) (fun i => x i.succ.succ) (mixedReplica 0) =
    c - x 0 - x 1 from rfl, sub_add_cancel, mixedSlotInput_update]

theorem mixedReflectionInput_left (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ) :
    coordinateAdditionInputs (mixedReplica 0) (mixedReflectionAffineInput n c x) 1 =
      mixedSlotInput (x 0) (c - x 0 - x 1) (fun i => x i.succ.succ) := by
  funext j
  exact mixedReflectionAffineInput_some n c x j

theorem mixedReflectionInput_right (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ) :
    coordinateAdditionInputs (mixedReplica 0) (mixedReflectionAffineInput n c x) 2 =
      mixedSlotInput (x 0) (x 1) (fun i => x i.succ.succ) := by
  rw [coordinateAdditionInputs_right]
  simp only [mixedReflectionAffineInput_some, mixedReflectionAffineInput_none, mixedSlotInput_update]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeMixedCoordinateSlices
namespace OAI

section

namespace Erdos3

def mixedCoordinateIndex (n : ℕ) : Fin (n + 2) → MixedReplicatedIndex (n + 1) :=
  Fin.cases (mixedHead (n + 1)) (fun j => mixedReplica j)

theorem mixedInputCoordinate_index (n : ℕ) (k : Fin (n + 2)) :
    mixedInputCoordinate n (mixedCoordinateIndex n k) = k := by
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k <;> rfl

theorem mixedInputCoordinate_eval (n : ℕ) {α : Type*} (x : Fin (n + 2) → α) :
    (fun j => x (mixedInputCoordinate n j)) =
      mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ) := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨k, rfl⟩
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k <;> rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3

def mixedSampledInput {d : ℕ} (π : Fin (d + 3) → Fin 2) (x : Fin 2 → ℤ) :
    MixedReplicatedIndex (d + 2) → ℤ :=
  mixedReplicatedInput (x (π 0)) (fun j => x (π j.succ))

theorem mixedSampledInput_slots {d : ℕ} (π : Fin (d + 3) → Fin 2) (x : Fin 2 → ℤ) :
    mixedSampledInput π x =
      mixedSlotInput (x (π 0)) (x (π 1)) (fun j => x (π j.succ.succ)) := by
  unfold mixedSampledInput mixedSlotInput
  congr 1
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem mixedSampledInput_coordinates {d : ℕ} (π : Fin (d + 3) → Fin 2) (x : Fin 2 → ℤ) :
    (fun j => x (π (mixedInputCoordinate (d + 1) j))) = mixedSampledInput π x := by
  exact (mixedInputCoordinate_eval (d + 1) (fun k => x (π k))).trans
    (mixedSampledInput_slots π x).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedCoordinateIndex_coordinate (n : ℕ) (j : MixedReplicatedIndex (n + 1)) :
    mixedCoordinateIndex n (mixedInputCoordinate n j) = j := by
  rcases mixedReplicated_cases j with rfl | ⟨k, rfl⟩
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k <;> rfl

def mixedAllCoordinates (s : ℕ) : List (MixedReplicatedIndex (s + 2)) :=
  List.ofFn (mixedCoordinateIndex (s + 1))

theorem mixedAllCoordinates_length (s : ℕ) : (mixedAllCoordinates s).length = s + 3 := by
  simp only [mixedAllCoordinates, List.length_ofFn]

theorem mixedAllCoordinates_nodup (s : ℕ) : (mixedAllCoordinates s).Nodup := by
  apply List.nodup_ofFn.mpr
  exact Function.LeftInverse.injective (mixedInputCoordinate_index (s + 1))

theorem mixedAllCoordinates_get (s : ℕ) (j : Fin (mixedAllCoordinates s).length) :
    (mixedAllCoordinates s).get j =
      mixedCoordinateIndex (s + 1) (Fin.cast (mixedAllCoordinates_length s) j) := by
  exact List.get_ofFn (mixedCoordinateIndex (s + 1)) j

theorem mem_mixedAllCoordinates (s : ℕ) (j : MixedReplicatedIndex (s + 2)) :
    j ∈ mixedAllCoordinates s := by
  apply List.mem_ofFn.mpr
  exact ⟨mixedInputCoordinate (s + 1) j, mixedCoordinateIndex_coordinate (s + 1) j⟩

def mixedCornerAssignmentEquiv (s : ℕ) :
    (Fin (mixedAllCoordinates s).length → Fin 2) ≃ (Fin (s + 3) → Fin 2) where
  toFun v j := v (Fin.cast (mixedAllCoordinates_length s).symm j)
  invFun v j := v (Fin.cast (mixedAllCoordinates_length s) j)
  left_inv v := by funext j; rfl
  right_inv v := by funext j; rfl

def mixedDiagonalCorner {s : ℕ} (v : Fin (s + 3) → Fin 2) (x : Fin 2 → ℤ) :
    MixedReplicatedIndex (s + 2) → ℤ := mixedSampledInput (fun k => (v k).rev) x

theorem mixedDiagonalCorner_zero {s : ℕ} (x : Fin 2 → ℤ) :
    mixedDiagonalCorner (fun _ : Fin (s + 3) => 0) x = fun _ => x 1 := by
  rw [mixedDiagonalCorner, ← mixedSampledInput_coordinates]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootLosses
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixedCornerSample_input {s : ℕ} (v : Fin (s + 3) → Fin 2) (x : Fin 2 → ℤ) :
    mixedDiagonalCorner v x = mixedSampledInput (mixedCornerSample v) x := rfl

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

theorem mixedWeightSample_first_input (s : ℕ) (x : Fin 2 → ℤ) :
    mixedSampledInput (mixedWeightSample s 0) x =
      fun j : MixedReplicatedIndex (s + 2) => x j.1 := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rfl
  · change x (if i.succ.val < (0 : Fin (s + 3)).val + 1 then 0 else 1) = x 1
    rw [if_neg (by simp only [Fin.val_succ, Fin.val_zero]; omega)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedWeightSample_last_input (s : ℕ) (x : Fin 2 → ℤ) :
    mixedSampledInput (mixedWeightSample s (Fin.last (s + 1)).succ) x = fun _ => x 0 := by
  have hs : mixedWeightSample s (Fin.last (s + 1)).succ = fun _ => (0 : Fin 2) := by
    funext j
    unfold mixedWeightSample
    apply if_pos
    simpa only [Fin.val_succ, Fin.val_last] using j.isLt
  rw [hs, ← mixedSampledInput_coordinates]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShiftStructure
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

omit [Fintype σ] in
theorem polynomialShift_bracket (d : ℕ) (x y : F.PolynomialShiftAlgebra d) :
    ⁅x, y⁆ = ⟨⁅x.left, y.left⁆ + F.adaptedDirectionalDerivative x.right y.left -
      F.adaptedDirectionalDerivative y.right x.left, 0⟩ := rfl

omit [Fintype σ] in
theorem polynomialShift_direction_bracket (d : ℕ) (h : RationalTorus.Algebra d)
    (p : F.adaptedLieSubalgebra (fun _ : Fin d => 1)) :
    ⁅(⟨0, h⟩ : F.PolynomialShiftAlgebra d), (⟨p, 0⟩ : F.PolynomialShiftAlgebra d)⁆ =
      ⟨F.adaptedDirectionalDerivative h p, 0⟩ := by
  rw [F.polynomialShift_bracket]
  simp only [zero_lie, zero_add, map_zero, sub_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s)

include b hF hω in
theorem polynomialShift_finiteDimensional (d : ℕ) :
    FiniteDimensional ℚ (F.PolynomialShiftAlgebra d) := by
  let w : Fin d → ℕ := fun _ => 1
  let : Finite (AdaptedBasisIndex w ω) := adaptedBasisIndex_finite w ω s (by simp [w]) hω
  let : FiniteDimensional ℚ (F.adaptedLieSubalgebra w) :=
    (F.adaptedMonomialBasis b ω hF w).finiteDimensional_of_finite
  let : FiniteDimensional ℚ (RationalTorus.Algebra d) :=
    (RationalTorus.basis d).finiteDimensional_of_finite
  exact FiniteDimensional.of_injective
    (LieAlgebra.SemiDirectSum.toProdl (F.adaptedShiftAction d)).toLinearMap
    (LieAlgebra.SemiDirectSum.toProdl (F.adaptedShiftAction d)).injective

include b hF hω in
theorem polynomialShift_finrank_le (d : ℕ) :
    finrank ℚ (F.PolynomialShiftAlgebra d) ≤
      Fintype.card ι * (s + 1) * (d + 1) ^ s + d := by
  let w : Fin d → ℕ := fun _ => 1
  let : Fintype (AdaptedBasisIndex w ω) :=
    adaptedBasisIndexFintype w ω s (by simp [w]) hω
  let : FiniteDimensional ℚ (F.adaptedLieSubalgebra w) :=
    (F.adaptedMonomialBasis b ω hF w).finiteDimensional_of_finite
  let : FiniteDimensional ℚ (RationalTorus.Algebra d) :=
    (RationalTorus.basis d).finiteDimensional_of_finite
  rw [(LieAlgebra.SemiDirectSum.toProdl (F.adaptedShiftAction d)).finrank_eq,
    Module.finrank_prod, finrank_eq_card_basis (F.adaptedMonomialBasis b ω hF w),
    finrank_eq_card_basis (RationalTorus.basis d), Fintype.card_fin]
  exact Nat.add_le_add_right
    (by simpa only [Fintype.card_fin] using adaptedBasisIndex_card_le w ω s (by simp [w]) hω) d

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def polynomialShiftBasis (t : ℕ) :
    Basis (AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) ℚ (F.PolynomialShiftAlgebra t) :=
  ((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod (RationalTorus.basis t)).map
    (LieAlgebra.SemiDirectSum.toProdl (F.adaptedShiftAction t)).symm

theorem polynomialShiftBasis_repr_inl (t : ℕ) (x : F.PolynomialShiftAlgebra t)
    (z : AdaptedBasisIndex (fun _ : Fin t => 1) ω) :
    (F.polynomialShiftBasis b ω hF t).repr x (.inl z) =
      b.repr (coefficients x.left.val z.val.1) z.val.2 := by
  change (F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).repr x.left z = _
  exact F.adaptedMonomialBasis_repr b ω hF (fun _ : Fin t => 1) x.left z

theorem polynomialShiftBasis_repr_inr (t : ℕ) (x : F.PolynomialShiftAlgebra t) (i : Fin t) :
    (F.polynomialShiftBasis b ω hF t).repr x (.inr i) = x.right i := by
  change (RationalTorus.basis t).repr x.right i = x.right i
  rfl

theorem polynomialShiftBasis_inl_left (t : ℕ)
    (z : AdaptedBasisIndex (fun _ : Fin t => 1) ω) :
    ((F.polynomialShiftBasis b ω hF t) (.inl z)).left =
      F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1) z := by
  change (((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod
    (RationalTorus.basis t)) (.inl z)).1 = _
  exact Basis.prod_apply_inl_fst _ _ z

theorem polynomialShiftBasis_inl_right (t : ℕ)
    (z : AdaptedBasisIndex (fun _ : Fin t => 1) ω) :
    ((F.polynomialShiftBasis b ω hF t) (.inl z)).right = 0 := by
  change (((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod
    (RationalTorus.basis t)) (.inl z)).2 = _
  exact Basis.prod_apply_inl_snd _ _ z

theorem polynomialShiftBasis_inr_left (t : ℕ) (i : Fin t) :
    ((F.polynomialShiftBasis b ω hF t) (.inr i)).left = 0 := by
  change (((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod
    (RationalTorus.basis t)) (.inr i)).1 = _
  exact Basis.prod_apply_inr_fst _ _ i

theorem polynomialShiftBasis_inr_right (t : ℕ) (i : Fin t) :
    ((F.polynomialShiftBasis b ω hF t) (.inr i)).right = RationalTorus.basis t i := by
  change (((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod
    (RationalTorus.basis t)) (.inr i)).2 = _
  exact Basis.prod_apply_inr_snd _ _ i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

namespace VectorPolynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficients_torusDerivative {t : ℕ} (i : Fin t)
    (p : VectorPolynomial (Fin t) ℚ L) (α : Fin t →₀ ℕ) :
    coefficients (directionalDerivative (RationalTorus.basis t i) p) α =
      (α i + 1 : ℚ) • coefficients p (α + Finsupp.single i 1) := by
  have hdir (j : Fin t) : (RationalTorus.basis t i) j = if i = j then 1 else 0 := by
    rw [← RationalTorus.basis_repr t (RationalTorus.basis t i) j,
      (RationalTorus.basis t).repr_self, Finsupp.single_apply]
  change coefficients (directionalDerivative (fun j : Fin t => (RationalTorus.basis t i) j) p) α = _
  rw [coefficients_directionalDerivative]
  simp_rw [hdir]
  simp

theorem torusDerivative_monomial_height {ι : Type*} (b : Basis ι ℚ L)
    {s t : ℕ} (β : Fin t →₀ ℕ) (hβ : Finsupp.weight (fun _ : Fin t => 1) β ≤ s)
    (i : Fin t) (j : ι) (α : Fin t →₀ ℕ) (k : ι) :
    RationalHeightLE (b.repr (coefficients
      (directionalDerivative (RationalTorus.basis t i) (monomial (R := ℚ) β (b j))) α) k) (s + 1) := by
  classical
  rw [coefficients_torusDerivative, coefficients_monomial]
  by_cases he : β = α + Finsupp.single i 1
  · rw [he, Finsupp.single_eq_same, map_smul, Finsupp.smul_apply, b.repr_self]
    have hi := (Finsupp.le_weight (fun _ : Fin t => 1) (s := i) (by norm_num) β).trans hβ
    rw [he, Finsupp.add_apply, Finsupp.single_eq_same] at hi
    have hn : RationalHeightLE ((α i + 1 : ℕ) : ℚ) (s + 1) := by
      constructor
      · simpa only [Rat.num_natCast, Int.natAbs_natCast] using hi.trans (Nat.le_succ s)
      · simp only [Rat.den_natCast]
        omega
    by_cases hj : j = k
    · subst k
      simpa only [Finsupp.single_eq_same, smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] using hn
    · rw [Finsupp.single_eq_of_ne (Ne.symm hj), smul_zero]
      exact rationalHeightLE_zero (by omega)
  · rw [Finsupp.single_eq_of_ne (Ne.symm he), smul_zero, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (by omega)

end VectorPolynomial

namespace NilpotentLieFiltration

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem polynomialShiftBasis_inl (t : ℕ) (i : AdaptedBasisIndex (fun _ : Fin t => 1) ω) :
    F.polynomialShiftBasis b ω hF t (.inl i) =
      LieAlgebra.SemiDirectSum.inl (F.adaptedShiftAction t)
        (F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1) i) := by
  apply LieAlgebra.SemiDirectSum.ext
  · exact F.polynomialShiftBasis_inl_left b ω hF t i
  · exact F.polynomialShiftBasis_inl_right b ω hF t i

theorem polynomialShiftBasis_inr (t : ℕ) (i : Fin t) :
    F.polynomialShiftBasis b ω hF t (.inr i) =
      LieAlgebra.SemiDirectSum.inr (F.adaptedShiftAction t) (RationalTorus.basis t i) := by
  apply LieAlgebra.SemiDirectSum.ext
  · exact F.polynomialShiftBasis_inr_left b ω hF t i
  · exact F.polynomialShiftBasis_inr_right b ω hF t i

theorem polynomialShiftBasis_mixed_height (hω : ∀ i, ω i ≤ s) (t : ℕ) (i : Fin t)
    (j : AdaptedBasisIndex (fun _ : Fin t => 1) ω)
    (k : AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) :
    RationalHeightLE ((F.polynomialShiftBasis b ω hF t).repr
      ⁅F.polynomialShiftBasis b ω hF t (.inr i), F.polynomialShiftBasis b ω hF t (.inl j)⁆ k) (s + 1) := by
  rw [F.polynomialShiftBasis_inr, F.polynomialShiftBasis_inl]
  rw [LieAlgebra.SemiDirectSum.inr_eq_mk, LieAlgebra.SemiDirectSum.inl_eq_mk,
    F.polynomialShift_direction_bracket]
  rcases k with k | k
  · rw [F.polynomialShiftBasis_repr_inl]
    change RationalHeightLE (b.repr (coefficients
      (directionalDerivative (RationalTorus.basis t i)
        (F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1) j).val) k.val.1) k.val.2) _
    rw [F.adaptedMonomialBasis_coe]
    exact torusDerivative_monomial_height b j.val.1 (j.property.trans (hω j.val.2)) i j.val.2 k.val.1 k.val.2
  · rw [F.polynomialShiftBasis_repr_inr]
    exact rationalHeightLE_zero (by omega)

theorem polynomialShiftBasis_structure_height (hω : ∀ i, ω i ≤ s) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) (t : ℕ)
    (i j k : AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) :
    RationalHeightLE (lieStructureConstants (F.polynomialShiftBasis b ω hF t) i j k) (max H (s + 1)) := by
  change RationalHeightLE ((F.polynomialShiftBasis b ω hF t).repr
    ⁅F.polynomialShiftBasis b ω hF t i, F.polynomialShiftBasis b ω hF t j⁆ k) _
  rcases i with i | i <;> rcases j with j | j
  · rw [F.polynomialShiftBasis_inl, F.polynomialShiftBasis_inl,
      ← (LieAlgebra.SemiDirectSum.inl (F.adaptedShiftAction t)).map_lie]
    rcases k with k | k
    · rw [F.polynomialShiftBasis_repr_inl]
      simp only [LieAlgebra.SemiDirectSum.inl_eq_mk]
      simpa only [F.adaptedMonomialBasis_repr] using
        (F.adaptedMonomialBasis_bracket_height b ω hF (fun _ : Fin t => 1) hH hc i j k).mono
          (Nat.le_max_left H (s + 1))
    · rw [F.polynomialShiftBasis_repr_inr]
      exact rationalHeightLE_zero (hH.trans (Nat.le_max_left _ _))
  · rw [← lie_skew, map_neg, Finsupp.neg_apply]
    exact ((F.polynomialShiftBasis_mixed_height b ω hF hω t j i k).mono (Nat.le_max_right _ _)).neg
  · exact (F.polynomialShiftBasis_mixed_height b ω hF hω t i j k).mono (Nat.le_max_right _ _)
  · rw [F.polynomialShiftBasis_inr, F.polynomialShiftBasis_inr,
      ← (LieAlgebra.SemiDirectSum.inr (F.adaptedShiftAction t)).map_lie,
      RationalTorus.lie_eq_zero, map_zero, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (hH.trans (Nat.le_max_left _ _))

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NormalizedMarkedPhase
namespace OAI

section

namespace Erdos3

theorem rationalLogHeight_nat_inv_mul_exp_bound (m : ℕ) (hm : 0 < m)
    {p : ℝ} (hp : 0 ≤ p) (hmp : (m : ℝ) ≤ Real.exp p) {x : ℚ}
    (hx : rationalLogHeight x ≤ p) :
    rationalLogHeight ((m : ℚ)⁻¹ * x) ≤ 2 * p + 1 := by
  have hmheight : RationalHeightLE (m : ℚ) m := by
    simp only [RationalHeightLE, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast]
    exact ⟨le_rfl, hm⟩
  have hinv := hmheight.inv (by exact_mod_cast hm.ne')
  apply rationalLogHeight_le_of_height (hinv.mul (rationalHeightLE_ceil_exp hx))
  rw [Nat.cast_mul]
  calc
    (m : ℝ) * ⌈Real.exp p⌉₊ ≤ Real.exp p * Real.exp (p + 1) :=
      mul_le_mul hmp (ceil_exp_le_exp_add_one hp) (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (2 * p + 1) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateFiber
namespace OAI

section

namespace Erdos3.NativeVectorCorrelation

theorem exists_fixed_coordinate {G I : Type*} [Fintype I]
    {degree N : ℕ} [NeZero N] {p q : ℝ}
    (H : Finset G) (hH : H.Nonempty) (f : G → I → ZMod N → ℂ)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp q)
    (hcorr : ∀ h ∈ H, Nonempty (NativeVectorCorrelation degree N p (f h))) :
    ∃ i : I, ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
      Real.exp (-q) * H.card ≤ (H'.card : ℝ) ∧
      ∀ h ∈ H', Nonempty (NativeVectorCorrelation degree N p (fun _ : Unit => f h i)) := by
  classical
  let W (h : {h // h ∈ H}) := Classical.choice (hcorr h.val h.property)
  obtain ⟨h₀, hh₀⟩ := hH
  let code (h : G) := if hh : h ∈ H then (W ⟨h, hh⟩).coordinate else (W ⟨h₀, hh₀⟩).coordinate
  obtain ⟨i, _, H', hsub, hH', hfixed, hdense⟩ := exists_exponential_constant_fiber
    H ⟨h₀, hh₀⟩ code Set.univ (Set.toFinite _) (fun _ _ => Set.mem_univ _)
    (by simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hI)
  refine ⟨i, H', hsub, hH', hdense, ?_⟩
  intro h hh
  let Wh := W ⟨h, hsub hh⟩
  have hi : Wh.coordinate = i := by
    simpa only [code, dif_pos (hsub hh)] using hfixed h hh
  exact ⟨{ Wh with
    coordinate := ()
    correlation := by simpa only [hi] using Wh.correlation }⟩

end Erdos3.NativeVectorCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeZeroDegreeCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeVectorCorrelation

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

theorem mean_correlation_of_degree_zero {I : Type*} {N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation 0 N p f) :
    Real.exp (-(2 * p)) ≤ ‖𝔼 x, f W.coordinate x‖ := by
  let c := W.test.observable (QuotientGroup.mk (1 : W.model.RealGroup))
  have hnorm : ‖c‖ ≤ Real.exp p := by
    have h := W.test.eval_budget W.complexity (0 : Unit → ℤ)
    rwa [RationalFilteredNilmanifold.Niltest.eval_step_zero] at h
  have heq : (𝔼 x, f W.coordinate x * star (W.test.evalCyclic N (fun _ => x))) =
      (𝔼 x, f W.coordinate x) * star c := by
    simp only [RationalFilteredNilmanifold.Niltest.evalCyclic,
      RationalFilteredNilmanifold.Niltest.eval_step_zero, ← Finset.expect_mul]
    rfl
  have h := W.correlation
  rw [heq, norm_mul, norm_star] at h
  have hbound : Real.exp (-(2 * p)) * Real.exp p ≤ ‖𝔼 x, f W.coordinate x‖ * Real.exp p := by
    rw [← Real.exp_add, show -(2 * p) + p = -p by ring]
    exact h.trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  exact le_of_mul_le_mul_right hbound (Real.exp_pos p)

end NativeVectorCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NativeMixedFourierProfiles
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def cyclicRealLinearPhase {N : ℕ} (β : ℝ) (n : ZMod N) : ℂ :=
  CircleFourier.character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle)

@[simp] theorem norm_cyclicRealLinearPhase {N : ℕ} (β : ℝ) (n : ZMod N) :
    ‖cyclicRealLinearPhase β n‖ = 1 := CircleFourier.norm_character _

theorem cyclicRealLinearPhase_unit_shift_error {N : ℕ} [NeZero N] (β : ℝ) :
    (𝔼 n : ZMod N, ‖cyclicRealLinearPhase β (n + 1) -
      CircleFourier.character (β : CircleFourier.Circle) * cyclicRealLinearPhase β n‖) ≤ 2 / N := by
  classical
  let b : ZMod N := ((N - 1 : ℕ) : ZMod N)
  have hpoint (n : ZMod N) :
      ‖cyclicRealLinearPhase β (n + 1) -
        CircleFourier.character (β : CircleFourier.Circle) * cyclicRealLinearPhase β n‖ ≤
        if n = b then 2 else 0 := by
    by_cases hn : n = b
    · rw [if_pos hn]
      calc
        _ ≤ ‖cyclicRealLinearPhase β (n + 1)‖ +
            ‖CircleFourier.character (β : CircleFourier.Circle) * cyclicRealLinearPhase β n‖ := norm_sub_le _ _
        _ = 2 := by simp only [norm_mul, norm_cyclicRealLinearPhase, CircleFourier.norm_character]; norm_num
    · rw [if_neg hn]
      have hnlt : n.val + 1 < N := by
        have hv := n.val_lt
        by_contra h
        have he : n.val = N - 1 := by omega
        apply hn
        rw [← ZMod.natCast_zmod_val n, he]
      have hval : (n + 1).val = n.val + 1 := by
        have he : n + 1 = ((n.val + 1 : ℕ) : ZMod N) := by simp
        rw [he, ZMod.val_natCast_of_lt hnlt]
      have heq : cyclicRealLinearPhase β (n + 1) =
          CircleFourier.character (β : CircleFourier.Circle) * cyclicRealLinearPhase β n := by
        simp only [cyclicRealLinearPhase, hval, Nat.cast_add, Nat.cast_one, add_mul,
          one_mul, AddCircle.coe_add, CircleFourier.character_add]
        ring
      rw [heq, sub_self, norm_zero]
  calc
    _ ≤ 𝔼 n : ZMod N, if n = b then (2 : ℝ) else 0 :=
      Finset.expect_le_expect (fun n _ => hpoint n)
    _ = 2 / N := by rw [Fintype.expect_eq_sum_div_card]; simp

theorem exists_fourier_of_real_linear_phase {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (β : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hcorr : ρ ≤ ‖𝔼 n, f n * star (cyclicRealLinearPhase β n)‖) :
    ∃ χ : AddChar (ZMod N) ℂ, ρ ^ 2 / 16 ≤ ‖finiteFourierCoeff f χ‖ :=
  exists_fourier_of_twisted_unit_shift (cyclicRealLinearPhase β) f
    (CircleFourier.character (β : CircleFourier.Circle))
    (fun n => (norm_cyclicRealLinearPhase β n).le) hf (CircleFourier.norm_character _)
    (cyclicRealLinearPhase_unit_shift_error β) hρ hρ1 hcorr

end Erdos3

end

end OAI
end


