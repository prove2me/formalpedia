-- Prove2me | Definitions.Def_OAIErdos3B063
-- name    : OAIErdos3B063
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T13:33:14.774293+00:00
-- url     : https://prove2.me/theorems/2568e5e3-e312-4751-a24b-eb624c942b29
-- title:
--   OpenAI Erdős-3 split, definitions bundle 64 of 207
-- statement:
--   Definitions bundle 64 of 207 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B062`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 64 available.
--
--   Modules: `OAI.Erdos3.EpochRecordHistory`, `OAI.Erdos3.EpochSymbolRecord.Controlled`, `OAI.Erdos3.EpochSymbolRecord.noConfusion`, `OAI.Erdos3.NativeRankRelation.CommonData.HasCommonInducedCorrelationFamily`, `OAI.Erdos3.NativeRankRelation.CommonData.HasCommonInducedCorrelationFamily.mono`, `OAI.Erdos3.NativeRankRelation.CommonData.HasCoveredInducedCorrelationFamily`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_local_induced_comparison_correlation`, `OAI.Erdos3.NativeRankRelation.CommonData.hasCommonInducedCorrelationFamily_of_model`, `OAI.Erdos3.NativeRankRelation.CommonData.induced_local_value_eq_nativeSpaceMap`, `OAI.Erdos3.NativeRankRelation.CommonData.localPhaseMarkedOrbit_induced_value`, `OAI.Erdos3.PhysicalEpochComparison.noConfusion`, `OAI.Erdos3.PhysicalEpochRecords`, `OAI.Erdos3.PhysicalEpochRecords.dimension`, `OAI.Erdos3.PhysicalEpochRecords.empty`, `OAI.Erdos3.PhysicalEpochSource.noConfusion`, `OAI.Erdos3.PositiveShiftBasis.anchoredDimension`, `OAI.Erdos3.PositiveShiftBasis.anchoredFactors`, `OAI.Erdos3.PositiveShiftBasis.anchoredLieSpace`, `OAI.Erdos3.PositiveShiftBasis.anchoredWeights`, `OAI.Erdos3.PositiveShiftBasis.mono`, `OAI.Erdos3.PositiveShiftBasis.recOn`, `OAI.Erdos3.PositiveShiftBasis.testingFamily`, `OAI.Erdos3.QuadraticMarked.Algebra`, `OAI.Erdos3.QuadraticMarked.Model`, `OAI.Erdos3.QuadraticMarked.Model.mono`, `OAI.Erdos3.QuadraticMarked.Seed`, `OAI.Erdos3.QuadraticMarked.evaluation`, `OAI.Erdos3.QuadraticMarked.filtration`, `OAI.Erdos3.QuadraticMarked.filtration_layers`, `OAI.Erdos3.QuadraticMarked.generator_height`, `OAI.Erdos3.QuadraticMarked.generator_mem`, `OAI.Erdos3.QuadraticMarked.generators`, `OAI.Erdos3.QuadraticMarked.localCharacter`, `OAI.Erdos3.QuadraticMarked.marked`, `OAI.Erdos3.QuadraticMarked.multidegree`, `OAI.Erdos3.QuadraticMarked.phase`, `OAI.Erdos3.QuadraticMarked.second_marked_span`, `OAI.Erdos3.QuadraticMarked.structure_height`, `OAI.Erdos3.QuadraticMarked.weight_pos`, `OAI.Erdos3.QuadraticMarked.weights`, `OAI.Erdos3.RationalFilteredNilmanifold.anchoredOptionFrequencyData`, `OAI.Erdos3.RationalFilteredNilmanifold.anchoredOptionObservableData`, `OAI.Erdos3.RationalFilteredNilmanifold.anchoredOptionReferenceData`, `OAI.Erdos3.additiveGraph_difference_card_hom`, `OAI.Erdos3.anchoredOptionInputs`, `OAI.Erdos3.character_relation_of_quadruple_pos`, `OAI.Erdos3.cross_correlation_fourier_energy`, `OAI.Erdos3.derivative_character_graph_energy`, `OAI.Erdos3.epochRecordIntersection`, `OAI.Erdos3.exists_cyclic_interval_fourier_smoothing`, `OAI.Erdos3.exists_cyclic_mixed_reflection`, `OAI.Erdos3.exists_inducedMarkedLipschitzBound_exp_bound`, `OAI.Erdos3.exists_inducedMarkedLogBudget_bound`, `OAI.Erdos3.exists_induced_marked_observable`, `OAI.Erdos3.exists_induced_marked_observable_explicit`, `OAI.Erdos3.exists_large_fourier_of_gowers_two`, `OAI.Erdos3.exists_large_fourier_of_mean_cross_correlation`, `OAI.Erdos3.exists_many_derivative_character_relations`, `OAI.Erdos3.exists_marked_phase_band_representatives`, `OAI.Erdos3.exists_nearby_phase_band_lift`, `OAI.Erdos3.exists_quadratic_affine_frequency_coordinates`, `OAI.Erdos3.exists_quadratic_affine_frequency_coordinates_budget`, `OAI.Erdos3.exists_quadratic_frequency_graph`, `OAI.Erdos3.exists_quadratic_frequency_small_difference`, `OAI.Erdos3.exists_remove_triple_interval`, `OAI.Erdos3.exists_unwrapped_family_reflected_correlation`, `OAI.Erdos3.exists_unwrapped_reflected_correlation`, `OAI.Erdos3.finiteFourierCoeff_convolution`, `OAI.Erdos3.finiteFourierCoeff_reflected_conjugate`, `OAI.Erdos3.gowersNorm_two_fourier`, `OAI.Erdos3.inducedMarkedLipschitzBound`, `OAI.Erdos3.inducedMarkedLogBudget`, `OAI.Erdos3.induced_marked_observable_scaled_parameter`, `OAI.Erdos3.marked_phase_correction_coordinate_norm_le`, `OAI.Erdos3.mem_tripleCarryInterval`, `OAI.Erdos3.phaseBandCoordinateConstant`, `OAI.Erdos3.phaseBandQuotientConstant`, `OAI.Erdos3.phase_band_quotient_dist_le`, `OAI.Erdos3.realMarkedParameterElement_scaled_integer_mem`, `OAI.Erdos3.sum_tripleCarry_indicator`, `OAI.Erdos3.torusPhaseLinear_eq_in_band_of_near`, `OAI.Erdos3.torusPhaseLinear_eq_of_close`, `OAI.Erdos3.torusPhaseLinear_group_lipschitz`, `OAI.Erdos3.torusPhaseLinear_group_lipschitz_exp`, `OAI.Erdos3.torusPhaseLinear_realLattice_integral`, `OAI.Erdos3.tripleCarryInterval`, `OAI.Erdos3.tripleCarryStart`, `OAI.Erdos3.tripleCarry_representative`, `OAI.Erdos3.tripleCyclicEmbed`, `OAI.Erdos3.tripleCyclicEmbed_expect_le`, `OAI.Erdos3.tripleCyclicEmbed_injective`, `OAI.Erdos3.tripleCyclicEmbed_pair_expect_le`, `OAI.Erdos3.triple_difference_val`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B197

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ShiftFailurePositiveBasis
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold

open Module CircleFourier
open scoped TensorProduct BigOperators

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module CircleFourier
open scoped TensorProduct BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

structure PositiveShiftBasis (degree N : ℕ) [NeZero N] (p : ℝ)
    (a J : ZMod N → ℝ) where
  L : Type u
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  geometry : model.GeometryComplexityLE p
  count : ℕ
  count_le_dim : count ≤ dim
  shifts : Finset (ZMod N)
  shifts_nonempty : shifts.Nonempty
  shifts_large : Real.exp (-p) * N ≤ (shifts.card : ℝ)
  frequency : ZMod N → Fin count → L →ₗ[ℚ] ℚ
  mode : ZMod N → Fin count → model.Niltest (fun _ : Unit => 1)
  test : ZMod N → model.Niltest (fun _ : Unit => 1)
  frequency_height : ∀ h ∈ shifts, ∀ j i, rationalLogHeight (frequency h j (model.basis i)) ≤ p
  mode_complexity : ∀ h ∈ shifts, ∀ j, (mode h j).ComplexityLE p
  mode_orbit : ∀ h ∈ shifts, ∀ j, (mode h j).orbit = (test h).orbit
  mode_norm : ∀ h ∈ shifts, ∀ j, (mode h j).normBound ≤ 1
  mode_vertical : ∀ h ∈ shifts, ∀ j z, z ∈ model.filtration.realification.subgroup degree → ∀ x,
    (mode h j).observable (z • x) = character
      ((realifyFunctional (frequency h j) z.coord : ℝ) : CircleFourier.Circle) * (mode h j).observable x
  mode_bias : ∀ h ∈ shifts, ∀ j, Real.exp (-p) <
    ‖𝔼 n, (mode h j).evalCyclic N (fun _ => n) * (a n : ℂ) * (J (n + h) : ℂ)‖
  independent : ∀ h ∈ shifts,
    LinearIndependent ℚ (fun j => (frequency h j).comp (model.filtration.layer degree).subtype)
  test_positive : ∀ h ∈ shifts, (test h).UnitIntervalValued
  test_complexity : ∀ h ∈ shifts, (test h).ComplexityLE p
  test_invariant : ∀ h ∈ shifts, ∀ z : model.RealGroup,
    z ∈ model.filtration.realification.subgroup degree →
    (∀ j, realifyFunctional (frequency h j) z.coord = 0) → ∀ x,
      (test h).observable (z • x) = (test h).observable x
  test_violation : ∀ h ∈ shifts, Real.exp (-p) <
    𝔼 n, a n * J (n + h) * ((test h).evalCyclic N (fun _ => n)).re

end Erdos3

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def mono {s N : ℕ} [NeZero N] {p q : ℝ} {a J : ZMod N → ℝ}
    (B : PositiveShiftBasis s N p a J) (hpq : p ≤ q) : PositiveShiftBasis s N q a J where
  L := B.L
  lie := B.lie
  algebra := B.algebra
  dim := B.dim
  topology := B.topology
  topologicalAdd := B.topologicalAdd
  continuousSMul := B.continuousSMul
  hausdorff := B.hausdorff
  model := B.model
  geometry := B.geometry.mono B.model hpq
  count := B.count
  count_le_dim := B.count_le_dim
  shifts := B.shifts
  shifts_nonempty := B.shifts_nonempty
  shifts_large := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
    (Nat.cast_nonneg N)).trans B.shifts_large
  frequency := B.frequency
  mode := B.mode
  test := B.test
  frequency_height := fun h hh j i => (B.frequency_height h hh j i).trans hpq
  mode_complexity := fun h hh j => (B.mode_complexity h hh j).mono hpq
  mode_orbit := B.mode_orbit
  mode_norm := B.mode_norm
  mode_vertical := B.mode_vertical
  mode_bias := fun h hh j => (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans_lt (B.mode_bias h hh j)
  independent := B.independent
  test_positive := B.test_positive
  test_complexity := fun h hh => (B.test_complexity h hh).mono hpq
  test_invariant := B.test_invariant
  test_violation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans_lt (B.test_violation h hh)

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open scoped BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}

noncomputable def testingFamily (B : PositiveShiftBasis s N q a J) :
    ZMod N × Fin B.count → ZMod N → ℂ := by
  classical
  exact fun hk n => if hk.1 ∈ B.shifts then (B.mode hk.1 hk.2).evalCyclic N (fun _ => n) else 0

end Erdos3.PositiveShiftBasis

end

section

universe u

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

end Erdos3

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

variable {J σ : Type*} {L : (Bool ⊕ (J × Bool)) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : (Bool ⊕ (J × Bool)) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)} {w : σ → ℕ}

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

noncomputable def anchoredOptionInputs {J : Type*} (j : J) : Finset (Option (Option J ⊕ J)) := by
  classical
  exact {none, some (.inl none), some (.inl (some j)), some (.inr j)}

namespace RationalFilteredNilmanifold

variable {J σ : Type*} {L : Option (Option J ⊕ J) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : Option (Option J ⊕ J) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)} {w : σ → ℕ}

noncomputable def anchoredOptionReferenceData
    (P : (D none).Niltest w) (P₀ : (D (some (.inl none))).Niltest w)
    (A : ∀ j, (D (some (.inl (some j)))).Niltest w) (B : ∀ j, (D (some (.inr j))).Niltest w) :
    ∀ i, (D i).Niltest w
  | none => P
  | some (.inl none) => P₀
  | some (.inl (some j)) => A j
  | some (.inr j) => B j

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

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

variable {J σ : Type*} [Fintype J] {L : (Bool ⊕ (J × Bool)) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : (Bool ⊕ (J × Bool)) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  (B : PositiveShiftBasis.{u} s N q a J)

abbrev anchoredLieSpace (L M : Fin B.count → Type u) :=
  optionLieSpace B.L (sumLieSpace (optionLieSpace B.L L) M)

abbrev anchoredDimension (d e : Fin B.count → ℕ) :=
  optionDimension B.dim (Sum.elim (optionDimension B.dim d) e)

variable {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  (D : ∀ j, RationalFilteredNilmanifold (L j) s (d j))
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))

noncomputable def anchoredFactors : ∀ i : Option (Option (Fin B.count) ⊕ Fin B.count),
    RationalFilteredNilmanifold (B.anchoredLieSpace L M i) s (B.anchoredDimension d e i) :=
  optionFactors B.model (sumFactors (optionFactors B.model D) E)

def anchoredWeights (w : Fin B.dim → ℕ) (v : ∀ j, Fin (d j) → ℕ) (v' : ∀ j, Fin (e j) → ℕ) :
    ∀ i, Fin (B.anchoredDimension d e i) → ℕ
  | none => w
  | some (.inl none) => w
  | some (.inl (some j)) => v j
  | some (.inr j) => v' j

end Erdos3.PositiveShiftBasis

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PhaseBandCoordinateLifts
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem torusPhaseLinear_realLattice_integral {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)
    (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))
    (γ : D.RealGroup) (hγ : γ ∈ D.realLattice) :
    ∃ a : Fin t → ℤ, torusPhaseLinear φ γ.coord = fun i => (a i : ℝ) := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hγ
  obtain ⟨a, ha⟩ := hphase z hz
  refine ⟨a, funext fun i => ?_⟩
  change torusPhaseLinear φ ((1 : ℝ) ⊗ₜ[ℚ] z.coord) i = (a i : ℝ)
  rw [torusPhaseLinear_tmul, _root_.one_mul, ha i, Rat.cast_intCast]

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

theorem realMarkedParameterElement_scaled_integer_mem
    (hdir : ∀ a : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
        D.filtration.Group) ∈ D.lattice) (a : Fin t → ℤ) :
    (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • (fun i => (a i : ℝ))) :
      D.RealGroup) ∈ D.realLattice := by
  have h := markedDirection_mem_realLattice_of_smul F v w marked t D (m : ℚ)
    (fun i => (a i : ℚ)) (hdir a)
  have heq : realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • (fun i => (a i : ℝ))) =
      (⟨realMarkedDirection F v w marked t ((m : ℚ) • (fun i => (a i : ℚ)))⟩ : D.RealGroup) := by
    apply NilpotentLieBCHGroup.ext
    change realMarkedParameterDirection F v w marked t _ = _
    rw [← realMarkedParameterDirection_rat]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast]
  exact heq ▸ h

theorem marked_phase_correction_coordinate_norm_le {p R : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hmp : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p)
    (hR : 1 ≤ R) (g z γ : D.RealGroup) (hg : g = z * γ)
    (hgphase : ‖torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord‖ ≤ 1 / 4)
    (hz : ‖(D.basis.baseChange ℝ).equivFun z.coord‖ ≤ R) :
    ‖(D.basis.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t
      ((m : ℝ) • torusPhaseLinear (normalizedMarkedPhase F v w marked t m) γ.coord))‖ ≤
        2 * Real.exp (5 * p) * R := by
  let φ := normalizedMarkedPhase F v w marked t m
  have hsum : torusPhaseLinear φ g.coord = torusPhaseLinear φ z.coord + torusPhaseLinear φ γ.coord := by
    rw [hg, torusPhaseLinear_mul D]
  have hγ : torusPhaseLinear φ γ.coord = torusPhaseLinear φ g.coord - torusPhaseLinear φ z.coord := by
    rw [hsum, add_sub_cancel_left]
  have hzphase : ‖torusPhaseLinear φ z.coord‖ ≤ Real.exp (2 * p) * R :=
    (normalizedMarkedPhase_coordinate_norm_le F v w marked t m D.basis hd hphase z.coord).trans
      (mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _))
  have hγnorm : ‖torusPhaseLinear φ γ.coord‖ ≤ 1 / 4 + Real.exp (2 * p) * R := by
    rw [hγ]
    exact (norm_sub_le _ _).trans (add_le_add hgphase hzphase)
  have hlarge : 1 ≤ Real.exp (2 * p) * R :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) hR
  have hγnorm' : ‖torusPhaseLinear φ γ.coord‖ ≤ 2 * Real.exp (2 * p) * R := by
    nlinarith
  have h := realMarkedParameterDirection_coordinate_norm_le F v w marked t D.basis ht hdir
    ((m : ℝ) • torusPhaseLinear φ γ.coord)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg m)] at h
  apply h.trans
  calc
    Real.exp (2 * p) * ((m : ℝ) * ‖torusPhaseLinear φ γ.coord‖) ≤
        Real.exp (2 * p) * (Real.exp p * (2 * Real.exp (2 * p) * R)) := by gcongr
    _ = 2 * Real.exp (5 * p) * R := by
      rw [show 5 * p = 2 * p + p + 2 * p by ring, Real.exp_add, Real.exp_add]
      ring

theorem exists_marked_phase_band_representatives (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {r d t m : ℕ}
      (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (_hw : ∀ i, 0 < w i) (_hv : ∀ i, v i ∈ F.layer (w i) 1)
      [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (t : ℝ) ≤ p → 0 < m → (m : ℝ) ≤ Real.exp p →
      (∀ i j, rationalLogHeight
        (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p) →
      (∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p) →
      (∀ z : D.filtration.Group, z ∈ D.lattice →
        IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) →
      (∀ a : Fin t → ℤ,
        (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
          D.filtration.Group) ∈ D.lattice) →
      ∀ g : D.RealGroup,
        (∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4) →
        ∃ z : D.RealGroup,
          (QuotientGroup.mk z : D.Space) = QuotientGroup.mk g ∧
          torusPhaseLinear (normalizedMarkedPhase F v w marked t m) z.coord =
            torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord ∧
          ‖(D.basis.baseChange ℝ).equivFun z.coord‖ ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨A, hA, hrep⟩ := exists_realification_representatives_exp_bound (s + 1)
  obtain ⟨B, hB, hprod⟩ := exists_bch_group_product_exp_bound (s + 1) (A + 2)
  refine ⟨(A + 10) + B + 2, by omega, ?_⟩
  intro I L _ _ r d t m F v w marked hw hv _ _ _ D p hp hD ht hm hmp hdir hphase hint hlat g hg
  let φ := normalizedMarkedPhase F v w marked t m
  let H := ⌈Real.exp p⌉₊
  have hc (i j k) : RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  obtain ⟨z, hz, γ, hγ, heq⟩ := hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice
    D.grid H (p + 1) D.grid_pos D.inner_grid hc (by linarith)
    (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))) g
  let R := Real.exp (((p + 1) + A) ^ A)
  have hR : 1 ≤ R := Real.one_le_exp (by positivity)
  have hznorm : ‖(D.basis.baseChange ℝ).equivFun z.coord‖ ≤ R :=
    (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr (fun i => by
      simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using hz i)
  obtain ⟨a, ha⟩ := torusPhaseLinear_realLattice_integral D φ hint γ hγ
  let δ : D.RealGroup := realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • (fun i => (a i : ℝ)))
  have hδ : δ ∈ D.realLattice := realMarkedParameterElement_scaled_integer_mem F v w marked hw hv t m D hlat a
  have hδphase : torusPhaseLinear φ δ.coord = torusPhaseLinear φ γ.coord := by
    change torusPhaseLinear φ (realMarkedParameterDirection F v w marked t _) = _
    rw [normalizedMarkedPhase_real_scaled_parameter F v w marked t m hm, ha]
  have hδnorm : ‖(D.basis.baseChange ℝ).equivFun δ.coord‖ ≤ 2 * Real.exp (5 * p) * R := by
    change ‖(D.basis.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t _)‖ ≤ _
    rw [← ha]
    exact marked_phase_correction_coordinate_norm_le F v w marked t m D hp hD.1 ht hmp hdir hphase
      hR g z γ heq ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun i => by
        simpa only [Real.norm_eq_abs] using hg i)) hznorm
  let q := p + (A + 10 : ℕ)
  have hpq : p + 1 ≤ q := by dsimp [q]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) A]
  have hq : 0 ≤ q := by positivity
  have hinput : 2 * Real.exp (5 * p) * R ≤ Real.exp ((q + 2) ^ (A + 2)) := by
    have hQ : 6 ≤ q + 2 := by dsimp [q]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) A]
    have hpQ : p ≤ q + 2 := by linarith
    have hQpow : q + 2 ≤ (q + 2) ^ A := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ q + 2) (by omega : 1 ≤ A)
    have hRpow : ((p + 1) + A) ^ A ≤ (q + 2) ^ A :=
      pow_le_pow_left₀ (by positivity) (by dsimp [q]; push_cast; linarith) A
    have hexp : 1 + 5 * p + ((p + 1) + A) ^ A ≤ (q + 2) ^ (A + 2) := by
      calc
        _ ≤ 7 * (q + 2) ^ A := by nlinarith
        _ ≤ (q + 2) ^ A * (q + 2) ^ 2 :=
          by nlinarith [pow_nonneg (by linarith : 0 ≤ q + 2) A, sq_nonneg (q + 2 - 3)]
        _ = _ := (pow_add _ _ _).symm
    calc
      _ ≤ Real.exp 1 * Real.exp (5 * p) * Real.exp (((p + 1) + A) ^ A) := by
        gcongr
        linarith [Real.add_one_le_exp (1 : ℝ)]
      _ = Real.exp (1 + 5 * p + ((p + 1) + A) ^ A) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr hexp
  have hRinput : R ≤ Real.exp ((q + 2) ^ (A + 2)) := by
    apply le_trans ?_ hinput
    have he : 1 ≤ Real.exp (5 * p) := Real.one_le_exp (by positivity)
    nlinarith [Real.exp_nonneg (5 * p)]
  refine ⟨z * δ, ?_, ?_, ?_⟩
  · rw [heq]
    exact (QuotientGroup.mk_mul_of_mem z hδ).trans
      (QuotientGroup.mk_mul_of_mem z (show γ ∈ D.realLattice from hγ)).symm
  · rw [heq, torusPhaseLinear_mul D, torusPhaseLinear_mul D, hδphase]
  · have hbound := hprod (D.basis.baseChange ℝ) (lieStructureConstants D.basis) H q
      D.filtration.realification.lowerCentralSeries_eq_bot [z, δ]
      (fun i j k => (realLieBasis_structure D.basis i j k).symm) hq
      (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ q))
      (by simpa using (show 2 ≤ s + 1 by omega))
      ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hpq)) hc
      (by
        intro x hx i
        have hxnorm : ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ Real.exp ((q + 2) ^ (A + 2)) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact hznorm.trans hRinput
          · exact hδnorm.trans hinput
        calc
          _ ≤ ‖(D.basis.baseChange ℝ).equivFun x.coord‖ := by
            simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using
              norm_le_pi_norm ((D.basis.baseChange ℝ).equivFun x.coord) i
          _ ≤ _ := hxnorm)
    have hfinal := Real.exp_le_exp.mpr (shifted_center_power_bound (A + 10) B hp)
    apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr
    intro i
    simpa only [List.prod_cons, List.prod_nil, mul_one, Real.norm_eq_abs, Basis.equivFun_apply] using
      (hbound i).trans hfinal

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d t : ℕ}
  (D : RationalFilteredNilmanifold L s d) (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)
  (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))

include hphase in
theorem torusPhaseLinear_eq_of_close (g h : D.RealGroup)
    (heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h)
    (hclose : dist (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord) < 1) :
    torusPhaseLinear φ g.coord = torusPhaseLinear φ h.coord := by
  obtain ⟨a, ha⟩ := torusPhaseLinear_realLattice_integral D φ hphase (g⁻¹ * h) (QuotientGroup.eq.mp heq)
  rw [torusPhaseLinear_mul, torusPhaseLinear_inv] at ha
  funext i
  have hai : -torusPhaseLinear φ g.coord i + torusPhaseLinear φ h.coord i = (a i : ℝ) := congrFun ha i
  have hi : |(a i : ℝ)| < 1 := by
    rw [← hai, neg_add_eq_sub, abs_sub_comm]
    exact (dist_le_pi_dist (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord) i).trans_lt hclose
  have hzero : a i = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hi)
  rw [hzero, Int.cast_zero] at hai
  linarith

include hphase in
theorem torusPhaseLinear_eq_in_band_of_near (g h z : D.RealGroup)
    (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4)
    (hh : ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4)
    (hz : (QuotientGroup.mk z : D.Space) = QuotientGroup.mk h)
    (hnear : dist (torusPhaseLinear φ z.coord) (torusPhaseLinear φ g.coord) < 1 / 4) :
    torusPhaseLinear φ z.coord = torusPhaseLinear φ h.coord := by
  apply torusPhaseLinear_eq_of_close D φ hphase z h hz
  have hgh : dist (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord) ≤ 1 / 2 := by
    have h := dist_le_norm_add_norm (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord)
    linarith
  have h := dist_triangle (torusPhaseLinear φ z.coord) (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord)
  linarith

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem torusPhaseLinear_group_lipschitz (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (φ (D.basis j) i) H) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    LipschitzWith (coordinateLipschitzBound t d H) (fun g : D.RealGroup => torusPhaseLinear φ g.coord) := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := (RationalTorus.nilmanifold t).filtration.realification.lowerCentralSeries_eq_bot)
    ((RationalTorus.basis t).baseChange ℝ)
  have hf := lipschitz_realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := (RationalTorus.nilmanifold t).filtration.lowerCentralSeries_eq_bot)
    D.basis (RationalTorus.basis t) φ H (fun i j => by
      change RationalHeightLE (φ (D.basis j) i) H
      exact hH i j)
  have hc := (RationalTorus.nilmanifold t).filtration.realification.stepOne_coordinates_lipschitz
    ((RationalTorus.basis t).baseChange ℝ)
  have h := hc.comp hf
  change LipschitzWith (1 * coordinateLipschitzBound (Fintype.card (Fin t)) (Fintype.card (Fin d)) H)
    (fun g : D.RealGroup => torusPhaseLinear φ g.coord) at h
  simpa only [one_mul, Fintype.card_fin] using h

theorem torusPhaseLinear_group_lipschitz_exp {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hcoords : ∀ i j, rationalLogHeight (φ (D.basis j) i) ≤ p) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), Real.exp_nonneg _⟩
      (fun g : D.RealGroup => torusPhaseLinear φ g.coord) := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  apply (torusPhaseLinear_group_lipschitz D φ ⌈Real.exp p⌉₊
    (fun i j => rationalHeightLE_ceil_exp (hcoords i j))).weaken
  have h := coordinateLipschitzBound_le_exp t d ⌈Real.exp p⌉₊
    (show 0 ≤ p + 1 by linarith) (ht.trans (by linarith : p ≤ p + 1))
    (hd.trans (by linarith : p ≤ p + 1)) (ceil_exp_le_exp_add_one hp)
  change (coordinateLipschitzBound t d ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp ((p + 3) ^ 2)
  simpa only [show p + 1 + 2 = p + 3 by ring] using h

include hphase in
theorem exists_nearby_phase_band_lift {K : ℝ≥0}
    (hK : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      LipschitzWith K (fun g : D.RealGroup => torusPhaseLinear φ g.coord))
    (g h : D.RealGroup)
    (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4)
    (hh : ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    letI := D.metricSpace
    let ρ := dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h)
    0 < ρ → (K : ℝ) * (2 * ρ) < 1 / 4 →
      ∃ z : D.RealGroup, (QuotientGroup.mk z : D.Space) = QuotientGroup.mk h ∧
        torusPhaseLinear φ z.coord = torusPhaseLinear φ h.coord ∧ dist z g < 2 * ρ := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := D.metricSpace
  dsimp only
  intro hρ hnear
  let ρ := dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h)
  obtain ⟨z, hzg, hz⟩ := rightCosetMetricSpace_exists_lift D.realLattice D.realLattice_closed_discrete.1
    g (2 * ρ) (QuotientGroup.mk h) (by
      change dist (QuotientGroup.mk h : D.Space) (QuotientGroup.mk g) < 2 * ρ
      rw [dist_comm]
      change ρ < 2 * ρ
      linarith)
  refine ⟨z, hz, ?_, hzg⟩
  apply torusPhaseLinear_eq_in_band_of_near D φ hphase g h z hg hh hz
  exact ((hK.dist_le_mul z g).trans (mul_le_mul_of_nonneg_left hzg.le K.coe_nonneg)).trans_lt hnear

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

noncomputable def phaseBandCoordinateConstant (s d H : ℕ) (R : ℝ≥0) : ℝ≥0 :=
  bchLogMetricConstant s d H R * bchLogMetricConstant s d H 1

noncomputable def phaseBandQuotientConstant (s d H : ℕ) (R K L : ℝ≥0) : ℝ≥0 :=
  2 * phaseBandCoordinateConstant s d H R * L +
    16 * (K + bchLogMetricConstant s d H 1 + phaseBandCoordinateConstant s d H R + 1)

theorem phase_band_quotient_dist_le {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t H : ℕ} (D : RationalFilteredNilmanifold L s d)
    (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)
    (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (R K A : ℝ≥0) (hR : 1 ≤ R)
    (hK : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      LipschitzWith K (fun g : D.RealGroup => torusPhaseLinear φ g.coord))
    (hrep : ∀ g : D.RealGroup, ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4 →
      ∃ x : D.RealGroup, (QuotientGroup.mk x : D.Space) = QuotientGroup.mk g ∧
        torusPhaseLinear φ x.coord = torusPhaseLinear φ g.coord ∧
        ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ R)
    (u : D.RealGroup → ℂ) (hu : ∀ g, ‖u g‖ ≤ 1)
    (hsame : ∀ g h : D.RealGroup, ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4 →
      ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4 →
      (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h → u g = u h)
    (hbox : ∀ g h : D.RealGroup, ‖(D.basis.baseChange ℝ).equivFun g.coord‖ ≤ (R : ℝ) + 1 →
      ‖(D.basis.baseChange ℝ).equivFun h.coord‖ ≤ (R : ℝ) + 1 →
      dist (u g) (u h) ≤ A *
        dist ((D.basis.baseChange ℝ).equivFun g.coord) ((D.basis.baseChange ℝ).equivFun h.coord))
    (g h : D.RealGroup) (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4)
    (hh : ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4) :
    letI := D.metricSpace
    dist (u g) (u h) ≤ phaseBandQuotientConstant s d H R K A *
      dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h) := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := D.metricSpace
  let C := bchLogMetricConstant s d H 1
  let B := phaseBandCoordinateConstant s d H R
  let S : ℝ := (K : ℝ) + C + B + 1
  let ρ := dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h)
  change dist (u g) (u h) ≤ (2 * (B : ℝ) * A + 16 * S) * ρ
  by_cases heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h
  · have huu := hsame g h hg hh heq
    have hρ : ρ = 0 := by simp only [ρ, heq, dist_self]
    simp only [huu, hρ, dist_self, mul_zero, le_refl]
  have hρ : 0 < ρ := dist_pos.mpr heq
  have hS : 0 ≤ S := by dsimp [S]; positivity
  by_cases hnear : S * ρ < 1 / 8
  · have hsmall (T : ℝ≥0) (hT : (T : ℝ) ≤ S) : (T : ℝ) * (2 * ρ) < 1 / 4 := by
      have ht := mul_le_mul_of_nonneg_right hT hρ.le
      nlinarith
    have hKS : (K : ℝ) ≤ S := by dsimp [S]; linarith [C.coe_nonneg, B.coe_nonneg]
    have hCS : (C : ℝ) ≤ S := by dsimp [S]; linarith [K.coe_nonneg, B.coe_nonneg]
    have hBS : (B : ℝ) ≤ S := by dsimp [S]; linarith [K.coe_nonneg, C.coe_nonneg]
    obtain ⟨x, hxq, hxp, hx⟩ := hrep g hg
    have hxphase : ‖torusPhaseLinear φ x.coord‖ ≤ 1 / 4 := by rw [hxp]; exact hg
    have hρx : dist (QuotientGroup.mk x : D.Space) (QuotientGroup.mk h) = ρ := by rw [hxq]
    obtain ⟨y, hyq, hyp, hyx⟩ := exists_nearby_phase_band_lift D φ hphase hK x h hxphase hh
      (by rw [hρx]; exact hρ) (by rw [hρx]; exact hsmall K hKS)
    rw [hρx] at hyx
    have hyphase : ‖torusPhaseLinear φ y.coord‖ ≤ 1 / 4 := by rw [hyp]; exact hh
    have hdxy : dist x y < 2 * ρ := by simpa only [dist_comm] using hyx
    have hCnear : (C : ℝ) * dist x y < 1 := by
      have ht := (mul_le_mul_of_nonneg_left hdxy.le C.coe_nonneg).trans_lt (hsmall C hCS)
      linarith
    have hcoords := dist_coordinates_le_of_near_box (D.basis.baseChange ℝ) (lieStructureConstants D.basis)
      (fun i j k => (realLieBasis_structure D.basis i j k).symm) hc R hR x y
      (fun i => by
        calc
          _ ≤ ‖(D.basis.baseChange ℝ).equivFun x.coord‖ := by
            simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using
              norm_le_pi_norm ((D.basis.baseChange ℝ).equivFun x.coord) i
          _ ≤ R := hx)
      (by simpa only [Fintype.card_fin] using hCnear)
    have hraw : bchBoxCoordinateBound s d H R * (C : ℝ) ≤ B := by
      change bchBoxCoordinateBound s d H R * (C : ℝ) ≤
        (bchBoxCoordinateBound s d H R + 1) * (C : ℝ)
      nlinarith [C.coe_nonneg]
    have hxy : dist ((D.basis.baseChange ℝ).equivFun x.coord)
        ((D.basis.baseChange ℝ).equivFun y.coord) ≤ (B : ℝ) * dist x y := by
      apply (show _ ≤ bchBoxCoordinateBound s d H R * (C : ℝ) * dist x y by
        simpa only [Fintype.card_fin, basisHomeomorph_apply] using hcoords).trans
      exact mul_le_mul_of_nonneg_right hraw dist_nonneg
    have hxy' : dist ((D.basis.baseChange ℝ).equivFun x.coord)
        ((D.basis.baseChange ℝ).equivFun y.coord) ≤ (B : ℝ) * (2 * ρ) :=
      hxy.trans (mul_le_mul_of_nonneg_left hdxy.le B.coe_nonneg)
    have hybox : ‖(D.basis.baseChange ℝ).equivFun y.coord‖ ≤ (R : ℝ) + 1 := by
      have ht := norm_sub_norm_le ((D.basis.baseChange ℝ).equivFun y.coord)
        ((D.basis.baseChange ℝ).equivFun x.coord)
      rw [← dist_eq_norm, dist_comm] at ht
      have hclose := hxy'.trans_lt (hsmall B hBS)
      linarith
    have hux := hsame x g hxphase hg hxq
    have huy := hsame y h hyphase hh hyq
    calc
      dist (u g) (u h) = dist (u x) (u y) := by rw [hux, huy]
      _ ≤ A * dist ((D.basis.baseChange ℝ).equivFun x.coord)
          ((D.basis.baseChange ℝ).equivFun y.coord) := hbox x y (by linarith) hybox
      _ ≤ A * ((B : ℝ) * (2 * ρ)) := mul_le_mul_of_nonneg_left hxy' A.coe_nonneg
      _ ≤ (2 * (B : ℝ) * A + 16 * S) * ρ := by nlinarith [mul_nonneg hS hρ.le]
  · have hdist := (dist_le_norm_add_norm (u g) (u h)).trans (add_le_add (hu g) (hu h))
    have hf : 1 / 8 ≤ S * ρ := le_of_not_gt hnear
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * B) A.coe_nonneg) hρ.le]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonInducedCorrelation
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

noncomputable def inducedMarkedLipschitzBound (s d u e : ℕ) (p : ℝ) (R : ℝ≥0) : ℝ≥0 :=
  2 * phaseBandQuotientConstant (s + 1) d ⌈Real.exp p⌉₊ R
    ⟨Real.exp ((p + 3) ^ 2), Real.exp_nonneg _⟩
    (markedLocalBoxConstant s d ⌈Real.exp p⌉₊ u e ⌈Real.exp p⌉₊ p (R + 1)
      ⟨Real.exp p, Real.exp_nonneg _⟩)

theorem exists_induced_marked_observable_explicit (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {r d t m e u : ℕ}
      (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (hm : 0 < m)
      [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ J))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ J))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ J))] [T2Space (ℝ ⊗[ℚ] (L ⧸ J))]
      (E : RationalFilteredNilmanifold (L ⧸ J) u e)
      (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
        (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)
      {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (t : ℝ) ≤ p → (m : ℝ) ≤ Real.exp p →
      (∀ i j, rationalLogHeight
        (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p) →
      (∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p) →
      (∀ i j, rationalLogHeight (E.basis.repr
        (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤ p) →
      (∀ z : D.filtration.Group, z ∈ D.lattice →
        IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) →
      (∀ a : Fin t → ℤ,
        (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
          D.filtration.Group) ∈ D.lattice) →
      ∀ V : E.Space → ℂ, (∀ x, ‖V x‖ ≤ 1) →
      (letI := E.metricSpace; LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ V) →
      letI := D.metricSpace
      ∃ G : D.Space → ℂ,
        LipschitzWith (inducedMarkedLipschitzBound s d u e p
          ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩) G ∧
        (∀ g : D.RealGroup,
          (∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4) →
          G (QuotientGroup.mk g) = markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g) ∧
        ∀ x, ‖G x‖ ≤ 2 := by
  obtain ⟨C, hC, hrepresentatives⟩ := exists_marked_phase_band_representatives s hs
  refine ⟨C, hC, ?_⟩
  intro I L _ _ r d t m e u F v w marked hw hv hm _ _ _ _ D J hJ _ _ _ _ E hmap p hp hD hE ht hmp hdir hphase heval hint hlat V hnorm hV
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := D.metricSpace
  let φ := normalizedMarkedPhase F v w marked t m
  let R : ℝ≥0 := ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩
  let K : ℝ≥0 := ⟨Real.exp ((p + 3) ^ 2), Real.exp_nonneg _⟩
  let H := ⌈Real.exp p⌉₊
  let A := markedLocalBoxConstant s d H u e H p (R + 1) ⟨Real.exp p, Real.exp_nonneg _⟩
  let f := markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V
  have hR : 1 ≤ R := Real.one_le_exp (by positivity)
  have norm_iff (z : Fin t → ℝ) : ‖z‖ ≤ 1 / 4 ↔ ∀ i, |z i| ≤ 1 / 4 := by
    simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num) (x := z))
  have hc (i j k) : RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hct (i j k) : RationalHeightLE (lieStructureConstants E.basis i j k) H :=
    rationalHeightLE_ceil_exp (hE.2.2.1 i j k)
  have hrep (g : D.RealGroup) (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4) :
      ∃ x : D.RealGroup, (QuotientGroup.mk x : D.Space) = QuotientGroup.mk g ∧
        torusPhaseLinear φ x.coord = torusPhaseLinear φ g.coord ∧
        ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ R :=
    hrepresentatives F v w marked hw hv D hp hD ht hm hmp hdir hphase hint hlat g ((norm_iff _).mp hg)
  have hdist (g h : D.RealGroup) (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4)
      (hh : ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4) :
      dist (f g) (f h) ≤ phaseBandQuotientConstant (s + 1) d H R K A *
        dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h) := by
    apply phase_band_quotient_dist_le D φ hint hc R K A hR
      (torusPhaseLinear_group_lipschitz_exp D φ hp hD.1 ht hphase) hrep f
      (fun x => markedLocalCoefficientValue_norm_le F v w marked hw hv t m hm D J hJ E hmap V hnorm x)
      (fun x y hx hy hxy => markedLocalCoefficientValue_eq_on_small_cosets
        F v w marked hw hv t m hm D J hJ E hmap hint V x y ((norm_iff _).mp hx) ((norm_iff _).mp hy) hxy)
      (fun x y hx hy => ?_) g h hg hh
    exact markedLocalCoefficientValue_coordinate_dist_le F v w marked hw hv t m hm D J hJ E hmap
      hp hD.1 ht hmp hdir hphase heval hc hct (R + 1) ⟨Real.exp p, Real.exp_nonneg _⟩
      (le_add_of_nonneg_left (by positivity)) V hV x y hx hy
  let X := {g : D.RealGroup // ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4}
  obtain ⟨G, hG, hGeq, hGnorm⟩ := exists_complex_extension_along_map
    (fun x : X => (QuotientGroup.mk x.val : D.Space)) (fun x : X => f x.val)
    (phaseBandQuotientConstant (s + 1) d H R K A) 1
    (fun x y => hdist x.val y.val x.property y.property)
    (fun x => markedLocalCoefficientValue_norm_le F v w marked hw hv t m hm D J hJ E hmap V hnorm x.val)
  refine ⟨G, hG, ?_, ?_⟩
  · intro g hg
    exact hGeq ⟨g, (norm_iff _).mpr hg⟩
  · intro x
    simpa only [NNReal.coe_one, mul_one] using hGnorm x

theorem induced_marked_observable_scaled_parameter
    {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e u t m : ℕ}
    (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (hm : 0 < m)
    (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
    (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
    (E : RationalFilteredNilmanifold (L ⧸ J) u e)
    (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
      (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)
    (V : E.Space → ℂ) (G : D.Space → ℂ)
    (hG : ∀ g : D.RealGroup,
      (∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4) →
      G (QuotientGroup.mk g) = markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g)
    (a : Fin t → ℝ) (ha : ∀ i, |a i| ≤ 1 / 4) (g : D.RealGroup)
    (hg : torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord = 0) :
    G (QuotientGroup.mk (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • a) * g)) =
      V (QuotientGroup.mk (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ g.coord⟩ : E.RealGroup)) := by
  rw [hG]
  · exact markedLocalCoefficientValue_scaled_parameter F v w marked hw hv t m hm D J hJ E hmap V a g hg
  · intro i
    rw [torusPhaseLinear_mul D, hg, add_zero]
    change |torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterDirection F v w marked t ((m : ℝ) • a)) i| ≤ 1 / 4
    rw [normalizedMarkedPhase_real_scaled_parameter F v w marked t m hm]
    exact ha i

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem localPhaseMarkedOrbit_induced_value
    {s r N d e k : ℕ} [NeZero N] {b p q P : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
    (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) (hm : 0 < m) (hs : 1 ≤ s)
    (E : RationalFilteredNilmanifold
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
    (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
    (hmap : ∀ z : E.RealGroup, z ∈ E.realLattice →
      (⟨(D.markedDependentEvaluation t 0).baseChange ℝ z.coord⟩ : Q.RealGroup) ∈ Q.realLattice)
    (hdir : ∀ a : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (fun i => (a i : ℚ))⟩ :
          E.filtration.Group) ∈ E.lattice)
    (V : Q.Space → ℂ) (G : E.Space → ℂ)
    (hG : ∀ z : E.RealGroup,
      (∀ i, |torusPhaseLinear (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t m) z.coord i| ≤ 1 / 4) →
      G (QuotientGroup.mk z) = markedLocalCoefficientValue D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t m hm E (D.dependentWordIdeal 0 2 0) le_rfl Q hmap V z)
    (h : ZMod N) (hsmall : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4) (n : ℤ) :
    G (QuotientGroup.mk ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m))) =
      V (QuotientGroup.mk (⟨D.dependentQuotientMap.toLinearMap.baseChange ℝ
        (∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
          ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val))⟩ : Q.RealGroup)) := by
  let φ := normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t m
  let g : E.RealGroup := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m)
  let γ : E.RealGroup := D.scaledLocalAffineCorrectingElement t u c h₀ m h
  let ε : E.RealGroup := D.localPhaseMarkedSmallElement t u c h₀ m h
  let z : E.RealGroup :=
    ⟨(lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
        (D.localPhaseMarkedLift t x y u c h₀ m h n)⟩
  have hγ : γ ∈ E.realLattice := D.scaledLocalAffineCorrectingElement_mem_realLattice
    t u c h₀ m E hdir h
  have hcoset : (QuotientGroup.mk g : E.Space) = QuotientGroup.mk (ε * z) := by
    calc
      _ = QuotientGroup.mk (g * γ⁻¹) :=
        (quotient_mk_mul_mem E.realLattice g ⟨γ⁻¹, E.realLattice.inv_mem hγ⟩).symm
      _ = _ := congrArg QuotientGroup.mk (D.localPhaseMarkedOrbit_lift_factorization t x y u c h₀ m hs h n)
  have hz : torusPhaseLinear φ z.coord = 0 := normalizedMarkedPhase_real_pure
    D.coefficientFreeFiltration D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    t m z.coord (D.localPhaseMarkedLift_pure t x y u c h₀ m h n)
  have hε : ε = realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t
        ((m : ℝ) • (fun i => -affineCyclicTorusLocalLift u c h₀ h i)) := by
    change realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t _ = _
    apply congrArg (realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t)
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_neg, neg_mul]
  change G (QuotientGroup.mk g) = _
  rw [hcoset, hε]
  apply (induced_marked_observable_scaled_parameter D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer hm E (D.dependentWordIdeal 0 2 0) le_rfl Q hmap V G hG
    (fun i => -affineCyclicTorusLocalLift u c h₀ h i)
    (fun i => by simpa only [abs_neg] using hsmall i) z hz).trans
  exact congrArg (fun a => V (QuotientGroup.mk (⟨a⟩ : Q.RealGroup)))
    (D.localPhaseMarkedLift_base_projection t x y u c h₀ m hm h n)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N d e k l : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) (hm : 0 < m) (hs : 1 ≤ s)
  (M : RationalFilteredNilmanifold
    (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s l)
  (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
  (hφ : E.lattice ≤ Q.lattice.comap (mapOfSteps
    (hL := E.filtration.lowerCentralSeries_eq_bot) (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
  (hmap : ∀ z : M.RealGroup, z ∈ M.realLattice →
    (⟨(D.markedDependentEvaluation t 0).baseChange ℝ z.coord⟩ : Q.RealGroup) ∈ Q.realLattice)
  (hdir : ∀ a : Fin t → ℤ,
    (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t (fun i => (a i : ℚ))⟩ :
        M.filtration.Group) ∈ M.lattice)

include hs hdir

theorem induced_local_value_eq_nativeSpaceMap (V : Q.Space → ℂ) (G : M.Space → ℂ)
    (hG : ∀ z : M.RealGroup,
      (∀ i, |torusPhaseLinear (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t m) z.coord i| ≤ 1 / 4) →
      G (QuotientGroup.mk z) = markedLocalCoefficientValue D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t m hm M (D.dependentWordIdeal 0 2 0) le_rfl Q hmap V z)
    (a : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (h : ZMod N) (hsmall : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4)
    (ha : a.log = positiveUnivariate (fun j => (x j).val +
      ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val)) (n : ℤ) :
    G (QuotientGroup.mk ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m))) =
      V (E.nativeSpaceMap Q D.dependentQuotientMap hφ (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => n) a))) := by
  apply (D.localPhaseMarkedOrbit_induced_value t x y u c h₀ m hm hs M Q hmap hdir V G hG h hsmall n).trans
  have hcoord : (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => n) a).coord =
      ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
        ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
    rw [E.filtration.realification.polynomialOrbitEval_coord, ha]
    simp only [positiveUnivariate, map_sum, eval_monomial, Finsupp.prod_single_index, pow_zero]
  rw [nativeSpaceMap_mk]
  apply congrArg (fun z : Q.RealGroup => V (QuotientGroup.mk z))
  apply NilpotentLieBCHGroup.ext
  change _ = D.dependentQuotientMap.toLinearMap.baseChange ℝ _
  rw [hcoord]

variable [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
  [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]

theorem exists_local_induced_comparison_correlation {A I J : Type*} [Fintype I] [Fintype J]
    {degree : ℕ} {z q₁ q₂ qV : ℝ} {S : Subgroup E.RealGroup} {T : Subgroup Q.RealGroup}
    (V : E.UnitVerticalObservable S I qV) (U : Q.UnitVerticalObservable T J qV)
    (G : J → M.Space → ℂ)
    (hG : ∀ j (z : M.RealGroup),
      (∀ i, |torusPhaseLinear (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t m) z.coord i| ≤ 1 / 4) →
      G j (QuotientGroup.mk z) = markedLocalCoefficientValue D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t m hm M (D.dependentWordIdeal 0 2 0) le_rfl Q hmap (U.observable j) z)
    (a v : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (h : ZMod N) (hsmall : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4)
    (ha : a.log = positiveUnivariate (fun j => (x j).val +
      ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val))
    (f : A → ZMod N → ℂ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp q₁) (hJ : (Fintype.card J : ℝ) ≤ Real.exp q₂)
    (B : NativeVectorCorrelation degree N z (fun ai : A × I => fun n =>
      f ai.1 n * star (V.observable ai.2 (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) v))))) :
    Nonempty (NativeVectorCorrelation degree N (z + q₁ + q₂)
      (fun ij : A × ((I × I) × (I × J)) => fun n =>
        f ij.1 n * star (G ij.2.2.2 (QuotientGroup.mk
          ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
            (correlationInput (h.val : ℤ) (n.val : ℤ)) (D.localPhaseMarkedOrbit t x y u c h₀ m)))) *
        star (V.observable ij.2.1.1 (QuotientGroup.mk
            (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) v)) *
          star (V.observable ij.2.1.2 (QuotientGroup.mk
            (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) a)))) *
        star (mapDifferenceObservable V U D.dependentQuotientMap hφ ij.2.2 (QuotientGroup.mk
          (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) a))))) := by
  have hvalue (j : J) (n : ZMod N) := D.induced_local_value_eq_nativeSpaceMap
    t x y u c h₀ m hm hs M E Q hφ hmap hdir (U.observable j) (G j) (hG j) a h hsmall ha (n.val : ℤ)
  have htwo := exists_native_two_unit_comparison f
    (fun i n => V.observable i (QuotientGroup.mk
      (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) v)))
    (fun i n => V.observable i (QuotientGroup.mk
      (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) a)))
    (fun j n => U.observable j (E.nativeSpaceMap Q D.dependentQuotientMap hφ (QuotientGroup.mk
      (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) a))))
    (fun n => V.unit _) (fun n => U.unit _) hq₁ hq₂ hI hJ B
  simpa only [hvalue, mapDifferenceObservable] using htwo

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InducedMarkedBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

def inducedMarkedLogBudget (C A B : ℕ) (p : ℝ) : ℝ :=
  let q := 6 * p + (p + C) ^ C + 2
  let a := (q + A) ^ A
  let t := a + q + 8 * p + 3
  let b := (t + B) ^ B
  2 * (b + 2 * a + 8 * p + (p + 3) ^ 2 + q + 10) + 132

theorem exists_inducedMarkedLogBudget_bound (C A B : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p → inducedMarkedLogBudget C A B p ≤ (p + N) ^ N := by
  let q : Polynomial ℕ := 6 * Polynomial.X + (Polynomial.X + Polynomial.C C) ^ C + 2
  let a := (q + Polynomial.C A) ^ A
  let t := a + q + 8 * Polynomial.X + 3
  let b := (t + Polynomial.C B) ^ B
  let P : Polynomial ℕ := 2 * (b + 2 * a + 8 * Polynomial.X + (Polynomial.X + 3) ^ 2 + q + 10) + 132
  obtain ⟨N, hN, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨N, hN, ?_⟩
  intro p hp
  have heq : P.eval₂ (Nat.castRingHom ℝ) p = inducedMarkedLogBudget C A B p := by
    simp [P, q, a, t, b, inducedMarkedLogBudget, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  rw [← heq]
  exact hbound p hp

theorem exists_inducedMarkedLipschitzBound_exp_bound (s u C : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (d e : ℕ) (p : ℝ) (R : ℝ≥0),
      0 ≤ p → (d : ℝ) ≤ p → (e : ℝ) ≤ p → (R : ℝ) ≤ Real.exp ((p + C) ^ C) →
      (inducedMarkedLipschitzBound s d u e p R : ℝ) ≤ Real.exp ((p + N) ^ N) := by
  obtain ⟨A, _, hsource⟩ := exists_bchBoxMetricConstant_exp_bound (s + 1) 1
  obtain ⟨B, _, htarget⟩ := exists_bchBoxMetricConstant_exp_bound u 1
  obtain ⟨N, hN, hbudget⟩ := exists_inducedMarkedLogBudget_bound C A B
  refine ⟨N, hN, ?_⟩
  intro d e p R hp hd he hR
  apply le_trans ?_ (Real.exp_le_exp.mpr (hbudget p hp))
  let r := (p + C) ^ C
  let q := 6 * p + r + 2
  let a := (q + A) ^ A
  let t := a + q + 8 * p + 3
  let b := (t + B) ^ B
  let W := b + 2 * a + 8 * p + (p + 3) ^ 2 + q + 10
  let H := ⌈Real.exp p⌉₊
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hpq : p + 1 ≤ q := by dsimp [q]; linarith
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hH : (H : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hpq)
  have hplus (x : ℝ) (hx : 0 ≤ x) : Real.exp x + 1 ≤ Real.exp (x + 1) := by
    calc
      _ ≤ Real.exp x * 2 := by linarith [Real.one_le_exp hx]
      _ ≤ Real.exp x * Real.exp 1 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hRplus : ((R + 1 : ℝ≥0) : ℝ) ≤ Real.exp (r + 1) := by
    change (R : ℝ) + 1 ≤ Real.exp (r + 1)
    exact (add_le_add hR (le_refl (1 : ℝ))).trans (hplus r hr)
  have hRq : (R : ℝ) ≤ Real.exp q := hR.trans (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  have hbox (D : ℝ≥0) (hD : (D : ℝ) ≤ Real.exp q) :
      bchBoxCoordinateBound (s + 1) d H D ≤ Real.exp a := by
    apply (bchBoxCoordinateBound_le_bchBoxMetricConstant (s + 1) d H D).trans
    apply hsource d H D q hq (hd.trans (by linarith)) hH
    simpa only [pow_one] using hD.trans (Real.exp_le_exp.mpr (by linarith : q ≤ q + 2))
  have hlog (D : ℝ≥0) (hD : (D : ℝ) ≤ Real.exp q) :
      (bchLogMetricConstant (s + 1) d H D : ℝ) ≤ Real.exp (a + 1) := by
    change bchBoxCoordinateBound (s + 1) d H D + 1 ≤ _
    exact (add_le_add (hbox D hD) (le_refl (1 : ℝ))).trans (hplus a ha)
  have hC0 : (bchLogMetricConstant (s + 1) d H 1 : ℝ) ≤ Real.exp (a + 1) :=
    hlog 1 (Real.one_le_exp hq)
  have hcoord : (phaseBandCoordinateConstant (s + 1) d H R : ℝ) ≤ Real.exp (2 * (a + 1)) := by
    change (bchLogMetricConstant (s + 1) d H R : ℝ) * (bchLogMetricConstant (s + 1) d H 1 : ℝ) ≤ _
    calc
      _ ≤ Real.exp (a + 1) * Real.exp (a + 1) :=
        mul_le_mul (hlog R hRq) hC0 (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hinput : Real.exp (5 * p) * ((R + 1 : ℝ≥0) : ℝ) ≤ Real.exp q := by
    calc
      _ ≤ Real.exp (5 * p) * Real.exp (r + 1) := mul_le_mul_of_nonneg_left hRplus (Real.exp_nonneg _)
      _ = Real.exp (5 * p + (r + 1)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [q]; linarith)
  have hret : (markedRetractionBoxConstant s d H p (R + 1) : ℝ) ≤ Real.exp (a + 5 * p) := by
    change bchBoxCoordinateBound (s + 1) d H (Real.exp (5 * p) * ((R + 1 : ℝ≥0) : ℝ)) * Real.exp (5 * p) ≤ _
    calc
      _ ≤ Real.exp a * Real.exp (5 * p) := mul_le_mul_of_nonneg_right
        (hbox ⟨Real.exp (5 * p) * ((R + 1 : ℝ≥0) : ℝ),
          mul_nonneg (Real.exp_nonneg _) (R + 1).coe_nonneg⟩ hinput) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hT : (markedEvaluationBoxRadius s d H p (R + 1) : ℝ) ≤ Real.exp t := by
    change Real.exp (2 * p) * (markedRetractionBoxConstant s d H p (R + 1) : ℝ) *
      ((R + 1 : ℝ≥0) : ℝ) + 1 ≤ _
    calc
      _ ≤ Real.exp (2 * p) * Real.exp (a + 5 * p) * Real.exp (r + 1) + 1 := by gcongr
      _ = Real.exp (a + 7 * p + r + 1) + 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (a + 7 * p + r + 1 + 1) := hplus _ (by positivity)
      _ ≤ Real.exp t := Real.exp_le_exp.mpr (by dsimp [t, q]; linarith)
  have htargetMetric : (bchBoxMetricConstant u e H (markedEvaluationBoxRadius s d H p (R + 1)) : ℝ) ≤
      Real.exp b := by
    apply htarget e H _ t ht (he.trans (by linarith)) (hH.trans (Real.exp_le_exp.mpr hqt))
    simpa only [pow_one] using hT.trans (Real.exp_le_exp.mpr (by linarith : t ≤ t + 2))
  have hlocal : (markedLocalBoxConstant s d H u e H p (R + 1) ⟨Real.exp p, Real.exp_nonneg _⟩ : ℝ) ≤
      Real.exp (b + a + 8 * p) := by
    change Real.exp p * (bchBoxMetricConstant u e H (markedEvaluationBoxRadius s d H p (R + 1)) : ℝ) *
      Real.exp (2 * p) * (markedRetractionBoxConstant s d H p (R + 1) : ℝ) ≤ _
    calc
      _ ≤ Real.exp p * Real.exp b * Real.exp (2 * p) * Real.exp (a + 5 * p) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hcoordW := hcoord.trans (Real.exp_le_exp.mpr (show 2 * (a + 1) ≤ W by dsimp [W]; nlinarith [sq_nonneg (p + 3)]))
  have hlocalW := hlocal.trans (Real.exp_le_exp.mpr (show b + a + 8 * p ≤ W by dsimp [W]; nlinarith [sq_nonneg (p + 3)]))
  have hC0W := hC0.trans (Real.exp_le_exp.mpr (show a + 1 ≤ W by dsimp [W]; nlinarith [sq_nonneg (p + 3)]))
  have hphaseW : Real.exp ((p + 3) ^ 2) ≤ Real.exp W := Real.exp_le_exp.mpr (by dsimp [W]; linarith)
  have honeW : 1 ≤ Real.exp W := Real.one_le_exp hW
  change 2 * (2 * (phaseBandCoordinateConstant (s + 1) d H R : ℝ) *
      (markedLocalBoxConstant s d H u e H p (R + 1) ⟨Real.exp p, Real.exp_nonneg _⟩ : ℝ) +
      16 * (Real.exp ((p + 3) ^ 2) + (bchLogMetricConstant (s + 1) d H 1 : ℝ) +
        (phaseBandCoordinateConstant (s + 1) d H R : ℝ) + 1)) ≤ Real.exp (2 * W + 132)
  calc
    _ ≤ 2 * (2 * Real.exp W * Real.exp W +
        16 * (Real.exp W + Real.exp W + Real.exp W + Real.exp W)) := by gcongr
    _ = 4 * Real.exp (2 * W) + 128 * Real.exp W := by
      rw [show 2 * W = W + W by ring, Real.exp_add W W]
      ring
    _ ≤ 132 * Real.exp (2 * W) := by
      have hexp : Real.exp W ≤ Real.exp (2 * W) := Real.exp_le_exp.mpr (by linarith)
      linarith
    _ ≤ Real.exp 132 * Real.exp (2 * W) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (132 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalEpochComparison
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

variable {σ L : Type*}
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

structure EpochSymbolRecord (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T : D.Niltest (fun _ : σ => 1)) where
  fast : LieSubalgebra ℚ D.filtration.AssociatedGraded
  spanning : Fin d → D.filtration.AssociatedGraded
  budget : ℝ
  denominator : ℕ
  modulus : ℕ
  auxiliary : ℕ
  shift : σ → ℚ
  sides : σ → ℝ
  denominator_pos : 0 < denominator
  modulus_pos : 0 < modulus
  auxiliary_pos : 0 < auxiliary
  sides_pos : ∀ i, 0 < sides i
  denominator_le : (denominator : ℝ) ≤ Real.exp budget
  span_eq : Submodule.span ℚ (Set.range spanning) = fast.toSubmodule
  graded : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω fast.toSubmodule
  height_le : ∀ i j, rationalLogHeight
    ((D.filtration.associatedGradedBasis D.basis ω hF).repr (spanning i) j) ≤ budget
  factorization : D.filtration.SymbolFactorizationIn D.basis ω hF sides
    ((T.scalarAffinePullback ((modulus : ℚ) * auxiliary) shift).symbol D.basis ω hF)
    budget denominator fast

namespace EpochSymbolRecord

variable {D : RationalFilteredNilmanifold L s d} {ω : Fin d → ℕ}
  {hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i})}
  {T : D.Niltest (fun _ : σ => 1)}

def Controlled (r : EpochSymbolRecord D ω hF T) (W : σ → ℝ) (p : ℝ) : Prop :=
  r.budget ≤ p ∧ (r.auxiliary : ℝ) ≤ Real.exp p ∧
    ∀ i, Real.exp (-p) * W i ≤ ((r.modulus : ℝ) * r.auxiliary) * r.sides i

end EpochSymbolRecord

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

variable {σ L : Type*}
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {ω : Fin d → ℕ}
  {hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i})}
  {T : D.Niltest (fun _ : σ => 1)}

noncomputable def epochRecordIntersection : List (EpochSymbolRecord D ω hF T) →
    LieSubalgebra ℚ D.filtration.AssociatedGraded
  | [] => ⊤
  | r :: rs => r.fast ⊓ epochRecordIntersection rs

inductive EpochRecordHistory : List (EpochSymbolRecord D ω hF T) → Prop
  | nil : EpochRecordHistory []
  | cons {r : EpochSymbolRecord D ω hF T} {rs : List (EpochSymbolRecord D ω hF T)}
      (history : EpochRecordHistory rs)
      (drop : finrank ℚ ↥(epochRecordIntersection rs ⊓ r.fast) <
        finrank ℚ (epochRecordIntersection rs)) : EpochRecordHistory (r :: rs)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

universe u v

structure PhysicalEpochSource (σ : Type u) [Fintype σ] (s bound : ℕ) where
  Carrier : Type v
  [lieRing : LieRing Carrier]
  [lieAlgebra : LieAlgebra ℚ Carrier]
  [topology : TopologicalSpace (ℝ ⊗[ℚ] Carrier)]
  [topologicalAddGroup : IsTopologicalAddGroup (ℝ ⊗[ℚ] Carrier)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] Carrier)]
  [t2Space : T2Space (ℝ ⊗[ℚ] Carrier)]
  dimension : ℕ
  dimension_le : dimension ≤ bound
  model : RationalFilteredNilmanifold Carrier s dimension
  weights : Fin dimension → ℕ
  adapted : ∀ j, model.filtration.layer j = Submodule.span ℚ (model.basis '' {i | j ≤ weights i})
  fixedMap : model.Niltest (fun _ : σ => 1)
  lower : σ → ℤ
  sides : σ → ℕ
  sides_pos : ∀ i, 0 < sides i
  incomingBudget : ℝ
  recordBudget : ℝ
  incoming_nonneg : 0 ≤ incomingBudget
  incoming_le_record : incomingBudget ≤ recordBudget
  geometry : model.GeometryComplexityLE incomingBudget
  coordinates_le : (Fintype.card σ : ℝ) ≤ incomingBudget

attribute [instance] PhysicalEpochSource.lieRing PhysicalEpochSource.lieAlgebra PhysicalEpochSource.topology PhysicalEpochSource.topologicalAddGroup PhysicalEpochSource.continuousSMul PhysicalEpochSource.t2Space

structure PhysicalEpochRecords {σ : Type u} [Fintype σ] {s bound : ℕ}
    (base : PhysicalEpochSource.{u, v} σ s bound) where
  records : List (EpochSymbolRecord base.model base.weights base.adapted base.fixedMap)
  history : EpochRecordHistory records
  controlled : ∀ r ∈ records, r.Controlled (fun i => (base.sides i : ℝ)) base.recordBudget

namespace PhysicalEpochRecords

variable {σ : Type u} [Fintype σ] {s bound : ℕ} {base : PhysicalEpochSource.{u, v} σ s bound}

def empty (base : PhysicalEpochSource.{u, v} σ s bound) : PhysicalEpochRecords base where
  records := []
  history := .nil
  controlled := by simp

noncomputable def dimension (state : PhysicalEpochRecords base) : ℕ :=
  finrank ℚ (epochRecordIntersection state.records)

end PhysicalEpochRecords

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v

structure PhysicalEpochComparison {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound : ℕ}
    (base : PhysicalEpochSource.{u, v} σ s bound) (m a J : ℕ) (gap : ℝ) where
  selected_pos : 0 < m
  auxiliary_pos : 0 < a
  pending_pos : 0 < J
  lower : σ → ℤ
  sides : σ → ℕ
  sides_pos : ∀ i, 0 < sides i
  contained : ∀ i, base.lower i ≤ lower i ∧ lower i + sides i ≤ base.lower i + base.sides i
  anchor : σ → ℤ
  refined : σ → ℤ
  anchor_inside : ∀ i, lower i ≤ anchor i ∧ anchor i < lower i + sides i
  refined_inside : ∀ i, lower i ≤ refined i ∧ refined i < lower i + sides i
  compatible : ∀ i, refined i ≡ anchor i [ZMOD (m * a : ℕ)]
  test : base.model.Niltest (fun _ : σ => 1)
  orbit : test.orbit = (base.fixedMap.scalarAffinePullback (m * a : ℕ) (fun i => (anchor i : ℚ))).orbit
  positive : test.UnitIntervalValued
  complexity : test.ComplexityLE base.incomingBudget
  gap_pos : 0 < gap
  gap_le_one : gap ≤ 1
  gap_inverse : gap⁻¹ ≤ Real.exp base.incomingBudget
  discrepancy : gap ≤ ‖residuePairMean test.eval lower sides (m * a) anchor refined (fun _ => J) false -
    residuePairMean test.eval lower sides (m * a) anchor refined (fun _ => J) true‖

namespace PhysicalEpochComparison

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap : ℝ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

end PhysicalEpochComparison

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3

open Module

variable {I ι ν L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_induced_marked_observable (s u : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {r d t m e : ℕ}
      (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (hm : 0 < m)
      [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ J))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ J))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ J))] [T2Space (ℝ ⊗[ℚ] (L ⧸ J))]
      (E : RationalFilteredNilmanifold (L ⧸ J) u e)
      (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
        (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)
      {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (t : ℝ) ≤ p → (m : ℝ) ≤ Real.exp p →
      (∀ i j, rationalLogHeight
        (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p) →
      (∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p) →
      (∀ i j, rationalLogHeight (E.basis.repr
        (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤ p) →
      (∀ z : D.filtration.Group, z ∈ D.lattice →
        IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) →
      (∀ a : Fin t → ℤ,
        (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
          D.filtration.Group) ∈ D.lattice) →
      ∀ V : E.Space → ℂ, (∀ x, ‖V x‖ ≤ 1) →
      (letI := E.metricSpace; LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ V) →
      letI := D.metricSpace
      ∃ G : D.Space → ℂ,
        LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ G ∧
        (∀ g : D.RealGroup,
          (∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4) →
          G (QuotientGroup.mk g) = markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g) ∧
        ∀ x, ‖G x‖ ≤ 2 := by
  obtain ⟨A, _, hext⟩ := exists_induced_marked_observable_explicit s hs
  obtain ⟨C, hC, hbound⟩ := exists_inducedMarkedLipschitzBound_exp_bound s u A
  refine ⟨C, hC, ?_⟩
  intro I L _ _ r d t m e F v w marked hw hv hm _ _ _ _ D J hJ _ _ _ _ E hmap p hp hD hE ht hmp hdir hphase heval hint hlat V hnorm hV
  let := D.metricSpace
  obtain ⟨G, hG, hGeq, hGnorm⟩ := hext F v w marked hw hv hm D J hJ E hmap
    hp hD hE ht hmp hdir hphase heval hint hlat V hnorm hV
  refine ⟨G, hG.weaken ?_, hGeq, hGnorm⟩
  change (inducedMarkedLipschitzBound s d u e p
    ⟨Real.exp ((p + A) ^ A), Real.exp_nonneg _⟩ : ℝ) ≤ Real.exp ((p + C) ^ C)
  exact hbound d e p ⟨Real.exp ((p + A) ^ A), Real.exp_nonneg _⟩ hp hD.1 hE.1 le_rfl

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3

end

section

namespace Erdos3.QuadraticMarked

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

abbrev Seed := RationalTorus.Algebra 1

noncomputable def filtration : DegreeRankLieFiltration Seed 1 1 :=
  (RationalTorus.filtration 1).canonicalDegreeRank

noncomputable def generators : Fin 1 → Seed := RationalTorus.basis 1

def weights : Fin 1 → ℕ := fun _ => 1

def marked : Fin 1 → Bool := fun _ => true

theorem weight_pos (i : Fin 1) : 0 < weights i := by
  change 0 < (1 : ℕ)
  omega

theorem generator_mem (i : Fin 1) : generators i ∈ filtration.layer (weights i) 1 := by
  change generators i ∈ (RationalTorus.filtration 1).rankLayer 1 1
  rw [NilpotentLieFiltration.rankLayer_one, (RationalTorus.filtration 1).one_eq_top]
  trivial

theorem second_marked_span : markedLieSpan generators weights marked 0 2 0 ≤
    (⊥ : LieIdeal ℚ Seed).toSubmodule := by
  rw [markedLieSpan_marked_terminal filtration generators weights marked weight_pos generator_mem]
  exact bot_le

abbrev Algebra (t : ℕ) := MarkedShiftQuotient filtration generators weights marked t

noncomputable def multidegree (t : ℕ) :
    MultidegreeLieFiltration (Fin 2) (Algebra t) 2 (mixedCorrelationDegree 1) :=
  markedShiftMultidegree filtration generators weights marked weight_pos generator_mem t

noncomputable def phase (t m : ℕ) := normalizedMarkedPhase filtration generators weights marked t m

noncomputable def evaluation (t : ℕ) :=
  markedBaseEvaluation filtration generators weights marked t (⊥ : LieIdeal ℚ Seed) second_marked_span 0

noncomputable def localCharacter {t d : ℕ} (m : ℕ)
    (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ) (g : D.RealGroup) : ℂ :=
  CircleFourier.character ((realifyFunctional η ((evaluation t).baseChange ℝ
    (normalizedMarkedRetraction filtration generators weights marked weight_pos generator_mem t m D g).coord) : ℝ) :
      CircleFourier.Circle)

def Model (t : ℕ) (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ) (p : ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
    ∃ (d : ℕ) (D : RationalFilteredNilmanifold (Algebra t) 2 d),
      d ≤ 3 * t + 2 ∧ ∃ M : D.MultidegreeStructure (mixedCorrelationDegree 1),
        M.filtration = multidegree t ∧ M.ComplexityLE p ∧
        (∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (phase t m z.coord)) ∧
        (∀ a : Fin t → ℤ, (⟨(m : ℚ) • markedQuotientDirection
          filtration generators weights marked t (fun i => (a i : ℚ))⟩ : D.filtration.Group) ∈ D.lattice) ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra t)
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra t) := IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 D.basis
         letI := D.metricSpace
         ∃ G : D.Space → ℂ, (∀ x, ‖G x‖ ≤ 2) ∧
           LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ G ∧
           ∀ g : D.RealGroup,
             (∀ i, |torusPhaseLinear (phase t m) g.coord i| ≤ 1 / 4) →
             G (QuotientGroup.mk g) = localCharacter m D η g)

theorem Model.mono {t : ℕ} {η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ}
    {p q : ℝ} (h : Model t η p) (hpq : p ≤ q) : Model t η q := by
  obtain ⟨m, hm, hmp, d, D, hd, M, hMF, hM, hint, hlat, hG⟩ := h
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpq), d, D, hd, M, hMF,
    hM.mono M hpq, hint, hlat, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra t) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 D.basis
  let := D.metricSpace
  obtain ⟨G, hn, hl, he⟩ := hG
  exact ⟨G, hn, hl.weaken (Real.exp_le_exp.mpr hpq), he⟩

theorem filtration_layers (j : ℕ) : filtration.associatedDegree.layer j =
    Submodule.span ℚ (RationalTorus.basis 1 '' {i | j ≤ weights i}) := by
  simpa only [filtration, NilpotentLieFiltration.canonicalDegreeRank_associatedDegree_layer, weights]
    using RationalTorus.basis_layers 1 j

theorem structure_height {p : ℝ} (hp : 0 ≤ p) (i j k : Fin 1) :
    rationalLogHeight (lieStructureConstants (RationalTorus.basis 1) i j k) ≤ p := by
  simpa [lieStructureConstants, RationalTorus.lie_eq_zero, rationalLogHeight] using hp

theorem generator_height {p : ℝ} (hp : 0 ≤ p) (i j : Fin 1) :
    rationalLogHeight ((RationalTorus.basis 1).repr (generators i) j) ≤ p :=
  rationalLogHeight_le_of_height (basis_repr_height_one _ _ _)
    (by simpa only [Nat.cast_one] using Real.one_le_exp hp)

end Erdos3.QuadraticMarked

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def HasCommonInducedCorrelationFamily
    {τ K I J : Type*} [Fintype I] [Fintype J]
    {s k r N n e degree : ℕ} [NeZero N] {b p q P Z : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ)
    (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
    [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
    {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
    (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T J Z)
    (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
      (hL := A.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
    (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (f : τ → K → ZMod N → ℂ) (B : ℝ) : Prop :=
    ∃ (m : ℕ) (_hm : 0 < m), (m : ℝ) ≤ Real.exp B ∧
            ∃ d : ℕ, d ≤ n * (s + 1) * (t + 1) ^ s + t ∧
              ∃ E : RationalFilteredNilmanifold
                (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
                  D.coefficientWeight D.coefficientIsDependent t) (s + 1) d,
                ∃ M : E.MultidegreeStructure (mixedCorrelationDegree s),
                  M.filtration = D.markedQuotientMultidegree t ∧ M.ComplexityLE B ∧
                  (letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
                     D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
                   letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
                     D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
                       IsModuleTopology.topologicalAddGroup ℝ _
                   letI := realification_moduleTopology_t2 E.basis
                   letI := E.metricSpace
                   ∃ G : J → E.Space → ℂ,
                     (∀ j z, ‖G j z‖ ≤ 2) ∧
                     (∀ j, LipschitzWith ⟨Real.exp B, Real.exp_nonneg _⟩ (G j)) ∧
                     ∀ z, Nonempty (NativeVectorCorrelation degree N B
                       (fun ij : K × ((I × I) × (I × J)) => fun n =>
                         f z ij.1 n * star (G ij.2.2.2 (QuotientGroup.mk
                           ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
                             (correlationInput ((h z).val : ℤ) (n.val : ℤ))
                             (D.localPhaseMarkedOrbit t x y u c h₀ m)))) *
                         star (V.observable ij.2.1.1 (QuotientGroup.mk
                             (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                               (fun _ => (n.val : ℤ)) (v z))) *
                           star (V.observable ij.2.1.2 (QuotientGroup.mk
                             (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                               (fun _ => (n.val : ℤ)) (a z))))) *
                         star (mapDifferenceObservable V U D.dependentQuotientMap hφ ij.2.2 (QuotientGroup.mk
                           (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                             (fun _ => (n.val : ℤ)) (a z)))))))

theorem hasCommonInducedCorrelationFamily_of_model
    {τ K I J : Type*} [Fintype I] [Fintype J]
    {s k r N n e degree : ℕ} [NeZero N] {b p q P Z : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ)
    (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
    [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
    {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
    (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T J Z)
    (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
      (hL := A.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
    (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (f : τ → K → ZMod N → ℂ) (B C : ℝ) (hs : 1 ≤ s)
    (hZ : 0 ≤ Z) (hI : (Fintype.card I : ℝ) ≤ Real.exp Z)
    (hJ : (Fintype.card J : ℝ) ≤ Real.exp Z)
    (hsmall : ∀ z i, |affineCyclicTorusLocalLift u c h₀ (h z) i| ≤ 1 / 4)
    (ha : ∀ z, (a z).log = positiveUnivariate (fun j => (x j).val +
      ∑ i, affineCyclicTorusLocalLift u c h₀ (h z) i • (y j i).val))
    (hcorr : ∀ z, Nonempty (NativeVectorCorrelation degree N Z (fun ij : K × I => fun n =>
      f z ij.1 n * star (V.observable ij.2 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (n.val : ℤ)) (v z)))))))
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp B)
    (d : ℕ) (hdim : d ≤ n * (s + 1) * (t + 1) ^ s + t)
    (E : RationalFilteredNilmanifold
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
    (M : E.MultidegreeStructure (mixedCorrelationDegree s))
    (hMF : M.filtration = D.markedQuotientMultidegree t) (hM : M.ComplexityLE B)
    (hmap : ∀ z : E.RealGroup, z ∈ E.realLattice →
      (⟨(D.markedDependentEvaluation t 0).baseChange ℝ z.coord⟩ : Q.RealGroup) ∈ Q.realLattice)
    (hlat : ∀ b : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (fun i => (b i : ℚ))⟩ : E.filtration.Group) ∈ E.lattice)
    (hobs :
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
          IsModuleTopology.topologicalAddGroup ℝ _
      letI := realification_moduleTopology_t2 E.basis
      letI := E.metricSpace
      ∃ G : J → E.Space → ℂ, (∀ j z, ‖G j z‖ ≤ 2) ∧
        (∀ j, LipschitzWith ⟨Real.exp B, Real.exp_nonneg _⟩ (G j)) ∧
        ∀ j (g : E.RealGroup),
          (∀ i, |torusPhaseLinear (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent t m) g.coord i| ≤ 1 / 4) →
          G j (QuotientGroup.mk g) = markedLocalCoefficientValue
            D.coefficientFreeFiltration D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
            D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t m hm E
            (D.dependentWordIdeal 0 2 0) le_rfl Q hmap (U.observable j) g)
    (hBC : B ≤ C) (hthree : Z + Z + Z ≤ C) :
    D.HasCommonInducedCorrelationFamily (degree := degree) t A Q V U hφ x y u c h₀ h a v f C := by
  unfold HasCommonInducedCorrelationFamily
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hBC), d, hdim, E, M, hMF,
    hM.mono M hBC, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let := E.metricSpace
  obtain ⟨G, hGn, hGL, hGe⟩ := hobs
  refine ⟨G, hGn, ?_, ?_⟩
  · intro j
    exact (hGL j).weaken (show (⟨Real.exp B, Real.exp_nonneg _⟩ : ℝ≥0) ≤
      ⟨Real.exp C, Real.exp_nonneg _⟩ from Real.exp_le_exp.mpr hBC)
  · intro z
    refine Nonempty.map (fun Cz => NativeVectorCorrelation.mono Cz hthree) ?_
    exact D.exists_local_induced_comparison_correlation
      (d := d) (e := e) (k := k) (l := n) (A := K) (I := I) (J := J)
      (degree := degree) (z := Z) (q₁ := Z) (q₂ := Z) (qV := Z) (S := S) (T := T)
      t x y u c h₀ m hm hs E A Q hφ hmap hlat
      V U G hGe (a z) (v z) (h z) (hsmall z) (ha z) (f z) hZ hZ hI hJ
      (Classical.choice (hcorr z))

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem HasCommonInducedCorrelationFamily.mono
    {τ K I J : Type*} [Fintype I] [Fintype J]
    {s k r N n e degree : ℕ} [NeZero N] {b p q P Z : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ)
    (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
    [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
    {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
    (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T J Z)
    (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
      (hL := A.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
    (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (f : τ → K → ZMod N → ℂ) {B C : ℝ}
    (hfamily : D.HasCommonInducedCorrelationFamily (degree := degree) t A Q V U hφ x y u c h₀ h a v f B)
    (hBC : B ≤ C) :
    D.HasCommonInducedCorrelationFamily (degree := degree) t A Q V U hφ x y u c h₀ h a v f C := by
  obtain ⟨m, hm, hmp, d, hdim, E, M, hMF, hM, hobs⟩ := hfamily
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hBC), d, hdim, E, M, hMF,
    hM.mono M hBC, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let := E.metricSpace
  obtain ⟨G, hGn, hGL, hcorr⟩ := hobs
  refine ⟨G, hGn, ?_, ?_⟩
  · intro j
    exact (hGL j).weaken (show (⟨Real.exp B, Real.exp_nonneg _⟩ : ℝ≥0) ≤
      ⟨Real.exp C, Real.exp_nonneg _⟩ from Real.exp_le_exp.mpr hBC)
  · intro z
    exact (hcorr z).map (fun W => W.mono hBC)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {τ K I : Type} [Fintype I] {s r N n degree : ℕ} [NeZero N]
  {b p q P Z : ℝ} {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b}
  {out : Fin W.outputDim} {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
  (D : R.CommonData P) (t : ℕ)
  (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : A.DegreeRankStructure (r + 1))
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : A.UnitVerticalObservable (T.realSubgroup s (r + 1)) I Z)
  (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
  (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (f : τ → K → ZMod N → ℂ)

def HasCoveredInducedCorrelationFamily (B : ℝ) : Prop :=
  ∃ Λ : Subgroup A.filtration.Group, Λ ≤ A.lattice ∧
    ∃ (m : ℕ) (hm : 0 < m)
      (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates A.basis Λ)
      (hout : bchSubgroupCoordinates A.basis Λ ⊆ denominatorGrid m),
      let A₀ := A.withLattice Λ m hm hin hout
      let T₀ := T.withLattice Λ m hm hin hout
      T₀.ComplexityLE B ∧
      ∃ e : ℕ, e ≤ n ∧ ∃ Q : RationalFilteredNilmanifold D.DependentQuotient s e,
        ∃ S : Q.DegreeRankStructure (r + 1),
          S.filtration = D.dependentQuotientFiltration ∧ S.ComplexityLE B ∧
          ∃ hφ : A₀.lattice ≤ Q.lattice.comap (mapOfSteps
            (hL := A₀.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap),
            ∃ V₀ : A₀.UnitVerticalObservable (T₀.realSubgroup s (r + 1)) I B,
              V₀.frequency = V.frequency ∧
              (∀ i z, V₀.observable i (QuotientGroup.mk z) = V.observable i (QuotientGroup.mk z)) ∧
              (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
               letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
                 IsModuleTopology.topologicalAddGroup ℝ _
               letI := realification_moduleTopology_t2 Q.basis
               ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp B ∧
                 ∃ U : Q.UnitVerticalObservable (S.realSubgroup s (r + 1)) (Fin k) B,
                   D.HasCommonInducedCorrelationFamily (degree := degree)
                     t A₀ Q V₀ U hφ x y u c h₀ h a v f B ∧
                   A₀.HasLowerRankOrbitFamily T₀ (fun _ : Unit => 1)
                     (fun z ij w => mapDifferenceObservable V₀ U D.dependentQuotientMap hφ ij
                       (QuotientGroup.mk (A₀.filtration.realification.polynomialOrbitEval
                         (fun _ : Unit => 1) w (a z)))) B)

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem finiteFourierCoeff_convolution (f g : G → ℂ) (χ : AddChar G ℂ) :
    finiteFourierCoeff (finiteConvolution f g) χ = finiteFourierCoeff f χ * finiteFourierCoeff g χ := by
  calc
    _ = 𝔼 x, f x * finiteFourierCoeff (fun y => g (y - x)) χ := by
      simp only [finiteFourierCoeff, finiteConvolution, Finset.expect_mul, Finset.mul_expect]
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro x _
      apply Finset.expect_congr rfl
      intro y _
      ring
    _ = 𝔼 x, f x * (star (χ x) * finiteFourierCoeff g χ) := by
      simp_rw [finiteFourierCoeff_translate]
    _ = _ := by
      change (𝔼 x, f x * (star (χ x) * finiteFourierCoeff g χ)) =
        (𝔼 x, f x * star (χ x)) * finiteFourierCoeff g χ
      rw [Finset.expect_mul]
      apply Finset.expect_congr rfl
      intro x _
      ring

theorem finiteFourierCoeff_reflected_conjugate (f : G → ℂ) (χ : AddChar G ℂ) :
    finiteFourierCoeff (fun x => star (f (-x))) χ = star (finiteFourierCoeff f χ) := by
  rw [finiteFourierCoeff, star_finiteFourierCoeff]
  apply Fintype.expect_equiv (Equiv.neg G)
  intro x
  simp only [Equiv.neg_apply, AddChar.map_neg_eq_inv, AddChar.inv_apply_eq_conj]
  rfl

theorem gowersNorm_two_fourier (f : G → ℂ) :
    gowersNorm 2 f ^ 4 = ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ ^ 4 := by
  let C := finiteConvolution f (fun x => star (f (-x)))
  calc
    _ = 𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x‖ ^ 2 := by
      simpa only [gowersNorm_one, Nat.zero_add, show 2 ^ 2 = 4 by norm_num,
        show 2 ^ 1 = 2 by norm_num] using gowersNorm_derivative 0 f
    _ = 𝔼 h, ‖C h‖ ^ 2 := by
      apply Fintype.expect_equiv (Equiv.neg G)
      intro h
      simp only [C, finiteConvolution, Equiv.neg_apply, neg_sub,
        sub_neg_eq_add, multiplicativeDerivative]
    _ = ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff C χ‖ ^ 2 := (finiteFourier_parseval C).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ _
      simp only [C, finiteFourierCoeff_convolution, finiteFourierCoeff_reflected_conjugate,
        norm_mul, norm_star]
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem cross_correlation_fourier_energy (f g : G → ℂ) :
    (𝔼 h, ‖𝔼 x, f x * star (g (x + h))‖ ^ 2) =
      ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ ^ 2 * ‖finiteFourierCoeff g χ‖ ^ 2 := by
  let C := finiteConvolution f (fun x => star (g (-x)))
  calc
    _ = 𝔼 h, ‖C h‖ ^ 2 := by
      apply Fintype.expect_equiv (Equiv.neg G)
      intro h
      simp only [C, finiteConvolution, Equiv.neg_apply, neg_sub, sub_neg_eq_add]
    _ = ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff C χ‖ ^ 2 := (finiteFourier_parseval C).symm
    _ = _ := by
      simp only [C, finiteFourierCoeff_convolution, finiteFourierCoeff_reflected_conjugate,
        norm_mul, norm_star, mul_pow]

theorem exists_large_fourier_of_mean_cross_correlation (f g : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ χ : AddChar G ℂ, (𝔼 h, ‖𝔼 x, f x * star (g (x + h))‖) ≤ ‖finiteFourierCoeff g χ‖ := by
  classical
  obtain ⟨χ, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun χ : AddChar G ℂ => ‖finiteFourierCoeff g χ‖) Finset.univ_nonempty
  have hmass : (∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2) ≤ 1 := by
    rw [finiteFourier_parseval]
    apply Finset.expect_le Finset.univ_nonempty
    intro x _
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hf x) 2
  have henergy : (𝔼 h, ‖𝔼 x, f x * star (g (x + h))‖ ^ 2) ≤ ‖finiteFourierCoeff g χ‖ ^ 2 := by
    rw [cross_correlation_fourier_energy]
    calc
      _ ≤ ∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2 * ‖finiteFourierCoeff g χ‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro ψ _
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hmax ψ (Finset.mem_univ ψ)) 2) (sq_nonneg _)
      _ = (∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2) * ‖finiteFourierCoeff g χ‖ ^ 2 :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ ‖finiteFourierCoeff g χ‖ ^ 2 := mul_le_of_le_one_left (sq_nonneg _) hmass
  refine ⟨χ, (sq_le_sq₀ (Finset.expect_nonneg (fun _ _ => norm_nonneg _)) (norm_nonneg _)).mp ?_⟩
  exact (expect_square_le (fun h => ‖𝔼 x, f x * star (g (x + h))‖)).trans henergy

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_fourier_of_gowers_two {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ χ : AddChar G ℂ, gowersNorm 2 f ^ 2 ≤ ‖finiteFourierCoeff f χ‖ := by
  classical
  obtain ⟨χ, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun χ : AddChar G ℂ => ‖finiteFourierCoeff f χ‖) Finset.univ_nonempty
  have hmass : (∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2) ≤ 1 := by
    rw [finiteFourier_parseval]
    apply Finset.expect_le Finset.univ_nonempty
    intro x _
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg (f x)) (hf x) 2
  have hfourth : gowersNorm 2 f ^ 4 ≤ ‖finiteFourierCoeff f χ‖ ^ 2 := by
    rw [gowersNorm_two_fourier]
    calc
      _ ≤ ∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ ^ 2 * ‖finiteFourierCoeff f ψ‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro ψ _
        have h := pow_le_pow_left₀ (norm_nonneg (finiteFourierCoeff f ψ))
          (hmax ψ (Finset.mem_univ ψ)) 2
        nlinarith [sq_nonneg (‖finiteFourierCoeff f ψ‖)]
      _ = ‖finiteFourierCoeff f χ‖ ^ 2 * ∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2 :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ ‖finiteFourierCoeff f χ‖ ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass (sq_nonneg ‖finiteFourierCoeff f χ‖)
  refine ⟨χ, (sq_le_sq₀ (sq_nonneg (gowersNorm 2 f)) (norm_nonneg (finiteFourierCoeff f χ))).mp ?_⟩
  simpa only [← pow_mul, show 2 * 2 = 4 by norm_num] using hfourth

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem character_relation_of_quadruple_pos (χ : G → AddChar G ℂ) (a h k : G)
    (hpos : 0 < additiveQuadrupleCorrelation (fun h x => χ h x) a h k) :
    χ (h - a) + χ k = χ h + χ (k - a) := by
  let ψ := χ (h - a) + χ k - χ h - χ (k - a)
  let c := χ (h - a) a * star (χ (k - a) a)
  have hfactor (x : G) :
      star (χ h x) * χ (h - a) (x + a) * χ k x * star (χ (k - a) (x + a)) =
        c * ψ x := by
    simp only [ψ, c, AddChar.sub_apply, AddChar.add_apply, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_conj, Complex.star_def, map_mul]
    ring
  have hmean : (𝔼 x, star (χ h x) * χ (h - a) (x + a) * χ k x *
      star (χ (k - a) (x + a))) = c * (𝔼 x, ψ x) := by
    simp_rw [hfactor]
    exact (Finset.mul_expect _ _ _).symm
  have hψ : ψ = 0 := by
    by_contra hn
    have hz : (𝔼 x, ψ x) = 0 := AddChar.expect_eq_zero_iff_ne_zero.mpr hn
    change 0 < ‖𝔼 x, star (χ h x) * χ (h - a) (x + a) * χ k x *
      star (χ (k - a) (x + a))‖ at hpos
    rw [hmean, hz, mul_zero, norm_zero] at hpos
    exact (lt_irrefl 0) hpos
  apply sub_eq_zero.mp
  calc
    (χ (h - a) + χ k) - (χ h + χ (k - a)) = ψ := by dsimp [ψ]; abel
    _ = 0 := hψ

theorem exists_many_derivative_character_relations
    (f : G → ℂ) (H : Finset G) (χ : G → AddChar G ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hdense : α * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, δ ≤ ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖) :
    ∃ Q : Finset (G × G × G), Q.Nonempty ∧
      (α * δ) ^ 4 / 2 * (Fintype.card G : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        χ (t.2.1 - t.1) + χ t.2.2 = χ t.2.1 + χ (t.2.2 - t.1) := by
  classical
  let g (h x : G) : ℂ := if h ∈ H then χ h x else 0
  have hg (h x : G) : ‖g h x‖ ≤ 1 := by
    dsimp [g]
    split_ifs
    · exact (AddChar.norm_apply _ _).le
    · simp
  have hzero (h : G) (hh : h ∉ H) (x : G) : g h x = 0 := by simp [g, hh]
  have hcorr' (h : G) (hh : h ∈ H) :
      δ ≤ ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖ := by
    simpa only [g, if_pos hh, finiteFourierCoeff] using hcorr h hh
  obtain ⟨Q, hQ, hcard, hrelations⟩ :=
    exists_many_correlated_additive_quadruples f g H hf hg hzero hα hδ hdense hcorr'
  refine ⟨Q, hQ, hcard, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂, h₃, h₄, hlarge⟩ := hrelations t ht
  refine ⟨h₁, h₂, h₃, h₄, character_relation_of_quadruple_pos χ t.1 t.2.1 t.2.2 ?_⟩
  have heq : additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 =
      additiveQuadrupleCorrelation (fun h x => χ h x) t.1 t.2.1 t.2.2 := by
    simp only [additiveQuadrupleCorrelation, g, if_pos h₁, if_pos h₂, if_pos h₃, if_pos h₄]
  rw [heq] at hlarge
  exact lt_of_lt_of_le (by positivity) hlarge

theorem derivative_character_graph_energy [DecidableEq G]
    (f : G → ℂ) (H : Finset G) (χ : G → AddChar G ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hdense : α * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, δ ≤ ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖) :
    (α * δ) ^ 4 / 2 * (Fintype.card G : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H χ) (additiveGraph H χ) : ℝ) := by
  classical
  obtain ⟨Q, _, hcard, hrelations⟩ :=
    exists_many_derivative_character_relations f H χ hf hα hδ hdense hcorr
  have henergy := graph_energy_of_few_quadruple_differences H Q χ {0}
    (fun t ht => let h := hrelations t ht; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (by
      intro t ht
      simp only [Finset.mem_singleton]
      rw [(hrelations t ht).2.2.2.2]
      abel)
  have henergy' : Q.card ≤ Finset.addEnergy (additiveGraph H χ) (additiveGraph H χ) := by
    simpa only [Finset.card_singleton, one_mul] using henergy
  exact hcard.trans (by exact_mod_cast henergy')

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem exists_quadratic_frequency_graph {p : ℝ} (hp : 0 ≤ p)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hG : Real.exp (-p) ≤ gowersNorm 3 f) :
    ∃ H : Finset G, H.Nonempty ∧
      Real.exp (-(128 * (p + 1))) * Fintype.card G ≤ (H.card : ℝ) ∧
      ∃ χ : G → AddChar G ℂ,
        (∀ h ∈ H, Real.exp (-(128 * (p + 1))) ≤
          ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖) ∧
        Real.exp (-(128 * (p + 1))) * (Fintype.card G : ℝ) ^ 3 ≤
          (Finset.addEnergy (additiveGraph H χ) (additiveGraph H χ) : ℝ) := by
  classical
  obtain ⟨H, hH, hdense, hderivative⟩ := exists_many_large_gowers_derivatives 1 f hf hp hG
  choose χ hχ using fun h =>
    exists_large_fourier_of_gowers_two (multiplicativeDerivative f h)
      (multiplicativeDerivative_norm_le_one f hf h)
  let d := derivativeInverseBudget 1 p
  have hd : d = 8 * p + 2 := by norm_num [d, derivativeInverseBudget]
  have hcorr (h : G) (hh : h ∈ H) : Real.exp (-(2 * d)) ≤
      ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖ := by
    calc
      _ = Real.exp (-d) ^ 2 := by rw [pow_two, ← Real.exp_add]; congr 1; ring
      _ ≤ gowersNorm 2 (multiplicativeDerivative f h) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_nonneg _) (hderivative h hh) 2
      _ ≤ _ := hχ h
  have hdP : d ≤ 128 * (p + 1) := by rw [hd]; linarith
  have h2dP : 2 * d ≤ 128 * (p + 1) := by rw [hd]; linarith
  have henergy := derivative_character_graph_energy f H χ hf
    (Real.exp_pos (-d)) (Real.exp_pos (-(2 * d))) hdense hcorr
  have hthreshold : Real.exp (-(128 * (p + 1))) ≤
      (Real.exp (-d) * Real.exp (-(2 * d))) ^ 4 / 2 := by
    rw [derivative_quadruple_exp_threshold]
    calc
      _ ≤ Real.exp (-(12 * d) - 1) := Real.exp_le_exp.mpr (by rw [hd]; linarith)
      _ ≤ _ := exp_sub_one_le_half_exp _
  refine ⟨H, hH, ?_, χ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hdP))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg h2dP)).trans (hcorr h hh)
  · exact (mul_le_mul_of_nonneg_right hthreshold (by positivity)).trans henergy

theorem exists_quadratic_frequency_small_difference {p : ℝ} (hp : 0 ≤ p)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hG : Real.exp (-p) ≤ gowersNorm 3 f) :
    ∃ H : Finset G, H.Nonempty ∧
      Real.exp (-(1024 * (p + 1))) * Fintype.card G ≤ (H.card : ℝ) ∧
      ∃ χ : G → AddChar G ℂ,
        (∀ h ∈ H, Real.exp (-(1024 * (p + 1))) ≤
          ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖) ∧
        ((additiveGraph H χ - additiveGraph H χ).card : ℝ) ≤
          Real.exp (1024 * (p + 1)) * H.card := by
  classical
  obtain ⟨H, hH, hdense, χ, hcorr, henergy⟩ := exists_quadratic_frequency_graph hp f hf hG
  let q := 128 * (p + 1)
  let P := 1024 * (p + 1)
  have hqP : q ≤ P := by dsimp [q, P]; linarith
  have henergy' : (Real.exp q)⁻¹ * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H χ) (additiveGraph H χ) : ℝ) := by
    rw [← Real.exp_neg]
    apply le_trans _ henergy
    gcongr
    exact_mod_cast Finset.card_le_univ H
  obtain ⟨J, hJH, hJ, hsize, hdiff⟩ :=
    exists_large_graph_subset_small_difference H hH χ (Real.exp_pos q) henergy'
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (2 : ℝ) ^ 4 ≤ Real.exp 4 := by
    calc
      _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) htwo 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hfourteen : (2 : ℝ) ^ 14 ≤ Real.exp 14 := by
    calc
      _ ≤ Real.exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) htwo 14
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hnegfour : Real.exp (-4) ≤ ((2 : ℝ) ^ 4)⁻¹ := by
    simpa only [Real.exp_neg, one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2 ^ 4) hfour
  have hsize' : Real.exp (-P) * Fintype.card G ≤ (J.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(2 * q + 4)) * Fintype.card G :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by dsimp [q, P]; linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-4) * (Real.exp (-q) * (Real.exp (-q) * Fintype.card G)) := by
        rw [show -(2 * q + 4) = -4 + -q + -q by ring, Real.exp_add, Real.exp_add]
        ring
      _ ≤ ((2 : ℝ) ^ 4)⁻¹ * (Real.exp (-q) * (Real.exp (-q) * Fintype.card G)) :=
        mul_le_mul_of_nonneg_right hnegfour (by positivity)
      _ ≤ ((2 : ℝ) ^ 4)⁻¹ * (Real.exp (-q) * H.card) := by
        gcongr
      _ = ((2 : ℝ) ^ 4)⁻¹ * (Real.exp q)⁻¹ * H.card := by
        rw [Real.exp_neg]
        ring
      _ ≤ _ := hsize
  refine ⟨J, hJ, hsize', χ, ?_, ?_⟩
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqP)).trans (hcorr h (hJH hh))
  · apply hdiff.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    calc
      (2 : ℝ) ^ 14 * Real.exp q ^ 6 ≤ Real.exp 14 * Real.exp q ^ 6 := by gcongr
      _ = Real.exp (6 * q + 14) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp P := Real.exp_le_exp.mpr (by dsimp [q, P]; linarith)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_cyclic_interval_fourier_smoothing {N : ℕ} [NeZero N]
    (a : ZMod N) (L : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (v : ZMod N → ℂ) (c : AddChar (ZMod N) ℂ → ℂ),
      (∀ x, ‖v x‖ ≤ 1) ∧
      (𝔼 x, ‖finiteIndicator (cyclicInterval a L) x - v x‖) ≤ 2 * δ ∧
      (∑ χ, ‖c χ‖) ≤ 2 / δ ∧ ∀ x, v x = ∑ χ, c χ * χ x := by
  obtain ⟨K, hK, hKN, hsmall, hratio⟩ := exists_smoothing_scale (NeZero.pos N) hδ hδ1
  let I := cyclicInterval a L
  let B := cyclicInterval (0 : ZMod N) K
  have hB : B.Nonempty := cyclicInterval_nonempty 0 hK
  have hcard : B.card = K := cyclicInterval_card 0 hKN
  refine ⟨smoothedIndicator I B,
    (fun χ => finiteFourierCoeff (averagingKernel B) χ * finiteFourierCoeff (finiteIndicator I) χ),
    smoothedIndicator_norm_le_one I hB, ?_, ?_, ?_⟩
  · apply mean_indicator_smoothing_error I hB
    intro h hh
    obtain ⟨m, hm, he⟩ := Finset.mem_image.mp hh
    have hmK : m ≤ K - 1 := by have := Finset.mem_range.mp hm; omega
    have hmreal : (m : ℝ) ≤ δ * N := (Nat.cast_le.mpr hmK).trans hsmall
    have hmean := cyclicInterval_nat_shift_error a L m
    have hhcast : (m : ZMod N) = h := by simpa using he
    rw [hhcast] at hmean
    apply hmean.trans
    apply (div_le_iff₀ (by exact_mod_cast NeZero.pos N : (0 : ℝ) < N)).mpr
    nlinarith
  · have hmass := smoothedIndicator_fourier_mass hB I
    rw [ZMod.card, hcard] at hmass
    exact hmass.trans hratio
  · intro x
    rw [smoothedIndicator_eq_convolution]
    simpa only [finiteFourierCoeff_convolution] using
      (finiteFourier_inversion (finiteConvolution (averagingKernel B) (finiteIndicator I)) x).symm

end Erdos3

end

section

namespace Erdos3

open scoped Pointwise

theorem additiveGraph_difference_card_hom
    {G K L : Type*} [AddCommGroup G] [AddCommGroup K] [AddCommGroup L]
    [DecidableEq G] [DecidableEq K] [DecidableEq L]
    (H : Finset G) (b : G → K) (e : K →+ L) (he : Function.Injective e) :
    (additiveGraph H (fun h => e (b h)) - additiveGraph H (fun h => e (b h))).card =
      (additiveGraph H b - additiveGraph H b).card := by
  let F : G × K →+ G × L := {
    toFun := fun x => (x.1, e x.2)
    map_zero' := by simp
    map_add' := by intro x y; simp }
  have hF : Function.Injective F := by
    intro x y h
    exact Prod.ext (congrArg (fun z : G × L => z.1) h)
      (he (congrArg (fun z : G × L => z.2) h))
  have hgraph : additiveGraph H (fun h => e (b h)) = (additiveGraph H b).image F := by
    unfold additiveGraph
    rw [Finset.image_image]
    rfl
  rw [hgraph]
  apply FreimanModel.card_difference_image_of_freiman
  exact FreimanModel.isAddFreimanIso_of_injOn_iterated_sums F (additiveGraph H b) 2
    hF.injOn hF.injOn

theorem exists_quadratic_affine_frequency_coordinates
    {N : ℕ} [NeZero N] {p : ℝ} (hp : 0 ≤ p) (f : ZMod N → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hG : Real.exp (-p) ≤ gowersNorm 3 f) :
    let P := 1024 * (p + 1)
    ∃ H : Finset (ZMod N), H.Nonempty ∧
      Real.exp (-(P + properAffineRecoveryLogLoss P 1)) * N ≤ (H.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (η ξ : (Fin r → ℤ) →+ ZMod N) (h₀ ξ₀ : ZMod N),
        (r : ℝ) ≤ properAffineRankBound P 1 ∧
        Set.InjOn η (centeredIntegerBox R : Set _) ∧
        ∀ h ∈ H, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x ∧
          Real.exp (-P) ≤ ‖finiteFourierCoeff (multiplicativeDerivative f h)
            (AddChar.zmodAddEquiv (ξ₀ + ξ x))‖ := by
  intro P
  classical
  obtain ⟨H, hH, hdense, χ, hcorr, hsmall⟩ := exists_quadratic_frequency_small_difference hp f hf hG
  let e₀ : AddChar (ZMod N) ℂ ≃+ ZMod N := (AddChar.zmodAddEquiv (n := N)).symm
  let e : AddChar (ZMod N) ℂ →+ (Unit → ZMod N) := {
    toFun := fun c _ => e₀ c
    map_zero' := by ext; simp
    map_add' := by intro c d; ext; simp }
  have he : Function.Injective e := by
    intro c d h
    exact e₀.injective (congrFun h ())
  let b (h : ZMod N) := e (χ h)
  have hsmall' : ((additiveGraph H b - additiveGraph H b).card : ℝ) ≤ Real.exp P * H.card := by
    rw [additiveGraph_difference_card_hom H χ e he]
    exact hsmall
  obtain ⟨J, hJH, hJ, hJdense, r, R, Φ, base, hrank, hproper, hrepr⟩ :=
    exists_small_difference_graph_affine_coordinates N (fun _ : Unit => N) H hH b
      (by dsimp [P]; positivity) hsmall'
  let reduce := FreimanModel.variableIntegerGraphReduction N (fun _ : Unit => N)
  let η := (AddMonoidHom.fst (ZMod N) (Unit → ZMod N)).comp (reduce.comp Φ)
  let ξ : (Fin r → ℤ) →+ ZMod N := {
    toFun := fun x => (reduce (Φ x)).2 ()
    map_zero' := by simp
    map_add' := by intro x y; simp }
  have hdense' : Real.exp (-P) * N ≤ (H.card : ℝ) := by
    simpa only [ZMod.card] using hdense
  have hJdense' : Real.exp (-properAffineRecoveryLogLoss P 1) * H.card ≤ (J.card : ℝ) := by
    simpa only [Fintype.card_unique] using hJdense
  refine ⟨J, hJ, ?_, r, R, η, ξ, (reduce base).1, (reduce base).2 (), ?_, hproper, ?_⟩
  · calc
      _ = Real.exp (-properAffineRecoveryLogLoss P 1) * (Real.exp (-P) * N) := by
        rw [neg_add, Real.exp_add]
        ring
      _ ≤ Real.exp (-properAffineRecoveryLogLoss P 1) * H.card :=
        mul_le_mul_of_nonneg_left hdense' (Real.exp_nonneg _)
      _ ≤ _ := hJdense'
  · simpa only [Fintype.card_unique] using hrank
  · intro h hh
    obtain ⟨x, hx, heq⟩ := hrepr h hh
    have hred : (h, b h) = reduce base + reduce (Φ x) := by
      have h := congrArg reduce heq
      simpa only [reduce, FreimanModel.variableIntegerGraphReduction_lift, map_add] using h
    have hfreq : AddChar.zmodAddEquiv ((reduce base).2 () + ξ x) = χ h := by
      have hv : e₀ (χ h) = (reduce base).2 () + ξ x := congrArg (fun v => v.2 ()) hred
      rw [← hv]
      exact (AddChar.zmodAddEquiv (n := N)).apply_symm_apply _
    refine ⟨x, hx, congrArg Prod.fst hred, ?_⟩
    rw [hfreq]
    exact hcorr h (hJH hh)

theorem exists_quadratic_affine_frequency_coordinates_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ (r : ℕ) (R : Fin r → ℕ) (η ξ : (Fin r → ℤ) →+ ZMod N) (h₀ ξ₀ : ZMod N),
          (r : ℝ) ≤ (p + C) ^ C ∧ Set.InjOn η (centeredIntegerBox R : Set _) ∧
          ∀ h ∈ H, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x ∧
            Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff (multiplicativeDerivative f h)
              (AddChar.zmodAddEquiv (ξ₀ + ξ x))‖ := by
  obtain ⟨C, hC, hbudget⟩ := exists_quadratic_affine_budget
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  obtain ⟨H, hH, hdense, r, R, η, ξ, h₀, ξ₀, hrank, hproper, hcorr⟩ :=
    exists_quadratic_affine_frequency_coordinates hp f hf hG
  obtain ⟨hcost, hrankCost, hcorrCost⟩ := hbudget p hp
  refine ⟨H, hH, ?_, r, R, η, ξ, h₀, ξ₀, hrank.trans hrankCost, hproper, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    obtain ⟨x, hx, hshift, hlarge⟩ := hcorr h hh
    exact ⟨x, hx, hshift, (Real.exp_le_exp.mpr (neg_le_neg hcorrCost)).trans hlarge⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicMixedReflection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def tripleCyclicEmbed {N : ℕ} (x : ZMod N) : ZMod (3 * N) := (x.val : ℕ)

theorem tripleCyclicEmbed_injective {N : ℕ} [NeZero N] :
    Function.Injective (tripleCyclicEmbed (N := N)) := by
  intro x y hxy
  have hN := NeZero.pos N
  have hx : x.val < 3 * N := by have := x.val_lt; omega
  have hy : y.val < 3 * N := by have := y.val_lt; omega
  have hv := congrArg ZMod.val hxy
  simp only [tripleCyclicEmbed, ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] at hv
  exact ZMod.val_injective N hv

theorem tripleCyclicEmbed_expect_le {N : ℕ} [NeZero N]
    (a : ZMod (3 * N)) (g : ZMod (3 * N) → ℝ) (hg : ∀ t, 0 ≤ g t) :
    (𝔼 y : ZMod N, g (a - tripleCyclicEmbed y)) ≤ 3 * (𝔼 t, g t) := by
  classical
  have he : Function.Injective (fun y : ZMod N => a - tripleCyclicEmbed y) := by
    intro x y hxy
    apply tripleCyclicEmbed_injective
    exact sub_right_inj.mp hxy
  have hsum : (∑ y : ZMod N, g (a - tripleCyclicEmbed y)) ≤ ∑ t, g t := by
    calc
      _ = ∑ t ∈ Finset.univ.image (fun y : ZMod N => a - tripleCyclicEmbed y), g t := by
        rw [Finset.sum_image he.injOn]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun t _ _ => hg t)
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, ZMod.card, ZMod.card]
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  calc
    _ ≤ (∑ t, g t) / N := div_le_div_of_nonneg_right hsum hN.le
    _ = _ := by push_cast; field_simp

theorem tripleCyclicEmbed_pair_expect_le {N : ℕ} [NeZero N]
    (z : ZMod N) (g : ZMod (3 * N) → ℝ) (hg : ∀ t, 0 ≤ g t) :
    (𝔼 x : ZMod N, 𝔼 y : ZMod N,
      g (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y)) ≤ 3 * (𝔼 t, g t) := by
  apply (Finset.expect_le_expect (fun x _ =>
    tripleCyclicEmbed_expect_le (tripleCyclicEmbed z - tripleCyclicEmbed x) g hg)).trans_eq
  exact Fintype.expect_const _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_remove_triple_interval {N : ℕ} [NeZero N]
    (z : ZMod N) (a : ZMod (3 * N)) (L : ℕ) (F : ZMod N → ZMod N → ℂ)
    (hF : ∀ x y, ‖F x y‖ ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hcorr : ρ ≤ ‖𝔼 x, 𝔼 y, F x y * finiteIndicator (cyclicInterval a L)
      (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y)‖) :
    ∃ χ : AddChar (ZMod (3 * N)) ℂ, ρ ^ 2 / 48 ≤
      ‖𝔼 x, 𝔼 y, F x y * star (χ (tripleCyclicEmbed x)) * star (χ (tripleCyclicEmbed y))‖ := by
  let δ := ρ / 12
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  obtain ⟨v, c, _, herr, hmass, hsum⟩ := exists_cyclic_interval_fourier_smoothing a L hδ hδ1
  let D (x y : ZMod N) := tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y
  let I := finiteIndicator (cyclicInterval a L)
  have herror : ‖𝔼 x, 𝔼 y, F x y * (I (D x y) - v (D x y))‖ ≤ 6 * δ := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    calc
      _ ≤ 𝔼 x, 𝔼 y, ‖I (D x y) - v (D x y)‖ := by
        apply Finset.expect_le_expect
        intro x _
        apply (RCLike.norm_expect_le (K := ℂ)).trans
        apply Finset.expect_le_expect
        intro y _
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hF x y)
      _ ≤ 3 * (𝔼 t, ‖I t - v t‖) :=
        tripleCyclicEmbed_pair_expect_le z (fun t => ‖I t - v t‖) (fun _ => norm_nonneg _)
      _ ≤ 6 * δ := by linarith
  have hdiff : ‖(𝔼 x, 𝔼 y, F x y * I (D x y)) - (𝔼 x, 𝔼 y, F x y * v (D x y))‖ ≤ 6 * δ := by
    simpa only [mul_sub, Finset.expect_sub_distrib] using herror
  have htriangle : ‖𝔼 x, 𝔼 y, F x y * I (D x y)‖ ≤
      ‖𝔼 x, 𝔼 y, F x y * v (D x y)‖ +
        ‖(𝔼 x, 𝔼 y, F x y * I (D x y)) - (𝔼 x, 𝔼 y, F x y * v (D x y))‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub
      (𝔼 x, 𝔼 y, F x y * v (D x y)) (𝔼 x, 𝔼 y, F x y * I (D x y))
  have hsmoothed : ρ / 2 ≤ ‖𝔼 x, 𝔼 y, F x y * v (D x y)‖ := by
    change ρ ≤ ‖𝔼 x, 𝔼 y, F x y * I (D x y)‖ at hcorr
    dsimp [δ] at hdiff
    linarith
  have heq : (𝔼 x, 𝔼 y, F x y * v (D x y)) =
      ∑ χ, c χ * (𝔼 x, 𝔼 y, F x y * χ (D x y)) := by
    calc
      _ = 𝔼 x, 𝔼 y, ∑ χ, c χ * (F x y * χ (D x y)) := by
        apply Finset.expect_congr rfl
        intro x _
        apply Finset.expect_congr rfl
        intro y _
        rw [hsum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ = _ := by simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  obtain ⟨χ, hχ⟩ := exists_large_weighted_term c
    (fun χ => 𝔼 x, 𝔼 y, F x y * χ (D x y)) (by positivity : 0 < ρ / 2)
    (by positivity : 0 < 2 / δ) hmass (by rwa [← heq])
  have hthreshold : (ρ / 2) / (2 / δ) = ρ ^ 2 / 48 := by
    dsimp [δ]
    field_simp
    ring
  rw [hthreshold] at hχ
  have hfactor : (𝔼 x, 𝔼 y, F x y * χ (D x y)) =
      χ (tripleCyclicEmbed z) *
        (𝔼 x, 𝔼 y, F x y * star (χ (tripleCyclicEmbed x)) * star (χ (tripleCyclicEmbed y))) := by
    simp_rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    simp only [D, addChar_sub_star]
    ring
  rw [hfactor, norm_mul, AddChar.norm_apply, one_mul] at hχ
  exact ⟨χ, hχ⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def tripleCarryStart (N : ℕ) : Fin 3 → ℕ := ![0, 2 * N, N]

def tripleCarryInterval (N : ℕ) (k : Fin 3) : Finset (ZMod (3 * N)) :=
  cyclicInterval (tripleCarryStart N k : ZMod (3 * N)) N

theorem mem_tripleCarryInterval {N : ℕ} [NeZero N] (k : Fin 3) (v : ZMod (3 * N)) :
    v ∈ tripleCarryInterval N k ↔
      tripleCarryStart N k ≤ v.val ∧ v.val < tripleCarryStart N k + N := by
  have hend : tripleCarryStart N k + N ≤ 3 * N := by
    fin_cases k <;> simp [tripleCarryStart] <;> omega
  simpa only [tripleCarryInterval, Nat.add_sub_cancel_left] using
    mem_cyclicInterval_representatives (tripleCarryStart N k) (tripleCarryStart N k + N)
      (by omega) hend v

theorem sum_tripleCarry_indicator {N : ℕ} [NeZero N] (v : ZMod (3 * N)) :
    (∑ k : Fin 3, finiteIndicator (tripleCarryInterval N k) v) = 1 := by
  have hv := v.val_lt
  have hN := NeZero.pos N
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [finiteIndicator, mem_tripleCarryInterval]
  change (if 0 ≤ v.val ∧ v.val < 0 + N then (1 : ℂ) else 0) +
    ((if 2 * N ≤ v.val ∧ v.val < 2 * N + N then 1 else 0) +
      (if N ≤ v.val ∧ v.val < N + N then 1 else 0)) = 1
  simp only [Nat.zero_le, true_and, zero_add]
  by_cases h0 : v.val < N
  · have h1 : ¬(2 * N ≤ v.val ∧ v.val < 2 * N + N) := by omega
    have h2 : ¬(N ≤ v.val ∧ v.val < N + N) := by omega
    simp [h0, h1, h2]
  · by_cases h1 : v.val < 2 * N
    · have h2 : N ≤ v.val ∧ v.val < N + N := by omega
      have h3 : ¬(2 * N ≤ v.val ∧ v.val < 2 * N + N) := by omega
      simp [h0, h2, h3]
    · have h2 : 2 * N ≤ v.val ∧ v.val < 2 * N + N := by omega
      have h3 : ¬(N ≤ v.val ∧ v.val < N + N) := by omega
      simp [h0, h2, h3]

theorem triple_difference_val {N : ℕ} [NeZero N] (z x y : ZMod N) :
    ((tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val : ℤ) =
      if 0 ≤ (z.val : ℤ) - x.val - y.val then (z.val : ℤ) - x.val - y.val
      else (z.val : ℤ) - x.val - y.val + 3 * N := by
  let t : ℤ := (z.val : ℤ) - x.val - y.val
  have hN := NeZero.pos N
  have hz := z.val_lt
  have hx := x.val_lt
  have hy := y.val_lt
  have hlo : -(2 * (N : ℤ)) < t := by dsimp [t]; omega
  have hhi : t < (N : ℤ) := by dsimp [t]; omega
  have hcast : (t : ZMod (3 * N)) =
      tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y := by
    simp [t, tripleCyclicEmbed]
  rw [← hcast, ZMod.val_intCast]
  change t % (3 * (N : ℤ)) = if 0 ≤ t then t else t + 3 * N
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, Int.emod_eq_of_lt ht (by omega)]
  · rw [if_neg ht]
    calc
      t % (3 * (N : ℤ)) = (t + 3 * N) % (3 * (N : ℤ)) := by simp
      _ = t + 3 * N := Int.emod_eq_of_lt (by omega) (by omega)

theorem tripleCarry_representative {N : ℕ} [NeZero N] (z x y : ZMod N) (k : Fin 3)
    (hk : tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y ∈ tripleCarryInterval N k) :
    ((z - x - y).val : ℤ) = (z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val := by
  let t : ℤ := (z.val : ℤ) - x.val - y.val
  have hN := NeZero.pos N
  have hz := z.val_lt
  have hx := x.val_lt
  have hy := y.val_lt
  have hm := triple_difference_val z x y
  have hk' := (mem_tripleCarryInterval k _).mp hk
  have hvalid : 0 ≤ t + (k.val : ℤ) * N ∧ t + (k.val : ℤ) * N < N := by
    change ((tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val : ℤ) =
      (if 0 ≤ t then t else t + 3 * N) at hm
    fin_cases k
    · change 0 ≤ (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val ∧
        (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val < 0 + N at hk'
      change 0 ≤ t + 0 * (N : ℤ) ∧ t + 0 * (N : ℤ) < N
      split_ifs at hm <;> dsimp [t] at * <;> omega
    · change 2 * N ≤ (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val ∧
        (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val < 2 * N + N at hk'
      change 0 ≤ t + 1 * (N : ℤ) ∧ t + 1 * (N : ℤ) < N
      split_ifs at hm <;> dsimp [t] at * <;> omega
    · change N ≤ (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val ∧
        (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val < N + N at hk'
      change 0 ≤ t + 2 * (N : ℤ) ∧ t + 2 * (N : ℤ) < N
      split_ifs at hm <;> dsimp [t] at * <;> omega
  have hcast : ((t + (k.val : ℤ) * N : ℤ) : ZMod N) = z - x - y := by
    simp [t]
  have hv := congrArg (fun v : ZMod N => (v.val : ℤ)) hcast
  rw [ZMod.val_intCast, Int.emod_eq_of_lt hvalid.1 hvalid.2] at hv
  rw [← hv]
  dsimp [t]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_unwrapped_family_reflected_correlation
    {T : Type*} [Fintype T] [Nonempty T] {N : ℕ} [NeZero N] {p : ℝ}
    (hp : 0 ≤ p) (R S : T → ℤ → ℤ → ℂ)
    (hR : ∀ t x n, ‖R t x n‖ ≤ 1) (hS : ∀ t y n, ‖S t y n‖ ≤ 1)
    (z : ZMod N) (b : T → ZMod N → ℂ) (hb : ∀ t x, ‖b t x‖ ≤ 1)
    (hcorr : Real.exp (-p) ≤ ‖𝔼 t, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      R t x.val (z - x - y).val * star (S t y.val (z - x - y).val) * b t x * star (b t y)‖) :
    ∃ (k : Fin 3) (A B : T → ℤ → ℂ),
      (∀ t n, ‖A t n‖ ≤ 1) ∧ (∀ t n, ‖B t n‖ ≤ 1) ∧
      Real.exp (-(2 * p + 10)) ≤ ‖𝔼 t, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
        R t x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
          star (S t y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) *
            A t x.val * B t y.val‖ := by
  let F (k : Fin 3) (x y : ZMod N) := 𝔼 t,
    R t x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
      star (S t y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) * b t x * star (b t y)
  let G (t : T) (x y : ZMod N) :=
    R t x.val (z - x - y).val * star (S t y.val (z - x - y).val) * b t x * star (b t y)
  let D (x y : ZMod N) := tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y
  have hcomm (H : T → ZMod N → ZMod N → ℂ) :
      (𝔼 x, 𝔼 y, 𝔼 t, H t x y) = 𝔼 t, 𝔼 x, 𝔼 y, H t x y := by
    calc
      _ = 𝔼 x, 𝔼 t, 𝔼 y, H t x y := by
        apply Finset.expect_congr rfl
        intro x _
        exact Finset.expect_comm _ _ _
      _ = _ := Finset.expect_comm _ _ _
  have hF (k : Fin 3) (x y : ZMod N) : ‖F k x y‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply (Finset.expect_le_expect (fun t _ => ?_)).trans_eq (Fintype.expect_const (1 : ℝ))
    simp only [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb t y)
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb t x)
    exact (mul_le_of_le_one_left (norm_nonneg _) (hR t _ _)).trans (hS t _ _)
  have hterm (k : Fin 3) (x y : ZMod N) :
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y) =
        (𝔼 t, G t x y) * finiteIndicator (tripleCarryInterval N k) (D x y) := by
    by_cases hk : D x y ∈ tripleCarryInterval N k
    · have hr := tripleCarry_representative z x y k hk
      simp only [finiteIndicator, if_pos hk, mul_one, F, G, hr]
    · simp only [finiteIndicator, if_neg hk, mul_zero]
  have hpoint (x y : ZMod N) :
      (∑ k : Fin 3, F k x y * finiteIndicator (tripleCarryInterval N k) (D x y)) = 𝔼 t, G t x y := by
    simp_rw [hterm]
    rw [← Finset.mul_sum, sum_tripleCarry_indicator, mul_one]
  have hsum : (∑ k : Fin 3, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y)) = 𝔼 t, 𝔼 x, 𝔼 y, G t x y := by
    rw [← hcomm G, ← Finset.expect_sum_comm]
    apply Finset.expect_congr rfl
    intro x _
    rw [← Finset.expect_sum_comm]
    exact Finset.expect_congr rfl (fun y _ => hpoint x y)
  obtain ⟨k, hk⟩ := exists_large_weighted_term (fun _ : Fin 3 => (1 : ℂ))
    (fun k => 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y))
    (Real.exp_pos (-p)) (by norm_num : (0 : ℝ) < 3) (by norm_num)
    (by simpa only [one_mul, hsum, G] using hcorr)
  have hρ1 : Real.exp (-p) / 3 ≤ 1 := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp)
    linarith only [he]
  obtain ⟨χ, hχ⟩ := exists_remove_triple_interval z (tripleCarryStart N k) N (F k) (hF k)
    (by positivity : 0 < Real.exp (-p) / 3) hρ1 hk
  let A (t : T) (n : ℤ) := b t (n : ZMod N) * star (χ (n : ZMod (3 * N)))
  let B (t : T) (n : ℤ) := star (b t (n : ZMod N)) * star (χ (n : ZMod (3 * N)))
  have hAe (t : T) (x : ZMod N) : A t (x.val : ℤ) = b t x * star (χ (tripleCyclicEmbed x)) := by
    simp [A, tripleCyclicEmbed]
  have hBe (t : T) (y : ZMod N) : B t (y.val : ℤ) = star (b t y) * star (χ (tripleCyclicEmbed y)) := by
    simp [B, tripleCyclicEmbed]
  have hfinal : (𝔼 x, 𝔼 y, F k x y * star (χ (tripleCyclicEmbed x)) * star (χ (tripleCyclicEmbed y))) =
      𝔼 t, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
        R t x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
          star (S t y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) * A t x.val * B t y.val := by
    simp_rw [F, Finset.expect_mul, hcomm]
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    rw [hAe, hBe]
    ring
  have htwo : Real.exp (-p) ^ 2 = Real.exp (-(2 * p)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hthreshold : (Real.exp (-p) / 3) ^ 2 / 48 = Real.exp (-(2 * p)) / 432 := by
    rw [div_pow, htwo]
    ring
  have h432 : (432 : ℝ) ≤ Real.exp 10 :=
    (by norm_num : (432 : ℝ) ≤ 2 ^ 10).trans (two_pow_le_exp_of_le 10 le_rfl)
  have hsmall : Real.exp (-(2 * p + 10)) ≤ (Real.exp (-p) / 3) ^ 2 / 48 := by
    rw [hthreshold]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 432)).mpr
    calc
      _ ≤ Real.exp (-(2 * p + 10)) * Real.exp 10 :=
        mul_le_mul_of_nonneg_left h432 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨k, A, B, ?_, ?_, ?_⟩
  · intro t n
    simpa only [A, norm_mul, norm_star, AddChar.norm_apply, mul_one] using hb t (n : ZMod N)
  · intro t n
    simpa only [B, norm_mul, norm_star, AddChar.norm_apply, mul_one] using hb t (n : ZMod N)
  · rw [hfinal] at hχ
    exact hsmall.trans hχ

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_unwrapped_reflected_correlation {N : ℕ} [NeZero N] {p : ℝ}
    (hp : 0 ≤ p) (R S : ℤ → ℤ → ℂ)
    (hR : ∀ x n, ‖R x n‖ ≤ 1) (hS : ∀ y n, ‖S y n‖ ≤ 1)
    (z : ZMod N) (b : ZMod N → ℂ) (hb : ∀ x, ‖b x‖ ≤ 1)
    (hcorr : Real.exp (-p) ≤ ‖𝔼 x : ZMod N, 𝔼 y : ZMod N,
      R x.val (z - x - y).val * star (S y.val (z - x - y).val) * b x * star (b y)‖) :
    ∃ (k : Fin 3) (A B : ℤ → ℂ), (∀ n, ‖A n‖ ≤ 1) ∧ (∀ n, ‖B n‖ ≤ 1) ∧
      Real.exp (-(2 * p + 10)) ≤ ‖𝔼 x : ZMod N, 𝔼 y : ZMod N,
        R x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
          star (S y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) * A x.val * B y.val‖ := by
  let F (k : Fin 3) (x y : ZMod N) :=
    R x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
      star (S y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) * b x * star (b y)
  let G (x y : ZMod N) := R x.val (z - x - y).val * star (S y.val (z - x - y).val) * b x * star (b y)
  let D (x y : ZMod N) := tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y
  have hF (k : Fin 3) (x y : ZMod N) : ‖F k x y‖ ≤ 1 := by
    simp only [F, norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb y)
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb x)
    exact (mul_le_of_le_one_left (norm_nonneg _) (hR _ _)).trans (hS _ _)
  have hterm (k : Fin 3) (x y : ZMod N) :
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y) =
        G x y * finiteIndicator (tripleCarryInterval N k) (D x y) := by
    by_cases hk : D x y ∈ tripleCarryInterval N k
    · have hr := tripleCarry_representative z x y k hk
      simp only [finiteIndicator, if_pos hk, mul_one, F, G, hr]
    · simp only [finiteIndicator, if_neg hk, mul_zero]
  have hpoint (x y : ZMod N) :
      (∑ k : Fin 3, F k x y * finiteIndicator (tripleCarryInterval N k) (D x y)) = G x y := by
    simp_rw [hterm]
    rw [← Finset.mul_sum, sum_tripleCarry_indicator, mul_one]
  have hsum : (∑ k : Fin 3, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y)) = 𝔼 x, 𝔼 y, G x y := by
    rw [← Finset.expect_sum_comm]
    apply Finset.expect_congr rfl
    intro x _
    rw [← Finset.expect_sum_comm]
    exact Finset.expect_congr rfl (fun y _ => hpoint x y)
  obtain ⟨k, hk⟩ := exists_large_weighted_term (fun _ : Fin 3 => (1 : ℂ))
    (fun k => 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y))
    (Real.exp_pos (-p)) (by norm_num : (0 : ℝ) < 3) (by norm_num)
    (by simpa only [one_mul, hsum, G] using hcorr)
  have hρ1 : Real.exp (-p) / 3 ≤ 1 := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp)
    linarith
  obtain ⟨χ, hχ⟩ := exists_remove_triple_interval z (tripleCarryStart N k) N (F k) (hF k)
    (by positivity : 0 < Real.exp (-p) / 3) hρ1 hk
  let A (n : ℤ) := b (n : ZMod N) * star (χ (n : ZMod (3 * N)))
  let B (n : ℤ) := star (b (n : ZMod N)) * star (χ (n : ZMod (3 * N)))
  have hA (n : ℤ) : ‖A n‖ ≤ 1 := by
    simpa only [A, norm_mul, norm_star, AddChar.norm_apply, mul_one] using hb (n : ZMod N)
  have hB (n : ℤ) : ‖B n‖ ≤ 1 := by
    simpa only [B, norm_mul, norm_star, AddChar.norm_apply, mul_one] using hb (n : ZMod N)
  have hAe (x : ZMod N) : A (x.val : ℤ) = b x * star (χ (tripleCyclicEmbed x)) := by
    simp [A, tripleCyclicEmbed]
  have hBe (y : ZMod N) : B (y.val : ℤ) = star (b y) * star (χ (tripleCyclicEmbed y)) := by
    simp [B, tripleCyclicEmbed]
  have htwo : Real.exp (-p) ^ 2 = Real.exp (-(2 * p)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hthreshold : (Real.exp (-p) / 3) ^ 2 / 48 = Real.exp (-(2 * p)) / 432 := by
    rw [div_pow, htwo]
    ring
  have h432 : (432 : ℝ) ≤ Real.exp 10 :=
    (by norm_num : (432 : ℝ) ≤ 2 ^ 10).trans (two_pow_le_exp_of_le 10 le_rfl)
  have hsmall : Real.exp (-(2 * p + 10)) ≤ (Real.exp (-p) / 3) ^ 2 / 48 := by
    rw [hthreshold]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 432)).mpr
    calc
      _ ≤ Real.exp (-(2 * p + 10)) * Real.exp 10 :=
        mul_le_mul_of_nonneg_left h432 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨k, A, B, hA, hB, ?_⟩
  simpa only [F, hAe, hBe, mul_assoc, mul_comm, mul_left_comm] using hsmall.trans hχ

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_cyclic_mixed_reflection (n : ℕ)
    {T : Type} [Fintype T] [Nonempty T] {N : ℕ} [NeZero N] {p : ℝ} (hp : 0 ≤ p)
    (K : T → ℤ → ℤ → (Fin n → ℤ) → ℂ) (hK : ∀ t h m u, ‖K t h m u‖ ≤ 1)
    (f : T → ZMod N → ℂ) (hf : ∀ t x, ‖f t x‖ ≤ 1)
    (A : T → Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ)
    (hA : ∀ t i x, ‖A t i x‖ ≤ 1) (hmiss : ∀ t i, MissesBoxCoordinate (A t i) i)
    (hcorr : Real.exp (-p) ≤ ‖𝔼 t, 𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
      f t (m + h + ∑ i, u i) * K t h.val m.val (fun i => (u i).val) *
        ∏ i, A t i (Fin.cons h (Fin.cons m u))‖) :
    ∃ (z : ZMod N) (k : Fin 3) (B : T → Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ),
      (∀ t i x, ‖B t i x‖ ≤ 1) ∧
      (∀ t i x y, (∀ j, j ≠ i → x j = y j) → B t i x = B t i y) ∧
      let c : ℤ := z.val + (k.val : ℤ) * N
      Real.exp (-(2 * ((2 ^ (n + 1) : ℕ) : ℝ) * p + 10)) ≤
        ‖𝔼 t, 𝔼 u : Fin n → ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
          (K t h.val (c - h.val - h'.val) (fun i => (u i).val) *
            star (K t h'.val (c - h.val - h'.val) (fun i => (u i).val))) *
              ∏ i, B t i (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun j => (u j).val)))‖ := by
  let φ (x : ZMod N) : ℤ := x.val
  let Kcyc (t : T) (h m : ZMod N) (u : Fin n → ZMod N) :=
    K t (φ h) (φ m) (fun i => φ (u i))
  obtain ⟨z, b, hb, hreflect⟩ := exists_mixed_reflected_exp_correlation n Kcyc f A hf hA hmiss hcorr
  let P := ((2 ^ (n + 1) : ℕ) : ℝ) * p
  have hP : 0 ≤ P := mul_nonneg (Nat.cast_nonneg _) hp
  let R (t : T × ((Fin n → ZMod N) × (Fin n → ZMod N))) (h m : ℤ) :=
    mixedTailDifference (K t.1) (fun i => φ (t.2.1 i)) (fun i => φ (t.2.2 i)) h m
  let b' (t : T × ((Fin n → ZMod N) × (Fin n → ZMod N))) (h : ZMod N) :=
    b t.1 t.2.1 t.2.2 h
  have hR : ∀ t h m, ‖R t h m‖ ≤ 1 := fun t h m =>
    mixedTailDifference_norm (K t.1) (hK t.1) _ _ h m
  have hmap (t : T) (u v : Fin n → ZMod N) (h m : ZMod N) :
      mixedTailDifference (Kcyc t) u v h m = R (t, (u, v)) (φ h) (φ m) :=
    mixedTailDifference_map φ (K t) u v h m
  have hinput : Real.exp (-P) ≤
      ‖𝔼 t, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
        R t h.val (z - h - h').val * star (R t h'.val (z - h - h').val) *
          b' t h * star (b' t h')‖ := by
    simpa only [P, neg_mul, b', expect_prod_split, hmap, φ] using
      hreflect.trans (Complex.re_le_norm _)
  obtain ⟨k, B₀, C₀, hB₀, hC₀, hunwrapped⟩ :=
    exists_unwrapped_family_reflected_correlation hP R R hR hR z b'
      (fun t h => hb t.1 t.2.1 t.2.2 h) hinput
  let c : ℤ := z.val + (k.val : ℤ) * N
  have hψ (x : ZMod N) : ((φ x : ℤ) : ZMod N) = x := by
    simp [φ]
  have hanchorInput : Real.exp (-(2 * P + 10)) ≤
      ‖𝔼 t, 𝔼 u : Fin n → ZMod N, 𝔼 v : Fin n → ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
        mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ h) (c - φ h - φ h') *
          star (mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ h')
            (c - φ h - φ h')) * B₀ (t, (u, v)) (φ h) * C₀ (t, (u, v)) (φ h')‖ := by
    simpa only [R, c, φ, expect_prod_split] using hunwrapped
  obtain ⟨B, hB, hBind, hfinal⟩ := exists_anchored_reflected_family φ
    (fun x : ℤ => (x : ZMod N)) hψ K hK c
    (fun t u v h => B₀ (t, (u, v)) h) (fun t u v h => C₀ (t, (u, v)) h)
    (fun t u v h => hB₀ (t, (u, v)) h) (fun t u v h => hC₀ (t, (u, v)) h) hanchorInput
  refine ⟨z, k, B, hB, hBind, ?_⟩
  simpa only [P, mul_assoc, c, φ] using hfinal

end Erdos3

end

end OAI

end


