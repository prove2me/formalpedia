-- Prove2me | Definitions.Def_OAIQ244Duke024
-- name    : OAIQ244Duke024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:15:59.211865+00:00
-- url     : https://prove2.me/theorems/15e33719-47cd-477f-b2da-40581d17ba15
-- title:
--   Definitions bundle OAIQ244Duke024 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 144 declarations of OpenAI's Lean: 38 definitions, 15 instances and 91 theorems. The definitions and types are `OAI.DukePrimeDegree.LowerInitial`, `OAI.DukePrimeDegree.UpperInitial`, `OAI.PrimeDegreePackets.arithmeticFlowGaussian`, `OAI.PrimeDegreePackets.complexFlowGaussian`, `OAI.PrimeDegreePackets.conditionalObservationEntropy`, `OAI.PrimeDegreePackets.conditionalSigmaEntropy`, `OAI.PrimeDegreePackets.fractionalIdealNonzeroIntegerEquiv`, `OAI.PrimeDegreePackets.fullLatticeInclusionMatrix`, `OAI.PrimeDegreePackets.futureName`, `OAI.PrimeDegreePackets.idealClassPartitionEquiv`, `OAI.PrimeDegreePackets.integralIdealFullEquiv`, `OAI.PrimeDegreePackets.localLatticeQuotient`, `OAI.PrimeDegreePackets.localLatticeQuotientMap`, `OAI.PrimeDegreePackets.localProductConstant`, `OAI.PrimeDegreePackets.nonzeroIntegerRowEquiv`, `OAI.PrimeDegreePackets.orderedComplexEmbeddings`, `OAI.PrimeDegreePackets.orderedDeletedPlacesEquiv`, `OAI.PrimeDegreePackets.orderedEuclideanMap`, `OAI.PrimeDegreePackets.orderedIdealBasis`, `OAI.PrimeDegreePackets.packetUnitKernel`, `OAI.PrimeDegreePackets.positiveUnitStabilizer`, `OAI.PrimeDegreePackets.powerfulFunction`, `OAI.PrimeDegreePackets.powerfulMoment`, `OAI.PrimeDegreePackets.powerfulRepresentation`, `OAI.PrimeDegreePackets.primaryIdealSingletonEquiv`, `OAI.PrimeDegreePackets.primeIdealEulerFactor`, `OAI.PrimeDegreePackets.primeIdealTowerEquiv`, `OAI.PrimeDegreePackets.productFiberIntegral`, `OAI.PrimeDegreePackets.realEmbeddingMap`, `OAI.PrimeDegreePackets.saturationIdealUnit`, `OAI.PrimeDegreePackets.siegelTransform`, `OAI.PrimeDegreePackets.signedFlowSum`, `OAI.PrimeDegreePackets.signedGlobalLabelEquiv`, `OAI.PrimeDegreePackets.totallyRealCompletedXi`, `OAI.PrimeDegreePackets.traceDualFullLattice`, `OAI.PrimeDegreePackets.twoSidedTube`, `OAI.PrimeDegreePackets.unitOrbitMellinKernel`, `OAI.PrimeDegreePackets.unitStabilizer`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_Topology`, `DukePrimeDegree_Dynamics_BlockEliminationSchedule`, `DukePrimeDegree_Geometry_MatrixConjugationDensity`, `DukePrimeDegree_Geometry_PluckerCovariance`, `PrimePackets_ConditionalObservations`, `PrimePackets_ConditionalSigmaEntropy`, `PrimePackets_DiscriminantBounds`, `PrimePackets_DivisorBounds`, `PrimePackets_ErgodicDecomposition`, `PrimePackets_FutureEntropyIncrements`, `PrimePackets_GaussianMellin`, `PrimePackets_IdealNorms`, `PrimePackets_IdealThetaFlow`, `PrimePackets_LatticeDuality`, `PrimePackets_LatticeTheta`, `PrimePackets_LocalEuler`, `PrimePackets_LocalModels`, `PrimePackets_OrbitProbability`, `PrimePackets_PacketAlgebra`, `PrimePackets_PowerfulIdeals`, `PrimePackets_PrimeFactors`, `PrimePackets_RootOverlaps`, `PrimePackets_RootRelations`, `PrimePackets_SplitEuler`, `PrimePackets_XiBoundary`, `PrimePackets_ZetaResidues`, `Ramification_HilbertRamification_ResidueExactSequence`, `Ramification_HilbertRamification_ValuationSubring`.
--
--   **Imports.** It imports the published bundle `Def_DukePrimeDegree`; the bundles `OAIQ244Duke002`, `OAIQ244Duke005`, `OAIQ244Duke006`, `OAIQ244Duke008`, `OAIQ244Duke011`, `OAIQ244Duke012` and `OAIQ244Duke013` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke036`; the statements `OAI.DukePrimeDegree.EliminationChain.predecessor_root_information`, `OAI.DukePrimeDegree.countable_patch_name_entropy_sublinear`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_eq_totallyReal`, `OAI.PrimeDegreePackets.integrable_weightedIdealUnitOrbits`, `OAI.PrimeDegreePackets.integral_unitOrbitMellinKernel`, `OAI.PrimeDegreePackets.totallyRealCompletedXi_logDeriv_re` and `OAI.PrimeDegreePackets.tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top`; the proofs of `OAI.DukePrimeDegree.EliminationChain.predecessor_root_information`, `OAI.DukePrimeDegree.completedXiGap_of_exceptionalRealZeroExclusion`, `OAI.DukePrimeDegree.diagonal_entropy_zero_of_atomic_positive_roots`, `OAI.DukePrimeDegree.exceptionalRealZeroExclusion_of_ray_realizations`, `OAI.DukePrimeDegree.exists_noncentral_neutral_return_sequence`, `OAI.DukePrimeDegree.extension_multiplicity_pos_of_ray_realizations`, `OAI.DukePrimeDegree.logRegularized_deriv_bound_of_completedXi_gap`, `OAI.DukePrimeDegree.no_odd_index_positive_zero_of_cyclic_characters`, `OAI.DukePrimeDegree.no_odd_index_zero_sign`, `OAI.PrimeDegreePackets.HeckeMellin.boundedDegree_near_one_zero_real_simple_unique`, `OAI.PrimeDegreePackets.HeckeMellin.completedIdealClassXi_eq`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_conj_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_eq_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_functionalEquation_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_logDeriv_base_le_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.dedekindXiZeros_ne_one_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.dedekindXiZeros_ne_zero_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.dedekindXi_realZeroPole_nonneg_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.idealThetaXi_reflection_totallyReal`, `OAI.PrimeDegreePackets.coprime_ideal_scaled_interval`, `OAI.PrimeDegreePackets.integrable_weightedIdealUnitOrbits` and `OAI.PrimeDegreePackets.totallyRealCompletedXi_logDeriv_re`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke002
import Definitions.Def_OAIQ244Duke005
import Definitions.Def_OAIQ244Duke006
import Definitions.Def_OAIQ244Duke008
import Definitions.Def_OAIQ244Duke011
import Definitions.Def_OAIQ244Duke012
import Definitions.Def_OAIQ244Duke013

section
-- module Solutions.OAIQ244_DUKE.Compat
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Topology
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The idele topology

The idele group `I_K` carries the restricted-product topology. This file records
the topological-group structure and the continuity of every local
component map.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

instance finiteIdeleGroupT2Space :
    T2Space (FiniteIdeleGroup K) :=
  inferInstance

instance infiniteIdeleGroupT2Space :
    T2Space (InfiniteIdeleGroup K) :=
  inferInstance

instance ideleGroupT2Space :
    T2Space (IdeleGroup K) :=
  inferInstance
end
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketAlgebra
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.globalLabels_smul_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module

universe u
open scoped TensorProduct
open Set Module
namespace PrimeDegreePackets

open scoped NumberField Pointwise nonZeroDivisors
open NumberField


lemma completedFractionalIdeal_mono {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] {I J : FractionalIdeal (𝓞 K)⁰ K} (h : I ≤ J) :
    completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) ≤ completedFractionalIdeal p J :=
  Submodule.span_mono (Set.image_mono h)

lemma completedFractionalIdeal_add {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I J : FractionalIdeal (𝓞 K)⁰ K) :
    completedFractionalIdeal p (I+J) = completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) ⊔ completedFractionalIdeal p J := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨a,ha,b,hb,rfl⟩ := (FractionalIdeal.mem_add I J x).mp hx
    rw [map_add]
    exact Submodule.add_mem _ ((show completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) ≤ _ from le_sup_left) (Submodule.subset_span ⟨a,ha,rfl⟩))
      ((show completedFractionalIdeal p J ≤ _ from le_sup_right) (Submodule.subset_span ⟨b,hb,rfl⟩))
  · apply sup_le
    · exact completedFractionalIdeal_mono p (show I ≤ I+J from le_sup_left)
    · exact completedFractionalIdeal_mono p (show J ≤ I+J from le_sup_right)

lemma completedFractionalIdeal_zero {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : completedFractionalIdeal p (0 : FractionalIdeal (𝓞 K)⁰ K) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨x,hx,rfl⟩
  have hx' : x = 0 := (FractionalIdeal.mem_zero_iff (𝓞 K)⁰).mp hx
  simp [hx']

lemma completedFractionalIdeal_ne_bot {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) ≠ ⊥ := by
  intro h
  apply hI
  apply le_antisymm _ bot_le
  intro x hx
  have H : (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) x ∈
      completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := Submodule.subset_span ⟨x,hx,rfl⟩
  rw [h] at H
  have H' : (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) x = 0 := H
  apply (FractionalIdeal.mem_zero_iff (𝓞 K)⁰).mpr
  exact (RingHom.injective (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K).toRingHom).eq_iff.mp (by simpa using H')

 

lemma completedFractionalIdeal_singleton_mul {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : FractionalIdeal (𝓞 K)⁰ K) (a : K) :
    completedFractionalIdeal p (FractionalIdeal.spanSingleton (𝓞 K)⁰ a * I) =
      (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) a •
        completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := by
  unfold completedFractionalIdeal
  rw [← Submodule.span_smul]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_smul_set]
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨z,hz,hyz⟩ := (FractionalIdeal.mem_singleton_mul).mp hy
    subst y
    exact ⟨_,⟨z,hz,rfl⟩,by simp [smul_eq_mul]⟩
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    refine ⟨a*z,?_,by simp [smul_eq_mul]⟩
    exact (FractionalIdeal.mem_singleton_mul).mpr ⟨z,hz,rfl⟩

lemma completedFractionalIdeal_nat_mul {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : FractionalIdeal (𝓞 K)⁰ K) (q : ℕ) :
    completedFractionalIdeal p (FractionalIdeal.spanSingleton (𝓞 K)⁰ (q : K) * I) =
      (q : PadicInt p) • completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [completedFractionalIdeal_singleton_mul]
  ext x
  simp only [Submodule.mem_smul_pointwise_iff_exists, map_natCast,
    Nat.cast_smul_eq_nsmul]



lemma completedFractionalIdeal_mul {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I J : FractionalIdeal (𝓞 K)⁰ K) :
    completedFractionalIdeal p (I*J) = completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) * completedFractionalIdeal p J := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    refine FractionalIdeal.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [map_mul]
      exact Submodule.mul_mem_mul (Submodule.subset_span ⟨a,ha,rfl⟩)
        (Submodule.subset_span ⟨b,hb,rfl⟩)
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · exact Submodule.mul_le.mpr (fun _ hx _ hy => completedFractionalIdeal_mul_mem p I J hx hy)



theorem completedMaximalOrder_unit_of_smul_eq {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (u : (LocalAlgebra p K)ˣ)
    (h : (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule =
      (completedMaximalOrder (K := K) p).toSubmodule) :
    ∃ v : (completedMaximalOrder (K := K) p)ˣ,
      ((v : completedMaximalOrder (K := K) p) : LocalAlgebra p K) = u := by
  let R := completedMaximalOrder (K := K) p
  have hu : (u : LocalAlgebra p K) ∈ R := by
    rw [← Subalgebra.mem_toSubmodule,← h]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨1,R.one_mem,by simp⟩
  have hui : (↑(u⁻¹) : LocalAlgebra p K) ∈ R := by
    obtain ⟨x,hx,hxu⟩ := (Submodule.mem_smul_pointwise_iff_exists 1 (↑u) R.toSubmodule).mp
      (h.symm ▸ R.one_mem)
    have he : x = (↑(u⁻¹) : LocalAlgebra p K) := by
      change (u : LocalAlgebra p K) * x = 1 at hxu
      have H := congrArg (fun y : LocalAlgebra p K => ↑(u⁻¹) * y) hxu
      simpa only [smul_eq_mul,← mul_assoc,Units.inv_mul,one_mul,mul_one] using H
    exact he ▸ hx
  refine ⟨⟨⟨u,hu⟩,⟨↑(u⁻¹),hui⟩,?_,?_⟩,rfl⟩ <;>
    apply Subtype.ext <;> simp

lemma saturationFractionalIdeal_ne_zero {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : saturationFractionalIdeal M ≠ 0 := by
  intro h
  have hbot : M.carrier = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hx' : x ∈ saturationFractionalIdeal M := Submodule.subset_span hx
    simpa [h] using hx'
  have H : (⊥ : Submodule ℚ K) = ⊤ := by simpa [hbot] using M.spans
  exact bot_ne_top H


theorem completed_saturation {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    completedFractionalIdeal p (saturationFractionalIdeal M) =
      (completedMaximalOrder (K := K) p).toSubmodule * completedLattice p M := by
  let f : K →ₐ[ℚ] LocalAlgebra p K := Algebra.TensorProduct.includeRight
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    change x ∈ Submodule.span (𝓞 K) (M.carrier : Set K) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have h1 : (1 : LocalAlgebra p K) ∈ (completedMaximalOrder (K := K) p).toSubmodule :=
        (completedMaximalOrder (K := K) p).one_mem
      have H := Submodule.mul_mem_mul h1
        (Submodule.subset_span ⟨x,hx,rfl⟩ : f x ∈ completedLattice p M)
      simp only [one_mul] at H
      exact H
    | zero => simp
    | add x y hx hy ihx ihy =>
      change f (x+y) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      change f ((a : K) * x) ∈ _
      rw [map_mul]
      have ha : f a ∈ completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K) :=
        Submodule.subset_span ⟨a,(FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr ⟨a,rfl⟩,rfl⟩
      have H := Submodule.mul_mem_mul ha ih
      rw [← mul_assoc] at H
      have hR : (completedMaximalOrder (K := K) p).toSubmodule *
          (completedMaximalOrder (K := K) p).toSubmodule =
          (completedMaximalOrder (K := K) p).toSubmodule := by
        simp only [completedMaximalOrder_toSubmodule,← completedFractionalIdeal_mul,one_mul]
      rw [show completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K) =
        (completedMaximalOrder (K := K) p).toSubmodule from rfl,hR] at H
      exact H
  · apply Submodule.mul_le.mpr
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a,ha,rfl⟩ := hx
      obtain ⟨a,rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp ha
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨b,hb,rfl⟩ := hy
        rw [← map_mul]
        exact Submodule.subset_span ⟨(a : K)*b,
          Submodule.smul_mem _ a (Submodule.subset_span hb),rfl⟩
      | zero => simp
      | add x y hx hy ihx ihy =>
        rw [mul_add]
        exact Submodule.add_mem _ ihx ihy
      | smul c x hx ih =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ c ih
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [add_mul]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ih =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c ih


lemma completedMaximalOrder_unit_smul {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (v : (completedMaximalOrder (K := K) p)ˣ) :
    ((v : completedMaximalOrder (K := K) p) : LocalAlgebra p K) •
        (completedMaximalOrder (K := K) p).toSubmodule =
      (completedMaximalOrder (K := K) p).toSubmodule := by
  let R := completedMaximalOrder (K := K) p
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact R.mul_mem (v : R).property hy
  · intro hx
    apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    refine ⟨((v⁻¹ : Rˣ) : R) * x,R.mul_mem ((v⁻¹ : Rˣ) : R).property hx,?_⟩
    change (↑(v : R) : LocalAlgebra p K) * (↑(↑(v⁻¹) : R) * x) = x
    have hv : (↑(v : R) : LocalAlgebra p K) * (↑(↑(v⁻¹) : R) : LocalAlgebra p K) = 1 := by
      exact congrArg (fun r : R => (r : LocalAlgebra p K)) v.mul_inv
    rw [← mul_assoc, hv, one_mul]

lemma local_saturation_homothety {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (c : (LocalAlgebra p K)ˣ)
    (h : completedLattice p N = (c : LocalAlgebra p K) • completedLattice p M) :
    completedFractionalIdeal p (saturationFractionalIdeal N) =
      (c : LocalAlgebra p K) • completedFractionalIdeal p (saturationFractionalIdeal M) := by
  rw [completed_saturation,completed_saturation,h,mul_smul_comm]

 

theorem local_scalar_choice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (i j c : (LocalAlgebra p K)ˣ)
    (hi : completedFractionalIdeal p (saturationFractionalIdeal N) =
      (i : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule)
    (hj : completedFractionalIdeal p (saturationFractionalIdeal M) =
      (j : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule)
    (h : completedLattice p N = (c : LocalAlgebra p K) • completedLattice p M) :
    ∃ z : (completedMaximalOrder (K := K) p)ˣ,
      completedLattice p N =
        ((i : LocalAlgebra p K) * ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) *
          (↑(j⁻¹) : LocalAlgebra p K)) • completedLattice p M := by
  let u : (LocalAlgebra p K)ˣ := i⁻¹*c*j
  have hu : (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule =
      (completedMaximalOrder (K := K) p).toSubmodule := by
    have H := local_saturation_homothety M N p c h
    rw [hi,hj,← mul_smul] at H
    calc
      (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule =
          (↑(i⁻¹) : LocalAlgebra p K) •
            (((c : LocalAlgebra p K)*(j : LocalAlgebra p K)) •
              (completedMaximalOrder (K := K) p).toSubmodule) := by
            simp [u,mul_smul,mul_assoc]
      _ = (↑(i⁻¹) : LocalAlgebra p K) •
            ((i : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule) := by rw [← H]
      _ = _ := by rw [← mul_smul,Units.inv_mul,one_smul]
  obtain ⟨z,hz⟩ := completedMaximalOrder_unit_of_smul_eq p u hu
  refine ⟨z,?_⟩
  rw [hz]
  have H : (i : LocalAlgebra p K) * (u : LocalAlgebra p K) * (↑(j⁻¹) : LocalAlgebra p K) = c := by
    simp [u,mul_assoc]
  rw [H]
  exact h



lemma fullLattice_clear_denominator {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (x : K) : ∃ z : ℤ, z ≠ 0 ∧ z • x ∈ M.carrier := by
  have hx : x ∈ Submodule.span ℚ (M.carrier : Set K) := by rw [M.spans]; trivial
  obtain ⟨y, hy, z, hz⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors ℤ)).mp hx
  rw [Submodule.span_eq] at hy
  refine ⟨z, mem_nonZeroDivisors_iff_ne_zero.mp z.property, ?_⟩
  rw [hz, ← IsScalarTower.algebraMap_smul ℚ, smul_smul,
    IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self, one_smul]
  exact hy


def saturationIdealUnit {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (saturationFractionalIdeal M) (saturationFractionalIdeal_ne_zero M)

lemma local_smul_mono {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (a : LocalAlgebra p K)
    {L N : Submodule (PadicInt p) (LocalAlgebra p K)} (h : L ≤ N) :
    a • L ≤ a • N := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y,h hy,rfl⟩


abbrev localLatticeQuotient {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (p : ℕ) [Fact p.Prime] :=
  (completedLattice p M) ⧸
    ((completedLattice p N).comap (completedLattice p M).subtype).toAddSubgroup

def localLatticeQuotientMap {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    M.carrier →+ localLatticeQuotient M N p :=
  (QuotientAddGroup.mk'
    ((completedLattice p N).comap (completedLattice p M).subtype).toAddSubgroup).comp
    (completionEmbedding M p).toAddMonoidHom



open Topology
open scoped Pointwise

open Polynomial



open scoped NNReal

open Polynomial
open scoped BigOperators

open IsDiscreteValuationRing IsLocalRing Module


open MeasureTheory
open scoped ENNReal

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_OrbitProbability
attribute [-instance] _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing

open Filter
open scoped BigOperators Topology
namespace PrimeDegreePackets



theorem finite_product_subpolynomial (f : ℕ → ℝ)
    (hf0 : ∀ p, 1 ≤ p → 0 ≤ f p) (hf : Tendsto f atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset ℕ, (∀ p ∈ S, 1 ≤ p) →
      (∏ p ∈ S, f p) ≤ C * (∏ p ∈ S, (p : ℝ)) ^ ε := by
  have hlarge : ∀ᶠ p : ℕ in atTop, f p ≤ (p : ℝ) ^ ε := by
    have hpow : Tendsto (fun p : ℕ => (p : ℝ) ^ ε) atTop atTop :=
      (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
    filter_upwards [hf.eventually_le_const (by norm_num : (1 : ℝ) < 2),
      hpow.eventually (eventually_ge_atTop (2 : ℝ))] with p hfp hpp
    exact hfp.trans hpp
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  let g : ℕ → ℝ := fun p => max 1 (f p)
  have hg : ∀ p, 1 ≤ g p := fun p => le_max_left _ _
  have hgpos : ∀ p, 0 < g p := fun p => lt_of_lt_of_le zero_lt_one (hg p)
  refine ⟨∏ p ∈ Finset.range N, g p, Finset.prod_pos (fun p _ => hgpos p), ?_⟩
  intro S hS
  have hpow : ∀ p ∈ S, 1 ≤ (p : ℝ) ^ ε := by
    intro p hp
    exact Real.one_le_rpow (by exact_mod_cast hS p hp) hε.le
  calc
    (∏ p ∈ S, f p) ≤ ∏ p ∈ S, (if p < N then g p else 1) * (p : ℝ) ^ ε := by
      apply Finset.prod_le_prod (fun p hp => hf0 p (hS p hp))
      intro p hp
      by_cases hpN : p < N
      · simp only [ite_eq_left hpN]
        exact (le_max_right 1 (f p)).trans (le_mul_of_one_le_right (hgpos p).le (hpow p hp))
      · simpa only [ite_eq_right hpN, one_mul] using hN p (Nat.le_of_not_gt hpN)
    _ = (∏ p ∈ S with p < N, g p) * (∏ p ∈ S, (p : ℝ) ^ ε) := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_filter]
    _ ≤ (∏ p ∈ Finset.range N, g p) * (∏ p ∈ S, (p : ℝ) ^ ε) := by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun p hp => (hpow p hp).trans' zero_le_one))
      apply Finset.prod_le_prod_of_subset_of_one_le
      · intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      · intro p _
        exact (hgpos p).le
      · intro p _ _
        exact hg p
    _ = (∏ p ∈ Finset.range N, g p) * (∏ p ∈ S, (p : ℝ)) ^ ε := by
      congr 1
      exact Real.finsetProd_rpow S _ (fun p _ => Nat.cast_nonneg p) ε

 

theorem localMajorant_product_le (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (q : ℝ),
      (∀ p ∈ S, 1 ≤ p) → (∏ p ∈ S, (p : ℝ)) ≤ q →
      (∏ p ∈ S, localMajorant n p) ≤ C * q ^ ε := by
  obtain ⟨C, hC, hprod⟩ := finite_product_subpolynomial (localMajorant n)
    (localMajorant_nonneg n) (localMajorant_tendsto_one n) ε hε
  refine ⟨C, hC, ?_⟩
  intro S q hS hq
  apply (hprod S hS).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)) hq hε.le

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeFactors
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators

 
def localProductConstant (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ℝ :=
  (localMajorant_product_le n ε hε).choose

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory NumberField IsDiscreteValuationRing
open scoped ENNReal Pointwise nonZeroDivisors



lemma model_generator_components_ne_zero {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] {ι : Type*} {R : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, Nontrivial (R i)] [∀ i, Algebra (PadicInt p) (R i)]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] ∀ i, R i)
    (v : (LocalAlgebra p K)ˣ) (hv : (v : LocalAlgebra p K) ∈ completedMaximalOrder (K := K) p)
    (i : ι) : E ⟨v,hv⟩ i ≠ 0 := by
  have hu : (⟨v,hv⟩ : completedMaximalOrder (K := K) p) ∈
      nonZeroDivisors (completedMaximalOrder (K := K) p) :=
    mem_nonZeroDivisors_of_injective (f := (completedMaximalOrder (K := K) p).val)
      Subtype.val_injective v.isUnit.mem_nonZeroDivisors
  apply nonZeroDivisor_component_ne_zero (i := i)
  rw [← MulEquivClass.map_nonZeroDivisors E]
  exact ⟨⟨v,hv⟩,hu,rfl⟩



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalModels
attribute [-instance] _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.globalLabels_smul_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology


namespace PrimeDegreePackets
open NumberField
open scoped BigOperators Pointwise NumberField nonZeroDivisors ENNReal


lemma fullLattice_ideal_relIndex {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : Module.finrank ℚ K = n) (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
    (fractionalIdealFullLattice hn (nonzeroIntegralIdealUnit J)).carrier.toAddSubgroup.relIndex
      (fractionalIdealFullLattice hn 1).carrier.toAddSubgroup = Ideal.absNorm J.1 := by
  change ((J.1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).toAddSubgroup.relIndex
    ((1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).toAddSubgroup = _
  rw [← show ((⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 1 from by simp,
    integralIdeal_subgroup_map J.1, integralIdeal_subgroup_map ⊤,
    AddSubgroup.relIndex_map_map_of_injective _ _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
  change J.1.toAddSubgroup.relIndex ⊤ = _
  rw [AddSubgroup.relIndex_top_right]
  rfl

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_DivisorBounds
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset


namespace PrimeDegreePackets
open Finset Nat


lemma powerful_square_cube {m : ℕ} (hm : IsPowerful m) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ^ 2 * b ^ 3 = m := by
  obtain ⟨b, c, hb, hc, hbc, hbs⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hm.1)
  have hbcdiv : b ∣ c := by
    apply (Nat.factorization_le_iff_dvd (by omega : b ≠ 0) (by omega : c ≠ 0)).mp
    intro p
    by_cases hp0 : b.factorization p = 0
    · simp [hp0]
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hp0)
    have hpb : p ∣ b := (hp.dvd_iff_one_le_factorization (by omega : b ≠ 0)).mpr (by omega)
    have hpm : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr
      ⟨hp, hbc ▸ dvd_mul_of_dvd_right hpb (c^2), hm.1⟩
    have htwo := hm.2 p hpm
    have hbone := hbs.natFactorization_le_one p
    have heq : m.factorization p = 2 * c.factorization p + b.factorization p := by
      rw [← hbc, Nat.factorization_mul (by positivity) (by omega : b ≠ 0), Nat.factorization_pow]
      simp
    omega
  obtain ⟨a, ha⟩ := hbcdiv
  have ha0 : 0 < a := by
    by_contra h
    have : a = 0 := by omega
    simp [this] at ha
    omega
  refine ⟨a, b, ha0, hb, ?_⟩
  rw [← hbc, ha]
  ring



noncomputable def powerfulRepresentation (m : {m : ℕ // IsPowerful m}) : ℕ × ℕ :=
  ⟨(powerful_square_cube m.property).choose,
    ((powerful_square_cube m.property).choose_spec).choose⟩

end PrimeDegreePackets


namespace PrimeDegreePackets
open Finset Nat

noncomputable def powerfulMoment (k : ℕ) : ℝ :=
  ∑' m : ℕ, powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4)

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PowerfulIdeals
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
namespace PrimeDegreePackets
open Finset Nat


def powerfulFunction (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨powerfulCorrection k, powerfulCorrection_zero k⟩

end PrimeDegreePackets

open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve

open scoped BigOperators Classical
open Finset Nat
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalEuler
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
namespace PrimeDegreePackets
open NumberField
open scoped BigOperators ENNReal nonZeroDivisors

 

def primaryIdealSingletonEquiv (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) : primaryIntegralIdeals K {p} ≃ PrimaryIdeal K p where
  toFun J := ⟨J.1.1,J.1.2,by
    have hk := Nat.eq_prime_pow_of_unique_prime_dvd
      (Ideal.absNorm_eq_zero_iff.not.mpr J.1.2) (fun {r} hr hd => by simpa using J.2 r hr hd)
    exact fun P hP => ideal_factor_mem_over K hp hk hP⟩
  invFun I := ⟨⟨I.1,I.2.1⟩,by
    intro r hr hd
    obtain ⟨k,hk⟩ := primary_ideal_norm_power K hp I
    rw [hk] at hd
    have he := (Nat.dvd_prime hp).mp (hr.dvd_of_dvd_pow hd)
    simpa using he.resolve_left hr.ne_one⟩
  left_inv _ := rfl
  right_inv _ := rfl



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.euclideanRowBasis_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.OAI.PrimeDegreePackets.rowBasis_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
namespace PrimeDegreePackets



theorem exists_SL_normalizedLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (hodd : Odd n) : ∃ g : G n, rowLattice g.1 = normalizedLattice M σ := by
  let B := embeddingMatrix M σ
  let A := |B.det| ^ (-(1 : ℝ) / n) • B
  have hd : |A.det| = 1 := normalizedMatrix_abs_det B hodd.pos
    (embeddingMatrix_det_ne_zero M σ hn)
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hd with h | h
  · exact ⟨⟨A, h⟩, rfl⟩
  · have hneg : (-A).det = 1 := by
      rw [Matrix.det_neg, Fintype.card_fin, hodd.neg_one_pow, h]
      norm_num
    exact ⟨⟨-A, hneg⟩, rowLattice_neg A⟩

open scoped NumberField nonZeroDivisors



def unitStabilizer {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : Subgroup (𝓞 K)ˣ where
  carrier := {u | ∀ x : K, x ∈ M.carrier ↔ (integralUnit u : K) * x ∈ M.carrier}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv x
    rw [map_mul, Units.val_mul, mul_assoc]
    exact (hv x).trans (hu ((integralUnit v : K) * x))
  inv_mem' := by
    intro u hu x
    have h := hu ((integralUnit u⁻¹ : K) * x)
    simpa [← mul_assoc] using h.symm



lemma unitSigns_eq_one_iff {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ) :
    unitSigns σ u = 1 ↔ ∀ i, 0 < σ i (integralUnit u : K) := by
  simp only [funext_iff, Pi.one_apply, Units.ext_iff]
  change (∀ i, SignType.sign (σ i (integralUnit u : K)) = 1) ↔ _
  simp only [sign_eq_one_iff]

 

def positiveUnitStabilizer {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) : Subgroup (𝓞 K)ˣ :=
  unitStabilizer M ⊓ (unitSigns σ).ker

lemma mem_positiveUnitStabilizer {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ) :
    u ∈ positiveUnitStabilizer M σ ↔ u ∈ unitStabilizer M ∧
      ∀ i, 0 < σ i (integralUnit u : K) := by
  simp only [positiveUnitStabilizer, Subgroup.mem_inf, MonoidHom.mem_ker,
    unitSigns_eq_one_iff]



def realEmbeddingMap {n : ℕ} {K : Type*} [Field K] (σ : OrderedEmbeddings n K) :
    K →ₗ[ℤ] (Fin n → ℝ) where
  toFun x i := σ i x
  map_add' x y := by ext i; exact map_add (σ i) x y
  map_smul' z x := by ext i; simp



lemma fullLattice_exists_ne_zero {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : ∃ x ∈ M.carrier, x ≠ 0 := by
  by_contra! h
  have hbot : M.carrier = ⊥ := le_antisymm (fun x hx => by simp [h x hx]) bot_le
  have H : (⊥ : Submodule ℚ K) = ⊤ := by simpa [hbot] using M.spans
  exact bot_ne_top H

lemma realEmbeddingMap_injective {n : ℕ} {K : Type*} [Field K]
    (σ : OrderedEmbeddings n K) (hn : 0 < n) : Function.Injective (realEmbeddingMap σ) := by
  intro x y h
  exact (σ ⟨0, hn⟩).injective (congrFun h ⟨0, hn⟩)



lemma rowLattice_embeddingMatrix {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) :
    rowLattice (embeddingMatrix M σ) = M.carrier.map (realEmbeddingMap σ) := by
  rw [← fullLattice_span_basis M, Submodule.map_span, ← Set.range_comp]
  rfl

lemma sum_orderedUnitLog_full {n : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ) :
    ∑ i, Real.log |σ i (u : K)| = 0 := by
  have h := NumberField.Units.sum_mult_mul_log u
  simp only [(show ∀ w : NumberField.InfinitePlace K, w.mult = 1 from
    fun w => (NumberField.IsTotallyReal.isReal w).mult_eq_one), Nat.cast_one, one_mul] at h
  rw [← Equiv.sum_comp (orderedRealPlaces σ)] at h
  simpa only [orderedRealPlaces_apply] using h

lemma diagonalFlow_orderedUnitLog {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K) (u : (𝓞 K)ˣ)
    (hu : ∀ i, 0 < σ i (u : K)) :
    (diagonalFlow (orderedUnitLog σ (Additive.ofMul u))).1 =
      Matrix.diagonal (fun i => σ i (u : K)) := by
  apply congrArg Matrix.diagonal
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    have h := sum_orderedUnitLog_full σ u
    rw [Fin.sum_univ_castSucc] at h
    simp only [orderedUnitLog_apply]
    rw [show -(∑ j : Fin d, Real.log |σ j.castSucc (u : K)|) =
      Real.log |σ (Fin.last d) (u : K)| by linarith]
    rw [abs_of_pos (hu _), Real.exp_log (hu _)]
  · simp only [Fin.snoc_castSucc, orderedUnitLog_apply, abs_of_pos (hu _), Real.exp_log (hu _)]

lemma diagonalFlow_injective (d : ℕ) : Function.Injective (@diagonalFlow d) := by
  intro u v huv
  ext i
  apply Real.exp_injective
  have h := congrArg (fun g : G (d + 1) => g.1 i.castSucc i.castSucc) huv
  simpa [diagonalFlow] using h



instance periodGroup_discrete {d : ℕ} (x : X (d + 1)) : DiscreteTopology (periodGroup x) := by
  induction x using Quotient.inductionOn with
  | h g =>
    let f : periodGroup (Quotient.mk _ g : X (d + 1)) → integralGroup (d + 1) := fun u =>
      ⟨g * (g * diagonalFlow u.1)⁻¹, by
        have hu := u.property
        change (Quotient.mk _ (g * diagonalFlow u.1) : X (d + 1)) = Quotient.mk _ g at hu
        have H := Quotient.exact hu
        change (QuotientGroup.rightRel (integralGroup (d + 1))) (g * diagonalFlow u.1) g at H
        exact QuotientGroup.rightRel_apply.mp H⟩
    let : DiscreteTopology (integralGroup (d + 1)) := by unfold integralGroup; infer_instance
    apply DiscreteTopology.of_continuous_injective (f := f)
    · apply Continuous.subtype_mk
      exact continuous_const.mul (continuous_const.mul
        ((continuous_diagonalFlow d).comp continuous_subtype_val)).inv
    · intro u v huv
      apply Subtype.ext
      apply diagonalFlow_injective d
      apply mul_left_cancel (a := g)
      apply inv_injective
      exact mul_left_cancel (congrArg Subtype.val huv)

instance periodSubmodule_discrete {d : ℕ} (x : X (d + 1)) :
    DiscreteTopology (periodGroup x).toIntSubmodule :=
  inferInstanceAs (DiscreteTopology (periodGroup x))

 

theorem periodGroup_hasFundamentalDomain {d : ℕ} (x : X (d + 1))
    [IsZLattice ℝ (periodGroup x).toIntSubmodule] :
    HasAddFundamentalDomain (periodGroup x) (LogCoordinates d) volume := by
  let L := (periodGroup x).toIntSubmodule
  have : DiscreteTopology L := inferInstanceAs (DiscreteTopology (periodGroup x))
  let b := Module.Free.chooseBasis ℤ L
  exact (ZLattice.isAddFundamentalDomain b volume).hasAddFundamentalDomain volume

 

theorem orbitVolume_ne_zero_ne_top {d : ℕ} (x : X (d + 1))
    [IsZLattice ℝ (periodGroup x).toIntSubmodule] : orbitVolume x ≠ 0 ∧ orbitVolume x ≠ ⊤ := by
  let L := (periodGroup x).toIntSubmodule
  have : DiscreteTopology L := inferInstanceAs (DiscreteTopology (periodGroup x))
  have h := ZLattice.covolume_ne_zero L volume
  change (orbitVolume x).toReal ≠ 0 at h
  exact ENNReal.toReal_ne_zero.mp h

lemma orbitalHaar_univ {d : ℕ} (x : X (d + 1))
    (h : HasAddFundamentalDomain (periodGroup x) (LogCoordinates d) volume) :
    orbitalHaar x Set.univ = orbitVolume x := by
  simp only [orbitalHaar, dite_eq_left h]
  rw [Measure.map_apply (continuous_orbitMap x).measurable MeasurableSet.univ]
  simp only [Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  change _ = addCovolume (periodGroup x) (LogCoordinates d) volume
  simp only [addCovolume, dite_eq_left h]

 

theorem orbitProbability_isProbabilityMeasure {d : ℕ} (x : X (d + 1))
    [IsZLattice ℝ (periodGroup x).toIntSubmodule] : IsProbabilityMeasure (orbitProbability x) := by
  constructor
  rw [orbitProbability, Measure.smul_apply, smul_eq_mul,
    orbitalHaar_univ x (periodGroup_hasFundamentalDomain x)]
  exact ENNReal.inv_mul_cancel (orbitVolume_ne_zero_ne_top x).1 (orbitVolume_ne_zero_ne_top x).2



lemma rightAction_injective {n : ℕ} (g : G n) :
    Function.Injective (fun x : X n => rightAction x g) := by
  intro x y h
  have := congrArg (fun z => rightAction z g⁻¹) h
  simpa using this

lemma diagonalFlow_commute_of_diagonal {d : ℕ} (g : G (d + 1))
    (hg : ∀ i j, i ≠ j → g.1 i j = 0) (u : LogCoordinates d) :
    g * diagonalFlow u = diagonalFlow u * g := by
  apply Subtype.ext
  change g.1 * Matrix.diagonal _ = Matrix.diagonal _ * g.1
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : i = j
  · subst j; exact mul_comm _ _
  · simp [hg i j h]

lemma orbitMap_rightAction_of_diagonal {d : ℕ} (x : X (d + 1)) (g : G (d + 1))
    (hg : ∀ i j, i ≠ j → g.1 i j = 0) (u : LogCoordinates d) :
    orbitMap (rightAction x g) u = rightAction (orbitMap x u) g := by
  simp only [orbitMap, rightAction_mul, diagonalFlow_commute_of_diagonal g hg u]

lemma periodGroup_rightAction_of_diagonal {d : ℕ} (x : X (d + 1)) (g : G (d + 1))
    (hg : ∀ i j, i ≠ j → g.1 i j = 0) :
    periodGroup (rightAction x g) = periodGroup x := by
  ext u
  change orbitMap (rightAction x g) u = rightAction x g ↔ orbitMap x u = x
  rw [orbitMap_rightAction_of_diagonal x g hg u]
  exact (rightAction_injective g).eq_iff

lemma periodGroup_orbitMap {d : ℕ} (x : X (d + 1)) (u : LogCoordinates d) :
    periodGroup (orbitMap x u) = periodGroup x := by
  apply periodGroup_rightAction_of_diagonal
  intro i j hij
  exact Matrix.diagonal_apply_ne _ hij

lemma periodGroup_eq_of_diagonalOrbit_eq {d : ℕ} {x y : X (d + 1)}
    (h : diagonalOrbit x = diagonalOrbit y) : periodGroup x = periodGroup y := by
  have hx := mem_diagonalOrbit_self x
  rw [h] at hx
  obtain ⟨u, rfl⟩ := hx
  exact periodGroup_orbitMap y u



lemma locallyHomothetic_refl {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : LocallyHomothetic M M := by
  intro p hp
  exact ⟨1, by simp⟩

lemma packetOrbits_nonempty {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d + 1) K) (σ : OrderedEmbeddings (d + 1) K) :
    (packetOrbits M σ).Nonempty := by
  refine ⟨diagonalOrbit (latticePoint M σ), M, locallyHomothetic_refl M,
    1, one_mem_signMatrices _, ?_⟩
  rw [rightAction_one]

lemma orbitBasepoint_spec {d : ℕ} {K : Type*} [Field K] [NumberField K]
    {M : FullLattice (d + 1) K} {σ : OrderedEmbeddings (d + 1) K}
    (O : packetOrbits M σ) : diagonalOrbit (orbitBasepoint O) = O.1 := by
  unfold orbitBasepoint
  refine Classical.epsilon_spec (p := fun x : X (d + 1) => diagonalOrbit x = O.1) ?_
  obtain ⟨M', _, w, _, hO⟩ := O.property
  exact ⟨rightAction (latticePoint M' σ) w, hO.symm⟩



lemma completedLattice_mul_mem {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) {a : K} (ha : a ∈ multiplierOrder M)
    (p : ℕ) [Fact p.Prime] {z : LocalAlgebra p K} (hz : z ∈ completedLattice p M) :
    Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) a * z ∈ completedLattice p M := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      rw [← map_mul]
      exact Submodule.subset_span ⟨a * b, ha b hb, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa [mul_add] using (completedLattice p M).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [mul_smul_comm] using (completedLattice p M).smul_mem c ih



open scoped Pointwise



open FractionalIdeal



lemma classRepresentative_spec (K : Type*) [Field K] [NumberField K]
    (c : ClassGroup (𝓞 K)) : ClassGroup.mk K (classRepresentative K c) = c :=
  by
    exact Classical.choose_spec
      (show ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = c from
        ClassGroup.induction K (fun I => ⟨I, rfl⟩) c)



theorem signMatrices_finite (n : ℕ) : (signMatrices n).Finite := by
  let f : signMatrices n → (Fin n → Bool) := fun g i => decide (g.1.1 i i = 1)
  apply Set.finite_coe_iff.mp
  apply Finite.of_injective f
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst j
    have H : decide (g.1.1 i i = 1) = decide (h.1.1 i i = 1) := congrFun he i
    rcases g.property.2 i with hi | hi <;> rcases h.property.2 i with hj | hj
    · exact hi.trans hj.symm
    · norm_num [hi, hj] at H
    · norm_num [hi, hj] at H
    · exact hi.trans hj.symm
  · rw [g.property.1 i j hij, h.property.1 i j hij]

lemma signValue_eq_one_or_neg_one (w : SignTypeˣ) : signValue w = 1 ∨ signValue w = -1 := by
  have hw := w.ne_zero
  cases h : (w : SignType) <;> simp_all

lemma signValue_sq (w : SignTypeˣ) : signValue w ^ 2 = 1 := by
  rcases signValue_eq_one_or_neg_one w with h | h <;> rw [h] <;> norm_num

lemma prod_abs_ordered_unit {n : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ) :
    ∏ i, |σ i (u : K)| = 1 := by
  have he := congrArg Real.exp (sum_orderedUnitLog_full σ u)
  rw [Real.exp_sum,Real.exp_zero] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.prod_congr rfl
  intro i _
  exact (Real.exp_log (abs_pos.mpr ((_root_.map_ne_zero (σ i)).mpr
    (integralUnit u).ne_zero))).symm



lemma diagonalFlow_abs_orderedUnitLog {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) (u : (𝓞 K)ˣ) :
    (diagonalFlow (orderedUnitLog σ (Additive.ofMul u))).1 =
      Matrix.diagonal (fun i => |σ i (u : K)|) := by
  apply congrArg Matrix.diagonal
  ext i
  have hpos (j : Fin (d+1)) : 0 < |σ j (u : K)| :=
    abs_pos.mpr ((_root_.map_ne_zero (σ j)).mpr (integralUnit u).ne_zero)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    have h := sum_orderedUnitLog_full σ u
    rw [Fin.sum_univ_castSucc] at h
    simp only [orderedUnitLog_apply]
    rw [show -(∑ j : Fin d, Real.log |σ j.castSucc (u : K)|) =
      Real.log |σ (Fin.last d) (u : K)| by linarith,Real.exp_log (hpos _)]
  · simp only [Fin.snoc_castSucc,orderedUnitLog_apply,Real.exp_log (hpos _)]

lemma signValue_unitSigns {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ) (i : Fin n) :
    signValue (unitSigns σ u i) * |σ i (u : K)| = σ i (u : K) :=
  sign_mul_abs _

lemma saturationFractionalIdeal_eq_of_carrier_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (h : N.carrier = P.carrier) :
    saturationFractionalIdeal N = saturationFractionalIdeal P := by
  apply FractionalIdeal.coeToSubmodule_injective
  change Submodule.span (𝓞 K) (N.carrier : Set K) = Submodule.span (𝓞 K) (P.carrier : Set K)
  rw [h]

 

lemma exists_integralUnit_of_same_saturation {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (b : K) (hb : b ≠ 0)
    (h : (P.carrier : Set K) = (fun x => b*x) '' (N.carrier : Set K))
    (hI : saturationFractionalIdeal N = saturationFractionalIdeal P) :
    ∃ u : (𝓞 K)ˣ, (u : K) = b ∧ P.carrier = u • N.carrier := by
  let a : Kˣ := Units.mk0 b hb
  have hcar : P.carrier = (scaleFullLattice N a).carrier := by
    apply SetLike.coe_injective
    rw [scaleFullLattice_carrier]
    exact h
  have hId := saturationFractionalIdeal_eq_of_carrier_eq P (scaleFullLattice N a) hcar
  rw [saturationFractionalIdeal_scale,← hI] at hId
  have hp : FractionalIdeal.spanSingleton (𝓞 K)⁰ b = 1 := by
    apply mul_right_cancel₀ (saturationFractionalIdeal_ne_zero N)
    simpa only [a,Units.val_mk0,one_mul] using hId.symm
  rw [← FractionalIdeal.spanSingleton_one] at hp
  obtain ⟨u,hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hp.symm
  have hu' : (u : K) = b := by simpa [Units.smul_def,Algebra.smul_def] using hu
  refine ⟨u,hu',?_⟩
  have ha : a = integralUnit u := by apply Units.ext; exact hu'.symm
  rw [hcar,ha,integralUnit,scaleFullLattice_unit_carrier]

lemma signValue_sign (w : SignTypeˣ) : SignType.sign (signValue w) = w := by
  have hw := w.ne_zero
  cases h : (w : SignType) <;> simp_all [signValue]

lemma signUnits_sq (w : SignTypeˣ) : w*w = 1 := by
  apply Units.ext
  have hw := w.ne_zero
  cases h : (w : SignType) <;> simp_all

lemma signUnits_inv (w : SignTypeˣ) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_left (signUnits_sq w)



lemma signValue_injective : Function.Injective signValue := by
  intro a b h
  apply Units.ext
  simpa only [signValue_sign] using congrArg SignType.sign h



def packetUnitKernel {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) : Subgroup (𝓞 K)ˣ :=
  letI := allSignedGlobalLabelMulAction M σ
  (MulAction.toPermHom (𝓞 K)ˣ (AllSignedGlobalLabel M)).ker

instance xSecondCountable (n : ℕ) : SecondCountableTopology (X n) :=
  (inverseQuotientHomeomorph n).secondCountableTopology

instance xLocallyCompact (n : ℕ) : LocallyCompactSpace (X n) :=
  (inverseQuotientHomeomorph n).isClosedEmbedding.locallyCompactSpace

instance xMetrizable (n : ℕ) : MetrizableSpace (X n) := by infer_instance



def nonzeroIntegerRowEquiv {n : ℕ} (g : G n) :
    {z : Fin n → ℤ // z ≠ 0} ≃ {v : rowLattice g.1 // (v : Fin n → ℝ) ≠ 0} :=
  (integerRowEquiv g).toEquiv.subtypeEquiv (by
    intro z
    change z ≠ 0 ↔ integerRowMap g.1 z ≠ 0
    constructor
    · intro hz h
      apply hz
      apply integerRowMap_injective g
      exact h.trans (map_zero _).symm
    · rintro hz rfl
      exact hz (map_zero _))



def siegelTransform {n : ℕ} (f : (Fin n → ℝ) → ℝ≥0∞) (x : X n) : ℝ≥0∞ :=
  ∑' v : {v : pointLattice x // (v : Fin n → ℝ) ≠ 0}, f v.1.1



def fullLatticeInclusionMatrix {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (h : N.carrier ≤ P.carrier) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => P.basis.repr ⟨N.basis i, h (N.basis i).property⟩ j



def signedFlowSum {d : ℕ} (f : (Fin (d+1) → ℝ) → ℝ≥0∞)
    (v : Fin (d+1) → ℝ) (u : LogCoordinates d) : ℝ≥0∞ :=
  ∑ w : Fin (d+1) → SignTypeˣ, f (fun i => signValue (w i)*logFlowWeights u i*v i)



def productFiberIntegral {d : ℕ} (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (z : ℝ) : ℝ≥0∞ :=
  ∑ w : Fin (d+1) → SignTypeˣ, ∫⁻ u : LogCoordinates d,
    f (Fin.snoc (fun i => signValue (w i.castSucc)*Real.exp (u i))
      (signValue (w (Fin.last d))*z*Real.exp (-∑ i, u i)))



def orderedDeletedPlacesEquiv {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    Fin d ≃ {w : NumberField.InfinitePlace K // w ≠ orderedRealPlaces σ (Fin.last d)} :=
  (finSuccAboveEquiv (Fin.last d)).trans
    ((orderedRealPlaces σ).subtypeEquiv (fun _ => not_congr (orderedRealPlaces σ).injective.eq_iff.symm))



def idealClassPartitionEquiv (K : Type*) [Field K] [NumberField K] :
    (Σ c : ClassGroup (𝓞 K), integralIdealClassFiber (classRepresentative K c)) ≃
      integralFractionalIdeals K where
  toFun x := ⟨x.2.1,x.2.2.1⟩
  invFun J := ⟨(ClassGroup.mk K J.1)⁻¹,
    ⟨J.1,J.2,by rw [classRepresentative_spec,inv_inv]⟩⟩
  left_inv := by
    rintro ⟨c,J⟩
    have h : (ClassGroup.mk K J.1)⁻¹ = c := by rw [J.2.2,classRepresentative_spec,inv_inv]
    apply Sigma.ext h
    exact (Subtype.heq_iff_coe_eq (fun x => by
      change (x.val ≤ 1 ∧ ClassGroup.mk K x = (ClassGroup.mk K (classRepresentative K ((ClassGroup.mk K J.val)⁻¹)))⁻¹) ↔ _
      rw [h])).mpr rfl
  right_inv _ := rfl



def orderedComplexEmbeddings {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) : Fin n ≃ (K →ₐ[ℚ] ℂ) :=
  Equiv.ofBijective (fun i => RingHom.equivRatAlgHom K ℂ (Complex.ofRealHom.comp (σ i)))
    (Fintype.bijective_iff_injective_and_card _ |>.mpr ⟨by
      intro i j h
      apply σ.injective
      ext a
      apply Complex.ofReal_injective
      exact congrArg (fun f : K →ₐ[ℚ] ℂ => f a) h,
      by rw [Fintype.card_fin,AlgHom.card,hn]⟩)



def signedGlobalLabelEquiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    SignedGlobalLabel M I ≃ globalLabels M I × (Fin n → SignTypeˣ) where
  toFun x := (x.lattice,x.signs)
  invFun x := ⟨x.1,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_MatrixConjugationDensity
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite measures in the matrix conjugation representation

This is the elementary recurrence part of the needed Borel-density
argument. A finite measure invariant under a strict real contraction is
concentrated at zero. Applied to matrix coefficients, split diagonal
conjugation forces invariant finite matrix measures onto diagonal matrices.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology

/-- Compat: Mathlib d13f23b's Borel structure on `Matrix`. -/
instance compatMatrixBorelSpace {n m : ℕ} : BorelSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin m → ℝ))

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealNorms
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix

open MeasureTheory Filter Set Module TopologicalSpace
namespace PrimeDegreePackets



def twoSidedTube {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (b t : ℝ) : Set (G n) :=
  {h | diagonalOneParameter ell hell (-t) * h * diagonalOneParameter ell hell t ∈ matrixBall n b ∧
       diagonalOneParameter ell hell t * h * diagonalOneParameter ell hell (-t) ∈ matrixBall n b}

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ErgodicDecomposition
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical

open MeasureTheory Set Topology UniformSpace TopologicalSpace


namespace PrimeDegreePackets

instance xStandardBorel (n : ℕ) : StandardBorelSpace (X n) :=
  standardBorel_of_sigmaCompact


instance diagonalLogAction_continuous (d : ℕ) :
    ContinuousSMul (Multiplicative (LogCoordinates d)) (X (d+1)) where
  continuous_smul := by
    change Continuous (fun p : Multiplicative (LogCoordinates d) × X (d+1) =>
      rightAction p.2 (diagonalFlow p.1.toAdd))
    exact (continuous_rightAction_uncurry (d+1)).comp
      (continuous_snd.prodMk ((continuous_diagonalFlow d).comp continuous_fst))



end PrimeDegreePackets


open scoped ENNReal Topology
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootRelations
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise


namespace PrimeDegreePackets

instance periodSubmodule_addSubgroup_discrete {d : ℕ} (x : X (d+1)) :
    DiscreteTopology (periodGroup x).toIntSubmodule.toAddSubgroup :=
  inferInstanceAs (DiscreteTopology (periodGroup x).toIntSubmodule)


end PrimeDegreePackets

open scoped Topology Classical ENNReal

open scoped Matrix Topology Classical
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockEliminationSchedule
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A full within-block elimination schedule

Upper entries are cleared in increasing row order, and lower entries
in decreasing row order. Transitivity of the block relation ensures
that each affected earlier entry has an earlier zero source entry.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def UpperInitial {n : ℕ} (r : Setoid (Fin n))
    (P : Finset (Fin n × Fin n)) : Prop :=
  P ⊆ blockUpperEntries r ∧ ∀ p ∈ P, ∀ q ∈ blockUpperEntries r, q.1 < p.1 → q ∈ P

def LowerInitial {n : ℕ} (r : Setoid (Fin n))
    (Q : Finset (Fin n × Fin n)) : Prop :=
  Q ⊆ blockLowerEntries r ∧ ∀ p ∈ Q, ∀ q ∈ blockLowerEntries r, p.1 < q.1 → q ∈ Q

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PluckerCovariance
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.compatMatrixBorelSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual frame minors under diagonal transport

The projective coordinates here are determinants of minors of an actual
real matrix frame. Changing its basis multiplies every coordinate by the
same determinant. Thus diagonal recurrence applies to these coordinates
without an assumed projective-action interface.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped BigOperators ENNReal

/-- Compat: Mathlib d13f23b's Borel structure on `Matrix`. -/
instance compatMatrixBorelSpacePlucker {n m : ℕ} : BorelSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin m → ℝ))

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalObservations
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conditional entropy of finite observations

The conditioning variable is the last argument. All identities below use
the actual distribution under `μ`, including its zero-mass cells.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PrimeDegreePackets

variable {Y α β γ : Type*} [MeasurableSpace Y]

def conditionalObservationEntropy [Fintype α] [Fintype β]
    (μ : Measure Y) (P : Y → α) (Q : Y → β) : ℝ :=
  observationEntropy μ (fun y => (Q y,P y)) - observationEntropy μ Q

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalSigmaEntropy
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite observation entropy conditioned on a sigma algebra -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace PrimeDegreePackets

variable {Y α : Type*} [mY : MeasurableSpace Y] [Fintype α]

def conditionalSigmaEntropy (μ : Measure Y) (P : Y → α) (m : MeasurableSpace Y) : ℝ :=
  ∫ y, finiteShannon (fun a =>
    (μ[({z | P z = a}.indicator (fun _ => (1 : ℝ))) | m]) y) ∂μ

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootOverlaps
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory

open MeasureTheory

open scoped BigOperators ENNReal

open NumberField Finset


namespace PrimeDegreePackets


def totallyRealCompletedXi (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  s * (s-1) * completionExponential (Module.finrank ℚ K)
    |(NumberField.discr K : ℝ)| s *
    Complex.Gamma (s/2) ^ Module.finrank ℚ K * NumberField.dedekindZeta K s

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_XiBoundary
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
namespace PrimeDegreePackets

@[simp] lemma totallyRealCompletedXi_one (K : Type*) [Field K] [NumberField K] :
    totallyRealCompletedXi K 1 = 0 := by simp [totallyRealCompletedXi]



end PrimeDegreePackets

open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeTheta
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix


namespace PrimeDegreePackets
open ThetaConstruction
variable {n : ℕ} {K : Type*} [Field K] [NumberField K]

def traceDualFullLattice (M : FullLattice n K) (hn : finrank ℚ K = n) : FullLattice n K where
  carrier := Submodule.span ℤ (Set.range ((Algebra.traceForm ℚ K).dualBasis
    (traceForm_nondegenerate ℚ K) (fullLatticeRatBasis M hn)))
  basis := Basis.span (((Algebra.traceForm ℚ K).dualBasis
    (traceForm_nondegenerate ℚ K) (fullLatticeRatBasis M hn)).linearIndependent.restrict_scalars' ℤ)
  spans := by
    rw [Submodule.span_span_of_tower, Basis.span_eq]

end PrimeDegreePackets


open Module MeasureTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeDuality
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory

open MeasureTheory Module WithLp

open scoped BigOperators NumberField nonZeroDivisors ENNReal
namespace PrimeDegreePackets
open ThetaConstruction

 
def arithmeticFlowGaussian {d : ℕ} {K : Type*} [Field K]
    (σ : OrderedEmbeddings (d+1) K) (a : K) (t : ℝ) (u : LogCoordinates d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-Real.pi*t*∑ i, (logFlowWeights u i*σ i a)^2))

end PrimeDegreePackets


namespace PrimeDegreePackets
open ThetaConstruction

 

def fractionalIdealNonzeroIntegerEquiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    NonzeroIntegerVector (Fin n) ≃ nonzeroIdealElements I := by
  let M := fractionalIdealFullLattice hn I
  let e : NonzeroIntegerVector (Fin n) ≃ {a : M.carrier // a ≠ 0} :=
    M.basis.equivFun.symm.toEquiv.subtypeEquiv (by
      intro z
      change z ≠ 0 ↔ M.basis.equivFun.symm z ≠ 0
      constructor
      · intro hz h
        apply hz
        apply M.basis.equivFun.symm.injective
        simpa only [_root_.map_zero] using h
      · intro hz h
        apply hz
        rw [h, _root_.map_zero])
  let f : {a : M.carrier // a ≠ 0} ≃ nonzeroIdealElements I :=
    { toFun := fun a => ⟨Units.mk0 (a.1:K) (by
        intro H
        exact a.2 (Subtype.ext H)),a.1.property⟩
      invFun := fun a => ⟨⟨(a.1:K),a.2⟩,by
        intro H
        exact a.1.ne_zero (congrArg Subtype.val H)⟩
      left_inv := fun a => by apply Subtype.ext; rfl
      right_inv := fun a => by apply Subtype.ext; apply Units.ext; rfl }
  exact e.trans f

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_DiscriminantBounds
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators

open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
namespace PrimeDegreePackets

 
def orderedEuclideanMap {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (σ : OrderedEmbeddings n K) : K →ₗ[ℚ] EuclideanSpace ℝ (Fin n) where
  toFun x := toLp 2 (fun i => σ i x)
  map_add' x y := by ext i; exact map_add (σ i) x y
  map_smul' q x := by ext i; exact map_rat_smul (σ i) q x

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FutureEntropyIncrements
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional entropy increments of stationary finite observations -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace PrimeDegreePackets

variable {Y α : Type*} [MeasurableSpace Y] [Fintype α]

def futureName (T : Y → Y) (P : Y → α) (N : ℕ) (y : Y) : Fin N → α :=
  orbitName T P N (T y)

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_GaussianMellin
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors
open scoped BigOperators NumberField nonZeroDivisors


namespace PrimeDegreePackets
open ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]

 
def complexFlowGaussian (σ : OrderedEmbeddings (d+1) K) (a : K)
    (t : ℝ) (u : LogCoordinates d) : ℂ :=
  Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
    ((∑ i, (logFlowWeights u i * σ i a)^2 : ℝ) : ℂ))

end PrimeDegreePackets


open MeasureTheory Module WithLp Set


namespace PrimeDegreePackets
open ThetaConstruction
variable {n : ℕ} {K : Type*} [Field K] [NumberField K]

def integralIdealFullEquiv (hn : finrank ℚ K = n) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    I ≃ₗ[ℤ] (fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)).carrier := by
  let f : I →ₗ[ℤ] (fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)).carrier :=
    { toFun := fun a => ⟨((a:𝓞 K):K), FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ a.2⟩
      map_add' := by intros; apply Subtype.ext; simp
      map_smul' := by intros; apply Subtype.ext; simp }
  apply LinearEquiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    apply NumberField.RingOfIntegers.coe_injective
    exact congrArg (fun x : (fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)).carrier =>
      (x:K)) hab
  · intro a
    obtain ⟨b,hb,he⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp a.2
    refine ⟨⟨b,hb⟩,Subtype.ext ?_⟩
    exact he

def orderedIdealBasis (hn : finrank ℚ K = n) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Basis (Fin n) ℤ I :=
  (fractionalIdealFullLattice hn (integralIdealFractionalUnit I hI)).basis.map
    (integralIdealFullEquiv hn I hI).symm

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealThetaFlow
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors
open scoped BigOperators NumberField nonZeroDivisors
open MeasureTheory Module WithLp Set

open scoped BigOperators NumberField ENNReal

open scoped BigOperators NumberField


namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]


def unitOrbitMellinKernel (σ : OrderedEmbeddings (d+1) K) (S : Subgroup (𝓞 K)ˣ)
    (a : K) (s : ℂ) (p : ℝ × LogCoordinates d) : ℂ :=
  (p.1:ℂ)^(((d+1:ℕ):ℂ)*s/2-1) *
    ∑' z : S, complexFlowGaussian σ ((z.val:K)*a) p.1 p.2

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_SplitEuler
attribute [-instance] _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedMaximalIdeal.instLiesOver _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module NumberField Filter Topology
open scoped NumberField nonZeroDivisors Classical BigOperators
namespace PrimeDegreePackets

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E]

 

def primeIdealTowerEquiv (p : ℕ) (hp : p ≠ 0) :
    (Σ P : idealsOverPrime F p, Ideal.primesOver P.val (𝓞 E)) ≃ idealsOverPrime E p := by
  let f : (Σ P : idealsOverPrime F p, Ideal.primesOver P.val (𝓞 E)) →
      idealsOverPrime E p := fun IQ => by
    refine ⟨IQ.2.val, (mem_idealsOverPrime_iff E hp _).mpr ⟨IQ.2.property.1, ?_⟩⟩
    have hP := ((mem_idealsOverPrime_iff F hp _).mp IQ.1.property).2
    rw [IQ.2.property.2.over] at hP
    simpa only [Ideal.mem_under, map_natCast] using hP
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨P, Q⟩ ⟨P', Q'⟩ he
    have hQ : Q.val = Q'.val := congrArg Subtype.val he
    have hP : P = P' := Subtype.ext (by
      rw [Q.property.2.over, Q'.property.2.over, hQ])
    cases hP
    exact congrArg (Sigma.mk P) (Subtype.ext hQ)
  · intro Q
    have hQ := (mem_idealsOverPrime_iff E hp _).mp Q.property
    let : Q.val.IsPrime := hQ.1
    have hP : Q.val.under (𝓞 F) ∈ idealsOverPrime F p := by
      apply (mem_idealsOverPrime_iff F hp _).mpr
      refine ⟨inferInstance, ?_⟩
      simpa only [Ideal.mem_under, map_natCast] using hQ.2
    refine ⟨⟨⟨Q.val.under (𝓞 F), hP⟩, ⟨Q.val, hQ.1, inferInstance⟩⟩, ?_⟩
    rfl



def primeIdealEulerFactor (K : Type*) [Field K] [NumberField K] (p : ℕ) (s : ℂ) : ℂ :=
  ∏ P : idealsOverPrime K p, (1 - (Ideal.absNorm P.val : ℂ) ^ (-s))⁻¹

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_ValuationSubring
attribute [-instance] _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instSMulCommClass _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace RamificationTheory

/-!
# Hilbert ramification theory: valuation-subring layer

This file manages the ordinary valuation-subring decomposition/inertia exact
sequence.  For an arbitrary valuation subring the residue action need not be
onto the full residue automorphism group; the canonical theorem is the exact
sequence with target equal to the range of the residue action.
-/

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The fixed-field description of decomposition source:
`L/Z_w` is Galois because `Z_w` is the fixed field of the finite
decomposition group action. -/
instance decompositionField_isGalois
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    IsGalois (decompositionField K A) L :=
  IsGalois.of_fixed_field L (decompositionGroup K A)

end ValuationSubring
end HilbertRamification

end
end RamificationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_ResidueExactSequence
attribute [-instance] _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.decompositionSubgroupMulSemiringAction _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace RamificationTheory

/-!
# The residue-action exact sequence

For a (possibly infinite) Galois extension and a chosen extension valuation,
the residue extension over the decomposition field is normal and reduction
gives the exact sequence

`1 → I_w → G_w → Gal(λ/κ) → 1`.

The base residue field is presented intrinsically as the quotient of the
fixed subring of the chosen valuation ring by the contraction of its maximal
ideal.  This fixed subring is exactly the valuation ring on the decomposition
field.  The profinite surjectivity proof is the compact inverse-limit argument
used in this construction, supplied by `Ideal.Quotient.stabilizerHom_surjective_of_profinite`.
-/

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

open scoped Pointwise Topology

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]

/-- Provides the instance `instIsInvariant`. -/
instance decompositionFixedSubring.instIsInvariant
    (A : _root_.ValuationSubring L) :
    Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) :=
  decompositionFixedSubring_isInvariant (K := K) A

end ValuationSubring
end HilbertRamification

end

end RamificationTheory
end


