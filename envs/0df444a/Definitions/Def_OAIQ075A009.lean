-- Prove2me | Definitions.Def_OAIQ075A009
-- name    : OAIQ075A009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:01:07.254608+00:00
-- url     : https://prove2.me/theorems/5527023e-80b3-4505-8499-8acad794f167
-- title:
--   Definitions bundle OAIQ075A009 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 244 declarations of OpenAI's Lean: 51 definitions, 1 inductive type or structure, 9 instances and 183 theorems. The definitions and types are `OAI.Generator.FiniteMatrixStage.scalarStage`, `OAI.Generator.IsII1Factor`, `OAI.Generator.MatrixUnitSystem.product`, `OAI.Generator.MatrixUnitSystem.reindex`, `OAI.Generator.Tracial.CornerPartition.binary`, `OAI.Generator.Tracial.dyadicSign`, `OAI.Generator.Tracial.includedProjection`, `OAI.Generator.Tracial.projectionSum`, `OAI.Generator.diagonalOperator`, `OAI.Generator.operatorEntry`, `OAI.Generator.tupleOrbitClosure`, `OAI.Generator.tupleOrbitMap`, `OAI.Generator.tupleSingle`, `OAI.Generator.vonNeumannOfWOTClosed`, `OAI.Generator.wstar`, `OAI.HochschildComparison.PartialUnitary.power`, `OAI.HochschildFinitePhase.extendedFrequency`, `OAI.HochschildMatrixSystems.MatrixSystem.coefficient`, `OAI.HochschildMatrixSystems.MatrixSystem.commutant`, `OAI.HochschildMatrixSystems.MatrixSystem.diagonalRoot`, `OAI.HochschildMatrixSystems.MatrixSystem.expectation`, `OAI.HochschildMatrixSystems.MatrixSystem.integerRootHom`, `OAI.HochschildMatrixSystems.MatrixSystem.phaseCoefficient`, `OAI.HochschildMatrixSystems.MatrixSystem.rankOne`, `OAI.HochschildMatrixSystems.MatrixSystem.rootUnitary`, `OAI.HochschildMatrixSystems.MatrixSystem.scalarMatrix`, `OAI.HochschildPatching.atomPower`, `OAI.HochschildPatching.residualScalar`, `OAI.HochschildPatching.unitaryCompletion`, `OAI.HochschildUltrapower.Ultrapower`, `OAI.HochschildUltrapower.boundedHom`, `OAI.HochschildUltrapower.centeredSequence`, `OAI.HochschildUltrapower.constant`, `OAI.HochschildUltrapower.ideal`, `OAI.HochschildUltrapower.quotientHom`, `OAI.HochschildUltrapower.quotientTrace`, `OAI.HochschildUltrapower.quotientTraceLinear`, `OAI.HochschildUltrapower.quotientUnitary`, `OAI.HochschildUltrapower.sequenceTraceLinear`, `OAI.HochschildUltrapower.traceScalarSequence` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_CommutantQuantization`, `BoundedHochschild_Corners`, `BoundedHochschild_DiffuseProjections`, `BoundedHochschild_Dixmier`, `BoundedHochschild_FinitePhases`, `BoundedHochschild_HarmonicSums`, `BoundedHochschild_HomogeneousTypeI`, `BoundedHochschild_IncrementalPatching`, `BoundedHochschild_MatrixCommutants`, `BoundedHochschild_MatrixSystems`, `BoundedHochschild_MixedWords`, `BoundedHochschild_PartialIsometries`, `BoundedHochschild_PartialUnitaries`, `BoundedHochschild_RankOneQuantization`, `BoundedHochschild_RelativeQuantization`, `BoundedHochschild_TraceExpectations`, `BoundedHochschild_TracialModulus`, `BoundedHochschild_UltrapowerMoments`, `BoundedHochschild_Ultrapowers`, `FactorGeneration_Bicommutant`, `FactorGeneration_GroupTrace`, `FactorGeneration_MatrixRefinement`, `FactorGeneration_MatrixSequence`, `FactorGeneration_MatrixUnits`, `FactorGeneration_OperatorLimits`, `FactorGeneration_PartialUnitaries`, `FactorGeneration_Pinching`, `FactorGeneration_ProjectionLimits`, `FactorGeneration_SpectralApproximation`, `FactorGeneration_SpectralPinching`, `FactorGeneration_Supports`, `FactorGeneration_Target`, `KadisonSimilarity_FreeProduct_DihedralWordIsometries`, `KadisonSimilarity_Representation_SquareArrayPadding`, `KadisonSimilarity_Tensor_EndpointTensors`, `KadisonSimilarity_Tensor_InvariantForms`, `KadisonSimilarity_Tensor_TensorPermutations`, `KadisonSimilarity_Tracial_TracialMatrixRealization`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A000`, `OAIQ075A001`, `OAIQ075A002`, `OAIQ075A003` and `OAIQ075A004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A014`, `OAIQ075A015`, `OAIQ075A016` and `OAIQ075A017`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A000
import Definitions.Def_OAIQ075A001
import Definitions.Def_OAIQ075A002
import Definitions.Def_OAIQ075A003
import Definitions.Def_OAIQ075A004

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_HarmonicSums
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Harmonic sine estimates, Fourier windows, tracial Hilbert spaces and unitary power rigidity. -/

noncomputable section


namespace HochschildRigidity
open Finset


section TraceHilbertSpace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)
lemma preGNS_norm_le (h1 : τ 1 = 1) (a : A) : ‖τ.toPreGNS a‖ ≤ ‖a‖ := by
  simpa only [mul_one, preGNS_norm_one τ h1] using preGNS_norm_mul_le τ a 1

open Finset
open scoped BigOperators

end TraceHilbertSpace

end HochschildRigidity
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TracialModulus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded-ball continuity, tracial null spaces and quotient seminorms. -/

noncomputable section


namespace TracialUltrapower
noncomputable section
open Filter
open scoped Topology BoundedContinuousFunction

section TraceIdeal
open scoped ComplexOrder
open HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)

 
def traceHilbertMap : A →L[ℂ] τ.PreGNS :=
  τ.toPreGNS.toLinearMap.mkContinuous 1 (fun a => by
    change ‖τ.toPreGNS a‖ ≤ 1 * ‖a‖
    rw [one_mul]
    exact preGNS_norm_le τ h1 a)

@[simp] theorem traceHilbertMap_apply (a : A) :
    traceHilbertMap τ h1 a = τ.toPreGNS a := rfl

variable (ω : Filter ℕ)

theorem nullSubmodule_mul_right (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (x y : ℕ →ᵇ A)
    (hx : x ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω) :
    x * y ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω := by
  rw [mem_nullSubmodule] at hx ⊢
  change Tendsto (fun j => ‖τ.toPreGNS (x j * y j)‖) ω (𝓝 0)
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun j => (preGNS_norm_mul_right_le τ htr _ _).trans
      (mul_le_mul_of_nonneg_right (y.norm_coe_le_norm j) (norm_nonneg _)))
  simpa only [mul_zero, ContinuousLinearMap.coe_coe, traceHilbertMap_apply] using hx.const_mul ‖y‖

theorem nullSubmodule_star (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (x : ℕ →ᵇ A) (hx : x ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω) :
    star x ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω := by
  rw [mem_nullSubmodule] at hx ⊢
  simpa only [ContinuousLinearMap.coe_coe, traceHilbertMap_apply,
    BoundedContinuousFunction.star_apply, preGNS_norm_star τ htr] using hx


end TraceIdeal
end
end TracialUltrapower
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Ultrapowers
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.BoundedHochschild.WeakSubspace.preannihilator_closed_instance _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.corner_closed _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.PopaCorner.algebra_closed _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tracial ultrapowers, quotient traces and bounded-ball maps. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open TracialUltrapower HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
include h1

def ideal : Ideal (ℕ →ᵇ A) where
  carrier := nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)
  zero_mem' := Submodule.zero_mem _
  add_mem' := fun hx hy => Submodule.add_mem _ hx hy
  smul_mem' := fun x y hy => by
    change x*y ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)
    have hs := nullSubmodule_star τ h1 (ω : Filter ℕ) htr y hy
    have ht := nullSubmodule_mul_right τ h1 (ω : Filter ℕ) htr (star y) (star x) hs
    have hh := nullSubmodule_star τ h1 (ω : Filter ℕ) htr _ ht
    rw [star_mul,star_star,star_star] at hh
    exact hh

instance ideal_twoSided : (ideal τ h1 ω htr).IsTwoSided where
  mul_mem_of_left := fun {x} y hx => nullSubmodule_mul_right τ h1 (ω : Filter ℕ) htr x y hx

instance ideal_starClosed : HochschildCStarQuotient.StarClosed (ideal τ h1 ω htr) where
  star_mem := fun {x} hx => nullSubmodule_star τ h1 (ω : Filter ℕ) htr x hx

instance ideal_closed : IsClosed (ideal τ h1 ω htr : Set (ℕ →ᵇ A)) :=
  isClosed_nullSubmodule (traceHilbertMap τ h1) (ω : Filter ℕ)

abbrev Ultrapower := (ℕ →ᵇ A) ⧸ ideal τ h1 ω htr

instance ultrapowerCStar : CStarAlgebra (Ultrapower τ h1 ω htr) :=
  let _ := ideal_twoSided τ h1 ω htr
  let _ := ideal_starClosed τ h1 ω htr
  HochschildCStarQuotient.quotientCStarAlgebra (ideal τ h1 ω htr)

lemma tendsto_sequenceTrace (x : ℕ →ᵇ A) :
    Tendsto (fun j => τ (x j)) (ω : Filter ℕ) (nhds (sequenceTrace τ ω x)) := by
  have hb : ∀ j, τ (x j) ∈ Metric.closedBall 0 ‖x‖ := by
    intro j
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (norm_trace_le τ h1 _).trans ((preGNS_norm_le τ h1 _).trans (x.norm_coe_le_norm j))
  obtain ⟨a,_,ha⟩ := (isCompact_closedBall (0:ℂ) ‖x‖).ultrafilter_le_nhds
    (ω.map (fun j => τ (x j))) (by
      rw [Ultrafilter.coe_map,le_principal_iff]
      change ∀ᶠ j in (ω : Filter ℕ), τ (x j) ∈ Metric.closedBall 0 ‖x‖
      exact Eventually.of_forall hb)
  have ht : Tendsto (fun j => τ (x j)) (ω : Filter ℕ) (nhds a) := ha
  simpa only [sequenceTrace,ht.limUnder_eq] using ht

def sequenceTraceLinear : (ℕ →ᵇ A) →ₗ[ℂ] ℂ where
  toFun := sequenceTrace τ ω
  map_add' x y := by
    apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω (x+y))
    simpa only [BoundedContinuousFunction.add_apply,map_add] using
      (tendsto_sequenceTrace τ h1 ω x).add (tendsto_sequenceTrace τ h1 ω y)
  map_smul' c x := by
    apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω (c • x))
    simpa only [BoundedContinuousFunction.smul_apply,map_smul,RingHom.id_apply] using
      (tendsto_sequenceTrace τ h1 ω x).const_smul c

lemma sequenceTrace_null (x : ℕ →ᵇ A) (hx : x ∈ ideal τ h1 ω htr) : sequenceTrace τ ω x = 0 := by
  apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω x)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun j => norm_trace_le τ h1 (x j))
  exact (mem_nullSubmodule _ _ x).mp hx

 
def quotientTraceLinear : Ultrapower τ h1 ω htr →ₗ[ℂ] ℂ :=
  (nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)).liftQ
    (sequenceTraceLinear τ h1 ω) (fun x hx => sequenceTrace_null τ h1 ω htr x hx)

@[simp] lemma quotientTraceLinear_mk (x : ℕ →ᵇ A) :
    quotientTraceLinear τ h1 ω htr (Ideal.Quotient.mk (ideal τ h1 ω htr) x) =
      sequenceTrace τ ω x := rfl

instance ultrapowerOrder : PartialOrder (Ultrapower τ h1 ω htr) :=
  CStarAlgebra.spectralOrder _

instance ultrapowerStarOrder : StarOrderedRing (Ultrapower τ h1 ω htr) :=
  CStarAlgebra.spectralOrderedRing _

lemma quotientTraceLinear_nonneg (X : Ultrapower τ h1 ω htr) (hX : 0 ≤ X) :
    0 ≤ quotientTraceLinear τ h1 ω htr X := by
  obtain ⟨Y,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective Y
  change 0 ≤ sequenceTrace τ ω (star y * y)
  apply ge_of_tendsto' (tendsto_sequenceTrace τ h1 ω _)
  intro j
  exact τ.map_nonneg (star_mul_self_nonneg (y j))

 
def quotientTrace : Ultrapower τ h1 ω htr →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (quotientTraceLinear τ h1 ω htr)
    (quotientTraceLinear_nonneg τ h1 ω htr)

@[simp] lemma quotientTrace_mk (x : ℕ →ᵇ A) :
    quotientTrace τ h1 ω htr (Ideal.Quotient.mk (ideal τ h1 ω htr) x) =
      sequenceTrace τ ω x := rfl

lemma quotientTrace_one : quotientTrace τ h1 ω htr 1 = 1 := by
  change sequenceTrace τ ω (1 : ℕ →ᵇ A) = 1
  apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω _)
  change Tendsto (fun _ : ℕ => τ (1:A)) (ω : Filter ℕ) (nhds 1)
  rw [h1]
  exact tendsto_const_nhds

lemma quotientTrace_tracial (X Y : Ultrapower τ h1 ω htr) :
    quotientTrace τ h1 ω htr (X*Y) = quotientTrace τ h1 ω htr (Y*X) := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective X
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective Y
  change sequenceTrace τ ω (x*y) = sequenceTrace τ ω (y*x)
  apply congrArg (limUnder (ω : Filter ℕ))
  funext j
  exact htr (x j) (y j)

lemma sequenceTrace_star_mul (x : ℕ →ᵇ A) :
    sequenceTrace τ ω (star x * x) =
      (sequenceTwoNorm (traceHilbertMap τ h1) ω x : ℂ)^2 := by
  apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω _)
  have hh := ((Complex.continuous_ofReal.tendsto _).comp
    (tendsto_sequenceTwoNorm (traceHilbertMap τ h1) ω x)).pow 2
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext j
  exact (PositiveLinearMap.preGNS_norm_sq τ (τ.toPreGNS (x j))).symm

lemma quotientTrace_preGNS_norm (X : Ultrapower τ h1 ω htr) :
    ‖(quotientTrace τ h1 ω htr).toPreGNS X‖ =
      quotientTwoNorm (traceHilbertMap τ h1) ω X := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective X
  change ‖(quotientTrace τ h1 ω htr).toPreGNS
    (Ideal.Quotient.mk (ideal τ h1 ω htr) x)‖ =
    sequenceTwoNorm (traceHilbertMap τ h1) ω x
  have hh := congrArg Complex.re
    (PositiveLinearMap.preGNS_norm_sq (quotientTrace τ h1 ω htr)
      ((quotientTrace τ h1 ω htr).toPreGNS (Ideal.Quotient.mk (ideal τ h1 ω htr) x)))
  change ((‖(quotientTrace τ h1 ω htr).toPreGNS
    (Ideal.Quotient.mk (ideal τ h1 ω htr) x)‖ : ℂ)^2).re =
      (sequenceTrace τ ω (star x*x)).re at hh
  rw [sequenceTrace_star_mul τ h1 ω] at hh
  simp only [← Complex.ofReal_pow,Complex.ofReal_re] at hh
  have hn := sequenceTwoNorm_nonneg (traceHilbertMap τ h1) ω x
  nlinarith [norm_nonneg ((quotientTrace τ h1 ω htr).toPreGNS
    (Ideal.Quotient.mk (ideal τ h1 ω htr) x))]

lemma quotientTrace_faithful (X : Ultrapower τ h1 ω htr)
    (hX : quotientTrace τ h1 ω htr (star X * X) = 0) : X = 0 := by
  apply (quotientTwoNorm_eq_zero_iff (traceHilbertMap τ h1) ω X).mp
  rw [← quotientTrace_preGNS_norm τ h1 ω htr]
  rw [PositiveLinearMap.preGNS_norm_def]
  simp [hX]

end HochschildUltrapower

namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open TracialUltrapower HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))

 
def quotientHom : (ℕ →ᵇ A) →⋆ₐ[ℂ] Ultrapower τ h1 ω htr where
  toRingHom := Ideal.Quotient.mk (ideal τ h1 ω htr)
  commutes' _ := rfl
  map_star' _ := rfl


def constant : A →⋆ₐ[ℂ] Ultrapower τ h1 ω htr :=
  (quotientHom τ h1 ω htr).comp constantSequence

lemma quotientTrace_constant (a : A) : quotientTrace τ h1 ω htr (constant τ h1 ω htr a) = τ a := by
  change sequenceTrace τ ω (BoundedContinuousFunction.const ℕ a) = τ a
  exact tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω _) tendsto_const_nhds

lemma constant_injective (hf : ∀ a : A, τ (star a*a) = 0 → a = 0) :
    Function.Injective (constant τ h1 ω htr) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hf
  rw [← quotientTrace_constant τ h1 ω htr, map_mul, map_star, map_sub, hab, sub_self,
    star_zero,zero_mul,map_zero]

variable {G : Type*} [Group G]

def boundedHom (u : ℕ → G →* unitary A) : G →* (ℕ →ᵇ A) where
  toFun g := BoundedContinuousFunction.mkOfBound
    ⟨fun j => (u j g : A), continuous_of_discreteTopology⟩ (2*‖(1:A)‖)
    (fun i j => by
      calc
        dist (u i g : A) (u j g : A) = ‖(u i g : A)-(u j g : A)‖ := dist_eq_norm _ _
        _ ≤ ‖(u i g : A)‖ + ‖(u j g : A)‖ := norm_sub_le _ _
        _ = 2*‖(1:A)‖ := by
          have hi := CStarRing.norm_coe_unitary_mul (u i g) (1:A)
          have hj := CStarRing.norm_coe_unitary_mul (u j g) (1:A)
          simp only [mul_one] at hi hj
          rw [hi,hj,two_mul])
  map_one' := by ext j; simp
  map_mul' g h := by ext j; simp

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma boundedHom_apply (u : ℕ → G →* unitary A) (g : G) (j : ℕ) :
    boundedHom u g j = (u j g : A) := rfl

end HochschildUltrapower
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Dixmier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert-space averaging and central elements in unitary orbit closures. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open Filter Topology
open scoped ComplexOrder
namespace HochschildDixmier
open BoundedHochschild HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

omit [StarOrderedRing M] in
lemma trace_orbit_hull (htr : ∀ x y : M, τ (x*y)=τ (y*x)) (a : M) :
    convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆ {b : M | τ b=τ a} := by
  apply convexHull_min
  · rintro _ ⟨u,rfl⟩; exact trace_conjugate τ htr u a
  · intro x hx y hy r t _hr _ht hrt
    change τ (r • x+t • y)=τ a
    rw [map_add,τ.map_smul_of_tower,τ.map_smul_of_tower,hx,hy,← add_smul,hrt,one_smul]

lemma trace_orbit_closure (h1 : τ 1=1) (htr : ∀ x y : M, τ (x*y)=τ (y*x)) (a b : M)
    (hb : gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) : τ b=τ a := by
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp hb
  choose c hc hcy using hy
  have hcτ : ∀ n, τ (c n)=τ a := fun n => trace_orbit_hull τ htr a (hc n)
  have ht : Tendsto (fun n => ‖τ.toPreGNS (c n-b)‖) atTop (𝓝 0) := by
    have hh := tendsto_iff_norm_sub_tendsto_zero.mp hyt
    simpa only [← hcy,← map_sub,gnsVector_norm] using hh
  have htτ : Tendsto (fun n => ‖τ (c n-b)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => HochschildUltrapower.norm_trace_le τ h1 (c n-b)) ht
  have hzero : ‖τ a-τ b‖=0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [map_sub,hcτ] using htτ)
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

end HochschildDixmier
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_DiffuseProjections
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diffuse projections of prescribed trace and conjugation estimates. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open Filter Topology
open scoped ComplexOrder
namespace HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  (τ : M →ₚ[ℂ] ℂ)



lemma projection_le_of_comparable_trace_le
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hcomp : p ≤ q ∨ q ≤ p) (ht : (τ p).re ≤ (τ q).re) : p ≤ q := by
  rcases hcomp with h|h
  · exact h
  · have hz : p-q=0 := by
      by_contra hn
      have hh := projection_trace_pos τ hfaith ((hq.le_iff_sub hp).mp h) hn
      rw [map_sub,Complex.sub_re] at hh
      linarith
    exact (sub_eq_zero.mp hz).le

end HochschildDiffuse

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TraceExpectations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace pairing norms, predual vectors and trace-preserving expectations. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder



open scoped ComplexOrder
namespace HochschildTraceNorm
open HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b : A, τ (a*b)=τ (b*a))

include htr in
lemma positive_weight_trace_bound (a x : A) (ha : 0 ≤ a) :
    ‖τ (a*x)‖ ≤ (τ a).re * ‖x‖ := by
  let r := CFC.sqrt a
  have hr : IsSelfAdjoint r := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)
  have hrr : r*r=a := CFC.sqrt_mul_sqrt_self a ha
  have hin : inner ℂ (τ.toPreGNS r) (τ.toPreGNS (x*r)) = τ (a*x) := by
    simp only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,hr.star_eq]
    rw [htr r (x*r),mul_assoc,hrr,htr x a]
  have hh : ‖τ.toPreGNS r‖^2=(τ a).re := by
    have h := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS r))
    simpa only [← Complex.ofReal_pow,Complex.ofReal_re,
      PositiveLinearMap.ofPreGNS_toPreGNS,hr.star_eq,hrr] using h
  calc
    _ = ‖inner ℂ (τ.toPreGNS r) (τ.toPreGNS (x*r))‖ := congrArg norm hin.symm
    _ ≤ ‖τ.toPreGNS r‖*‖τ.toPreGNS (x*r)‖ := norm_inner_le_norm _ _
    _ ≤ ‖τ.toPreGNS r‖*(‖x‖*‖τ.toPreGNS r‖) :=
      mul_le_mul_of_nonneg_left (preGNS_norm_mul_le τ x r) (norm_nonneg _)
    _ = (τ a).re*‖x‖ := by rw [← hh]; ring

end HochschildTraceNorm

 

open scoped ComplexOrder



open scoped ComplexOrder



open scoped ComplexOrder



open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialIsometries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial isometries and comparison of equal-trace projections. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild HochschildRigidity HochschildDixmier
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

namespace PartialIso
omit [StarOrderedRing M] in
lemma eq_of_le_of_initial_eq {v w : PartialIso M} (h : v ≤ w)
    (hi : v.initial=w.initial) : v=w := by
  apply ext
  have hh := h.2
  rw [hi,w.mul_initial] at hh
  exact hh.symm

end PartialIso

end HochschildComparison
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MatrixSystems
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix systems, expectations and rational projection approximation. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder







open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
variable {M : Type*} [CStarAlgebra M]
variable {n : ℕ} (E : MatrixSystem M n)

 
def expectation : M →ₗ[ℂ] M where
  toFun x := (n : ℂ)⁻¹ • ∑ i, ∑ j, E.entry i j*x*E.entry j i
  map_add' x y := by simp only [mul_add, add_mul, Finset.sum_add_distrib, smul_add]
  map_smul' c x := by
    simp only [mul_smul_comm, smul_mul_assoc, ← Finset.smul_sum]
    exact smul_comm _ _ _

lemma expectation_apply (x : M) : E.expectation x =
    (n : ℂ)⁻¹ • ∑ i, ∑ j, E.entry i j*x*E.entry j i := rfl

lemma expectation_star (x : M) : E.expectation (star x) = star (E.expectation x) := by
  simp [expectation_apply, star_smul, star_sum, star_mul, E.star_entry,mul_assoc]

lemma entry_mul_expectation (a b : Fin n) (x : M) :
    E.entry a b*E.expectation x =
      (n : ℂ)⁻¹ • ∑ j, E.entry a j*x*E.entry j b := by
  classical
  simp only [expectation_apply,mul_smul_comm,Finset.mul_sum,← mul_assoc,E.entry_mul]
  simp only [ite_mul,zero_mul]
  rw [Finset.sum_comm]
  simp

lemma expectation_mul_entry (a b : Fin n) (x : M) :
    E.expectation x*E.entry a b =
      (n : ℂ)⁻¹ • ∑ j, E.entry a j*x*E.entry j b := by
  have hh := congrArg star (E.entry_mul_expectation b a (star x))
  simpa [star_mul,← E.expectation_star,E.star_entry,star_smul,star_sum,mul_assoc] using hh

lemma commute_expectation (x : M) (i j : Fin n) :
    Commute (E.expectation x) (E.entry i j) :=
  (E.expectation_mul_entry i j x).trans (E.entry_mul_expectation i j x).symm

lemma expectation_eq_self (hn : n ≠ 0) (x : M)
    (hx : ∀ i j, Commute x (E.entry i j)) : E.expectation x=x := by
  classical
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  calc
    E.expectation x = (n : ℂ)⁻¹ • ∑ i, ∑ j, x*(E.entry i j*E.entry j i) := by
      simp only [expectation_apply,← mul_assoc,← fun i j => (hx i j).eq]
    _ = (n : ℂ)⁻¹ • ((n : ℂ) • (x * ∑ i, E.entry i i)) := by
      simp only [E.entry_mul,ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
      simp only [← Finset.mul_sum,nsmul_eq_mul,Nat.cast_smul_eq_nsmul]
    _ = x := by rw [E.sum_diagonal,mul_one,smul_smul,inv_mul_cancel₀ hnC,one_smul]

variable [PartialOrder M]

lemma trace_expectation (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hn : n ≠ 0) (x : M) : τ (E.expectation x)=τ x := by
  classical
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hterm (i j : Fin n) : τ (E.entry i j*x*E.entry j i)=τ (x*E.entry j j) := by
    rw [htr,← mul_assoc,E.entry_mul,ite_eq_left rfl,htr]
  simp only [expectation_apply,map_smul,map_sum,hterm]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,← map_sum,← Finset.mul_sum,
    E.sum_diagonal,mul_one,smul_eq_mul]
  simp [← Nat.cast_smul_eq_nsmul ℂ n (τ x),smul_eq_mul,hnC]

lemma trace_adjoint (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (x y : M) : τ (E.expectation x*y)=τ (x*E.expectation y) := by
  classical
  have hterm (i j : Fin n) : τ ((E.entry i j*x*E.entry j i)*y)=
      τ (x*(E.entry j i*y*E.entry i j)) := by
    rw [mul_assoc,mul_assoc,htr]
    simp only [mul_assoc]
  simp only [expectation_apply,smul_mul_assoc,mul_smul_comm,map_smul,
    Finset.sum_mul,Finset.mul_sum,map_sum,hterm]
  rw [Finset.sum_comm]

end MatrixSystem
end HochschildMatrixSystems

 

 

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MatrixCommutants
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix coefficients, commutant algebras and their preduals. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
variable {M : Type*} [CStarAlgebra M]
variable {n : ℕ} (E : MatrixSystem M n)

 
def commutant : StarSubalgebra ℂ M where
  carrier := {x | ∀ i j, Commute x (E.entry i j)}
  zero_mem' := fun i j => Commute.zero_left _
  one_mem' := fun i j => Commute.one_left _
  add_mem' := fun hx hy i j => (hx i j).add_left (hy i j)
  mul_mem' := fun hx hy i j => (hx i j).mul_left (hy i j)
  algebraMap_mem' c := fun i j => Algebra.commutes c (E.entry i j)
  star_mem' := fun hx i j => by
    have hh := congrArg star (hx j i).eq
    change _ * _ = _ * _
    simpa only [star_mul,E.star_entry] using hh.symm

instance commutant_closed : IsClosed (E.commutant : Set M) := by
  change IsClosed {x : M | ∀ i j, x*E.entry i j = E.entry i j*x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

 
def coefficient (i j : Fin n) (x : M) : M := ∑ k, E.entry k i*x*E.entry j k

lemma entry_mul_coefficient (a b i j : Fin n) (x : M) :
    E.entry a b*E.coefficient i j x=E.entry a i*x*E.entry j b := by
  classical
  simp only [coefficient,Finset.mul_sum,← mul_assoc,E.entry_mul,ite_mul,zero_mul]
  simp

lemma coefficient_mul_entry (a b i j : Fin n) (x : M) :
    E.coefficient i j x*E.entry a b=E.entry a i*x*E.entry j b := by
  classical
  simp only [coefficient,Finset.sum_mul,mul_assoc,E.entry_mul,mul_ite,mul_zero]
  simp [← mul_assoc]

lemma coefficient_mem (i j : Fin n) (x : M) : E.coefficient i j x ∈ E.commutant := by
  intro a b
  exact (E.coefficient_mul_entry a b i j x).trans (E.entry_mul_coefficient a b i j x).symm

lemma reconstruct (x : M) : ∑ i, ∑ j, E.entry i j*E.coefficient i j x=x := by
  simp only [E.entry_mul_coefficient,← Finset.mul_sum,← Finset.sum_mul,E.sum_diagonal,one_mul,mul_one]

lemma factor_of_commutant (A : StarSubalgebra ℂ M) (hA : A=E.commutant)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M)) :
    ∀ b : A, (∀ x : A, Commute b x) → ∃ c : ℂ, b=c • (1 : A) := by
  subst A
  intro b hb
  have hc : ∀ x : M, Commute (b:M) x := by
    intro x
    rw [← E.reconstruct x]
    apply Commute.sum_right
    intro i hi
    apply Commute.sum_right
    intro j hj
    exact (b.property i j).mul_right (show Commute (b:M) (E.coefficient i j x) from
      congrArg (fun z : E.commutant => (z:M)) (hb ⟨_,E.coefficient_mem i j x⟩).eq)
  obtain ⟨c,hc⟩ := hfactor b hc
  exact ⟨c,Subtype.ext hc⟩

lemma coefficient_star (i j : Fin n) (x : M) :
    star (E.coefficient i j x)=E.coefficient j i (star x) := by
  simp only [coefficient,star_sum,star_mul,E.star_entry,mul_assoc]

lemma coefficient_corner (i : Fin n) (x : M) :
    E.entry i i*E.coefficient i i x*E.entry i i = E.entry i i*x*E.entry i i := by
  rw [E.entry_mul_coefficient,mul_assoc,E.entry_mul,ite_eq_left rfl]

lemma coefficient_mul (i : Fin n) (x y : M) :
    E.coefficient i i x*E.coefficient i i y = E.coefficient i i (x*E.entry i i*y) := by
  classical
  simp only [coefficient,Finset.sum_mul,Finset.mul_sum]
  congr 1
  ext j
  have hterm (k : Fin n) :
      (E.entry k i*x*E.entry i k)*(E.entry j i*y*E.entry i j)=
        if k=j then E.entry j i*(x*E.entry i i*y)*E.entry i j else 0 := by
    by_cases h : k=j
    · subst k
      rw [ite_eq_left rfl]
      calc
        (E.entry j i*x*E.entry i j)*(E.entry j i*y*E.entry i j) =
            E.entry j i*x*(E.entry i j*E.entry j i)*y*E.entry i j := by noncomm_ring
        _ = _ := by rw [E.entry_mul,ite_eq_left rfl]; noncomm_ring
    · rw [ite_eq_right h]
      calc
        (E.entry k i*x*E.entry i k)*(E.entry j i*y*E.entry i j) =
            E.entry k i*x*(E.entry i k*E.entry j i)*y*E.entry i j := by noncomm_ring
        _ = 0 := by rw [E.entry_mul,ite_eq_right h,mul_zero,zero_mul,zero_mul]
  simp only [hterm]
  simp

lemma diagonal_proj (i : Fin n) : IsStarProjection (E.entry i i) := by
  exact ⟨by change E.entry i i*E.entry i i=E.entry i i; rw [E.entry_mul,ite_eq_left rfl],
    by change star (E.entry i i)=E.entry i i; exact E.star_entry i i⟩

variable [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma coefficient_of_commutant (i : Fin n) {x : M} (hx : x ∈ E.commutant) :
    E.coefficient i i (E.entry i i*x)=x := by
  classical
  calc
    E.coefficient i i (E.entry i i*x) = ∑ k, (E.entry k k)*x := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        E.entry k i*(E.entry i i*x)*E.entry i k = (E.entry k i*E.entry i i)*(x*E.entry i k) := by
          noncomm_ring
        _ = (E.entry k i*E.entry i i)*(E.entry i k*x) := by rw [(hx i k).eq]
        _ = E.entry k k*x := by rw [E.entry_mul,ite_eq_left rfl,← mul_assoc,E.entry_mul,ite_eq_left rfl]
    _ = x := by rw [← Finset.sum_mul,E.sum_diagonal,one_mul]

end MatrixSystem
end HochschildMatrixSystems

 

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CommutantQuantization
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small matrix expectations and coefficient energy bounds. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
variable {M : Type*} [CStarAlgebra M]
variable {n : ℕ} (E : MatrixSystem M n)

lemma coefficient_product_matrix (i l : Fin n) (x y : M) :
    E.coefficient i l (x*y)=∑ j, E.coefficient i j x*E.coefficient j l y := by
  classical
  symm
  calc
    _ = ∑ j,∑ k, E.entry k i*x*(E.entry j j*y*E.entry l k) := by
      apply Finset.sum_congr rfl
      intro j hj
      change (∑ k,E.entry k i*x*E.entry j k)*E.coefficient j l y=_
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_assoc,E.entry_mul_coefficient]
    _ = ∑ k, E.entry k i*x*((∑ j,E.entry j j)*y*E.entry l k) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
    _ = _ := by simp only [E.sum_diagonal,one_mul,coefficient,mul_assoc]

lemma sum_coefficient_diagonal (hn : n ≠ 0) (x : M) :
    (∑ i,E.coefficient i i x)=(n:ℂ) • E.expectation x := by
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [coefficient,expectation_apply,smul_smul,mul_inv_cancel₀ hnC,one_smul]
  exact Finset.sum_comm

variable [PartialOrder M] [StarOrderedRing M]

lemma coefficient_norm_sq_sum (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (x : M) :
    (∑ i,∑ j, ‖τ.toPreGNS (E.coefficient i j x)‖^2)=(n:ℝ)*‖τ.toPreGNS x‖^2 := by
  have hh : (∑ i,∑ j,τ (star (E.coefficient j i x)*E.coefficient j i x))=
      (n:ℂ)*τ (star x*x) := by
    simp only [E.coefficient_star,← map_sum,← E.coefficient_product_matrix]
    rw [E.sum_coefficient_diagonal hn,map_smul,smul_eq_mul,E.trace_expectation τ htr hn]
  have hr := congrArg Complex.re hh
  simp only [Complex.re_sum,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at hr
  simp only [norm_sq]
  rw [Finset.sum_comm]
  exact hr

omit [StarOrderedRing M] in
lemma trace_entry_commutant (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (c : M)
    (hc : c ∈ E.commutant) (i j : Fin n) :
    τ (E.entry i j*c)=if i=j then (n:ℂ)⁻¹*τ c else 0 := by
  classical
  have hcyc (k : Fin n) : τ (E.entry k k*c)=τ (E.entry i i*c) := by
    calc
      _ = τ (E.entry k i*(E.entry i k*c)) := by rw [← mul_assoc,E.entry_mul,ite_eq_left rfl]
      _ = τ ((E.entry i k*c)*E.entry k i) := htr _ _
      _ = _ := by rw [mul_assoc,(hc k i).eq,← mul_assoc,E.entry_mul,ite_eq_left rfl]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl]
    have hh : (n:ℂ)*τ (E.entry i i*c)=τ c := by
      calc
        _ = ∑ k,τ (E.entry k k*c) := by
          simp only [hcyc,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        _ = τ c := by rw [← map_sum,← Finset.sum_mul,E.sum_diagonal,one_mul]
    have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    rw [← hh,← mul_assoc,inv_mul_cancel₀ hnC,one_mul]
  · rw [ite_eq_right hij]
    calc
      _ = τ (E.entry i j*(E.entry j j*c)) := by rw [← mul_assoc,E.entry_mul,ite_eq_left rfl]
      _ = τ ((E.entry j j*c)*E.entry i j) := htr _ _
      _ = 0 := by rw [mul_assoc,(hc i j).eq,← mul_assoc,E.entry_mul,ite_eq_right (Ne.symm hij),zero_mul,map_zero]

end MatrixSystem
end HochschildMatrixSystems
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Corners
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.CStarCorner.instAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.BoundedHochschild.CentralCorner.compressMap_coe _root_.OAI.BoundedHochschild.CentralCorner.compressMap_includeMap _root_.OAI.BoundedHochschild.CentralCorner.extend_apply _root_.OAI.BoundedHochschild.CentralCorner.includeMap_apply _root_.OAI.BoundedHochschild.CentralCorner.restrict_apply _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.nestedCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.HochschildPatching.ofCornerUnitary_coe _root_.OAI.HochschildPatching.ofCornerUnitary_support _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral corners, corner preduals and factor structure. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder







open Filter Topology
open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (p : M) (hp : IsStarProjection p)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

lemma cornerTrace_one (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hp0 : p ≠ 0) :
    cornerTrace p hp τ 1=1 := by
  rw [cornerTrace_apply,corner_coe_one,projection_trace_real τ p hp]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
    (HochschildDiffuse.projection_trace_pos τ hfaith hp hp0).ne')

end HochschildCorners

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (p : M) (hp : IsStarProjection p)

lemma corner_factor_of_matrix_diagonal {n : ℕ} (E : MatrixSystem M n) (i : Fin n)
    (hip : E.entry i i ≤ p)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M)) :
    ∀ b : Corner p hp, (∀ x : Corner p hp, Commute b x) → ∃ c : ℂ, b=c • (1 : Corner p hp) := by
  intro b hb
  let r := E.entry i i
  have hr := E.diagonal_proj i
  have hpr : p*r=r := (hr.le_iff_mul_eq_right hp).mp hip
  have hrp : r*p=r := (hr.le_iff_mul_eq_left hp).mp hip
  have hrmem : r ∈ corner p hp := ⟨hpr,hrp⟩
  have hbr : Commute (b:M) r := congrArg (fun a : Corner p hp => (a:M)) (hb ⟨r,hrmem⟩).eq
  let d : E.commutant := ⟨E.coefficient i i (b:M),E.coefficient_mem i i b⟩
  have hd : ∀ c : E.commutant, Commute d c := by
    intro c
    have hrc : r*(c:M)=(c:M)*r := (c.property i i).eq.symm
    have hrrc : r*(r*(c:M))=r*(c:M) := by rw [← mul_assoc,hr.isIdempotentElem.eq]
    have hrcr : (r*(c:M))*r=r*(c:M) := by rw [hrc,mul_assoc,hr.isIdempotentElem.eq]
    have hcpm : r*(c:M) ∈ corner p hp := ⟨by rw [← mul_assoc,hpr],by
      rw [hrc,mul_assoc,hrp]⟩
    have hbc : (b:M)*(r*(c:M))=(r*(c:M))*(b:M) :=
      congrArg (fun a : Corner p hp => (a:M)) (hb ⟨_,hcpm⟩).eq
    apply Subtype.ext
    change E.coefficient i i (b:M)*(c:M)=(c:M)*E.coefficient i i (b:M)
    calc
      _ = E.coefficient i i (b:M)*E.coefficient i i (r*(c:M)) := by
        rw [E.coefficient_of_commutant i c.property]
      _ = E.coefficient i i ((b:M)*r*(r*(c:M))) := E.coefficient_mul i _ _
      _ = E.coefficient i i ((r*(c:M))*r*(b:M)) := by
        rw [mul_assoc (b:M) r,hrrc,hbc,hrcr]
      _ = E.coefficient i i (r*(c:M))*E.coefficient i i (b:M) := (E.coefficient_mul i _ _).symm
      _ = _ := by rw [E.coefficient_of_commutant i c.property]
  obtain ⟨c,hc⟩ := E.factor_of_commutant _ rfl hfactor d hd
  have hdc : E.coefficient i i (b:M)=c • (1:M) := congrArg (fun a : E.commutant => (a:M)) hc
  have hbrc : (b:M)*r=c • r := by
    have hh := E.coefficient_corner i (b:M)
    rw [hdc, mul_smul_comm,smul_mul_assoc,mul_one,hr.isIdempotentElem.eq] at hh
    rw [← hbr.eq,mul_assoc,hr.isIdempotentElem.eq] at hh
    exact hh.symm
  let a := (b:M)-c • p
  have hap : a*p=a := by dsimp [a]; rw [sub_mul,b.property.2,smul_mul_assoc,hp.isIdempotentElem.eq]
  have har : a*r=0 := by dsimp [a]; rw [sub_mul,hbrc,smul_mul_assoc,hpr,sub_self]
  have hra : r*a=0 := by dsimp [a]; rw [mul_sub,← hbr.eq,hbrc,mul_smul_comm,hrp,sub_self]
  have haxr (x : M) : a*x*r=0 := by
    have hmem : p*x*r ∈ corner p hp := ⟨by rw [← mul_assoc,← mul_assoc,hp.isIdempotentElem.eq],by
      rw [mul_assoc,hrp]⟩
    have hbX : (b:M)*(p*x*r)=(p*x*r)*(b:M) :=
      congrArg (fun y : Corner p hp => (y:M)) (hb ⟨_,hmem⟩).eq
    have hac : a*(p*x*r)=(p*x*r)*a := by
      dsimp [a]
      rw [sub_mul,mul_sub,hbX,smul_mul_assoc,mul_smul_comm,hmem.1,hmem.2]
    calc
      a*x*r = a*(p*x*r) := by rw [← mul_assoc,← mul_assoc,hap]
      _ = (p*x*r)*a := hac
      _ = 0 := by rw [mul_assoc,hra,mul_zero]
  have ha0 : a=0 := by
    calc
      a = ∑ j, a*E.entry j j := by rw [← Finset.mul_sum,E.sum_diagonal,mul_one]
      _ = ∑ j, (a*E.entry j i*r)*E.entry i j := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [r]
        rw [mul_assoc a (E.entry j i),E.entry_mul,ite_eq_left rfl,mul_assoc,E.entry_mul,ite_eq_left rfl]
      _ = 0 := by simp only [haxr,zero_mul,Finset.sum_const_zero]
  refine ⟨c,Subtype.ext (sub_eq_zero.mp ha0)⟩

end HochschildCorners
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FinitePhases
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite additive characters, phase matrices and orthogonality. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
namespace HochschildFinitePhase
variable {I : Type*} [Fintype I]

variable [DecidableEq I]

lemma sum_character (v : I → ZMod 3) :
    ∑ g,character v g=if v=0 then (Fintype.card (I → ZMod 3):ℂ) else 0 := by
  classical
  by_cases hv : v=0
  · subst v
    simp only [character_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,ite_true]
  · rw [ite_eq_right hv]
    exact AddChar.sum_eq_zero_of_ne_one ((character_eq_one_iff v).not.mpr hv)

lemma orthogonality (v w : I → ZMod 3) :
    ∑ g,star (character v g)*character w g=
      if v=w then (Fintype.card (I → ZMod 3):ℂ) else 0 := by
  classical
  simp only [character_star,← character_add,sum_character]
  congr 1
  exact propext neg_add_eq_zero

lemma character_parseval {J H : Type*} [Fintype J] [SeminormedAddCommGroup H]
    [InnerProductSpace ℂ H] (f : J → (I → ZMod 3)) (hf : Function.Injective f) (v : J → H) :
    (∑ g : I → ZMod 3, ‖∑ j, character (f j) g • v j‖^2)=
      (Fintype.card (I → ZMod 3):ℝ)*(∑ j,‖v j‖^2) := by
  classical
  have hh : (∑ g : I → ZMod 3, ⟪∑ j, character (f j) g • v j,
      ∑ j,character (f j) g • v j⟫_ℂ)=
      (Fintype.card (I → ZMod 3):ℂ)*(∑ j,⟪v j,v j⟫_ℂ) := by
    simp only [sum_inner,inner_sum]
    simp only [inner_smul_left,inner_smul_right]
    calc
      _ = ∑ j,∑ k,(∑ g,star (character (f k) g)*character (f j) g)*⟪v k,v j⟫_ℂ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro g hg
        simp only [Complex.star_def]
        ring
      _ = _ := by simp only [orthogonality,hf.eq_iff]; simp [← Finset.mul_sum]
  have hr := congrArg Complex.re hh
  simp only [Complex.re_sum,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    zero_mul,sub_zero] at hr
  simpa only [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex] using hr

end HochschildFinitePhase

 

 

open scoped BigOperators ComplexConjugate InnerProductSpace
namespace HochschildFinitePhase
variable {I : Type*} [DecidableEq I]

def extendedFrequency : Option (OffDiagonal I) → (I → ZMod 3)
  | none => 0
  | some p => frequency p.val.1 p.val.2

lemma extendedFrequency_injective : Function.Injective (extendedFrequency (I:=I)) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact False.elim (frequency_ne_zero b.property h.symm)
  | some a =>
    cases b with
    | none => exact False.elim (frequency_ne_zero a.property h)
    | some b =>
      have hab := frequency_injective a.property b.property h
      congr 1
      exact Subtype.ext (Prod.ext hab.1 hab.2)

variable [Fintype I]

lemma character_single (i : I) (g : I → ZMod 3) : character (Pi.single i 1) g=phase g i := by
  simp [character_apply,Pi.single_apply,phase]

lemma character_frequency (i j : I) (g : I → ZMod 3) :
    character (frequency i j) g=star (phase g i)*phase g j := by
  rw [frequency,sub_eq_add_neg,character_add,← character_star]
  simp only [character_single]
  exact mul_comm _ _

lemma offDiagonal_sum {A : Type*} [AddCommMonoid A] (f : I → I → A) :
    (∑ p : OffDiagonal I, f p.val.1 p.val.2)=∑ i,∑ j,if i=j then 0 else f i j := by
  classical
  rw [← Fintype.sum_prod_type (f := fun p : I × I => if p.1=p.2 then (0:A) else f p.1 p.2)]
  change (∑ p : {p : I × I // p.1 ≠ p.2}, f p.val.1 p.val.2)=_
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : I × I => p.1 ≠ p.2)) (by simp)
    (fun p => f p.1 p.2),Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp_all

lemma phase_star_self (g : I → ZMod 3) (i : I) : star (phase g i)*phase g i=1 := by
  rw [← character_single i g,character_star,← character_add,neg_add_cancel,character_zero]

lemma extended_sum {A : Type*} [AddCommMonoid A] [Module ℂ A] (c : I → I → A)
    (g : I → ZMod 3) :
    (∑ p : Option (OffDiagonal I),character (extendedFrequency p) g •
      (Option.rec (∑ i,c i i) (fun p : OffDiagonal I => c p.val.1 p.val.2) p))=
      ∑ i,∑ j,(star (phase g i)*phase g j) • c i j := by
  classical
  rw [Fintype.sum_option]
  simp only [extendedFrequency,character_zero,one_smul,character_frequency]
  rw [offDiagonal_sum (fun i j => (star (phase g i)*phase g j) • c i j),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : c i i = ∑ j : I,if i=j then c i i else 0 := by simp
  rw [hd,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl,ite_eq_left rfl,add_zero,phase_star_self,one_smul]
  · simp [hij]

lemma phase_parseval {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : I → I → H) :
    (∑ g : I → ZMod 3, ‖∑ i,∑ j,(star (phase g i)*phase g j) • c i j‖^2)=
      (Fintype.card (I → ZMod 3):ℝ)*
        (‖∑ i,c i i‖^2+∑ i,∑ j,if i=j then 0 else ‖c i j‖^2) := by
  let v : Option (OffDiagonal I) → H := fun p => Option.rec (∑ i,c i i)
    (fun p : OffDiagonal I => c p.val.1 p.val.2) p
  calc
    _ = ∑ g : I → ZMod 3,‖∑ p,character (extendedFrequency p) g • v p‖^2 := by
      apply Finset.sum_congr rfl
      intro g hg
      congr 2
      exact (extended_sum c g).symm
    _ = _ := by
      rw [character_parseval extendedFrequency extendedFrequency_injective v]
      simp only [v,Fintype.sum_option]
      rw [offDiagonal_sum (fun i j => ‖c i j‖^2)]

end HochschildFinitePhase
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialUnitaries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial unitaries, ordered limits and trace estimates. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace PartialUnitary
section
omit [PartialOrder M] [StarOrderedRing M]

lemma support_proj (v : PartialUnitary M) : IsStarProjection v.support := v.val.initial_proj
lemma star_mul_self_eq_support (v : PartialUnitary M) : star (v : M)*v=v.support := rfl
lemma mul_star_self_eq_support (v : PartialUnitary M) : (v : M)*star (v : M)=v.support := v.property
lemma mul_support (v : PartialUnitary M) : (v : M)*v.support=v := v.val.mul_initial
lemma support_mul (v : PartialUnitary M) : v.support*(v : M)=v := by
  change v.val.initial*(v : M)=v
  rw [← v.property]; exact v.val.final_mul
lemma star_support (v : PartialUnitary M) : star (v : M)*v.support=star (v : M) := by
  simpa only [star_mul,star_star,v.support_proj.isSelfAdjoint.star_eq] using congrArg star v.support_mul
lemma support_star (v : PartialUnitary M) : v.support*star (v : M)=star (v : M) := by
  simpa only [star_mul,star_star,v.support_proj.isSelfAdjoint.star_eq] using congrArg star v.mul_support
end

section
omit [PartialOrder M] [StarOrderedRing M]

lemma orthogonal_symm {v w : PartialUnitary M} (h : v.support*w.support=0) : w.support*v.support=0 :=
  PartialIso.orthogonal_initial_symm h
lemma mul_eq_zero {v w : PartialUnitary M} (h : v.support*w.support=0) : (v : M)*w=0 := by
  calc
    _ = ((v : M)*v.support)*(w.support*(w : M)) := by rw [mul_support,support_mul]
    _ = (v : M)*(v.support*w.support)*w := by simp only [mul_assoc]
    _ = 0 := by rw [h,mul_zero,zero_mul]

lemma support_orthogonalSum (v w : PartialUnitary M) (h : v.support*w.support=0) :
    (v.orthogonalSum w h).support=v.support+w.support :=
  PartialIso.orthogonalSum_initial v.val w.val h (by simpa only [v.property,w.property] using h)
end



section
omit [PartialOrder M] [StarOrderedRing M]

def power (v : PartialUnitary M) (k : Bool × ℕ) : M :=
  (if k.1 then star (v : M) else (v : M))^(k.2+1)
lemma support_power (v : PartialUnitary M) (k : Bool × ℕ) : v.support*v.power k=v.power k := by
  have h : v.support*(if k.1 then star (v : M) else (v : M)) =
      (if k.1 then star (v : M) else (v : M)) := by split <;> first | exact v.support_star | exact v.support_mul
  dsimp only [power]
  rw [pow_succ',← mul_assoc,h]
lemma power_support (v : PartialUnitary M) (k : Bool × ℕ) : v.power k*v.support=v.power k := by
  have h : (if k.1 then star (v : M) else (v : M))*v.support =
      (if k.1 then star (v : M) else (v : M)) := by split <;> first | exact v.star_support | exact v.mul_support
  dsimp only [power]
  rw [pow_succ,mul_assoc,h]

lemma add_pow_succ_of_orthogonal {a b : M} (hab : a*b=0) (hba : b*a=0) (n : ℕ) :
    (a+b)^(n+1)=a^(n+1)+b^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,ih,add_mul,mul_add,mul_add,← pow_succ,← pow_succ]
    have h₁ : a^(n+1)*b=0 := by rw [pow_succ,mul_assoc,hab,mul_zero]
    have h₂ : b^(n+1)*a=0 := by rw [pow_succ,mul_assoc,hba,mul_zero]
    rw [h₁,h₂,add_zero,zero_add]
lemma power_orthogonalSum (v w : PartialUnitary M) (h : v.support*w.support=0) (k : Bool × ℕ) :
    (v.orthogonalSum w h).power k=v.power k+w.power k := by
  have hab := mul_eq_zero h
  have hba := mul_eq_zero (orthogonal_symm h)
  dsimp only [power]
  rw [coe_orthogonalSum]
  split
  · rw [star_add]
    exact add_pow_succ_of_orthogonal (by simpa only [star_mul,star_zero] using congrArg star hba)
      (by simpa only [star_mul,star_zero] using congrArg star hab) _
  · exact add_pow_succ_of_orthogonal hab hba _
end

end PartialUnitary
end HochschildComparison

 

 

open Filter Topology
open scoped ComplexOrder







open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include htr in
lemma norm_trace_mul_le_gns (a b : M) :
    ‖τ (a*b)‖ ≤ ‖τ.toPreGNS a‖*‖τ.toPreGNS b‖ := by
  have hi : inner ℂ (τ.toPreGNS (star a)) (τ.toPreGNS b)=τ (a*b) := by
    simp only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,star_star]
  rw [← hi]
  simpa only [preGNS_norm_star τ htr] using norm_inner_le_norm (𝕜 := ℂ) (τ.toPreGNS (star a)) (τ.toPreGNS b)

include htr in
lemma small_compression_trace_bound {q : M} (hq : IsStarProjection q)
    (A x z y B : M) (c : ℂ) (ε : ℝ)
    (hA : ‖A‖ ≤ 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hxq : x*q=x) (hqy : q*y=y)
    (hsmall : ‖τ.toPreGNS (q*z*q-c • q)‖ ≤ ε*‖τ.toPreGNS q‖) :
    ‖τ (A*x*z*y*B)‖ ≤ (ε+‖c‖)*(τ q).re := by
  let D : M := q*z*q-c • q
  let G : M := y*B*A*x
  have hG : ‖G‖ ≤ 1 := by
    dsimp [G]
    simpa only [one_mul] using norm_mul_le_of_le (norm_mul_le_of_le (norm_mul_le_of_le hy hB) hA) hx
  have hGq : G*q=G := by dsimp [G]; simp only [mul_assoc,hxq]
  have hqG : q*G=G := by dsimp [G]; rw [← mul_assoc,← mul_assoc,← mul_assoc,hqy]
  have hGgns : ‖τ.toPreGNS G‖ ≤ ‖τ.toPreGNS q‖ := by
    calc
      _ = ‖τ.toPreGNS (G*q)‖ := congrArg (fun t => ‖τ.toPreGNS t‖) hGq.symm
      _ ≤ ‖G‖*‖τ.toPreGNS q‖ := preGNS_norm_mul_le τ G q
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hG (norm_nonneg _)
  have hrotate : τ (A*x*z*y*B)=τ (z*G) := by
    calc
      _ = τ ((A*x)*(z*y*B)) := by congr 1; simp only [mul_assoc]
      _ = τ ((z*y*B)*(A*x)) := htr _ _
      _ = _ := by congr 1; simp only [G,mul_assoc]
  have hinsert : τ (q*z*q*G)=τ (z*G) := by
    calc
      _ = τ (q*(z*G)) := by congr 1; simp only [mul_assoc,hqG]
      _ = τ ((z*G)*q) := htr _ _
      _ = _ := by rw [mul_assoc,hGq]
  have htrace : τ (A*x*z*y*B)=τ (D*G)+c*τ (q*G) := by
    calc
      _ = τ (q*z*q*G) := hrotate.trans hinsert.symm
      _ = τ (D*G+c • (q*G)) := by
        congr 1
        simp only [D,sub_mul,smul_mul_assoc,sub_add_cancel]
      _ = _ := by rw [map_add,map_smul,smul_eq_mul]
  have hscalar : ‖τ (q*G)‖ ≤ (τ q).re := by
    exact (HochschildTraceNorm.positive_weight_trace_bound τ htr q G hq.nonneg).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hG (τ.map_nonneg hq.nonneg).1)
  have herror : ‖τ (D*G)‖ ≤ ε*(τ q).re := by
    apply (norm_trace_mul_le_gns τ htr D G).trans
    calc
      _ ≤ (ε*‖τ.toPreGNS q‖)*‖τ.toPreGNS q‖ := mul_le_mul hsmall hGgns (norm_nonneg _) (hsmall.trans' (norm_nonneg _))
      _ = _ := by rw [← projection_gns_sq τ hq]; ring
  rw [htrace]
  apply (norm_add_le _ _).trans
  rw [norm_mul,add_mul]
  exact add_le_add herror (mul_le_mul_of_nonneg_left hscalar (norm_nonneg c))
end HochschildPatching
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MixedWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mixed-word Taylor expansions, moment corners and patch coefficients. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M]


variable {I : Type*} (F : I → M)

variable [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
include htr in
lemma wordProduct_tendsto {J L : Type*} {f : Filter L} (ρ : L → J → M) (σ : J → M)
    (hρ : ∀ k, GNSTendsto τ (fun i => ρ i k) f (σ k))
    (hbn : ∀ i k, ‖ρ i k‖ ≤ 1) (l : List (J × M)) :
    GNSTendsto τ (fun i => wordProduct (ρ i) l) f (wordProduct σ l) := by
  induction l with
  | nil => exact GNSTendsto.const τ 1 f
  | cons ka l ih =>
    obtain ⟨k,a⟩ := ka
    apply GNSTendsto.mul τ htr ((hρ k).mul τ htr (GNSTendsto.const τ a f) 1 (fun i => hbn i k)) ih ‖a‖
    intro i
    simpa only [one_mul] using norm_mul_le_of_le (hbn i k) (le_refl ‖a‖)

lemma trace_tendsto_of_gns (h1 : τ 1=1) {J : Type*} {f : Filter J} {x : J → M} {y : M}
    (h : GNSTendsto τ x f y) : Tendsto (fun i => τ (x i)) f (𝓝 (τ y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ h
  intro i
  rw [← map_sub]
  exact HochschildUltrapower.norm_trace_le τ h1 _


end HochschildPatching

 

 

open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison

variable {M : Type*} [CStarAlgebra M]
variable {I : Type*} (F : I → M)
def atomPower {K : ℕ} (v : PartialUnitary M) (a : WordAtom I K) : M := v.power (a.1.1,a.1.2.val)
end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M]
variable {I : Type*} (F : I → M) (τ : M →ₚ[ℂ] ℂ)

lemma normalized_corner_trace_eq (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (v : PartialUnitary M) (z : M) :
    τ ((1-v.support)*z*(1-v.support))=τ z-τ (star (v:M)*z*(v:M)) := by
  have hp := v.support_proj.one_sub
  have hcompress : τ ((1-v.support)*z*(1-v.support))=τ ((1-v.support)*z) := by
    rw [htr,← mul_assoc,hp.isIdempotentElem.eq]
  rw [hcompress,sub_mul,one_mul,map_sub]
  congr 1
  rw [htr (star (v:M)*z) (v:M),← mul_assoc,v.mul_star_self_eq_support]

end HochschildPatching

 

 

open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {I : Type*} (F : I → M)

variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

def residualScalar (v : PartialUnitary M) (z : M) : ℂ :=
  (((τ (1-v.support)).re : ℂ)⁻¹)*τ ((1-v.support)*z*(1-v.support))
end HochschildPatching
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_RankOneQuantization
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rank-one projections, phase coefficients and small corners. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
open HochschildFinitePhase
variable {M : Type*} [CStarAlgebra M]
variable {n : ℕ} (E : MatrixSystem M n)

def scalarMatrix (a : Fin n → Fin n → ℂ) : M := ∑ i,∑ j,a i j • E.entry i j

lemma scalarMatrix_mul (a b : Fin n → Fin n → ℂ) :
    E.scalarMatrix a * E.scalarMatrix b = E.scalarMatrix (fun i l => ∑ j,a i j*b j l) := by
  classical
  simp only [scalarMatrix,Finset.sum_mul,Finset.mul_sum,smul_mul_smul_comm,E.entry_mul,
    smul_ite,smul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  calc
    _ = ∑ j,∑ i,∑ l,(a i j*b j l) • E.entry i l :=
      Finset.sum_congr rfl (fun j hj => Finset.sum_comm)
    _ = ∑ i,∑ j,∑ l,(a i j*b j l) • E.entry i l := Finset.sum_comm
    _ = ∑ i,∑ l,∑ j,(a i j*b j l) • E.entry i l :=
      Finset.sum_congr rfl (fun i hi => Finset.sum_comm)
    _ = _ := by simp only [Finset.sum_smul]

lemma scalarMatrix_star (a : Fin n → Fin n → ℂ) :
    star (E.scalarMatrix a)=E.scalarMatrix (fun i j => star (a j i)) := by
  simp only [scalarMatrix,star_sum,star_smul,E.star_entry]
  exact Finset.sum_comm

lemma phase_star_self' (g : Fin n → ZMod 3) (i : Fin n) :
    phase g i*star (phase g i)=1 := by rw [mul_comm]; exact phase_star_self g i

def rankOne (g : Fin n → ZMod 3) : M :=
  E.scalarMatrix (fun i j => (n:ℂ)⁻¹*(phase g i*star (phase g j)))

lemma rankOne_star (g : Fin n → ZMod 3) : star (E.rankOne g)=E.rankOne g := by
  rw [rankOne,scalarMatrix_star]
  congr 1
  funext i j
  simp only [star_mul,star_inv₀,star_natCast,star_star]
  ring

lemma rankOne_mul (hn : n ≠ 0) (g : Fin n → ZMod 3) : E.rankOne g*E.rankOne g=E.rankOne g := by
  rw [rankOne,scalarMatrix_mul]
  congr 1
  funext i l
  have ht (j : Fin n) :
      ((n:ℂ)⁻¹*(phase g i*star (phase g j)))*((n:ℂ)⁻¹*(phase g j*star (phase g l)))=
        ((n:ℂ)⁻¹)^2*(phase g i*star (phase g l)) := by
    calc
      _ = ((n:ℂ)⁻¹)^2*(phase g i*star (phase g l))*(star (phase g j)*phase g j) := by ring
      _ = _ := by rw [phase_star_self,mul_one]
  simp only [ht,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp

lemma rankOne_projection (hn : n ≠ 0) (g : Fin n → ZMod 3) : IsStarProjection (E.rankOne g) :=
  ⟨E.rankOne_mul hn g,E.rankOne_star g⟩

section
variable [PartialOrder M]

lemma trace_scalarMatrix_commutant (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0)
    (a : Fin n → Fin n → ℂ) (c : M) (hc : c ∈ E.commutant) :
    τ (E.scalarMatrix a*c)=(n:ℂ)⁻¹*(∑ i,a i i)*τ c := by
  simp only [scalarMatrix,Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,smul_eq_mul,
    E.trace_entry_commutant τ htr hn c hc,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [← Finset.sum_mul]
  ring

lemma trace_rankOne_commutant (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0)
    (g : Fin n → ZMod 3) (c : M) (hc : c ∈ E.commutant) :
    τ (E.rankOne g*c)=(n:ℂ)⁻¹*τ c := by
  rw [rankOne,E.trace_scalarMatrix_commutant τ htr hn _ c hc]
  simp only [phase_star_self',mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul]
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  rw [mul_inv_cancel₀ hnC,mul_one]

lemma trace_rankOne (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (h1 : τ 1=1) (hn : n ≠ 0)
    (g : Fin n → ZMod 3) : τ (E.rankOne g)=(n:ℂ)⁻¹ := by
  simpa only [mul_one,h1] using E.trace_rankOne_commutant τ htr hn g 1 E.commutant.one_mem

end

lemma coefficient_ext {x y : M} (h : ∀ i j,E.coefficient i j x=E.coefficient i j y) : x=y := by
  rw [← E.reconstruct x,← E.reconstruct y]
  simp only [h]

lemma coefficient_entry (i j a b : Fin n) :
    E.coefficient i j (E.entry a b)=if i=a ∧ b=j then (1:M) else 0 := by
  classical
  simp only [coefficient,E.entry_mul,ite_mul,zero_mul]
  by_cases hia : i=a
  · subst a
    by_cases hbj : b=j
    · subst b
      simp only [ite_true,and_self,E.sum_diagonal]
    · simp [hbj]
  · simp [hia]

lemma coefficient_smul (i j : Fin n) (c : ℂ) (x : M) :
    E.coefficient i j (c • x)=c • E.coefficient i j x := by
  simp only [coefficient,mul_smul_comm,smul_mul_assoc,Finset.smul_sum]

lemma coefficient_sum {J : Type*} (s : Finset J) (i j : Fin n) (f : J → M) :
    E.coefficient i j (∑ k ∈ s,f k)=∑ k ∈ s,E.coefficient i j (f k) := by
  simp only [coefficient,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_comm

lemma coefficient_scalarMatrix (a : Fin n → Fin n → ℂ) (i j : Fin n) :
    E.coefficient i j (E.scalarMatrix a)=a i j • (1:M) := by
  classical
  simp only [scalarMatrix,E.coefficient_sum,E.coefficient_smul,E.coefficient_entry,smul_ite,smul_zero]
  simp only [ite_and]
  simp

lemma coefficient_mul_mem (i j : Fin n) (x c : M) (hc : c ∈ E.commutant) :
    E.coefficient i j (x*c)=E.coefficient i j x*c := by
  simp only [coefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = E.entry k i*x*(c*E.entry j k) := by noncomm_ring
    _ = _ := by rw [(hc j k).eq]; noncomm_ring

def phaseCoefficient (g : Fin n → ZMod 3) (x : M) : M :=
  (n:ℂ)⁻¹ • ∑ i,∑ j,(star (phase g i)*phase g j) • E.coefficient i j x

lemma phaseCoefficient_mem (g : Fin n → ZMod 3) (x : M) : E.phaseCoefficient g x ∈ E.commutant := by
  apply E.commutant.smul_mem
  apply E.commutant.sum_mem
  intro i hi
  apply E.commutant.sum_mem
  intro j hj
  exact E.commutant.smul_mem (E.coefficient_mem i j x) _

lemma rankOne_compression (g : Fin n → ZMod 3) (x : M) :
    E.rankOne g*x*E.rankOne g=E.rankOne g*E.phaseCoefficient g x := by
  apply E.coefficient_ext
  intro i l
  rw [E.coefficient_mul_mem i l _ _ (E.phaseCoefficient_mem g x)]
  rw [coefficient_product_matrix]
  simp only [coefficient_product_matrix,rankOne,coefficient_scalarMatrix,
    smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  simp only [phaseCoefficient,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

variable [PartialOrder M] [StarOrderedRing M]

lemma rankOne_compression_norm (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0)
    (g : Fin n → ZMod 3) (x : M) :
    ‖τ.toPreGNS (E.rankOne g*x*E.rankOne g)‖^2=
      (n:ℝ)⁻¹*‖τ.toPreGNS (E.phaseCoefficient g x)‖^2 := by
  rw [E.rankOne_compression g x, norm_sq,norm_sq]
  have hb := E.phaseCoefficient_mem g x
  have hcomm : Commute (E.phaseCoefficient g x) (E.rankOne g) := by
    dsimp only [rankOne,scalarMatrix]
    apply Commute.sum_right
    intro i hi
    apply Commute.sum_right
    intro j hj
    exact (hb i j).smul_right _
  have hprod : star (E.rankOne g*E.phaseCoefficient g x)*(E.rankOne g*E.phaseCoefficient g x)=
      E.rankOne g*(star (E.phaseCoefficient g x)*E.phaseCoefficient g x) := by
    rw [star_mul,E.rankOne_star]
    have hstar : Commute (star (E.phaseCoefficient g x)) (E.rankOne g) := by
      simpa only [E.rankOne_star] using (commute_star_star.mpr hcomm)
    calc
      _ = star (E.phaseCoefficient g x)*(E.rankOne g*E.rankOne g)*E.phaseCoefficient g x := by noncomm_ring
      _ = _ := by rw [E.rankOne_mul hn g,hstar.eq]; noncomm_ring
  rw [hprod,E.trace_rankOne_commutant τ htr hn g _
    (E.commutant.mul_mem (E.commutant.star_mem' hb) hb)]
  have he : (n:ℂ)⁻¹=Complex.ofReal ((n:ℝ)⁻¹) := by simp
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

end MatrixSystem
end HochschildMatrixSystems

 

 

open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
open HochschildFinitePhase
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (E : MatrixSystem M n)

lemma phaseCoefficient_energy_bound (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (x : M) :
    (∑ g : Fin n → ZMod 3, ‖τ.toPreGNS (E.phaseCoefficient g x)‖^2) ≤
      (Fintype.card (Fin n → ZMod 3):ℝ)*
        (‖τ.toPreGNS (E.expectation x)‖^2+‖τ.toPreGNS x‖^2/(n:ℝ)) := by
  classical
  have hdiag : ‖∑ i,τ.toPreGNS (E.coefficient i i x)‖^2=
      (n:ℝ)^2*‖τ.toPreGNS (E.expectation x)‖^2 := by
    rw [← map_sum,E.sum_coefficient_diagonal hn,map_smul,norm_smul,mul_pow]
    simp
  have hoff : (∑ i,∑ j,if i=j then 0 else ‖τ.toPreGNS (E.coefficient i j x)‖^2) ≤
      (n:ℝ)*‖τ.toPreGNS x‖^2 := by
    rw [← E.coefficient_norm_sq_sum τ htr hn x]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · positivity
    · exact le_rfl
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  calc
    _ = (n:ℝ)⁻¹^2 * ∑ g : Fin n → ZMod 3,
        ‖∑ i,∑ j,(star (phase g i)*phase g j) • τ.toPreGNS (E.coefficient i j x)‖^2 := by
      simp only [phaseCoefficient,map_smul,map_sum,norm_smul,norm_inv,Complex.norm_natCast,mul_pow,
        ← Finset.mul_sum]
    _ = (n:ℝ)⁻¹^2 * ((Fintype.card (Fin n → ZMod 3):ℝ)*
        ((n:ℝ)^2*‖τ.toPreGNS (E.expectation x)‖^2+
          ∑ i,∑ j,if i=j then 0 else ‖τ.toPreGNS (E.coefficient i j x)‖^2)) := by
      rw [phase_parseval,hdiag]
    _ ≤ (n:ℝ)⁻¹^2 * ((Fintype.card (Fin n → ZMod 3):ℝ)*
        ((n:ℝ)^2*‖τ.toPreGNS (E.expectation x)‖^2+(n:ℝ)*‖τ.toPreGNS x‖^2)) := by
      gcongr
    _ = _ := by field_simp

lemma exists_phase_energy_bound {I : Type*} [Fintype I] (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (x : I → M) :
    ∃ g : Fin n → ZMod 3,
      (∑ i, ‖τ.toPreGNS (E.phaseCoefficient g (x i))‖^2) ≤
        ∑ i,(‖τ.toPreGNS (E.expectation (x i))‖^2+‖τ.toPreGNS (x i)‖^2/(n:ℝ)) := by
  classical
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    E.phaseCoefficient_energy_bound τ htr hn (x i))
  rw [Finset.sum_comm,← Finset.mul_sum] at hh
  by_contra hg
  push Not at hg
  have hstrict : (Fintype.card (Fin n → ZMod 3):ℝ)*
      (∑ i,(‖τ.toPreGNS (E.expectation (x i))‖^2+‖τ.toPreGNS (x i)‖^2/(n:ℝ))) <
        ∑ g : Fin n → ZMod 3, ∑ i,‖τ.toPreGNS (E.phaseCoefficient g (x i))‖^2 := by
    rw [← nsmul_eq_mul,← Finset.card_univ,← Finset.sum_const]
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun _ _ => hg _)
  exact (not_lt_of_ge hh) hstrict

end MatrixSystem
end HochschildMatrixSystems

 

 

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_RelativeQuantization
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative small corners, root phases and weak powers of unitaries. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder
namespace HochschildQuantization
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems HochschildCorners
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (p : M) (hp : IsStarProjection p)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

lemma corner_trace_re (a : Corner p hp) :
    (cornerTrace p hp τ a).re=(τ p).re⁻¹*(τ (a:M)).re := by
  rw [cornerTrace_apply]
  simp only [← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

end HochschildQuantization

 

 

 

open scoped BigOperators ComplexConjugate InnerProductSpace
namespace HochschildRootPhase
variable {I : Type*} [Fintype I]
variable {m : ℕ} [NeZero m]

variable [DecidableEq I]

lemma sum_character (v : I → ZMod m) :
    ∑ g,character v g=if v=0 then (Fintype.card (I → ZMod m):ℂ) else 0 := by
  classical
  by_cases hv : v=0
  · subst v
    simp only [character_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,ite_true]
  · rw [ite_eq_right hv]
    exact AddChar.sum_eq_zero_of_ne_one ((character_eq_one_iff v).not.mpr hv)

lemma orthogonality (v w : I → ZMod m) :
    ∑ g,star (character v g)*character w g=
      if v=w then (Fintype.card (I → ZMod m):ℂ) else 0 := by
  classical
  simp only [character_star,← character_add,sum_character]
  congr 1
  exact propext neg_add_eq_zero

lemma character_parseval {J H : Type*} [Fintype J] [SeminormedAddCommGroup H]
    [InnerProductSpace ℂ H] (f : J → (I → ZMod m)) (hf : Function.Injective f) (v : J → H) :
    (∑ g : I → ZMod m, ‖∑ j, character (f j) g • v j‖^2)=
      (Fintype.card (I → ZMod m):ℝ)*(∑ j,‖v j‖^2) := by
  classical
  have hh : (∑ g : I → ZMod m, ⟪∑ j, character (f j) g • v j,
      ∑ j,character (f j) g • v j⟫_ℂ)=
      (Fintype.card (I → ZMod m):ℂ)*(∑ j,⟪v j,v j⟫_ℂ) := by
    simp only [sum_inner,inner_sum]
    simp only [inner_smul_left,inner_smul_right]
    calc
      _ = ∑ j,∑ k,(∑ g,star (character (f k) g)*character (f j) g)*⟪v k,v j⟫_ℂ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro g hg
        simp only [Complex.star_def]
        ring
      _ = _ := by simp only [orthogonality,hf.eq_iff]; simp [← Finset.mul_sum]
  have hr := congrArg Complex.re hh
  simp only [Complex.re_sum,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    zero_mul,sub_zero] at hr
  simpa only [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex] using hr

end HochschildRootPhase

 

 

open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
open HochschildRootPhase
variable {M : Type*} [CStarAlgebra M]
variable {n m : ℕ} [NeZero m] (E : MatrixSystem M n)

def diagonalRoot (k : ZMod m) (g : Fin n → ZMod m) : M :=
  ∑ i, character (Pi.single i k) g • E.entry i i

lemma diagonalRoot_zero (g : Fin n → ZMod m) : E.diagonalRoot 0 g=1 := by
  simp only [diagonalRoot,Pi.single_zero,character_zero,one_smul,E.sum_diagonal]

lemma diagonalRoot_mul (k l : ZMod m) (g : Fin n → ZMod m) :
    E.diagonalRoot k g*E.diagonalRoot l g=E.diagonalRoot (k+l) g := by
  classical
  simp only [diagonalRoot,Finset.sum_mul,Finset.mul_sum,smul_mul_smul_comm,E.entry_mul,smul_ite,smul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Pi.single_add,character_add]

lemma diagonalRoot_star (k : ZMod m) (g : Fin n → ZMod m) :
    star (E.diagonalRoot k g)=E.diagonalRoot (-k) g := by
  simp only [diagonalRoot,star_sum,star_smul,E.star_entry,character_star,Pi.single_neg]

lemma diagonalRoot_unitary (k : ZMod m) (g : Fin n → ZMod m) : E.diagonalRoot k g ∈ unitary M := by
  constructor
  · rw [diagonalRoot_star,diagonalRoot_mul,neg_add_cancel,diagonalRoot_zero]
  · rw [diagonalRoot_star,diagonalRoot_mul,add_neg_cancel,diagonalRoot_zero]

def rootUnitary (g : Fin n → ZMod m) : unitary M := ⟨E.diagonalRoot 1 g,E.diagonalRoot_unitary 1 g⟩

def integerRootHom (g : Fin n → ZMod m) : Multiplicative ℤ →* unitary M where
  toFun k := ⟨E.diagonalRoot (k.toAdd : ZMod m) g,E.diagonalRoot_unitary _ g⟩
  map_one' := Subtype.ext (by change E.diagonalRoot ((0 : ℤ) : ZMod m) g=1; rw [Int.cast_zero,E.diagonalRoot_zero])
  map_mul' k l := Subtype.ext (by
    dsimp
    rw [Int.cast_add,E.diagonalRoot_mul])

lemma rootUnitary_zpow (g : Fin n → ZMod m) (k : ℤ) :
    ((E.rootUnitary g)^k : unitary M).val=E.diagonalRoot (k : ZMod m) g := by
  have h := (E.integerRootHom g).map_zpow (Multiplicative.ofAdd (1:ℤ)) k
  have hpow : (Multiplicative.ofAdd (1:ℤ))^k=Multiplicative.ofAdd k := by
    apply Multiplicative.toAdd.injective
    simp
  rw [hpow] at h
  have hone : (E.integerRootHom g) (Multiplicative.ofAdd (1:ℤ))=E.rootUnitary g :=
    Subtype.ext (by change E.diagonalRoot ((1:ℤ) : ZMod m) g=E.diagonalRoot 1 g; rw [Int.cast_one])
  rw [hone] at h
  exact congrArg (fun a : unitary M => (a:M)) h.symm

variable [PartialOrder M]

lemma trace_root_parseval (τ : M →ₚ[ℂ] ℂ) (a : M) (k : ZMod m) (hk : k ≠ 0) :
    (∑ g : Fin n → ZMod m, ‖τ (a*E.diagonalRoot k g)‖^2)=
      (Fintype.card (Fin n → ZMod m):ℝ)*(∑ i,‖τ (a*E.entry i i)‖^2) := by
  have hh := character_parseval (fun i : Fin n => Pi.single i k)
    (single_frequency_injective k hk) (fun i => τ (a*E.entry i i))
  simpa only [diagonalRoot,Finset.mul_sum,mul_smul_comm,map_sum,map_smul,smul_eq_mul] using hh

end MatrixSystem
end HochschildMatrixSystems

 

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n m : ℕ} [NeZero m] (E : MatrixSystem M n)

lemma trace_root_energy_bound (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0)
    (a : M) (k : ZMod m) (hk : k ≠ 0) :
    (∑ g : Fin n → ZMod m, ‖τ (a*E.diagonalRoot k g)‖^2) ≤
      (Fintype.card (Fin n → ZMod m):ℝ)*(‖a‖^2/(n:ℝ)) := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  have hdiag (i : Fin n) : (τ (E.entry i i)).re=(n:ℝ)⁻¹ := by
    have hh : τ (E.entry i i)=(n:ℂ)⁻¹ := by
      simpa [h1] using E.trace_entry_commutant τ htr hn 1 E.commutant.one_mem i i
    rw [hh,← Complex.ofReal_natCast,← Complex.ofReal_inv,Complex.ofReal_re]
  have hb (i : Fin n) : ‖τ (a*E.entry i i)‖ ≤ (n:ℝ)⁻¹*‖a‖ := by
    rw [htr]
    exact (HochschildTraceNorm.positive_weight_trace_bound τ htr (E.entry i i) a
      (E.diagonal_proj i).nonneg).trans_eq (by rw [hdiag])
  rw [E.trace_root_parseval τ a k hk]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ _i : Fin n,((n:ℝ)⁻¹*‖a‖)^2 := Finset.sum_le_sum (fun i hi =>
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (norm_nonneg _))).mpr (hb i))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp

lemma exists_root_trace_energy {I : Type*} [Fintype I] (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0)
    (a : I → M) (k : I → ZMod m) (hk : ∀ i, k i ≠ 0) :
    ∃ g : Fin n → ZMod m,
      (∑ i,‖τ (a i*E.diagonalRoot (k i) g)‖^2) ≤ (∑ i,‖a i‖^2)/(n:ℝ) := by
  classical
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    E.trace_root_energy_bound τ h1 htr hn (a i) (k i) (hk i))
  rw [Finset.sum_comm,← Finset.mul_sum,← Finset.sum_div] at hh
  by_contra hg
  push Not at hg
  have hstrict : (Fintype.card (Fin n → ZMod m):ℝ)*((∑ i,‖a i‖^2)/(n:ℝ)) <
      ∑ g : Fin n → ZMod m, ∑ i,‖τ (a i*E.diagonalRoot (k i) g)‖^2 := by
    rw [← nsmul_eq_mul,← Finset.card_univ,← Finset.sum_const]
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun _ _ => hg _)
  exact (not_lt_of_ge hh) hstrict

end MatrixSystem

open BoundedHochschild HochschildRigidity HochschildSakai
universe u v

end HochschildMatrixSystems
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_IncrementalPatching
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.BoundedHochschild.CentralCorner.compressMap_coe _root_.OAI.BoundedHochschild.CentralCorner.compressMap_includeMap _root_.OAI.BoundedHochschild.CentralCorner.extend_apply _root_.OAI.BoundedHochschild.CentralCorner.includeMap_apply _root_.OAI.BoundedHochschild.CentralCorner.restrict_apply _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.composePartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.nestedCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.HochschildComparison.Frame.zero_part _root_.OAI.HochschildComparison.PartialIso.ofProjection_coe _root_.OAI.HochschildComparison.PartialIso.ofProjection_final _root_.OAI.HochschildComparison.PartialIso.ofProjection_initial _root_.OAI.HochschildComparison.PartialIso.restrict_coe _root_.OAI.HochschildComparison.PartialIso.restrict_initial _root_.OAI.HochschildPatching.asPartialUnitary_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner partial unitaries, incremental moment estimates and unitary completion. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildSakai HochschildCorners HochschildComparison
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (q : M) (hq : IsStarProjection q)

lemma corner_coe_pow_succ (a : Corner q hq) (n : ℕ) : ((a^(n+1) : Corner q hq):M)=(a:M)^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (a := a),corner_coe_mul,ih]
    exact (pow_succ (a : M) (n+1)).symm

lemma signedExponent_ne_zero (k : Bool × ℕ) : signedExponent k ≠ 0 := by
  dsimp [signedExponent]; split <;> omega
lemma ofCornerUnitary_power (u : unitary (Corner q hq)) (k : Bool × ℕ) :
    (ofCornerUnitary q hq u).power k=(((u^signedExponent k : unitary (Corner q hq)) : Corner q hq):M) := by
  dsimp only [PartialUnitary.power,signedExponent]
  split
  · rw [zpow_neg,show (k.2 : ℤ)+1=((k.2+1 : ℕ):ℤ) by simp,zpow_natCast,← Unitary.star_eq_inv,
      Unitary.coe_star,SubmonoidClass.coe_pow,corner_coe_star,corner_coe_pow_succ,star_pow]
    rfl
  · rw [show (k.2 : ℤ)+1=((k.2+1 : ℕ):ℤ) by simp,zpow_natCast,SubmonoidClass.coe_pow,corner_coe_pow_succ]
    rfl

end HochschildPatching

 

 

 

open scoped ComplexOrder







namespace HochschildPatching

lemma expBudget_zero (δ C : ℝ) : expBudget δ C 0=0 := by simp [expBudget]
lemma patchRate_ge_one {n T : ℝ} (hT : T<1) : 1 ≤ patchRate n T := by
  unfold patchRate
  have : 0 ≤ 2*n^2/(1-T) := div_nonneg (mul_nonneg (by norm_num) (sq_nonneg n)) (by linarith)
  linarith
lemma patch_slope_bound {δ n T s B : ℝ} (hδ : 0 ≤ δ) (hn : 0 ≤ n) (hT : T<1) (hs : s ≤ T) (hB : 0 ≤ B) :
    n*patchTolerance δ n+n^2*(patchTolerance δ n+2*B/(1-s)) ≤ patchRate n T*(δ+B) := by
  have hden : 0<n+n^2+1 := by nlinarith [sq_nonneg n]
  have heps : patchTolerance δ n*(n+n^2) ≤ δ := by
    unfold patchTolerance
    calc
      δ/(n+n^2+1)*(n+n^2) ≤ δ/(n+n^2+1)*(n+n^2+1) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hδ hden.le)
      _ = δ := div_mul_cancel₀ _ hden.ne'
  have hds : 0<1-s := by linarith
  have hdt : 0<1-T := by linarith
  have hr : 2*n^2/(1-s) ≤ 2*n^2/(1-T) :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (sq_nonneg n)) hdt (by linarith)
  have hrB := mul_le_mul_of_nonneg_right hr hB
  have hC := patchRate_ge_one (n := n) hT
  have hCd : δ ≤ patchRate n T*δ := by nlinarith
  have he : n*patchTolerance δ n+n^2*(patchTolerance δ n+2*B/(1-s))=
      patchTolerance δ n*(n+n^2)+(2*n^2/(1-s))*B := by ring
  rw [he]
  calc
    _ ≤ δ+(2*n^2/(1-T))*B := add_le_add heps hrB
    _ ≤ patchRate n T*(δ+B) := by unfold patchRate at *; nlinarith

lemma expBudget_patch_bound {δ n T s t : ℝ} (hδ : 0 ≤ δ) (hn : 0 ≤ n)
    (hT : T<1) (hs : 0 ≤ s) (hsT : s ≤ T) (ht : 0 ≤ t) :
    expBudget δ (patchRate n T) s+
      (n*patchTolerance δ n+n^2*(patchTolerance δ n+2*expBudget δ (patchRate n T) s/(1-s)))*t ≤
        expBudget δ (patchRate n T) (s+t) := by
  have hb := expBudget_nonneg hδ ((by norm_num : (0 : ℝ) ≤ 1).trans (patchRate_ge_one (n := n) hT)) hs
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right (patch_slope_bound hδ hn hT hsT hb) ht)).trans (expBudget_increment hδ)
end HochschildPatching

 

 

 

open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
include htr in
lemma trace_supported_insertion {q : M} (hq : IsStarProjection q) (A x B : M)
    (hA : ‖A‖ ≤ 1) (hx : ‖x‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hqx : q*x=x) :
    ‖τ (A*x*B)‖ ≤ (τ q).re := by
  have he : τ (A*x*B)=τ (q*(x*B*A)) := by
    rw [mul_assoc,htr A (x*B),← mul_assoc,← mul_assoc,hqx]
  rw [he]
  apply (HochschildTraceNorm.positive_weight_trace_bound τ htr q (x*B*A) hq.nonneg).trans
  have hn : ‖x*B*A‖ ≤ 1 := by simpa only [one_mul] using norm_mul_le_of_le (norm_mul_le_of_le hx hB) hA
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (τ.map_nonneg hq.nonneg).1

variable {I : Type*} (F : I → M)


def unitaryCompletion (v : PartialUnitary M) : unitary M :=
  ⟨(v:M)+(1-v.support),by
    apply Unitary.mem_iff.mpr
    have hp := v.support_proj
    have horth : v.support*(1-v.support)=0 := by rw [mul_sub,mul_one,hp.isIdempotentElem.eq,sub_self]
    let w := ofCornerUnitary (1-v.support) hp.one_sub 1
    have hw : w.support=1-v.support := ofCornerUnitary_support ..
    have hwv : (w:M)=1-v.support := rfl
    let he := v.orthogonalSum w (by rwa [hw])
    have hs : he.support=1 := by dsimp only [he]; rw [PartialUnitary.support_orthogonalSum,hw,add_sub_cancel]
    constructor
    · have hh := he.star_mul_self_eq_support.trans hs
      change star ((v:M)+(w:M))*((v:M)+(w:M))=1 at hh
      simpa only [hwv] using hh
    · have hh := he.mul_star_self_eq_support.trans hs
      change ((v:M)+(w:M))*star ((v:M)+(w:M))=1 at hh
      simpa only [hwv] using hh⟩

end HochschildPatching
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_UltrapowerMoments
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.composePartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.HochschildComparison.Frame.zero_part _root_.OAI.HochschildComparison.PartialIso.ofProjection_coe _root_.OAI.HochschildComparison.PartialIso.ofProjection_final _root_.OAI.HochschildComparison.PartialIso.ofProjection_initial _root_.OAI.HochschildComparison.PartialIso.restrict_coe _root_.OAI.HochschildComparison.PartialIso.restrict_initial _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered sequences and unitary moments in tracial ultrapowers. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildUltrapower
open HochschildRigidity TracialUltrapower HochschildPatching
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1) (ω : Ultrafilter ℕ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))

def traceScalarSequence (a : ℕ →ᵇ M) : ℕ →ᵇ M :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (1:M)).compLeftContinuousBounded ℕ
    ((HochschildTraceNorm.traceCLM τ).compLeftContinuousBounded ℕ a)
@[simp] lemma traceScalarSequence_apply (a : ℕ →ᵇ M) (n : ℕ) :
    traceScalarSequence τ a n=τ (a n) • (1:M) := rfl

lemma quotient_traceScalarSequence (a : ℕ →ᵇ M) :
    quotientHom τ h1 ω htr (traceScalarSequence τ a)=
      quotientTrace τ h1 ω htr (quotientHom τ h1 ω htr a) • (1:Ultrapower τ h1 ω htr) := by
  change quotientHom τ h1 ω htr (traceScalarSequence τ a)=sequenceTrace τ ω a • (1:Ultrapower τ h1 ω htr)
  rw [← map_one (quotientHom τ h1 ω htr),← map_smul]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change _ ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)
  rw [mem_nullSubmodule]
  change Tendsto (fun j => ‖τ.toPreGNS (τ (a j) • (1:M)-sequenceTrace τ ω a • (1:M))‖) (ω : Filter ℕ) (nhds 0)
  have ht := ((tendsto_sequenceTrace τ h1 ω a).sub_const (sequenceTrace τ ω a)).norm
  have hnorm : ‖τ.toPreGNS (1:M)‖=1 := by
    rw [PositiveLinearMap.preGNS_norm_def]
    simp [h1]
  simpa only [← sub_smul,map_smul,norm_smul,hnorm,mul_one,sub_self,norm_zero] using ht

def centeredSequence (a : ℕ →ᵇ M) : ℕ →ᵇ M := a-traceScalarSequence τ a
@[simp] lemma centeredSequence_apply (a : ℕ →ᵇ M) (n : ℕ) :
    centeredSequence τ a n=a n-τ (a n) • (1:M) := rfl
lemma quotient_centeredSequence (a : ℕ →ᵇ M) :
    quotientHom τ h1 ω htr (centeredSequence τ a)=
      quotientHom τ h1 ω htr a -
        quotientTrace τ h1 ω htr (quotientHom τ h1 ω htr a) • (1:Ultrapower τ h1 ω htr) := by
  rw [centeredSequence,map_sub,quotient_traceScalarSequence]
include h1 in
lemma norm_centered_half (a : M) (ha : ‖a‖ ≤ 1) : ‖(1/2:ℂ) • (a-τ a • (1:M))‖ ≤ 1 := by
  have ht := (norm_trace_le τ h1 a).trans ((preGNS_norm_le τ h1 a).trans ha)
  have hone : ‖(1:M)‖ ≤ 1 := IsStarProjection.norm_le _ (IsStarProjection.one M)
  rw [norm_smul]
  have h2 : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [h2]
  have hs : ‖τ a • (1:M)‖ ≤ 1 := by
    rw [norm_smul]
    exact (mul_le_mul ht hone (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hh := (norm_sub_le a (τ a • (1:M))).trans (add_le_add ha hs)
  linarith

def unitarySequence (u : ℕ → unitary M) : unitary (ℕ →ᵇ M) :=
  ⟨boundedHom (fun n => zpowersHom (unitary M) (u n)) (Multiplicative.ofAdd 1),by
    constructor <;> ext n <;> simp [zpowersHom]⟩
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma unitarySequence_apply (u : ℕ → unitary M) (n : ℕ) :
    (unitarySequence u : ℕ →ᵇ M) n=(u n:M) := by simp [unitarySequence,zpowersHom]

def quotientUnitary (u : ℕ → unitary M) : unitary (Ultrapower τ h1 ω htr) :=
  Unitary.map { (quotientHom τ h1 ω htr).toMonoidHom with map_star' := fun a => map_star (quotientHom τ h1 ω htr) a } (unitarySequence u)
@[simp] lemma quotientUnitary_coe (u : ℕ → unitary M) :
    (quotientUnitary τ h1 ω htr u : Ultrapower τ h1 ω htr)=quotientHom τ h1 ω htr (unitarySequence u : ℕ →ᵇ M) := rfl

end HochschildUltrapower

 

 

open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildPatching
open HochschildComparison
variable {M A : Type*} [CStarAlgebra M] [CStarAlgebra A]
variable {I : Type*} {K : ℕ}

@[simp] lemma mapUnitary_coe (φ : M →⋆ₐ[ℂ] A) (u : unitary M) :
    (mapUnitary φ u : A)=φ (u:M) := rfl
lemma mapUnitary_zpow (φ : M →⋆ₐ[ℂ] A) (u : unitary M) (k : ℤ) :
    ((mapUnitary φ u)^k : unitary A).val=φ ((u^k : unitary M):M) := by
  rw [← map_zpow]
  rfl

lemma unitary_power_eq (u : unitary M) (k : Bool × ℕ) :
    (asPartialUnitary u).power k=((u^signedExponent k : unitary M):M) := by
  dsimp only [PartialUnitary.power,signedExponent]
  split
  · rw [zpow_neg,show (k.2 : ℤ)+1=((k.2+1 : ℕ):ℤ) by simp,zpow_natCast,← Unitary.star_eq_inv,
      Unitary.coe_star,SubmonoidClass.coe_pow,star_pow]
    rfl
  · rw [show (k.2 : ℤ)+1=((k.2+1 : ℕ):ℤ) by simp,zpow_natCast,SubmonoidClass.coe_pow]
    rfl

@[simp] lemma evalSequence_apply (n : ℕ) (a : ℕ →ᵇ M) : evalSequence n a=a n := rfl
lemma eval_unitarySequence (u : ℕ → unitary M) (n : ℕ) :
    mapUnitary (evalSequence n) (HochschildUltrapower.unitarySequence u)=u n := by
  apply Subtype.ext
  change ((u n)^(1:ℤ) : unitary M).val=(u n:M)
  rw [zpow_one]
end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction





namespace HochschildPatching
variable {K : ℕ}
lemma exists_finite_reindex (a : Option ℕ) (l : List (WordAtom ℕ K)) :
    ∃ m : ℕ, ∃ f : ℕ → Fin m,
      (a.map f).map Fin.val=a ∧
      (l.map (mapAtom f id)).map (mapAtom Fin.val id)=l := by
  classical
  let s : Finset ℕ := (a.toList ++ l.flatMap (fun b => b.2.toList)).toFinset
  obtain ⟨m,hm⟩ := s.exists_nat_subset_range
  let f : ℕ → Fin (m+1) := fun i => if hi : i < m+1 then ⟨i,hi⟩ else ⟨0,Nat.zero_lt_succ m⟩
  have hf (i : ℕ) (hi : i ∈ s) : (f i).val=i := by
    have hh := Finset.mem_range.mp (hm hi)
    dsimp only [f]
    rw [dite_eq_left (Nat.lt_succ_of_lt hh)]
  refine ⟨m+1,f,?_,?_⟩
  · cases a with
    | none => rfl
    | some i =>
      have hi : i ∈ s := by simp [s]
      simpa using congrArg some (hf i hi)
  · rw [List.map_map]
    conv_rhs => rw [← List.map_id l]
    apply List.map_congr_left
    intro b hb
    rcases b with ⟨k,b⟩
    cases b with
    | none => rfl
    | some i =>
      have hi : i ∈ s := by
        simp only [s,List.mem_toFinset,List.mem_append,List.mem_flatMap]
        exact Or.inr ⟨(k,some i),hb,by simp⟩
      simp only [Function.comp_apply,mapAtom,id_eq,Option.map_some,hf i hi]

end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_HomogeneousTypeI
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The abelian commutant of a finite homogeneous type I matrix system. -/

noncomputable section

namespace HochschildMatrixSystems
namespace MatrixSystem

variable {M : Type*} [CStarAlgebra M] {n : ℕ} (E : MatrixSystem M n)

lemma commutant_central (hcomm : ∀ a b : E.commutant, Commute a b)
    (a : E.commutant) (x : M) : (a : M) * x = x * (a : M) := by
  have hc : Commute (a : M) x := by
    rw [← E.reconstruct x]
    apply Commute.sum_right
    intro i _
    apply Commute.sum_right
    intro j _
    exact (a.property i j).mul_right (show Commute (a : M) (E.coefficient i j x) from
      congrArg (fun z : E.commutant => (z : M))
        (hcomm a ⟨_, E.coefficient_mem i j x⟩).eq)
  exact hc.eq

lemma commutant_commutative_of_abelian_diagonal (i : Fin n)
    (hi : FinitePathMain.AbelianProjection (E.entry i i)) :
    ∀ a b : E.commutant, Commute a b := by
  intro a b
  have hcut (a : E.commutant) : E.entry i i * (a : M) * E.entry i i =
      E.entry i i * (a : M) := by
    rw [mul_assoc, (a.property i i).eq, ← mul_assoc, (E.diagonal_proj i).isIdempotentElem.eq]
  have hprod (a b : E.commutant) :
      (E.entry i i * (a : M)) * (E.entry i i * (b : M)) =
        E.entry i i * ((a : M) * (b : M)) := by
    calc
      _ = (E.entry i i * (a : M) * E.entry i i) * (b : M) := by noncomm_ring
      _ = _ := by rw [hcut]; noncomm_ring
  have h := hi.2 (a : M) (b : M)
  change (E.entry i i * (a : M) * E.entry i i) *
      (E.entry i i * (b : M) * E.entry i i) =
    (E.entry i i * (b : M) * E.entry i i) *
      (E.entry i i * (a : M) * E.entry i i) at h
  simp only [hcut, hprod] at h
  have he := congrArg (E.coefficient i i) h
  change E.coefficient i i (E.entry i i * ((a * b : E.commutant) : M)) =
    E.coefficient i i (E.entry i i * ((b * a : E.commutant) : M)) at he
  rw [E.coefficient_of_commutant i (a * b).property,
    E.coefficient_of_commutant i (b * a).property] at he
  exact Subtype.ext he

end MatrixSystem
end HochschildMatrixSystems

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Target
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Generator

/-! Weak operator generation of concrete finite diffuse factors with separable Banach preduals. -/
noncomputable section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The manuscript's W*(s), as the intersection of all weakly closed unital
star subalgebras containing s. This does not invoke a double-commutant theorem. -/
def wstar (s : Set (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  sInf {S | WOTClosed S ∧ s ⊆ S}

theorem subset_wstar (s : Set (H →L[ℂ] H)) : s ⊆ wstar s := by
  intro x hx
  exact StarSubalgebra.mem_sInf.mpr fun S hS => hS.2 hx

theorem wstar_le {s : Set (H →L[ℂ] H)} {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hS : WOTClosed S) (hs : s ⊆ S) : wstar s ≤ S :=
  sInf_le ⟨hS, hs⟩

theorem wstar_closed (s : Set (H →L[ℂ] H)) : WOTClosed (wstar s) := by
  unfold WOTClosed
  have heq : {T : H →WOT[ℂ] H | T.toCLM ∈ wstar s} =
      ⋂ (S : StarSubalgebra ℂ (H →L[ℂ] H)) (_ : WOTClosed S ∧ s ⊆ S),
        {T : H →WOT[ℂ] H | T.toCLM ∈ S} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, wstar, StarSubalgebra.mem_sInf]
  rw [heq]
  exact isClosed_iInter fun S => isClosed_iInter fun h => h.1

/-- A nonzero finite diffuse factor, stated by its center, isometries, and
projections. These hypotheses do not include any generation conclusion. -/
structure IsII1Factor (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop where
  nonzero : (0 : H →L[ℂ] H) ≠ 1
  weaklyClosed : WOTClosed S
  factor : ∀ x : S, (∀ y : S, y * x = x * y) → ∃ c : ℂ, x = algebraMap ℂ S c
  finite : ∀ v : S, star v * v = 1 → v * star v = 1
  diffuse : ∀ p : S, IsStarProjection p → p ≠ 0 →
    ∃ q : S, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q

end

end Generator

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Bicommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Finite diagonal amplification and the projection onto a simultaneous
operator orbit. These are the analytic ingredients of the bicommutant theorem. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

def diagonalOperator (T : H →L[ℂ] H) : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i)))

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem diagonalOperator_apply (T : H →L[ℂ] H) (x : FiniteHilbert ι H) (i : ι) :
    diagonalOperator T x i=T (x i) := rfl

theorem diagonalOperator_star (T : H →L[ℂ] H) :
    diagonalOperator (ι := ι) (star T)=star (diagonalOperator (ι := ι) T) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply,diagonalOperator_apply,
    ContinuousLinearMap.adjoint_inner_right]

def tupleOrbitMap (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : FiniteHilbert ι H) :
    S →ₗ[ℂ] FiniteHilbert ι H where
  toFun a := diagonalOperator a.val x
  map_add' a b := by ext i; rfl
  map_smul' c a := by ext i; rfl

def tupleOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : FiniteHilbert ι H) :
    Submodule ℂ (FiniteHilbert ι H) := (tupleOrbitMap S x).range.topologicalClosure

instance tupleOrbitClosure_complete (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) : CompleteSpace (tupleOrbitClosure S x) :=
  inferInstanceAs (CompleteSpace (tupleOrbitMap S x).range.topologicalClosure)

theorem mem_tupleOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) : x ∈ tupleOrbitClosure S x := by
  apply Submodule.le_topologicalClosure
  refine ⟨1,?_⟩
  ext i
  rfl

theorem tupleOrbitClosure_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) (a : S) {y : FiniteHilbert ι H}
    (hy : y ∈ tupleOrbitClosure S x) : diagonalOperator a.val y ∈ tupleOrbitClosure S x := by
  have h : (tupleOrbitMap S x).range.topologicalClosure ≤
      (tupleOrbitClosure S x).comap (diagonalOperator a.val).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨b,rfl⟩
      apply Submodule.le_topologicalClosure
      refine ⟨a*b,?_⟩
      ext i
      rfl
    · exact (Submodule.isClosed_topologicalClosure _).preimage (diagonalOperator a.val).continuous
  exact h hy

theorem tupleOrbitProjection_commutes (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) (a : S) :
    (tupleOrbitClosure S x).starProjection*diagonalOperator a.val=
      diagonalOperator a.val*(tupleOrbitClosure S x).starProjection := by
  apply starProjection_commutes_of_invariant
  · exact fun y hy => tupleOrbitClosure_invariant S x a hy
  · rw [← diagonalOperator_star]
    exact fun y hy => tupleOrbitClosure_invariant S x (star a) hy

variable [DecidableEq ι]

def tupleSingle (i : ι) : H →L[ℂ] FiniteHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem tupleSingle_apply (i j : ι) (x : H) :
    tupleSingle i x j=(Pi.single i x : ι → H) j := rfl

omit [CompleteSpace H] in
theorem tuple_eq_sum_single (x : FiniteHilbert ι H) :
    x=∑ i,tupleSingle i (x i) := by
  ext j
  simp [WithLp.ofLp_sum,tupleSingle_apply,Pi.single_apply]

omit [CompleteSpace H] [Fintype ι] in
theorem diagonalOperator_single (T : H →L[ℂ] H) (i : ι) (x : H) :
    diagonalOperator T (tupleSingle i x)=tupleSingle i (T x) := by
  ext j
  by_cases h : j=i <;> simp [h]

def operatorEntry (Q : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H) (i j : ι) : H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp (Q.comp (tupleSingle j))

omit [Fintype ι] in
theorem operatorEntry_mem_centralizer (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (Q : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H)
    (hQ : ∀ a : S,Q*diagonalOperator a.val=diagonalOperator a.val*Q) (i j : ι) :
    operatorEntry Q i j ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := by
  intro a ha
  ext z
  change a (Q (tupleSingle j z) i)=Q (tupleSingle j (a z)) i
  have h := congrArg (fun T : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H =>
    T (tupleSingle j z) i) (hQ ⟨a,ha⟩)
  simpa only [mul_apply_eq_comp,diagonalOperator_apply,
    diagonalOperator_single] using h.symm

omit [CompleteSpace H] in
theorem diagonalOperator_commutes_of_entries (T : H →L[ℂ] H)
    (Q : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H)
    (h : ∀ i j,operatorEntry Q i j*T=T*operatorEntry Q i j) :
    Q*diagonalOperator T=diagonalOperator T*Q := by
  ext x i
  rw [tuple_eq_sum_single x]
  simp only [map_sum,mul_apply_eq_comp,diagonalOperator_single]
  simp only [WithLp.ofLp_sum,Finset.sum_apply,diagonalOperator_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun a : H →L[ℂ] H => a (x j)) (h i j)

theorem bicommutant_tuple_mem_closure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (x : FiniteHilbert ι H) : diagonalOperator T x ∈ tupleOrbitClosure S x := by
  let Q := (tupleOrbitClosure S x).starProjection
  have hcomm : Q*diagonalOperator T=diagonalOperator T*Q :=
    diagonalOperator_commutes_of_entries T Q (fun i j => hT _
      (operatorEntry_mem_centralizer S Q (tupleOrbitProjection_commutes S x) i j))
  apply Submodule.starProjection_eq_self_iff.mp
  have h := congrArg (fun a : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H => a x) hcomm
  change Q (diagonalOperator T x)=diagonalOperator T (Q x) at h
  rw [show Q x=x from Submodule.starProjection_eq_self_iff.mpr (mem_tupleOrbitClosure S x)] at h
  exact h

end

/-! The double commutant theorem for actual unital star subalgebras of B(H).
Finite simultaneous strong approximation constructs a WOT-convergent net.
No bounded approximation or separable-predual theorem is claimed here. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem bicommutant_finite_strong_approximation (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : S,∀ x ∈ s,‖T x-a.val x‖ < ε := by
  classical
  let x : FiniteHilbert s H := WithLp.toLp 2 (fun i : s => i.val)
  have h := bicommutant_tuple_mem_closure S T hT x
  obtain ⟨z,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp h ε hε
  refine ⟨a,?_⟩
  intro y hy
  have hb := PiLp.norm_apply_le (diagonalOperator T x-tupleOrbitMap S x a) (⟨y,hy⟩ : s)
  exact hb.trans_lt (by simpa only [dist_eq_norm] using ha)

theorem bicommutant_exists_strong_net (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    ∃ a : Finset H × ℕ → S,∀ x : H,
      Tendsto (fun d => (a d).val x) atTop (𝓝 (T x)) := by
  classical
  have hex (d : Finset H × ℕ) := bicommutant_finite_strong_approximation S T hT d.1
    (1/((d.2 : ℝ)+1)) (by positivity)
  choose a ha using hex
  refine ⟨a,?_⟩
  intro x
  apply (tendsto_iff_dist_tendsto_zero).mpr
  have hsnd : Tendsto (fun d : Finset H × ℕ => d.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  apply squeeze_zero' (Eventually.of_forall (fun d => dist_nonneg)) ?_
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd)
  filter_upwards [eventually_ge_atTop (({x} : Finset H),0)] with d hd
  rw [dist_comm,dist_eq_norm]
  exact (ha d x (hd.1 (Finset.mem_singleton_self x))).le

theorem wotClosed_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))=S := by
  classical
  apply Set.Subset.antisymm
  · intro T hT
    obtain ⟨a,ha⟩ := bicommutant_exists_strong_net S T hT
    have hw : Tendsto (fun d => ContinuousLinearMapWOT.ofCLM (a d).val) atTop
        (𝓝 (ContinuousLinearMapWOT.ofCLM T)) := by
      apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
      intro x y
      exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp (ha x)
    exact hS.mem_of_tendsto hw (Eventually.of_forall (fun d => (a d).property))
  · intro T hT a ha
    exact (ha T hT).symm

def vonNeumannOfWOTClosed (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S) :
    VonNeumannAlgebra H where
  toStarSubalgebra := S
  centralizer_centralizer' := wotClosed_bicommutant S hS

end

/-! Countable algebraic generators give a separable star algebra using only
continuous addition and scalar multiplication. No multiplication continuity is
required, so the result applies to the two-norm on a tracial quotient. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_GroupTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialRepresentation
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm₂_smul (c : ℂ) (T : Algebra (M := M)) : τ.norm₂ (c • T) = ‖c‖*τ.norm₂ T :=
  norm_smul _ _

theorem norm₂_eq_zero_iff (T : Algebra (M := M)) : τ.norm₂ T = 0 ↔ T = 0 := by
  constructor
  · intro h
    exact τ.separating T (norm_eq_zero.mp h)
  · rintro rfl
    exact τ.norm₂_zero

end TracialRepresentation

end

end UltrapowerBridge

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_OperatorLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Operator-norm completeness of the manuscript's concrete algebra, derived
from its actual double-commutant property. No quotient completeness is assumed. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance baseNormedAlgebraRat (M : VonNeumannAlgebra H) : NormedAlgebra ℚ M.toStarSubalgebra :=
  .restrictScalars ℚ ℂ M.toStarSubalgebra

end

/-! Bounded operator families have weak operator ultralimits. This is proved
from Banach--Alaoglu and Riesz representation, not assumed as compactness. -/
open Filter
open scoped Topology

/-! Operator-norm balls of an actual von Neumann algebra are compact for the
weak operator topology, using the previously constructed operator ultralimits. -/

end Tracial

/-! Operator order bounds are closed in the weak operator topology. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable {ι : Type*} [Fintype ι]

def projectionSum (a : ι → AlgebraProjection M) (c : ι → ℂ) : M.toStarSubalgebra :=
  ∑ i, c i • (a i).val

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Supports
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Kernel and range projections constructed in the actual von Neumann algebra.
Membership follows from commutant invariance, with no spectral theorem assumed. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Kernel projections fix the range of every operator they annihilate. -/
theorem kernelProjection_mul_of_mul_eq_zero (x y : M.toStarSubalgebra) (h : x*y=0) :
    (kernelProjection x).val*y=y := by
  apply Subtype.ext
  ext ξ
  apply kernelProjection_fixes
  exact congrArg (fun t : M.toStarSubalgebra => (t : H →L[ℂ] H) ξ) h

/-- For self-adjoint x, its range projection kills every y killed by x. -/
theorem rangeProjection_mul_eq_zero (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (h : x*y=0) : (rangeProjection x).val*y=0 := by
  change (1-(kernelProjection (star x)).val)*y=0
  rw [hx.star_eq,sub_mul,one_mul,kernelProjection_mul_of_mul_eq_zero x y h,sub_self]

end

/-! Spectral sign cuts from continuous positive parts and actual range projections.
These are constructed operators, not assumed Borel functional calculus data. -/
open scoped CStarAlgebra

/-! A polar operator is constructed by extending the isometry on a range.
No polar-decomposition or projection-comparison hypothesis is used. -/

/-! Polar decomposition inside the given concrete von Neumann algebra. -/
open scoped CStarAlgebra

/-! Exact initial and final support projections of the constructed polar part. -/
open scoped CStarAlgebra
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite pinching in the actual ambient algebra. The squared L2 energy
is a sum of the energies of the mutually orthogonal compression blocks.
These identities do not postulate a local-quantizing partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

/-! Partition refinement decreases the actual compression energy. The final
selection theorem retains membership in the prescribed subalgebra. -/

theorem pinch_corner_compression (x : M.toStarSubalgebra) :
    Q.pinch (p.val*x*p.val) = Q.pinch x := by
  unfold pinch
  apply Finset.sum_congr rfl
  intro i _
  have hl : p.val*(Q.piece i).val = (Q.piece i).val := Q.piece_le i
  have hr := projection_mul_of_le (Q.piece_le i)
  simp only [← mul_assoc, hr]
  simp only [mul_assoc, hl]

end CornerPartition

end

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M}

theorem ofFamily_pinch {ι : Type*} [Fintype ι] (a : ι → AlgebraProjection M)
    (ha : ∀ i j, i ≠ j → (a i).val*(a j).val=0)
    (ht : ∑ i, (a i).val=p.val) (x : M.toStarSubalgebra) :
    (ofFamily a ha ht).pinch x = ∑ i, (a i).val*x*(a i).val := by
  exact Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => (a i).val*x*(a i).val)

end CornerPartition

end

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralPinching
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
/-- Splitting p at an explicitly given subprojection q. -/
def binary (p q : AlgebraProjection M) (hq : q ≤ p) : CornerPartition p :=
  ofFamily (fun b : Bool => if b then q else
    ⟨p.val-q.val,q.property.sub_of_mul_eq_right p.property hq⟩)
    (by
      intro i j hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · change (p.val-q.val)*q.val=0
        rw [sub_mul,hq,q.property.isIdempotentElem.eq,sub_self]
      · change q.val*(p.val-q.val)=0
        rw [mul_sub,projection_mul_of_le hq,q.property.isIdempotentElem.eq,sub_self]
      · exact (hij rfl).elim)
    (by
      rw [Fintype.sum_bool]
      change q.val+(p.val-q.val)=p.val
      abel)

theorem binary_pinch (p q : AlgebraProjection M) (hq : q ≤ p) (x : M.toStarSubalgebra) :
    (binary p q hq).pinch x = q.val*x*q.val+(p.val-q.val)*x*(p.val-q.val) := by
  rw [binary,ofFamily_pinch,Fintype.sum_bool]
  rfl

end CornerPartition

end

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition

theorem binary_pinch_of_commutes (p q : AlgebraProjection M) (hq : q ≤ p)
    (x : M.toStarSubalgebra) (hl : p.val*x=x) (hr : x*p.val=x)
    (hc : q.val*x=x*q.val) : (binary p q hq).pinch x=x := by
  have hqq : q.val*x*q.val=q.val*x := by
    rw [hc,mul_assoc,q.property.isIdempotentElem.eq]
  rw [binary_pinch]
  simp only [sub_mul,mul_sub,hl,hr,hqq]
  rw [hc]
  simp only [mul_assoc,projection_mul_of_le hq]
  abel

end CornerPartition

end

/-! Interval bounds propagated through constructed spectral corner splits. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem compress_scalar_shift {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) (t : ℝ) :
    q.val*(p.val*x*p.val-(t : ℂ) • p.val)*q.val =
      q.val*x*q.val-(t : ℂ) • q.val := by
  have hl : p.val*q.val=q.val := hqp
  have hr := projection_mul_of_le hqp
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  simp only [← mul_assoc,hr]
  simp only [mul_assoc,hl,q.property.isIdempotentElem.eq]

end

/-! Finite dyadic trees of actual spectral interval cuts. -/

/-! Constructed cuts preserve commutation with other operators. -/
section
open scoped CStarAlgebra
open UltrapowerBridge ContinuousLinearMap LinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem kernelProjection_commutes (x y : M.toStarSubalgebra)
    (hxy : Commute x y) (hxys : Commute x (star y)) :
    Commute (kernelProjection x).val y := by
  let k := x.val.ker.starProjection
  have hk : IsIdempotentElem k.toLinearMap :=
    (isStarProjection_starProjection (U := x.val.ker)).isIdempotentElem.toLinearMap
  have h₁ := kernel_invariant_of_commutes x.val y.val (congrArg Subtype.val hxy.eq)
  have h₂ : x.val.ker ∈ Module.End.invtSubmodule y.val.adjoint.toLinearMap := by
    exact kernel_invariant_of_commutes x.val (star y).val (congrArg Subtype.val hxys.eq)
  have hc : Commute k.toLinearMap y.val.toLinearMap := by
    apply (LinearMap.IsIdempotentElem.commute_iff hk).mpr
    change k.range ∈ Module.End.invtSubmodule y.val.toLinearMap ∧
      k.ker ∈ Module.End.invtSubmodule y.val.toLinearMap
    rw [Submodule.range_starProjection,Submodule.ker_starProjection]
    exact ⟨h₁,ContinuousLinearMap.orthogonal_mem_invtSubmodule h₂⟩
  apply Subtype.ext
  ext ξ
  exact congrArg (fun t : H →ₗ[ℂ] H => t ξ) hc.eq

end

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/

/-! Finite spectral approximation for an actual normal operator. -/

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def includedProjection (h : N ≤ M) (p : AlgebraProjection N) : AlgebraProjection M :=
  ⟨algebraInclusion h p.val,by
    constructor
    · change algebraInclusion h p.val * algebraInclusion h p.val = algebraInclusion h p.val
      rw [← map_mul,p.property.isIdempotentElem.eq]
    · change star (algebraInclusion h p.val)=algebraInclusion h p.val
      rw [← map_star,p.property.isSelfAdjoint.star_eq]⟩

end

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixUnits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite matrix algebras from matrix-unit laws. No factor or trace
hypothesis is needed for the algebraic construction. -/
open scoped BigOperators

namespace MatrixUnitSystem
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable (E : MatrixUnitSystem ι A)

variable [StarModule ℂ A]

theorem sandwich (a : Matrix ι ι ℂ) (o i j : ι) :
    E.entry o i * E.hom a * E.entry j o = a i j • E.entry o o := by
  simp only [hom_apply, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    E.mul_entry, smul_ite, smul_zero]
  simp [E.mul_entry, smul_ite]

theorem hom_injective (o : ι) (ho : E.entry o o ≠ 0) : Function.Injective E.hom := by
  intro a b hab
  ext i j
  have h := congrArg (fun x => E.entry o i*x*E.entry j o) hab
  rw [E.sandwich, E.sandwich] at h
  exact (smul_left_injective ℂ ho) h

/-! Commuting unital systems multiply to a larger full matrix algebra.
This proves compatibility algebraically; it does not construct a system in
a relative commutant or establish irreducibility of an infinite union. -/
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem diagonal_ne_zero [Nontrivial A] (o : ι) : E.entry o o ≠ 0 := by
  intro h
  have hz (i : ι) : E.entry i i = 0 := by
    have hio : E.entry i o = 0 := by
      have hm := E.mul_entry i o o o
      simpa [h] using hm.symm
    have hm := E.mul_entry i o o i
    simpa [hio] using hm.symm
  have ht := E.total
  simp only [hz, Finset.sum_const_zero] at ht
  exact zero_ne_one ht

theorem injective [Nontrivial A] [Nonempty ι] : Function.Injective E.hom :=
  E.hom_injective (Classical.arbitrary ι) (E.diagonal_ne_zero _)

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

def product : MatrixUnitSystem (ι × κ) A where
  entry a b := E.entry a.1 b.1 * F.entry a.2 b.2
  star_entry a b := by
    rw [star_mul,E.star_entry,F.star_entry]
    exact (hc _ _ _ _).eq.symm
  mul_entry a b c d := by
    have hr : (E.entry a.1 b.1*F.entry a.2 b.2)*(E.entry c.1 d.1*F.entry c.2 d.2)=
        (E.entry a.1 b.1*E.entry c.1 d.1)*(F.entry a.2 b.2*F.entry c.2 d.2) := by
      calc _ = E.entry a.1 b.1*(F.entry a.2 b.2*E.entry c.1 d.1)*F.entry c.2 d.2 := by
              simp only [mul_assoc]
           _ = _ := by rw [(hc c.1 d.1 a.2 b.2).eq.symm]; simp only [mul_assoc]
    rw [hr,E.mul_entry,F.mul_entry]
    by_cases h1 : b.1=c.1 <;> by_cases h2 : b.2=c.2 <;>
      simp [h1,h2,Prod.ext_iff]
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,F.total,mul_one,E.total]

omit [StarModule ℂ A] in
theorem product_entry (a b : ι × κ) :
    (E.product F hc).entry a b = E.entry a.1 b.1 * F.entry a.2 b.2 := rfl

omit [StarModule ℂ A] in
theorem product_sum_left (i j : ι) :
    (∑ k, (E.product F hc).entry (i,k) (j,k)) = E.entry i j := by
  simp only [product_entry, ← Finset.mul_sum, F.total, mul_one]

omit [StarModule ℂ A] in
theorem product_sum_right (k l : κ) :
    (∑ i, (E.product F hc).entry (i,k) (i,l)) = F.entry k l := by
  simp only [product_entry, ← Finset.sum_mul, E.total, one_mul]

/-! Corner amplification inside the actual matrix-unit commutant. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

/-! Diffuseness passes to the full matrix-unit commutant by splitting a
compressed projection and amplifying the split. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem diagonal_projection (o : ι) : IsStarProjection (E.entry o o) := by
  exact ⟨by show E.entry o o*E.entry o o=E.entry o o; simpa using E.mul_entry o o o o,E.star_entry o o⟩

open scoped BigOperators

/-! Actual matrix amplification by coefficients in the full matrix-unit
commutant. The evaluation homomorphism is proved surjective algebraically. -/
open scoped BigOperators

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! A normal element of a diffuse finite factor has L2 approximations in
constructed full dyadic matrix algebras. No prescribed MASA is needed. -/

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/

/-! Reindex full matrix units without changing their actual algebra or
relative commutant. This keeps iterated constructions indexed by Fin n. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def reindex (E : MatrixUnitSystem ι A) (e : κ ≃ ι) : MatrixUnitSystem κ A where
  entry i j := E.entry (e i) (e j)
  star_entry i j := E.star_entry _ _
  mul_entry i j k l := by simpa only [e.apply_eq_iff_eq] using E.mul_entry (e i) (e j) (e k) (e l)
  total := (e.sum_comp (fun i => E.entry i i)).trans E.total

open UltrapowerBridge

end MatrixUnitSystem

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/
section
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vonNeumann_wotClosed (M : VonNeumannAlgebra H) : WOTClosed M.toStarSubalgebra := by
  change IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ (M : Set (H →L[ℂ] H))}
  rw [← M.centralizer_centralizer]
  change IsClosed {T : H →WOT[ℂ] H |
    ∀ S ∈ Set.centralizer (M : Set (H →L[ℂ] H)),S*T.toCLM=T.toCLM*S}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro S
  apply isClosed_iInter
  intro hS
  have he : {T : H →WOT[ℂ] H | S*T.toCLM=T.toCLM*S} =
      {T : H →WOT[ℂ] H |
        (ContinuousLinearMapWOT.equiv.symm S)*T=T*(ContinuousLinearMapWOT.equiv.symm S)} := by
    ext T
    let e : (H →WOT[ℂ] H) ≃ (H →L[ℂ] H) := ContinuousLinearMapWOT.equiv
    exact e.injective.eq_iff
  rw [he]
  exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)

end Tracial
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def scalarStage (N : VonNeumannAlgebra H) : FiniteMatrixStage N where
  size := 1
  positive := by norm_num
  units := {
    entry := fun _ _ => 1
    star_entry := by intros; simp
    mul_entry := by
      intro i j k l
      rw [ite_eq_left (Subsingleton.elim j k),one_mul]
    total := by simp }

end FiniteMatrixStage

end

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wstar_starAlgebra_eq_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    wstar (S : Set (H →L[ℂ] H))=(bicommutantVonNeumann S).toStarSubalgebra := by
  apply le_antisymm
  · apply wstar_le (Tracial.vonNeumann_wotClosed _)
    intro a ha
    change a ∈ (bicommutantVonNeumann S : Set (H →L[ℂ] H))
    rw [bicommutantVonNeumann_coe]
    exact fun b hb => (hb a ha).symm
  · intro a ha
    have hb : a ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
      rwa [← bicommutantVonNeumann_coe]
    rw [← SetLike.mem_coe,← wotClosed_bicommutant _ (wstar_closed _)]
    exact fun b hb' => hb b (fun c hc => hb' c (subset_wstar _ hc))

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_PartialUnitaries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Popa's extension order on actual supported partial unitaries, and its
exact L2 distance identity. -/

/-! Actual L2 limits of partial unitaries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

/-! Actual orthogonal corner unitaries from dyadic trace cuts. These supply
weakly vanishing scalar matrix coefficients for the scalar-commutant case
of Popa's coordinate nonintertwining criterion. -/
section
open Filter
open scoped Topology BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

def dyadicSign (n : ℕ) (i : DyadicIndex (n+1)) : ℂ := if i.2 then -1 else 1

end

/-! Popa 1308.3982v3, §1.5, scalar-target specialization. The sequence is
constructed from actual dyadic trace cuts in each nonzero corner; neither
nonintertwining nor Haar existence is an assumption. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralWordIsometries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized dihedral word inclusions on actual tracial Hilbert spaces. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
  (htr : ∀ a b, τ (a * b) = τ (b * a))
  (V : R →ₗ[ℂ] E) (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (P Q : StarSubalgebra ℂ R) (hf : ScalarFree τ P Q)
  (d s e : R) (hd : d ∈ P) (hs : s ∈ Q) (he : e ∈ P)
  (hd0 : τ d = 0) (hs0 : τ s = 0)
  (hdd : d * d = 1) (hss : s * s = 1)
  (hdstar : star d = d) (hsstar : star s = s)
  (hestar : star e = e) (hee : e * e = e)

variable (VA : Q →ₗ[ℂ] K)
  (hA : ∀ a b : Q, inner ℂ (VA a) (VA b) = τ (star (a : R) * (b : R)))
  (t : ℝ) (ht : 0 < t) (hte : τ e = (t : ℂ))

/-- Isometric inclusion of the completed tracial base space as the `k`-th
actual dihedral word space. -/
def dihedralWordIsometry (hdense : DenseRange VA) (k : ℕ) : K →ₗᵢ[ℂ] E :=
  (normalizedDihedralWordMap V Q d s e t k).extendOfIsometry (e := VA) hdense
    (norm_normalizedDihedralWordMap τ hτ htr V hinner P Q hf d s e hd hs he hd0 hs0 hdd hss
      hdstar hsstar hestar hee VA hA t ht hte k)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SquareArrayPadding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Zero padding of Hilbert arrays

The coordinate inclusion along an arbitrary finite injection is isometric.
Extension of an operator by zero consequently preserves scalar commutator
norms and the norms of their matrix amplifications. No dimension factor occurs.
-/

noncomputable section
namespace KadisonSimilarity

section Coordinates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

@[simp] theorem copyEmbeddingMap_apply_image (e : Fin r ↪ Fin m)
    (x : HilbertCopies H r) (i : Fin r) : copyEmbeddingMap e x (e i) = x i := by
  simp [copyEmbeddingMap, Pi.single_apply, e.injective.eq_iff]

end Coordinates

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorPermutations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Permutations of completed Hilbert tensor words

The permutation maps are constructed from the multilinear universal property
and proved isometric on the algebraic tensor power before completion.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (E)

variable {E}

/-- The corresponding permutation on the completed Hilbert tensor power. -/
def completedTensorPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    CompletedTensorWord E n →ₗᵢ[ℂ] CompletedTensorWord E n :=
  (tensorPermutationIsometry σ).completion

@[simp] theorem completedTensorPermutation_word {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → E) :
    completedTensorPermutation σ (completedTensorWord x) =
      completedTensorWord (fun i => x (σ.symm i)) := by
  change (tensorPermutationIsometry σ).completion
    (tensorWord x : CompletedTensorWord E n) = _
  rw [LinearIsometry.completion_apply_coe]
  change (tensorPermutationLinear σ (tensorWord x) : CompletedTensorWord E n) = _
  rw [tensorPermutationLinear_word]
  rfl

/-- Every tensor-position permutation fixes a repeated-letter tensor. -/
@[simp] theorem completedTensorPermutation_constant {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : E) :
    completedTensorPermutation σ (completedTensorWord (fun _ : Fin n => x)) =
      completedTensorWord (fun _ : Fin n => x) := by
  rw [completedTensorPermutation_word]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointTensors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Completed tensor words with an unrestricted first endpoint

The endpoint and the centered tail may live in different Hilbert spaces.
Their completed tensor product has total elementary words and carries
the operators `I ⊗ A` and endpoint slices.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- An unrestricted endpoint followed by a completed centered tail. -/
abbrev EndpointTensor (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (n : ℕ) :=
  HilbertTensor E (CompletedTensorWord F n)

/-- Insert an endpoint in front of a completed tail vector. -/
def endpointInsert {n : ℕ} (d : E) :
    CompletedTensorWord F n →L[ℂ] EndpointTensor E F n :=
  UniformSpace.Completion.toComplL.comp (TensorProduct.mkL ℂ E (CompletedTensorWord F n) d)

/-- The elementary word with an unrestricted first endpoint. -/
def endpointWord {n : ℕ} (d : E) (x : Fin n → F) : EndpointTensor E F n :=
  endpointInsert d (completedTensorWord x)

@[simp] theorem endpointInsert_apply {n : ℕ} (d : E) (w : CompletedTensorWord F n) :
    endpointInsert d w = (d ⊗ₜ[ℂ] w : E ⊗[ℂ] CompletedTensorWord F n) := rfl

@[simp] theorem norm_endpointInsert {n : ℕ} (d : E) (w : CompletedTensorWord F n) :
    ‖endpointInsert d w‖ = ‖d‖ * ‖w‖ := by
  exact (UniformSpace.Completion.norm_coe (d ⊗ₜ[ℂ] w)).trans
    (TensorProduct.norm_tmul d w)

@[simp] theorem inner_endpointInsert {n : ℕ} (d c : E)
    (x z : CompletedTensorWord F n) :
    inner ℂ (endpointInsert d x) (endpointInsert c z) = inner ℂ d c * inner ℂ x z := by
  exact (UniformSpace.Completion.inner_coe (d ⊗ₜ[ℂ] x) (c ⊗ₜ[ℂ] z)).trans
    (TensorProduct.inner_tmul ℂ d c x z)

@[simp] theorem inner_endpointWord {n : ℕ} (d c : E) (x z : Fin n → F) :
    inner ℂ (endpointWord d x) (endpointWord c z) =
      inner ℂ d c * ∏ i, inner ℂ (x i) (z i) := by
  rw [endpointWord, endpointWord, inner_endpointInsert, inner_completedTensorWord]

variable {E' F' : Type*}
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- The completed tensor product of an endpoint map and a bounded tail operator. -/
def endpointTensorMap {k l : ℕ} (p : E →L[ℂ] E')
    (A : CompletedTensorWord F k →L[ℂ] CompletedTensorWord F' l) :
    EndpointTensor E F k →L[ℂ] EndpointTensor E' F' l :=
  (TensorProduct.mapL p A).completion

@[simp] theorem endpointTensorMap_insert {k l : ℕ} (p : E →L[ℂ] E')
    (A : CompletedTensorWord F k →L[ℂ] CompletedTensorWord F' l)
    (d : E) (x : CompletedTensorWord F k) :
    endpointTensorMap p A (endpointInsert d x) = endpointInsert (p d) (A x) := by
  change (TensorProduct.mapL p A).completion
      ((d ⊗ₜ[ℂ] x : E ⊗[ℂ] CompletedTensorWord F k) :
        UniformSpace.Completion (E ⊗[ℂ] CompletedTensorWord F k)) =
    ((p d ⊗ₜ[ℂ] A x : E' ⊗[ℂ] CompletedTensorWord F' l) :
      UniformSpace.Completion (E' ⊗[ℂ] CompletedTensorWord F' l))
  rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]

/-- The actual operator `I_E ⊗ A` on completed endpoint tensors. -/
def endpointAmplification {k l : ℕ}
    (A : CompletedTensorWord F k →L[ℂ] CompletedTensorWord F l) :
    EndpointTensor E F k →L[ℂ] EndpointTensor E F l :=
  endpointTensorMap (ContinuousLinearMap.id ℂ E) A

@[simp] theorem endpointAmplification_insert {k l : ℕ}
    (A : CompletedTensorWord F k →L[ℂ] CompletedTensorWord F l)
    (d : E) (x : CompletedTensorWord F k) :
    endpointAmplification A (endpointInsert d x) = endpointInsert d (A x) := by
  exact endpointTensorMap_insert (ContinuousLinearMap.id ℂ E) A d x

/-- A bounded operator acting only on the unrestricted endpoint. -/
def endpointHeadAction {n : ℕ} (p : E →L[ℂ] E) :
    EndpointTensor E F n →L[ℂ] EndpointTensor E F n :=
  endpointTensorMap p (ContinuousLinearMap.id ℂ (CompletedTensorWord F n))

@[simp] theorem endpointHeadAction_insert {n : ℕ} (p : E →L[ℂ] E)
    (d : E) (x : CompletedTensorWord F n) :
    endpointHeadAction p (endpointInsert d x) = endpointInsert (p d) x :=
  endpointTensorMap_insert p (ContinuousLinearMap.id ℂ _) d x

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantForms
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite-stage coefficient form

The coefficient function used by the invariant argument is proved multilinear
from the linear source letters and conjugate-linear test letters. No finite or
completed coefficient expansion is part of this construction.
-/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexConjugate TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The elementary completed word retains multilinearity in every letter. -/
theorem completedTensorWord_update_add {n : ℕ} (x : Fin n → F) (i : Fin n) (a b : F) :
    completedTensorWord (Function.update x i (a + b)) =
      completedTensorWord (Function.update x i a) + completedTensorWord (Function.update x i b) := by
  have h := (tensorWordMultilinear n).map_update_add x i a b
  simpa only [tensorWordMultilinear_apply, completedTensorWord,
    UniformSpace.Completion.coe_add] using congrArg
      (fun z : TensorWord F n => (z : CompletedTensorWord F n)) h

theorem completedTensorWord_update_smul {n : ℕ} (x : Fin n → F) (i : Fin n) (c : ℂ) (a : F) :
    completedTensorWord (Function.update x i (c • a)) =
      c • completedTensorWord (Function.update x i a) := by
  have h := (tensorWordMultilinear n).map_update_smul x i c a
  simpa only [tensorWordMultilinear_apply, completedTensorWord,
    UniformSpace.Completion.coe_smul] using congrArg
      (fun z : TensorWord F n => (z : CompletedTensorWord F n)) h

theorem endpointWord_add_endpoint {n : ℕ} (d c : E) (x : Fin n → F) :
    endpointWord (d + c) x = endpointWord d x + endpointWord c x := by
  exact (congrArg
    (fun z : E ⊗[ℂ] CompletedTensorWord F n =>
      (z : HilbertTensor E (CompletedTensorWord F n)))
    (TensorProduct.add_tmul d c (completedTensorWord x))).trans
      (hilbertTensor_coe_add _ _)

theorem endpointWord_smul_endpoint {n : ℕ} (c : ℂ) (d : E) (x : Fin n → F) :
    endpointWord (c • d) x = c • endpointWord d x := by
  exact (congrArg
    (fun z : E ⊗[ℂ] CompletedTensorWord F n =>
      (z : HilbertTensor E (CompletedTensorWord F n)))
    (TensorProduct.smul_tmul' c d (completedTensorWord x)).symm).trans
      (UniformSpace.Completion.coe_smul c (d ⊗ₜ[ℂ] completedTensorWord x))

theorem endpointWord_update_add {n : ℕ} (d : E) (x : Fin n → F) (i : Fin n) (a b : F) :
    endpointWord d (Function.update x i (a + b)) =
      endpointWord d (Function.update x i a) + endpointWord d (Function.update x i b) := by
  simp only [endpointWord, completedTensorWord_update_add, map_add]

theorem endpointWord_update_smul {n : ℕ} (d : E) (x : Fin n → F) (i : Fin n) (c : ℂ) (a : F) :
    endpointWord d (Function.update x i (c • a)) =
      c • endpointWord d (Function.update x i a) := by
  simp only [endpointWord, completedTensorWord_update_smul, map_smul]

variable {D : Type*} [AddCommGroup D] [Module ℂ D] {k l : ℕ}

/-- The coefficient with distinguished endpoint and two groups of tail letters. -/
def invariantStageCoefficient
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) (Ω : E)
    (testEndpoint : D →ₗ⋆[ℂ] E) (sourceLetter : D →ₗ[ℂ] F)
    (testLetter : D →ₗ⋆[ℂ] F) (v : Option (Fin k ⊕ Fin l) → D) : ℂ :=
  inner ℂ (endpointWord (testEndpoint (v none)) (pullLetters testLetter testIndex v))
    (Y (endpointWord Ω (pullLetters sourceLetter sourceIndex v)))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixRealization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix stages inside an actual tracial Hilbert representation

A trace-preserving matrix embedding supplies the normalized Hilbert--Schmidt
geometry, the corner left action, and the centered projection used by the
invariant-intertwiner argument. No invariant-theory conclusion is an input.
-/

noncomputable section
namespace KadisonSimilarity

variable {R E α : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [Fintype α] [DecidableEq α]

section Conjugation

variable [StarModule ℂ R]

variable (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E)
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (htrace : ∀ a b, τ (a * b) = τ (b * a))
  (hdense : DenseRange V)

/-- The actual tracial conjugation is obtained by extending algebraic involution
from the dense represented algebra. -/
def tracialConjugation : E →ₗᵢ⋆[ℂ] E :=
  (V.comp (starLinearEquiv ℂ).toLinearMap).extendOfIsometry
    (e := V) hdense (norm_tracial_star τ V hinner htrace)

end Conjugation

end KadisonSimilarity

end

end OAI
end


