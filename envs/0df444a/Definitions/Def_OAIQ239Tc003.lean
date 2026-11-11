-- Prove2me | Definitions.Def_OAIQ239Tc003
-- name    : OAIQ239Tc003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:09:45.644087+00:00
-- url     : https://prove2.me/theorems/5e981da6-a761-4f22-9cb0-8b9e39098060
-- title:
--   Definitions bundle OAIQ239Tc003 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 218 declarations of OpenAI's Lean: 107 definitions, 2 inductive types or structures and 109 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.first`, `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.principal`, `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.zero`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.End`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.actualSquareFirst`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.adjointCLM`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.halfJet`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.squareFirst`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.transformedFirst`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.weightedPrincipal`, `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.V`, `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat`, `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.laplacian`, `OAI.TamingCompatibility.GeometricHilbert.KernelExtension.push`, `OAI.TamingCompatibility.GeometricHilbert.KernelSeries.clip`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.End`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.First`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.Principal`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.cutoffPrincipal`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.euclideanPrincipal`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.residual`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.MetricDerivative`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.MetricTensor`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.centeredDerivative`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.centeredMap`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffel`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelBilinearNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelBilinearNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelCLM`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelDualNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelDualNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelEndomorphismNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelEndomorphismNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelMetricDerivativeNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelMetricDerivativeNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelMetricTensorNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelMetricTensorNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.christoffelValue`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.coordinateJet`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.inverseRegularDomain` and 69 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_ChartEnergyIntegral`, `TamingCompatibility_Charts_ChartMetric`, `TamingCompatibility_Charts_CoordinateIntegrand`, `TamingCompatibility_Charts_Coordinates`, `TamingCompatibility_Charts_FiniteCharts`, `TamingCompatibility_Charts_FirstJetGauge`, `TamingCompatibility_Charts_MetricCalculus`, `TamingCompatibility_Charts_SummableCutoff`, `TamingCompatibility_Charts_UnitaryFrames`, `TamingCompatibility_Currents_GeometricSeparatingProbability`, `TamingCompatibility_DifferentialForms_ChristoffelCLM`, `TamingCompatibility_DifferentialForms_Dpos`, `TamingCompatibility_DifferentialForms_End`, `TamingCompatibility_DifferentialForms_GeometricFrameTest`, `TamingCompatibility_DifferentialForms_InnerJLeft`, `TamingCompatibility_DifferentialForms_JAction`, `TamingCompatibility_DifferentialForms_MetricCoords`, `TamingCompatibility_DifferentialForms_MetricDensity`, `TamingCompatibility_DifferentialForms_MetricPairingCLM`, `TamingCompatibility_DifferentialForms_MetricTensor`, `TamingCompatibility_DifferentialForms_PositiveFunctions`, `TamingCompatibility_DifferentialForms_Sign`, `TamingCompatibility_DifferentialForms_Space`, `TamingCompatibility_DifferentialForms_StarTwoComp`, `TamingCompatibility_DifferentialForms_SymbolMap`, `TamingCompatibility_DifferentialForms_TopForms`, `TamingCompatibility_DifferentialForms_UnitaryFrame`, `TamingCompatibility_Elliptic_MatrixGarding`, `TamingCompatibility_Elliptic_OperatorCalculus`, `TamingCompatibility_Elliptic_WeightedPrincipal`, `TamingCompatibility_Functional_NormalPatch`, `TamingCompatibility_Functional_PlaneNormalization`, `TamingCompatibility_HeatFlow_FlatHeat`, `TamingCompatibility_Hodge_HodgeCutoffFamilies`, `TamingCompatibility_Hodge_HodgeCutoffSquare`, `TamingCompatibility_Hodge_HodgeKernelSeriesCore`, `TamingCompatibility_Hodge_HodgeManifoldKernelExtension`, `TamingCompatibility_Hodge_HodgeMatrixEnergy`, `TamingCompatibility_Hodge_HodgeNormalInverse`, `TamingCompatibility_Hodge_HodgeParametrixDomain`, `TamingCompatibility_Hodge_HodgeVolterraKernel`, `TamingCompatibility_Hodge_LocalCodifferential`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc006`, `OAIQ239Tc007` and `OAIQ239Tc008`; the statements `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.actualSquareFirst_skew`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.transformedFirst_zero`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.compact_cutoff_matrix`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.pullbackMetric_scalar_hasFDerivAt_zero` and `OAI.TamingCompatibility.GeometricHilbert.OrthogonalJets.gauge_contDiff`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.actualSquareFirst_skew` and `OAI.TamingCompatibility.GeometricHilbert.NormalJets.pullbackMetric_scalar_hasFDerivAt_zero`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
namespace TamingCompatibility

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

omit [IsManifold Model ∞ X] in
lemma eval_swap (α : TwoForm X) (x : X) (u v : TangentSpace Model x) :
    eval α x v u = -eval α x u v := by
  have hs : (![u, v] ∘ Equiv.swap (0 : Fin 2) 1) = ![v, u] := by
    funext i
    fin_cases i <;> simp
  simpa only [eval, hs, ContinuousAlternatingMap.coe_toAlternatingMap] using
    (α x).toAlternatingMap.map_swap ![u, v] (show (0 : Fin 2) ≠ 1 by decide)

omit [IsManifold Model ∞ X] in
lemma eval_neg_left (α : TwoForm X) (x : X) (u v : TangentSpace Model x) :
    eval α x (-u) v = -eval α x u v := by
  simpa only [neg_one_smul, smul_eq_mul, neg_one_mul, eval] using
    (α x).vecCons_smul ![v] (-1 : ℝ) u

omit [IsManifold Model ∞ X] in
lemma eval_neg_right (α : TwoForm X) (x : X) (u v : TangentSpace Model x) :
    eval α x u (-v) = -eval α x u v := by
  rw [eval_swap, eval_neg_left, eval_swap, neg_neg]

omit [IsManifold Model ∞ X] in
lemma eval_neg_neg (α : TwoForm X) (x : X) (u v : TangentSpace Model x) :
    eval α x (-u) (-v) = eval α x u v := by
  rw [eval_neg_left, eval_neg_right, neg_neg]

def jAction (J : AlmostComplexStructure X) (α : TwoForm X) : TwoForm X :=
  fun x => (α x).compContinuousLinearMap (J.endomorphism x)

lemma eval_jAction (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (u v : TangentSpace Model x) :
    eval (jAction J α) x u v =
      eval α x (J.endomorphism x u) (J.endomorphism x v) := by
  simp only [eval, jAction, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

def invariantPart (J : AlmostComplexStructure X) (α : TwoForm X) : TwoForm X :=
  (1 / 2 : ℝ) • (α + jAction J α)

def antiInvariantPart (J : AlmostComplexStructure X) (α : TwoForm X) : TwoForm X :=
  (1 / 2 : ℝ) • (α - jAction J α)

lemma eval_invariantPart (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (u v : TangentSpace Model x) :
    eval (invariantPart J α) x u v =
      (eval α x u v + eval α x (J.endomorphism x u) (J.endomorphism x v)) / 2 := by
  change (1 / 2 : ℝ) * (eval α x u v + eval (jAction J α) x u v) = _
  rw [eval_jAction]
  ring

lemma invariantPart_isInvariant (J : AlmostComplexStructure X) (α : TwoForm X) :
    IsInvariant (invariantPart J α) J := by
  intro x u v
  rw [eval_invariantPart, eval_invariantPart, J.square, J.square, eval_neg_neg, add_comm]

lemma eval_invariantPart_complexLine (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (v : TangentSpace Model x) :
    eval (invariantPart J α) x v (J.endomorphism x v) =
      eval α x v (J.endomorphism x v) := by
  rw [eval_invariantPart, J.square, eval_neg_right]
  rw [eval_swap α x v (J.endomorphism x v), neg_neg]
  ring

lemma tames_invariantPart {J : AlmostComplexStructure X} {α : TwoForm X}
    (h : Tames α J) : Tames (invariantPart J α) J := by
  intro x v hv
  rw [eval_invariantPart_complexLine]
  exact h x v hv

omit [IsManifold Model ∞ X] in
lemma TwoForm.ext_eval {α β : TwoForm X}
    (h : ∀ x u v, eval α x u v = eval β x u v) : α = β := by
  funext x
  ext v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  simpa only [eval, ← hv] using h x (v 0) (v 1)

lemma jAction_involutive (J : AlmostComplexStructure X) :
    Function.Involutive (jAction J) := by
  intro α
  apply TwoForm.ext_eval
  intro x u v
  rw [eval_jAction, eval_jAction, J.square, J.square, eval_neg_neg]

lemma jAction_add (J : AlmostComplexStructure X) (α β : TwoForm X) :
    jAction J (α + β) = jAction J α + jAction J β := rfl

lemma jAction_smul (J : AlmostComplexStructure X) (c : ℝ) (α : TwoForm X) :
    jAction J (c • α) = c • jAction J α := rfl

lemma antiInvariantPart_idempotent (J : AlmostComplexStructure X) (α : TwoForm X) :
    antiInvariantPart J (antiInvariantPart J α) = antiInvariantPart J α := by
  have hneg (β : TwoForm X) : jAction J (-β) = -jAction J β := rfl
  unfold antiInvariantPart
  simp only [sub_eq_add_neg, jAction_smul, jAction_add, hneg, jAction_involutive J α]
  module

omit [IsManifold Model ∞ X] in
lemma pullback_add (α β : TwoForm X) (f : Space → X) :
    pullback (α + β) f = pullback α f + pullback β f := rfl

omit [IsManifold Model ∞ X] in
lemma pullback_smul (c : ℝ) (α : TwoForm X) (f : Space → X) :
    pullback (c • α) f = c • pullback α f := rfl

omit [IsManifold Model ∞ X] in
lemma IsSmooth.add {α β : TwoForm X} (hα : IsSmooth α) (hβ : IsSmooth β) :
    IsSmooth (α + β) := by
  intro f U hU hf
  rw [pullback_add]
  exact (hα f U hU hf).add (hβ f U hU hf)

omit [IsManifold Model ∞ X] in
lemma IsSmooth.smul (c : ℝ) {α : TwoForm X} (hα : IsSmooth α) :
    IsSmooth (c • α) := by
  intro f U hU hf
  rw [pullback_smul]
  exact (hα f U hU hf).const_smul c

def associatedBilinear (J : AlmostComplexStructure X) (α : TwoForm X) (x : X) :
    TangentSpace Model x →L[ℝ] TangentSpace Model x →L[ℝ] ℝ := by
  letI : NormedAddCommGroup (TangentSpace Model x) := inferInstanceAs (NormedAddCommGroup Space)
  letI : NormedSpace ℝ (TangentSpace Model x) := inferInstanceAs (NormedSpace ℝ Space)
  exact ((ContinuousLinearMap.compL ℝ (TangentSpace Model x) (TangentSpace Model x) ℝ).flip
      (J.endomorphism x)) ∘L
    ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := TangentSpace Model x) (F := ℝ)
      (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L (α x).curryLeft)

lemma associatedBilinear_apply (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (u v : TangentSpace Model x) :
    associatedBilinear J α x u v = eval α x u (J.endomorphism x v) := by
  change (α x) (Matrix.vecCons u (fun _ : Fin 1 => J.endomorphism x v)) =
    (α x) ![u, J.endomorphism x v]
  congr 1
  ext i
  fin_cases i <;> rfl

lemma IsInvariant.shift_J {J : AlmostComplexStructure X} {α : TwoForm X}
    (h : IsInvariant α J) (x : X) (u v : TangentSpace Model x) :
    eval α x (J.endomorphism x u) v = -eval α x u (J.endomorphism x v) := by
  have he := h x u (J.endomorphism x v)
  rw [J.square, eval_neg_right] at he
  linarith

lemma IsInvariant.associatedBilinear_symm {J : AlmostComplexStructure X} {α : TwoForm X}
    (h : IsInvariant α J) (x : X) (u v : TangentSpace Model x) :
    associatedBilinear J α x u v = associatedBilinear J α x v u := by
  simp only [associatedBilinear_apply]
  calc
    eval α x u (J.endomorphism x v) = -eval α x (J.endomorphism x u) v := by
      rw [h.shift_J x u v, neg_neg]
    _ = eval α x v (J.endomorphism x u) := (eval_swap α x (J.endomorphism x u) v).symm

lemma IsInvariant.associatedBilinear_hermitian {J : AlmostComplexStructure X} {α : TwoForm X}
    (h : IsInvariant α J) (x : X) (u v : TangentSpace Model x) :
    associatedBilinear J α x (J.endomorphism x u) (J.endomorphism x v) =
      associatedBilinear J α x u v := by
  rw [associatedBilinear_apply, associatedBilinear_apply]
  exact h x u (J.endomorphism x v)

lemma Tames.associatedBilinear_pos {J : AlmostComplexStructure X} {α : TwoForm X}
    (h : Tames α J) (x : X) (v : TangentSpace Model x) (hv : v ≠ 0) :
    0 < associatedBilinear J α x v v := by
  rw [associatedBilinear_apply]
  exact h x v hv

lemma associatedBilinear_invariantPart_fundamental
    (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (u v : TangentSpace Model x) :
    associatedBilinear J (invariantPart J α) x (J.endomorphism x u) v =
      eval (invariantPart J α) x u v := by
  rw [associatedBilinear_apply]
  exact invariantPart_isInvariant J α x u v

end TamingCompatibility

open scoped Manifold ContDiff Topology
open Filter Set

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitaryFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryFrame

abbrev V := EuclideanSpace ℝ (Fin 4)

end TamingCompatibility.UnitaryFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_InnerJLeft
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryBasis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_J_left (J : E →ₗᵢ[ℝ] E) (hJ : ∀ v, J (J v) = -v) (v w : E) :
    ⟪J v, w⟫ = -⟪v, J w⟫ := by
  have h := J.inner_map_map v (J w)
  rw [hJ, inner_neg_right] at h
  linarith

lemma inner_self_J (J : E →ₗᵢ[ℝ] E) (hJ : ∀ v, J (J v) = -v) (v : E) :
    ⟪v, J v⟫ = 0 := by
  have h := inner_J_left J hJ v v
  rw [real_inner_comm] at h
  linarith

end TamingCompatibility.UnitaryBasis

open ContinuousAlternatingMap
namespace TamingCompatibility.GeometricSymbol
open UnitaryFrame
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev TwoForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E [⋀^Fin 2]→L[ℝ] ℝ

lemma eval_swap (α : TwoForm E) (u v : E) : α ![v,u] = -α ![u,v] := by
  have hs : (![u,v] ∘ Equiv.swap (0 : Fin 2) 1) = ![v,u] := by
    ext i; fin_cases i <;> simp
  simpa only [hs, ContinuousAlternatingMap.coe_toAlternatingMap] using
    α.toAlternatingMap.map_swap ![u,v] (show (0 : Fin 2) ≠ 1 by decide)

lemma eval_self (α : TwoForm E) (u : E) : α ![u,u] = 0 :=
  α.map_eq_zero_of_eq (v := ![u,u]) (i := 0) (j := 1) rfl (by decide)

def antiInvariant (J : E →L[ℝ] E) (α : TwoForm E) : TwoForm E :=
  (1 / 2 : ℝ) • (α - α.compContinuousLinearMap J)

lemma eval_neg_left (α : TwoForm E) (u v : E) : α ![-u,v] = -α ![u,v] := by
  simpa only [neg_one_smul, smul_eq_mul, neg_one_mul] using
    α.vecCons_smul ![v] (-1 : ℝ) u

lemma eval_neg_right (α : TwoForm E) (u v : E) : α ![u,-v] = -α ![u,v] := by
  rw [eval_swap, eval_neg_left, eval_swap, neg_neg]

end TamingCompatibility.GeometricSymbol

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_FiniteCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility.ManifoldLocalization
open Set Function
open scoped Topology Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]

structure FiniteCharts (X : Type*) [TopologicalSpace X] [ChartedSpace Space X]
    [IsManifold Model ∞ X] where
  centers : Finset X
  partition : SmoothPartitionOfUnity centers Model X
  subordinate : partition.IsSubordinate (fun p => (extChartAt Model p.val).source)

variable (A : FiniteCharts X)

omit [T2Space X] [CompactSpace X] in
lemma partition_sum (x : X) : ∑ p : A.centers, A.partition p x = 1 := by
  simpa only [finsum_eq_sum_of_fintype] using A.partition.sum_eq_one (mem_univ x)

def coordinateSupport (p : A.centers) : Set Space :=
  (extChartAt Model p.val) '' tsupport (A.partition p)

omit [T2Space X] in
lemma coordinateSupport_compact (p : A.centers) : IsCompact (coordinateSupport A p) := by
  apply (isClosed_tsupport _).isCompact.image_of_continuousOn
  exact (continuousOn_extChartAt p.val).mono (A.subordinate p)

omit [T2Space X] [CompactSpace X] in
lemma coordinateSupport_subset (p : A.centers) :
    coordinateSupport A p ⊆ (extChartAt Model p.val).target := by
  rintro y ⟨x,hx,rfl⟩
  exact (extChartAt Model p.val).map_source (A.subordinate p hx)

section Extension
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_indicator_of_compact {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hz : ∀ x ∈ U, x ∉ K → f x = 0) :
    ContDiff ℝ ∞ (U.indicator f) ∧ HasCompactSupport (U.indicator f) := by
  have hs : support (U.indicator f) ⊆ K := by
    intro x hx
    by_contra h
    by_cases hu : x ∈ U
    · exact hx (by rw [indicator_of_mem hu]; exact hz x hu h)
    · exact hx (indicator_of_notMem hu f)
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hK hs⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hu : x ∈ U
  · apply ((hf x hu).contDiffAt (hU.mem_nhds hu)).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hu] with y hy
    exact indicator_of_mem hy f
  · have hx : x ∉ K := fun h => hu (hKU h)
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact notMem_support.mp (fun h => hy (hs h))
end Extension

end TamingCompatibility.ManifoldLocalization

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
namespace TamingCompatibility.SmoothAlmostComplex

abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev Model := 𝓘(ℝ, Space)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

structure AlmostComplexStructure (X : Type*) [TopologicalSpace X]
    [ChartedSpace Space X] [IsManifold Model ∞ X] where
  endomorphism : (x : X) → TangentSpace Model x →L[ℝ] TangentSpace Model x
  square : ∀ x v, endomorphism x (endomorphism x v) = -v
  smooth : ContMDiff Model.tangent Model.tangent ∞
    (fun p : TangentBundle Model X =>
      (⟨p.proj, endomorphism p.proj p.2⟩ : TangentBundle Model X))

lemma contMDiffAt_localConstant
    (e : Trivialization Space (π Space (TangentSpace Model : X → Type)))
    [MemTrivializationAtlas e] {x : X} (hx : x ∈ e.baseSet) (v : Space) :
    ContMDiffAt Model Model.tangent ∞
      (fun y => (⟨y, e.symmL ℝ y v⟩ : TangentBundle Model X)) x := by
  apply (e.contMDiffAt_section_iff hx).mpr
  have hc : ContMDiffAt Model Model ∞ (fun _ : X => v) x := contMDiffAt_const
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  simp [e.symmL_apply hy, e.mk_symm hy, e.apply_symm_apply (show (y, v) ∈ e.target by simpa only [Trivialization.mem_target] using hy)]

lemma contMDiffOn_coord_apply (J : AlmostComplexStructure X)
    (e : Trivialization Space (π Space (TangentSpace Model : X → Type)))
    [MemTrivializationAtlas e] (v : Space) :
    ContMDiffOn Model Model ∞
      (fun y => e.continuousLinearMapAt ℝ y (J.endomorphism y (e.symmL ℝ y v)))
      e.baseSet := by
  intro y hy
  have hs := J.smooth.contMDiffAt.comp y (contMDiffAt_localConstant e hy v)
  have hc := (e.contMDiffAt_section_iff hy).mp hs
  apply (hc.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [e.open_baseSet.mem_nhds hy] with z hz
  exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hz _

def coord (J : AlmostComplexStructure X)
    (e : Trivialization Space (π Space (TangentSpace Model : X → Type)))
    [MemTrivializationAtlas e] (y : X) :
    Space →L[ℝ] Space :=
  (e.continuousLinearMapAt ℝ y).comp ((J.endomorphism y).comp (e.symmL ℝ y))

lemma contDiffOn_coord_chart (J : AlmostComplexStructure X) (x : X) :
    ContDiffOn ℝ ∞
      (fun z => coord J (trivializationAt Space (TangentSpace Model) x)
        ((extChartAt Model x).symm z))
      (extChartAt Model x).target := by
  rw [contDiffOn_clm_apply]
  intro v
  rw [← contMDiffOn_iff_contDiffOn]
  change ContMDiffOn Model Model ∞
    ((fun y => (trivializationAt Space (TangentSpace Model) x).continuousLinearMapAt ℝ y
      (J.endomorphism y ((trivializationAt Space (TangentSpace Model) x).symmL ℝ y v))) ∘
        (extChartAt Model x).symm) _
  apply (contMDiffOn_coord_apply J (trivializationAt Space (TangentSpace Model) x) v).comp
    (contMDiffOn_extChartAt_symm x)
  intro z hz
  simpa only [Set.mem_preimage, TangentBundle.trivializationAt_baseSet, extChartAt_source] using
    (extChartAt Model x).map_target hz

end TamingCompatibility.SmoothAlmostComplex

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricCoords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped Manifold ContDiff
noncomputable section
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
noncomputable section
open scoped Manifold ContDiff Topology
open Bundle Filter Set
noncomputable section
open Set
namespace TamingCompatibility
open Bundle Set
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

def metricCoords (J : AlmostComplexStructure X) (α : TwoForm X) (x y : X) :
    Space →L[ℝ] Space →L[ℝ] ℝ :=
  ContinuousLinearMap.inCoordinates Space (TangentSpace Model)
    (Space →L[ℝ] ℝ) (fun z => TangentSpace Model z →L[ℝ] ℝ)
    x y x y (associatedBilinear J α y)

end TamingCompatibility

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility.MetricDensity
open scoped BigOperators
open Matrix
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gram (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ) : Matrix ι ι ℝ :=
  fun i j => B (b i) (b j)

lemma gram_posDef (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ u v, B u v = B v u) (hp : ∀ u : E, u ≠ 0 → 0 < B u u) :
    (gram b B).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    exact hs _ _
  · intro x hx
    let v : E := ∑ i, x i • b i
    have hv : v ≠ 0 := by
      intro h
      apply hx
      funext i
      have hi := congrArg (fun w => b.repr w i) h
      simpa [v, Finsupp.single_apply] using hi
    have he : B v v = star x ⬝ᵥ (gram b B *ᵥ x) := by
      simp [v, gram, Matrix.mulVec, dotProduct, Finset.mul_sum,
        map_sum, map_smul, mul_comm, hs]
    rw [← he]
    exact hp v hv

def density (A : Matrix ι ι ℝ) : ℝ := Real.sqrt A.det

lemma density_pos (A : Matrix ι ι ℝ) (hA : A.PosDef) : 0 < density A :=
  Real.sqrt_pos.2 hA.det_pos

lemma density_transform (A L : Matrix ι ι ℝ) :
    density (L.transpose * A * L) = |L.det| * density A := by
  unfold density
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [show L.det * A.det * L.det = L.det ^ 2 * A.det by ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

lemma contDiffOn_det {n : WithTop ℕ∞} {A : D → Matrix ι ι ℝ} {U : Set D}
    (hA : ∀ i j, ContDiffOn ℝ n (fun x => A x i j) U) :
    ContDiffOn ℝ n (fun x => (A x).det) U := by
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro s _
  apply contDiffOn_const.mul
  exact contDiffOn_prod (fun i _ => hA (s i) i)

lemma contDiffOn_density {n : WithTop ℕ∞} {A : D → Matrix ι ι ℝ} {U : Set D}
    (hA : ∀ i j, ContDiffOn ℝ n (fun x => A x i j) U)
    (hp : ∀ x ∈ U, (A x).PosDef) :
    ContDiffOn ℝ n (fun x => density (A x)) U := by
  exact (contDiffOn_det hA).sqrt (fun x hx => (hp x hx).det_pos.ne')

lemma contDiffOn_gram_density {n : WithTop ℕ∞} (b : Module.Basis ι ℝ E)
    {B : D → E →L[ℝ] E →L[ℝ] ℝ} {U : Set D}
    (hB : ContDiffOn ℝ n B U)
    (hs : ∀ x ∈ U, ∀ u v, B x u v = B x v u)
    (hp : ∀ x ∈ U, ∀ u : E, u ≠ 0 → 0 < B x u u) :
    ContDiffOn ℝ n (fun x => density (gram b (B x))) U := by
  apply contDiffOn_density
  · intro i j
    exact (hB.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  · intro x hx
    exact gram_posDef b (B x) (hs x hx) (hp x hx)

def pullMetric (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E E ℝ).flip L ∘L B) ∘L L

@[simp] lemma pullMetric_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) (u v : E) :
    pullMetric B L u v = B (L u) (L v) := rfl

lemma gram_pullMetric (b : Module.Basis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) :
    gram b (pullMetric B L) =
      (LinearMap.toMatrix b b L.toLinearMap).transpose * gram b B *
        LinearMap.toMatrix b b L.toLinearMap := by
  ext i j
  change B (L (b i)) (L (b j)) = _
  conv_lhs => rw [← b.sum_repr (L (b i)), ← b.sum_repr (L (b j))]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    gram, Matrix.mul_apply, Matrix.transpose_apply, LinearMap.toMatrix_apply,
    ContinuousLinearMap.coe_coe, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma density_pullMetric (b : Module.Basis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) :
    density (gram b (pullMetric B L)) =
      |LinearMap.det L.toLinearMap| * density (gram b B) := by
  rw [gram_pullMetric, density_transform, LinearMap.det_toMatrix]

end TamingCompatibility.MetricDensity

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility.ManifoldVolume
open _root_.MeasureTheory Set Bundle
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

def chartMetric (J : AlmostComplexStructure X) (α : TwoForm X) (p : X) (z : Space) :
    Space →L[ℝ] Space →L[ℝ] ℝ :=
  metricCoords J (invariantPart J α) p ((extChartAt Model p).symm z)

lemma chartMetric_apply (J : AlmostComplexStructure X) (α : TwoForm X) (p : X)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    chartMetric J α p z u v = associatedBilinear J (invariantPart J α)
      ((extChartAt Model p).symm z)
      ((trivializationAt Space (TangentSpace Model) p).symmL ℝ
        ((extChartAt Model p).symm z) u)
      ((trivializationAt Space (TangentSpace Model) p).symmL ℝ
        ((extChartAt Model p).symm z) v) := by
  let e := extChartAt Model p
  let te := trivializationAt Space (TangentSpace Model) p
  have hs : e.symm z ∈ (chartAt Space p).source := by
    simpa only [e, extChartAt_source] using e.map_target hz
  have ht : e.symm z ∈ te.baseSet := by
    simpa only [te, TangentBundle.trivializationAt_baseSet] using hs
  unfold chartMetric metricCoords
  rw [inCoordinates_apply_eq₂ ht ht (Set.mem_univ _)]
  change (Bundle.Trivial.trivialization X ℝ).linearMapAt ℝ (e.symm z) _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply,
    te.symmL_apply ht, te.symmL_apply ht]

lemma chartMetric_symm (J : AlmostComplexStructure X) (α : TwoForm X) (p : X)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    chartMetric J α p z u v = chartMetric J α p z v u := by
  rw [chartMetric_apply J α p hz, chartMetric_apply J α p hz]
  exact (invariantPart_isInvariant J α).associatedBilinear_symm _ _ _

lemma chartMetric_pos (J : AlmostComplexStructure X) (α : TwoForm X)
    (htame : Tames α J) (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target)
    (u : Space) (hu : u ≠ 0) : 0 < chartMetric J α p z u u := by
  rw [chartMetric_apply J α p hz]
  apply (tames_invariantPart htame).associatedBilinear_pos
  let te := trivializationAt Space (TangentSpace Model) p
  have ht : (extChartAt Model p).symm z ∈ te.baseSet := by
    simpa only [te, TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (extChartAt Model p).map_target hz
  intro h
  have hc := congrArg (te.continuousLinearMapAt ℝ ((extChartAt Model p).symm z)) h
  rw [te.continuousLinearMapAt_symmL ht, map_zero] at hc
  exact hu hc

def chartDensity (J : AlmostComplexStructure X) (α : TwoForm X) (p : X) (z : Space) : ℝ :=
  MetricDensity.density (MetricDensity.gram (stdOrthonormalBasis ℝ Space).toBasis
    (chartMetric J α p z))

lemma chartDensity_pos (J : AlmostComplexStructure X) (α : TwoForm X)
    (htame : Tames α J) (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    0 < chartDensity J α p z :=
  MetricDensity.density_pos _ (MetricDensity.gram_posDef _ _
    (chartMetric_symm J α p hz) (chartMetric_pos J α htame p hz))

lemma inverseChart_derivative (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) :
    mfderiv Model Model (extChartAt Model p).symm z =
      (trivializationAt Space (TangentSpace Model) p).symmL ℝ
        ((extChartAt Model p).symm z) := by
  have hs : (extChartAt Model p).symm z ∈ (chartAt Space p).source := by
    simpa only [extChartAt_source] using (extChartAt Model p).map_target hz
  rw [TangentBundle.symmL_trivializationAt hs, (extChartAt Model p).right_inv hz]
  simp only [Model, modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ]

lemma chartMetric_derivative (J : AlmostComplexStructure X) (α : TwoForm X) (p : X)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    chartMetric J α p z u v = associatedBilinear J (invariantPart J α)
      ((extChartAt Model p).symm z)
      (mfderiv Model Model (extChartAt Model p).symm z u)
      (mfderiv Model Model (extChartAt Model p).symm z v) := by
  rw [chartMetric_apply J α p hz, inverseChart_derivative p hz]
  rfl

lemma inverseChart_comp_transition (p q : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target)
    (hq : (extChartAt Model p).symm z ∈ (extChartAt Model q).source) :
    mfderiv Model Model (extChartAt Model q).symm
        ((extChartAt Model q) ((extChartAt Model p).symm z)) ∘L
      fderiv ℝ ((extChartAt Model q) ∘ (extChartAt Model p).symm) z =
        mfderiv Model Model (extChartAt Model p).symm z := by
  have hp' : MDifferentiableAt Model Model (extChartAt Model p).symm z :=
    ((contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).mdifferentiableAt (by simp)
  have hq' : MDifferentiableAt Model Model (extChartAt Model q)
      ((extChartAt Model p).symm z) := by
    apply (contMDiffOn_extChartAt (I := Model) (x := q) (n := ∞)).contMDiffAt _
      |>.mdifferentiableAt (by simp)
    simpa only [extChartAt_source] using (isOpen_extChartAt_source q).mem_nhds hq
  erw [← mfderiv_eq_fderiv, mfderiv_comp z hq' hp', ← ContinuousLinearMap.comp_assoc]
  have hinv := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := Model) hq
  simp only [Model, modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ] at hinv
  erw [hinv]
  rfl

lemma chartMetric_transition (J : AlmostComplexStructure X) (α : TwoForm X) (p q : X)
    {z : Space} (hz : z ∈ (extChartAt Model p).target)
    (hq : (extChartAt Model p).symm z ∈ (extChartAt Model q).source) :
    chartMetric J α p z = MetricDensity.pullMetric
      (chartMetric J α q ((extChartAt Model q) ((extChartAt Model p).symm z)))
      (fderiv ℝ ((extChartAt Model q) ∘ (extChartAt Model p).symm) z) := by
  ext u v
  rw [MetricDensity.pullMetric_apply, chartMetric_derivative J α p hz,
    chartMetric_derivative J α q ((extChartAt Model q).map_source hq)]
  have hd := inverseChart_comp_transition p q hz hq
  have hu := congrArg (fun L : Space →L[ℝ] Space => L u) hd
  have hv := congrArg (fun L : Space →L[ℝ] Space => L v) hd
  change (mfderiv Model Model (extChartAt Model q).symm
    ((extChartAt Model q) ((extChartAt Model p).symm z)))
    ((fderiv ℝ ((extChartAt Model q) ∘ (extChartAt Model p).symm) z) u) = _ at hu
  change (mfderiv Model Model (extChartAt Model q).symm
    ((extChartAt Model q) ((extChartAt Model p).symm z)))
    ((fderiv ℝ ((extChartAt Model q) ∘ (extChartAt Model p).symm) z) v) = _ at hv
  erw [hu, hv, (extChartAt Model q).left_inv hq]
  rfl

lemma chartDensity_transition (J : AlmostComplexStructure X) (α : TwoForm X) (p q : X)
    {z : Space} (hz : z ∈ (extChartAt Model p).target)
    (hq : (extChartAt Model p).symm z ∈ (extChartAt Model q).source) :
    chartDensity J α p z =
      |LinearMap.det (fderiv ℝ ((extChartAt Model q) ∘
        (extChartAt Model p).symm) z).toLinearMap| *
      chartDensity J α q ((extChartAt Model q) ((extChartAt Model p).symm z)) := by
  unfold chartDensity
  rw [chartMetric_transition J α p q hz hq, MetricDensity.density_pullMetric]

def chartOverlap (p q : X) : Set Space :=
  (extChartAt Model p).target ∩ (extChartAt Model p).symm ⁻¹' (extChartAt Model q).source

def transition (p q : X) : Space → Space :=
  (extChartAt Model q) ∘ (extChartAt Model p).symm

omit [IsManifold Model ∞ X] in
lemma chartOverlap_open (p q : X) : IsOpen (chartOverlap p q) :=
  (continuousOn_extChartAt_symm p).isOpen_inter_preimage
    (isOpen_extChartAt_target p) (isOpen_extChartAt_source q)

omit [IsManifold Model ∞ X] in
lemma transition_injOn (p q : X) : Set.InjOn (transition p q) (chartOverlap p q) := by
  intro z hz w hw he
  apply (extChartAt Model p).symm.injOn hz.1 hw.1
  exact (extChartAt Model q).injOn hz.2 hw.2 he

omit [IsManifold Model ∞ X] in
lemma transition_image_overlap (p q : X) :
    transition p q '' chartOverlap p q = chartOverlap q p := by
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨(extChartAt Model q).map_source hz.2, ?_⟩
    change (extChartAt Model q).symm ((extChartAt Model q)
      ((extChartAt Model p).symm z)) ∈ (extChartAt Model p).source
    rw [(extChartAt Model q).left_inv hz.2]
    exact (extChartAt Model p).map_target hz.1
  · intro hw
    refine ⟨transition q p w, ⟨(extChartAt Model p).map_source hw.2, ?_⟩, ?_⟩
    · change (extChartAt Model p).symm ((extChartAt Model p)
        ((extChartAt Model q).symm w)) ∈ (extChartAt Model q).source
      rw [(extChartAt Model p).left_inv hw.2]
      exact (extChartAt Model q).map_target hw.1
    · dsimp only [transition, Function.comp_apply]
      rw [(extChartAt Model p).left_inv hw.2, (extChartAt Model q).right_inv hw.1]

lemma transition_differentiableAt (p q : X) {z : Space} (hz : z ∈ chartOverlap p q) :
    DifferentiableAt ℝ (transition p q) z := by
  have hp' : MDifferentiableAt Model Model (extChartAt Model p).symm z :=
    ((contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz.1)).mdifferentiableAt (by simp)
  have hq' : MDifferentiableAt Model Model (extChartAt Model q)
      ((extChartAt Model p).symm z) := by
    apply (contMDiffOn_extChartAt (I := Model) (x := q) (n := ∞)).contMDiffAt _
      |>.mdifferentiableAt (by simp)
    simpa only [extChartAt_source] using (isOpen_extChartAt_source q).mem_nhds hz.2
  exact mdifferentiableAt_iff_differentiableAt.mp (hq'.comp z hp')

lemma integral_overlap (J : AlmostComplexStructure X) (α : TwoForm X)
    (p q : X) (f : X → ℝ) :
    (∫ z in chartOverlap p q, chartDensity J α p z * f ((extChartAt Model p).symm z)) =
      ∫ w in chartOverlap q p, chartDensity J α q w * f ((extChartAt Model q).symm w) := by
  rw [← transition_image_overlap p q,
    integral_image_eq_integral_abs_det_fderiv_smul volume (chartOverlap_open p q).measurableSet
      (fun z hz => (transition_differentiableAt p q hz).hasFDerivAt.hasFDerivWithinAt)
      (transition_injOn p q)]
  apply setIntegral_congr_fun (chartOverlap_open p q).measurableSet
  intro z hz
  dsimp only
  rw [smul_eq_mul, chartDensity_transition J α p q hz.1 hz.2]
  dsimp only [transition, Function.comp_apply]
  rw [(extChartAt Model q).left_inv hz.2]
  ring

variable [T2Space X] [CompactSpace X]
variable (A : ManifoldLocalization.FiniteCharts X)

def chartWeight (J : AlmostComplexStructure X) (α : TwoForm X) (p : A.centers) : Space → ℝ :=
  (extChartAt Model p.val).target.indicator (fun z =>
    A.partition p ((extChartAt Model p.val).symm z) * chartDensity J α p.val z)

omit [T2Space X] [CompactSpace X] in
lemma chartWeight_nonneg (J : AlmostComplexStructure X) (α : TwoForm X)
    (p : A.centers) (z : Space) : 0 ≤ chartWeight A J α p z := by
  apply Set.indicator_nonneg
  intro y _
  exact mul_nonneg (A.partition.nonneg _ _) (Real.sqrt_nonneg _)

variable [MeasurableSpace X] [BorelSpace X]

def chartInverse (p : X) (z : Space) : X := by
  classical
  exact if z ∈ (extChartAt Model p).target then (extChartAt Model p).symm z else p

omit [T2Space X] [CompactSpace X] [IsManifold Model ∞ X] in
lemma chartInverse_measurable (p : X) : Measurable (chartInverse p) := by
  classical
  exact (continuousOn_extChartAt_symm p).measurable_piecewise
    continuousOn_const (isOpen_extChartAt_target p).measurableSet

def chartMeasure (J : AlmostComplexStructure X) (α : TwoForm X) (p : A.centers) :
    Measure X := Measure.map (chartInverse p.val)
      (volume.withDensity (fun z => ENNReal.ofReal (chartWeight A J α p z)))

def geometricVolume (J : AlmostComplexStructure X) (α : TwoForm X) : Measure X :=
  ∑ p : A.centers, chartMeasure A J α p

end TamingCompatibility.ManifoldVolume

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_CoordinateIntegrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility.ManifoldVolume
open _root_.MeasureTheory Set Bundle
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]

def coordinateIntegrand (J : AlmostComplexStructure X) (α : TwoForm X)
    (p : X) (f : X → ℝ) : Space → ℝ :=
  (extChartAt Model p).target.indicator
    (fun z => chartDensity J α p z * f ((extChartAt Model p).symm z))

lemma continuous_indicator_compact {E F : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace F] [Zero F] {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {f : E → F}
    (hf : ContinuousOn f U) (hz : ∀ x ∈ U, x ∉ K → f x = 0) :
    Continuous (U.indicator f) ∧ HasCompactSupport (U.indicator f) := by
  have hs : Function.support (U.indicator f) ⊆ K := by
    intro x hx
    by_contra h
    by_cases hu : x ∈ U
    · exact hx (by rw [indicator_of_mem hu]; exact hz x hu h)
    · exact hx (indicator_of_notMem hu f)
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hK hs⟩
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hu : x ∈ U
  · apply ((hf x hu).continuousAt (hU.mem_nhds hu)).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hu] with y hy
    exact indicator_of_mem hy f
  · have hx : x ∉ K := fun h => hu (hKU h)
    apply (show ContinuousAt (fun _ : E => (0 : F)) x from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact Function.notMem_support.mp (fun h => hy (hs h))

omit [T2Space X] [CompactSpace X] in

lemma integral_coordinateIntegrand_eq (J : AlmostComplexStructure X) (α : TwoForm X)
    (p q : X) (f : X → ℝ)
    (hfp : tsupport f ⊆ (extChartAt Model p).source)
    (hfq : tsupport f ⊆ (extChartAt Model q).source) :
    (∫ z, coordinateIntegrand J α p f z) = ∫ z, coordinateIntegrand J α q f z := by
  have h (a b : X) (hb : tsupport f ⊆ (extChartAt Model b).source) :
      coordinateIntegrand J α a f = (chartOverlap a b).indicator
        (fun z => chartDensity J α a z * f ((extChartAt Model a).symm z)) := by
    funext z
    by_cases ha : z ∈ (extChartAt Model a).target
    · by_cases hba : (extChartAt Model a).symm z ∈ (extChartAt Model b).source
      · have hab : z ∈ chartOverlap a b := ⟨ha,hba⟩
        simp only [coordinateIntegrand, indicator_of_mem ha, indicator_of_mem hab]
      · have hn : (extChartAt Model a).symm z ∉ tsupport f := fun h => hba (hb h)
        have hab : z ∉ chartOverlap a b := fun h => hba h.2
        simp only [coordinateIntegrand, indicator_of_mem ha, indicator_of_notMem hab,
          image_eq_zero_of_notMem_tsupport hn, mul_zero]
    · have hab : z ∉ chartOverlap a b := fun h => ha h.1
      simp only [coordinateIntegrand, indicator_of_notMem ha, indicator_of_notMem hab]
  rw [h p q hfq, h q p hfp, integral_indicator (chartOverlap_open p q).measurableSet,
    integral_indicator (chartOverlap_open q p).measurableSet]
  exact integral_overlap J α p q f

end TamingCompatibility.ManifoldVolume

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_UnitaryFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.LocalUnitaryFrame
open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev Bilinear (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

lemma skew (B : Bilinear E) (J : E →L[ℝ] E)
    (hJ : ∀ u, J (J u) = -u) (hBJ : ∀ u v, B (J u) (J v) = B u v) (u v : E) :
    B (J u) v = -B u (J v) := by
  have h := hBJ u (J v)
  rw [hJ, map_neg] at h
  linarith

lemma orthogonal_J (B : Bilinear E) (J : E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u)
    (hJ : ∀ u, J (J u) = -u) (hBJ : ∀ u v, B (J u) (J v) = B u v) (u : E) :
    B u (J u) = 0 := by
  have h := skew B J hJ hBJ u u
  rw [hB (J u) u] at h
  linarith

def normalize (B : Bilinear E) (u : E) : E := (Real.sqrt (B u u))⁻¹ • u

lemma normalize_unit (B : Bilinear E) (u : E) (h : 0 < B u u) :
    B (normalize B u) (normalize B u) = 1 := by
  have hp : (Real.sqrt (B u u)) ^ 2 = B u u := Real.sq_sqrt h.le
  have hn : Real.sqrt (B u u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h)
  simp only [normalize, map_smul, _root_.smul_apply, smul_eq_mul]
  field_simp
  exact hp.symm

lemma normalize_eq_of_unit (B : Bilinear E) (u : E) (h : B u u = 1) :
    normalize B u = u := by simp [normalize, h]

def transverse (B : Bilinear E) (J : E →L[ℝ] E) (u w : E) : E :=
  w - B u w • u - B (J u) w • J u

lemma transverse_orthogonal (B : Bilinear E) (J : E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u)
    (hJ : ∀ u, J (J u) = -u) (hBJ : ∀ u v, B (J u) (J v) = B u v)
    (u w : E) (hu : B u u = 1) :
    B u (transverse B J u w) = 0 ∧ B (J u) (transverse B J u w) = 0 := by
  have hz := orthogonal_J B J hB hJ hBJ u
  have hz' : B (J u) u = 0 := by rw [hB, hz]
  have hj : B (J u) (J u) = 1 := (hBJ u u).trans hu
  constructor <;> simp [transverse, map_sub, map_smul, hu, hz, hz', hj]

lemma transverse_eq (B : Bilinear E) (J : E →L[ℝ] E) (u w : E)
    (hw : B u w = 0) (hjw : B (J u) w = 0) : transverse B J u w = w := by
  simp [transverse, hw, hjw]

def frame (J : E →L[ℝ] E) (u w : E) : Fin 4 → E := ![u,J u,w,J w]

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {B : D → Bilinear E} {v w : D → E} {J : D → E →L[ℝ] E}
variable {U : Set D}

lemma contDiffOn_evaluate (hB : ContDiffOn ℝ ∞ B U)
    (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (fun x => B x (v x) (w x)) U := (hB.clm_apply hv).clm_apply hw

lemma contDiffOn_normalize (hB : ContDiffOn ℝ ∞ B U) (hv : ContDiffOn ℝ ∞ v U)
    (hp : ∀ x ∈ U, 0 < B x (v x) (v x)) :
    ContDiffOn ℝ ∞ (fun x => normalize (B x) (v x)) U := by
  apply ContDiffOn.smul _ hv
  apply ContDiffOn.inv
  · exact (contDiffOn_evaluate hB hv hv).sqrt (fun x hx => ne_of_gt (hp x hx))
  · intro x hx
    exact ne_of_gt (Real.sqrt_pos.mpr (hp x hx))

lemma contDiffOn_transverse (hB : ContDiffOn ℝ ∞ B U)
    (hJ : ContDiffOn ℝ ∞ J U) (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (fun x => transverse (B x) (J x) (v x) (w x)) U :=
  (hw.sub ((contDiffOn_evaluate hB hv hw).smul hv)).sub
    ((contDiffOn_evaluate hB (hJ.clm_apply hv) hw).smul (hJ.clm_apply hv))

end TamingCompatibility.LocalUnitaryFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_StarTwoComp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap

namespace TamingCompatibility.ManifoldHodge
open Bundle ContinuousAlternatingMap ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

local instance instNormedAddCommGroupTangentSpaceRealSpaceModel_r612de4_1 (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)
local instance instNormedSpaceRealTangentSpaceSpaceModel_r612de4_1 (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance instFiniteDimensionalRealTangentSpaceSpaceModel_r612de4_1 (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)
def coordinateJ (J : AlmostComplexStructure X) (p : X) (z : Space) : Space →L[ℝ] Space :=
  SmoothAlmostComplex.coord
    (⟨J.endomorphism,J.square,J.smooth⟩ : SmoothAlmostComplex.AlmostComplexStructure X)
    (trivializationAt Space (TangentSpace Model) p) ((extChartAt Model p).symm z)

lemma coordinateJ_smooth (J : AlmostComplexStructure X) (p : X) :
    ContDiffOn ℝ ∞ (coordinateJ J p) (extChartAt Model p).target :=
  SmoothAlmostComplex.contDiffOn_coord_chart ⟨J.endomorphism,J.square,J.smooth⟩ p

end TamingCompatibility.ManifoldHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_TopForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.TopForms
open ContinuousAlternatingMap
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] {n : ℕ}

def coefficient (b : Module.Basis (Fin n) ℝ E)
    (ν α : E [⋀^Fin n]→L[ℝ] ℝ) : ℝ := α b / ν b

lemma eval_eq_det_mul (b : Module.Basis (Fin n) ℝ E)
    (α : E [⋀^Fin n]→L[ℝ] ℝ) (v : Fin n → E) : α v = α b * b.det v := by
  have he := congrArg (fun a : E [⋀^Fin n]→ₗ[ℝ] ℝ => a v)
    (AlternatingMap.eq_smul_basis_det b α.toAlternatingMap)
  exact he

lemma coefficient_smul (b : Module.Basis (Fin n) ℝ E)
    (ν α : E [⋀^Fin n]→L[ℝ] ℝ) (hν : ν b ≠ 0) : coefficient b ν α • ν = α := by
  ext v
  change (α b / ν b) * ν v = α v
  rw [eval_eq_det_mul b ν v,eval_eq_det_mul b α v]
  field_simp

lemma coefficient_smul_left (b : Module.Basis (Fin n) ℝ E)
    (ν : E [⋀^Fin n]→L[ℝ] ℝ) (hν : ν b ≠ 0) (r : ℝ) :
    coefficient b ν (r • ν) = r := by
  change (r * ν b) / ν b = r
  exact mul_div_cancel_right₀ r hν

lemma eval_ne_zero (b : Module.Basis (Fin n) ℝ E)
    (ν : E [⋀^Fin n]→L[ℝ] ℝ) (hν : ν ≠ 0) : ν b ≠ 0 := by
  intro h
  apply hν
  ext v
  change ν v = 0
  rw [eval_eq_det_mul b ν v,h,zero_mul]

lemma comp_ne_zero (L : E ≃L[ℝ] D) (ν : D [⋀^Fin n]→L[ℝ] ℝ) (hν : ν ≠ 0) :
    ν.compContinuousLinearMap L.toContinuousLinearMap ≠ 0 := by
  intro h
  apply hν
  ext v
  have he := congrArg (fun a : E [⋀^Fin n]→L[ℝ] ℝ => a (fun i => L.symm (v i))) h
  simpa only [compContinuousLinearMap_apply,ContinuousLinearEquiv.coe_coe,
    Function.comp_def,ContinuousLinearEquiv.apply_symm_apply,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply] using he

lemma coefficient_comp (b : Module.Basis (Fin n) ℝ E) (c : Module.Basis (Fin n) ℝ D)
    (L : E ≃L[ℝ] D) (ν α : D [⋀^Fin n]→L[ℝ] ℝ) (hν : ν ≠ 0) :
    coefficient b (ν.compContinuousLinearMap L.toContinuousLinearMap) (α.compContinuousLinearMap L.toContinuousLinearMap) =
      coefficient c ν α := by
  have he := congrArg (fun a : D [⋀^Fin n]→L[ℝ] ℝ => a.compContinuousLinearMap L.toContinuousLinearMap)
    (coefficient_smul c ν α (eval_ne_zero c ν hν))
  have hes : (coefficient c ν α • ν).compContinuousLinearMap L.toContinuousLinearMap =
      coefficient c ν α • ν.compContinuousLinearMap L.toContinuousLinearMap := by ext v; rfl
  rw [hes] at he
  rw [← he,coefficient_smul_left b _ (eval_ne_zero b _ (comp_ne_zero L ν hν))]

end TamingCompatibility.TopForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Sign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.OrientationSign
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sign (t : ℝ) : ℝ := if 0 < t then 1 else -1

end TamingCompatibility.OrientationSign

namespace TamingCompatibility.ManifoldTop
open Bundle ContinuousAlternatingMap ManifoldHodge
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

def basisIndex : Fin (Module.finrank ℝ Space) ≃ Fin 4 := finCongr (by simp [Space])
def basis : Module.Basis (Fin 4) ℝ Space := (stdOrthonormalBasis ℝ Space).toBasis.reindex basisIndex

lemma density_basis (B : Space →L[ℝ] Space →L[ℝ] ℝ) :
    MetricDensity.density (MetricDensity.gram basis B) =
      MetricDensity.density (MetricDensity.gram (stdOrthonormalBasis ℝ Space).toBasis B) := by
  unfold MetricDensity.density
  congr 1
  have he : MetricDensity.gram basis B =
      (MetricDensity.gram (stdOrthonormalBasis ℝ Space).toBasis B).submatrix basisIndex.symm basisIndex.symm := by
    ext i j
    simp [MetricDensity.gram,basis,Module.Basis.reindex_apply]
  rw [he,Matrix.det_submatrix_equiv_self]

omit [IsManifold Model ∞ X] in
lemma scalar_smooth_of_charts {f : X → ℝ}
    (hf : ∀ p : X, ContDiffOn ℝ ∞ (f ∘ (extChartAt Model p).symm) (extChartAt Model p).target) :
    ContMDiff Model 𝓘(ℝ,ℝ) ∞ f := by
  intro x
  have h := ((hf x) ((extChartAt Model x) x)
    ((extChartAt Model x).map_source (mem_extChartAt_source x))).contDiffAt (extChartAt_target_mem_nhds x)
  have hc : ContMDiffAt Model 𝓘(ℝ,ℝ) ∞ (f ∘ (extChartAt Model x).symm) ((extChartAt Model x) x) :=
    contMDiffAt_iff_contDiffAt.mpr h
  apply (hc.comp x (contMDiffAt_extChartAt (n := ∞) (I := Model) (x := x))).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := Model) x).mem_nhds (mem_extChartAt_source x)] with y hy
  simp only [Function.comp_apply,(extChartAt Model x).left_inv hy]

end TamingCompatibility.ManifoldTop

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_LocalCodifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section

namespace TamingCompatibility.MetricHodge
open ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local instance instFiniteDimensionalRealContinuousMultilinearMapFin_solutions {k : ℕ} : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective
local instance instFiniteDimensionalRealContinuousAlternatingMapFin_solutions {k : ℕ} : FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective ContinuousAlternatingMap.toContinuousMultilinearMapLinear
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective

end TamingCompatibility.MetricHodge

namespace TamingCompatibility.SmoothHodge
open MetricHodge
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
local instance instFiniteDimensionalRealContinuousMultilinearMapFin_solutions {k : ℕ} : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective
local instance instFiniteDimensionalRealContinuousAlternatingMapFin_solutions {k : ℕ} : FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective ContinuousAlternatingMap.toContinuousMultilinearMapLinear
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective

end TamingCompatibility.SmoothHodge

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_MatrixGarding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap
namespace TamingCompatibility.MatrixEnergy

lemma exists_small_error {K : ℝ} (hK : 0 < K) : ∃ δ : ℝ, 0 < δ ∧ 16*K*δ^2 ≤ 1/2 := by
  refine ⟨(Real.sqrt (32*K))⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)), ?_⟩
  have hs := Real.sq_sqrt (show 0 ≤ 32*K by positivity)
  rw [inv_pow,hs]
  field_simp
  norm_num

end TamingCompatibility.MatrixEnergy

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartEnergyIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open Bundle ManifoldLocalization ManifoldVolume ManifoldHodge
open Set _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)

lemma cutoff_square_tsupport (p : A.centers) :
    tsupport (fun x => (A.partition p x)^2) ⊆ tsupport (A.partition p) := by
  simpa only [pow_two] using (tsupport_mul_subset_left (f := fun x => A.partition p x) (g := fun x => A.partition p x))

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
open scoped BigOperators
namespace TamingCompatibility.ManifoldLocalization
open _root_.MeasureTheory Set Function
open scoped Topology Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (k : ℕ)

abbrev CoordinateFiber (k : ℕ) := EuclideanSpace ℂ (Fin k → Fin (Module.finrank ℝ Space))

abbrev ChartL2 := PiLp 2 (fun _ : A.centers => Lp (CoordinateFiber k) 2
  (volume : Measure Space))

end TamingCompatibility.ManifoldLocalization

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open scoped RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

abbrev MetricTensor := V →L[ℝ] V →L[ℝ] ℝ
abbrev MetricDerivative := V →L[ℝ] MetricTensor (V := V)

def christoffelValue (G : MetricDerivative (V := V)) (u v : V) : V :=
  (InnerProductSpace.toDual ℝ V).symm
    ((1/2 : ℝ) • (G u v + G v u - (G.flip u).flip v))

lemma christoffelValue_inner (G : MetricDerivative (V := V)) (u v w : V) :
    ⟪christoffelValue G u v,w⟫ = (G u v w + G v u w - G w u v)/2 := by
  simp only [christoffelValue, InnerProductSpace.toDual_symm_apply,
    smul_apply, sub_apply,
    add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

lemma christoffelValue_add_left (G : MetricDerivative (V := V)) (x y z : V) :
    christoffelValue G (x+y) z = christoffelValue G x z + christoffelValue G y z := by
  apply ext_inner_right ℝ
  intro w
  simp only [christoffelValue_inner, inner_add_left, map_add,
    add_apply]
  ring

lemma christoffelValue_smul_left (G : MetricDerivative (V := V)) (c : ℝ) (x z : V) :
    christoffelValue G (c • x) z = c • christoffelValue G x z := by
  apply ext_inner_right ℝ
  intro w
  simp only [christoffelValue_inner, real_inner_smul_left, map_smul,
    smul_apply, smul_eq_mul]
  ring

lemma christoffelValue_add_right (G : MetricDerivative (V := V)) (x y z : V) :
    christoffelValue G x (y+z) = christoffelValue G x y + christoffelValue G x z := by
  apply ext_inner_right ℝ
  intro w
  simp only [christoffelValue_inner, inner_add_left, map_add,
    add_apply]
  ring

lemma christoffelValue_smul_right (G : MetricDerivative (V := V)) (c : ℝ) (x z : V) :
    christoffelValue G x (c • z) = c • christoffelValue G x z := by
  apply ext_inner_right ℝ
  intro w
  simp only [christoffelValue_inner, real_inner_smul_left, map_smul,
    smul_apply, smul_eq_mul]
  ring

def christoffel (G : MetricDerivative (V := V)) : V →L[ℝ] V →L[ℝ] V :=
  (((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] V) ≃ₗ[ℝ] (V →L[ℝ] V)).toLinearMap).comp
    (LinearMap.mk₂ ℝ (christoffelValue G) (christoffelValue_add_left G)
      (christoffelValue_smul_left G) (christoffelValue_add_right G)
      (christoffelValue_smul_right G))).toContinuousLinearMap

@[simp] lemma christoffel_apply (G : MetricDerivative (V := V)) (u v : V) :
    christoffel G u v = christoffelValue G u v := rfl

def coordinateJet (G : MetricDerivative (V := V)) (z : V) : V :=
  z - (1/2 : ℝ) • christoffel G z z

@[simp] lemma coordinateJet_zero (G : MetricDerivative (V := V)) :
    coordinateJet G 0 = 0 := by simp [coordinateJet]

def normalJacobian (G : MetricDerivative (V := V)) (z : V) : V →L[ℝ] V :=
  ContinuousLinearMap.id ℝ V - christoffel G z

@[simp] lemma normalJacobian_zero (G : MetricDerivative (V := V)) :
    normalJacobian G 0 = ContinuousLinearMap.id ℝ V := by simp [normalJacobian]

def pullbackMetric (g : V → MetricTensor (V := V)) (G : MetricDerivative (V := V))
    (z : V) : MetricTensor (V := V) :=
  (g (coordinateJet G z)).bilinearComp (normalJacobian G z) (normalJacobian G z)

@[simp] lemma pullbackMetric_zero (g : V → MetricTensor (V := V))
    (G : MetricDerivative (V := V)) : pullbackMetric g G 0 = g 0 := by
  ext v w
  simp [pullbackMetric, ContinuousLinearMap.bilinearComp_apply]

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_MetricCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity
open scoped ContDiff RealInnerProductSpace
abbrev V := EuclideanSpace ℝ (Fin 4)
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupMetricTensorV_r612de4_1 : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorV_r612de4_1 : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace
abbrev EMetric := (InnerProductSpace.toDual ℝ V).toContinuousLinearMap

def volumeDensity (M : MetricTensor (V := V)) : ℝ :=
  MetricDensity.density (MetricDensity.gram (stdOrthonormalBasis ℝ V).toBasis M)

lemma gram_euclidean : MetricDensity.gram (stdOrthonormalBasis ℝ V).toBasis EMetric = 1 := by
  ext i j
  simp [MetricDensity.gram, EMetric, Matrix.one_apply, OrthonormalBasis.inner_eq_ite]

def metricOperator : MetricTensor (V := V) →L[ℝ] (V →L[ℝ] V) :=
  (ContinuousLinearMap.compL ℝ V (V →L[ℝ] ℝ) V)
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearMap

lemma metricOperator_euclidean : metricOperator EMetric = ContinuousLinearMap.id ℝ V := by
  apply ContinuousLinearMap.ext
  intro u
  exact (InnerProductSpace.toDual ℝ V).symm_apply_apply u

def cometric (M : MetricTensor (V := V)) : V →L[ℝ] V :=
  ContinuousLinearMap.inverse (metricOperator M)

def principal (M : MetricTensor (V := V)) (i j : Fin 4) : ℝ :=
  ⟪cometric M (EuclideanSpace.basisFun (Fin 4) ℝ i),
    EuclideanSpace.basisFun (Fin 4) ℝ j⟫

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFrameTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.ScalarPair
open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv ContDiff
abbrev F := EuclideanSpace ℂ (Fin 2)

def inject (j : Fin 2) : ℝ →L[ℝ] F :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℂ) j ∘L Complex.ofRealCLM

end TamingCompatibility.ScalarPair

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.SchwartzCutoff
open Set Filter
open scoped ContDiff Topology SchwartzMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma smooth {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun x => φ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact hφ.contDiffAt.smul ((hf x (hs hx)).contDiffAt (hU.mem_nhds (hs hx)))
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy,zero_smul]

omit [NormedSpace ℝ E] in
lemma compact {f : E → F} {φ : E → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (fun x => φ x • f x) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _)

def schwartz [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) : 𝓢(E,F) :=
  (compact hc).toSchwartzMap (smooth hU hf hφ hs)

@[simp] lemma schwartz_apply [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (x : E) :
    schwartz hU hf hφ hc hs x = φ x • f x := rfl
end TamingCompatibility.SchwartzCutoff

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ChristoffelCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open scoped RealInnerProductSpace ContDiff Topology
open Set Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

local instance christoffelDualNormedAddCommGroup : NormedAddCommGroup (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance christoffelDualNormedSpace : NormedSpace ℝ (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance christoffelMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance christoffelMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := V)) :=
  ContinuousLinearMap.toNormedSpace
local instance christoffelMetricDerivativeNormedAddCommGroup :
    NormedAddCommGroup (MetricDerivative (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance christoffelMetricDerivativeNormedSpace :
    NormedSpace ℝ (MetricDerivative (V := V)) := ContinuousLinearMap.toNormedSpace

local instance christoffelEndomorphismNormedAddCommGroup : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance christoffelEndomorphismNormedSpace : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace
local instance christoffelBilinearNormedAddCommGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance christoffelBilinearNormedSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

def christoffelCLM : MetricDerivative (V := V) →L[ℝ] (V →L[ℝ] V →L[ℝ] V) :=
  LinearMap.toContinuousLinearMap
    { toFun := christoffel
      map_add' := by
        intro G H
        ext u v
        apply ext_inner_right ℝ
        intro w
        simp only [christoffel_apply, christoffelValue_inner, add_apply,
          inner_add_left]
        ring
      map_smul' := by
        intro c G
        ext u v
        apply ext_inner_right ℝ
        intro w
        simp only [christoffel_apply, christoffelValue_inner, smul_apply,
          real_inner_smul_left, smul_eq_mul, RingHom.id_apply]
        ring }

@[simp] lemma christoffelCLM_apply (G : MetricDerivative (V := V)) :
    christoffelCLM G = christoffel G := rfl

lemma christoffel_contDiff : ContDiff ℝ ∞ (christoffel (V := V)) :=
  by
    convert! (christoffelCLM (V := V)).contDiff using 1
    all_goals try with_reducible_and_instances rfl

def jointJet (G : V → MetricDerivative (V := V)) (pz : V × V) : V :=
  coordinateJet (G pz.1) pz.2

def centeredMap (B : V → V →L[ℝ] V) (G : V → MetricDerivative (V := V))
    (pz : V × V) : V × V :=
  (pz.1, pz.1 + B pz.1 (jointJet G pz))

def centeredDerivative (B : V ≃L[ℝ] V) : (V × V) ≃L[ℝ] (V × V) :=
  (ContinuousLinearEquiv.refl ℝ V).skewProd B (ContinuousLinearMap.id ℝ V)

end TamingCompatibility.GeometricHilbert.NormalJets


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricPairingCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.MetricForms
open MetricHodge
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
local instance instFiniteDimensionalRealContinuousMultilinearMapFin_solutions {k : ℕ} : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective
local instance instFiniteDimensionalRealContinuousAlternatingMapFin_solutions {k : ℕ} : FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective ContinuousAlternatingMap.toContinuousMultilinearMapLinear
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective

end TamingCompatibility.MetricForms

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeMatrixEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap RealInnerProductSpace
namespace TamingCompatibility.HodgeMatrixEnergy
abbrev W := EuclideanSpace ℝ (Fin 6)
end TamingCompatibility.HodgeMatrixEnergy

end
end

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.HodgeNormalSymbol
abbrev W := EuclideanSpace ℝ (Fin 6)
abbrev Q := EuclideanSpace ℝ (Fin 8)

end TamingCompatibility.HodgeNormalSymbol

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets
open Set Metric
open scoped ContDiff
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def dpos (F : P × V → W) (q : P × V) : V →L[ℝ] W :=
  (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ P V)

omit [FiniteDimensional ℝ V] in
lemma dpos_contDiff (F : P × V → W) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (dpos F) := by
  exact (hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiff_const

end TamingCompatibility.GeometricHilbert.UniformJets

end

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SymbolMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.OrthogonalJets
open scoped RealInnerProductSpace ContDiff
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

abbrev End := W →L[ℝ] W

def gauge (A : V →L[ℝ] End (W := W)) (z : V) : End (W := W) := NormedSpace.exp (A z)

end TamingCompatibility.GeometricHilbert.OrthogonalJets


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_FirstJetGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FirstJetGauge
open scoped ContDiff RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
abbrev End := W →L[ℝ] W

def adjointCLM : End (W := W) →L[ℝ] End (W := W) :=
  ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] lemma adjointCLM_apply (A : End (W := W)) : adjointCLM A = A.adjoint := rfl

def squareFirst (P' : ι → ι → End (W := W)) (a : ι → W →L[ℝ] Q)
    (b : W →L[ℝ] Q) (ρ : ℝ) (j : ι) : End (W := W) :=
  -ρ⁻¹ • (∑ i, P' i j) + b.adjoint ∘L a j - (a j).adjoint ∘L b

def halfJet (q : ι → V →L[ℝ] ℝ) (b : ι → End (W := W)) : V →L[ℝ] End (W := W) :=
  ∑ i, (q i).smulRight ((1/2:ℝ) • b i)

def transformedFirst (a : ι → ι → V → ℝ) (b : ι → V → End (W := W))
    (U : V → End (W := W)) (e : ι → V) (j : ι) (z : V) : End (W := W) :=
  (U z).adjoint ∘L ((b j z) ∘L U z -
    ∑ i, (a i j z+a j i z) • (fderiv ℝ U z (e i)))

end TamingCompatibility.GeometricHilbert.FirstJetGauge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_SummableCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter _root_.MeasureTheory Finset
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff
variable {X : Type*}

def exceptional (c : ℕ → X → ℝ) : Set X := {x | ¬ Summable (fun n => c n x)}

end TamingCompatibility.SummableCutoff

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PositiveFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility

open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

abbrev MetricUnit (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) :=
  {p : TangentBundle Model X // g.inner p.proj p.2 p.2 = 1}

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_GeometricSeparatingProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility
open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

local instance unitMeasurable (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) : MeasurableSpace (MetricUnit g) := borel _
local instance unitBorel (g : ContMDiffRiemannianMetric Model ∞ Space
    (TangentSpace Model : X → Type)) : BorelSpace (MetricUnit g) := ⟨rfl⟩

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_FlatHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open _root_.MeasureTheory Set
open scoped RealInnerProductSpace ContDiff
abbrev V := EuclideanSpace ℝ (Fin 4)

def heat (t : ℝ) (z : V) : ℝ :=
  (4*Real.pi*t)⁻¹^2 * Real.exp (-‖z‖^2/(4*t))

def laplacian (f : V → ℝ) (x : V) : ℝ :=
  ∑ i : Fin 4, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.basisFun (Fin 4) ℝ i)) x
    (EuclideanSpace.basisFun (Fin 4) ℝ i)

end TamingCompatibility.GeometricHilbert.FlatHeat

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_End
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open scoped ContDiff RealInnerProductSpace
open FlatHeat (V heat)
open Filter Set
open scoped Topology
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
abbrev End := W →L[ℝ] W
abbrev Principal := Fin 4 → Fin 4 → ℝ
abbrev First := Fin 4 → End (W := W)
def euclideanPrincipal : Principal := fun i j => if i = j then 1 else 0

def residual (a : V → Principal) (b : V → First (W := W))
    (c : V → End (W := W)) (t : ℝ) (z : V) : End (W := W) :=
  (∑ i, ∑ j, ((euclideanPrincipal i j - a z i j) *
    fderiv ℝ (fun y => fderiv ℝ (heat t) y (EuclideanSpace.basisFun (Fin 4) ℝ j)) z
      (EuclideanSpace.basisFun (Fin 4) ℝ i)) • ContinuousLinearMap.id ℝ W) +
  (∑ i, (fderiv ℝ (heat t) z (EuclideanSpace.basisFun (Fin 4) ℝ i)) • b z i) +
    heat t z • c z

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_OperatorCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open scoped ContDiff
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def principalMatrix (a : ι → V → W →L[ℝ] Q) (ρ : V → ℝ) (i j : ι) (x : V) : W →L[ℝ] W :=
  (ρ x • a i x).adjoint ∘L a j x

def lowerMatrix (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (i : ι) (x : V) : W →L[ℝ] W := (ρ x • a i x).adjoint ∘L b x

def firstMatrix (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (j : ι) (x : V) : W →L[ℝ] W :=
  -(ρ x)⁻¹ • (∑ i, fderiv ℝ (principalMatrix a ρ i j) x (e i)) +
    (b x).adjoint ∘L a j x - (a j x).adjoint ∘L b x

def zeroMatrix (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (x : V) : W →L[ℝ] W :=
  -(ρ x)⁻¹ • (∑ i, fderiv ℝ (lowerMatrix a b ρ i) x (e i)) + (b x).adjoint ∘L b x

def gaugeFirst (e : ι → V) (a : ι → ι → V → ℝ) (b : ι → V → W →L[ℝ] W)
    (U : V → W →L[ℝ] W) (j : ι) (x : V) : W →L[ℝ] W :=
  (U x).adjoint ∘L (b j x ∘L U x - ∑ i, (a i j x + a j i x) • fderiv ℝ U x (e i))

def gaugeZero (e : ι → V) (a : ι → ι → V → ℝ) (b : ι → V → W →L[ℝ] W)
    (c U : V → W →L[ℝ] W) (x : V) : W →L[ℝ] W :=
  (U x).adjoint ∘L (c x ∘L U x + (∑ i, b i x ∘L fderiv ℝ U x (e i)) -
    ∑ i, ∑ j, a i j x • fderiv ℝ (fun z => fderiv ℝ U z (e j)) x (e i))

end TamingCompatibility.GeometricHilbert.OperatorCalculus


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_WeightedPrincipal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FirstJetGauge
open Filter
open scoped ContDiff Topology
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def weightedPrincipal (a : ι → V → W →L[ℝ] Q) (ρ : V → ℝ) (i j : ι) (x : V) :
    End (W := W) := (ρ x • a i x).adjoint ∘L a j x

variable [Fintype ι]

def actualSquareFirst (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (j : ι) (x : V) : End (W := W) :=
  squareFirst (fun i j => fderiv ℝ (weightedPrincipal a ρ i j) x (e i))
    (fun i => a i x) (b x) (ρ x) j

end TamingCompatibility.GeometricHilbert.FirstJetGauge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_PlaneNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def first (a : V) : V := ‖a‖⁻¹ • a

end TamingCompatibility.PlaneVariation

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCutoffSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open scoped ContDiff
variable {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def cutoffFirst (e : ι → V) (a : ι → ι → V → ℝ)
    (b : ι → V → W →L[ℝ] W) (χ : V → ℝ) (j : ι) (z : V) : W →L[ℝ] W :=
  χ z • b j z - (∑ i, (a i j z+a j i z)*fderiv ℝ χ z (e i)) • ContinuousLinearMap.id ℝ W

def cutoffZero (e : ι → V) (a : ι → ι → V → ℝ)
    (b : ι → V → W →L[ℝ] W) (c : V → W →L[ℝ] W) (χ : V → ℝ) (z : V) : W →L[ℝ] W :=
  χ z • c z - (∑ i, ∑ j, a i j z * fderiv ℝ (fun y => fderiv ℝ χ y (e j)) z (e i)) •
    ContinuousLinearMap.id ℝ W + ∑ i, fderiv ℝ χ z (e i) • b i z

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open OperatorCalculus FlatHeat Filter Set
open scoped Topology ContDiff
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def cutoffPrincipal (a : Fin 4 → Fin 4 → V → ℝ) (χ : V → ℝ)
    (i j : Fin 4) (z : V) : ℝ :=
  euclideanPrincipal i j + χ z * (a i j z - euclideanPrincipal i j)

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCutoffFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.CutoffFamilies
open OperatorCalculus NormalHeatResidual UniformJets FlatHeat Filter Set Metric
open scoped Topology ContDiff
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def principal (a : Fin 4 → Fin 4 → P × V → ℝ) (χ : V → ℝ) (x : P × V) (i j : Fin 4) : ℝ :=
  cutoffPrincipal (fun i j z => a i j (x.1,z)) χ i j x.2

def first (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (χ : V → ℝ) (x : P × V) (j : Fin 4) : W →L[ℝ] W :=
  cutoffFirst (EuclideanSpace.basisFun (Fin 4) ℝ) (fun i j z => a i j (x.1,z))
    (fun j z => b j (x.1,z)) χ j x.2

def zero (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (χ : V → ℝ) (x : P × V) : W →L[ℝ] W :=
  cutoffZero (EuclideanSpace.basisFun (Fin 4) ℝ) (fun i j z => a i j (x.1,z))
    (fun j z => b j (x.1,z)) (fun z => c (x.1,z)) χ x.2

end TamingCompatibility.GeometricHilbert.CutoffFamilies

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeVolterraKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open _root_.MeasureTheory Set
variable {X B : Type*} [MeasurableSpace X]
  [NormedRing B] [NormedAlgebra ℝ B]
variable (μ : Measure X) [SFinite μ]

abbrev Kernel := ℝ → X → X → B

end TamingCompatibility.GeometricHilbert.VolterraKernel

end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelSeriesCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelSeries
open _root_.MeasureTheory Set Filter VolterraKernel
open scoped Topology
variable {X B : Type*} [MeasurableSpace X]
  [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
variable (μ : Measure X) [SFinite μ]

variable [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]

def clip (T : ℝ) (K : Kernel (X := X) (B := B)) : Kernel (X := X) (B := B) :=
  fun t x y => if t ∈ Ioc 0 T then K t x y else 0

end TamingCompatibility.GeometricHilbert.KernelSeries

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeManifoldKernelExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldKernelExtension
open Set Filter
open scoped Manifold Topology
variable {E X G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X]
  [NormedAddCommGroup G]
attribute [local instance] Classical.propDecidable
local notation "I" => 𝓘(ℝ,E)

def push (p : X) (f : E × E → G) (x : X × X) : G :=
  if x ∈ (extChartAt I p).source ×ˢ (extChartAt I p).source then
    f (extChartAt I p x.1, extChartAt I p x.2) else 0

end TamingCompatibility.ManifoldKernelExtension

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open Set Filter
open scoped ContDiff Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def inverseRegularDomain (C : OpenPartialHomeomorph V V) : Set V :=
  C.target ∩ (fun y => fderiv ℝ (C : V → V) (C.symm y)) ⁻¹'
    {L : V →L[ℝ] V | L.IsInvertible}

end TamingCompatibility.GeometricHilbert.NormalJets

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelExtension
open Set Filter
open scoped Topology ContDiff
variable {E F W : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup W]
attribute [local instance] Classical.propDecidable

def push (C : OpenPartialHomeomorph E F) (f : E → W) (y : F) : W :=
  if y ∈ C.target then f (C.symm y) else 0

end TamingCompatibility.GeometricHilbert.KernelExtension

end
end

end

end OAI
end


