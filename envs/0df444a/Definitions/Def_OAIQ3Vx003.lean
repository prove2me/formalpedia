-- Prove2me | Definitions.Def_OAIQ3Vx003
-- name    : OAIQ3Vx003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:30:47.070448+00:00
-- url     : https://prove2.me/theorems/3da7ffb4-c23f-424d-8099-b6196ca75ca1
-- title:
--   Definitions bundle OAIQ3Vx003 of the split of OpenAI, Strongly rational unitary vertex operator algebras and conformal nets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinimalVertex.main`, carved from OpenAI's openai/math development (OpenAI, *Strongly rational unitary vertex operator algebras and conformal nets*, OpenAI Math Release, September 25, 2026, result family 280, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 185 declarations of OpenAI's Lean: 31 definitions, 2 inductive types or structures, 1 instance and 151 theorems. The definitions and types are `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.LocalState`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.PrimaryTestField`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.PrimaryTestField.field`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.conformalHamiltonian`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.normalizedField`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.primaryAlgebra`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.primaryGraphData`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.rotation`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.smoothEnergyPower`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.smoothSmear`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.stateCommutant`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.stressPropagator`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.stressPropagatorSmooth`, `OAI.StronglyRationalVOA.HilbertScale.rotation`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.Field.smoothCircle`, `OAI.StronglyRationalVOA.SmoothCircleFamily`, `OAI.StronglyRationalVOA.SmoothCircleFunction.IsReal`, `OAI.StronglyRationalVOA.SmoothCircleFunction.add`, `OAI.StronglyRationalVOA.SmoothCircleFunction.constant`, `OAI.StronglyRationalVOA.SmoothCircleFunction.differentiated`, `OAI.StronglyRationalVOA.SmoothCircleFunction.mul`, `OAI.StronglyRationalVOA.SmoothCircleFunction.ofRealPeriodic`, `OAI.StronglyRationalVOA.SmoothCircleFunction.power`, `OAI.StronglyRationalVOA.SmoothCircleFunction.quadraticFamily`, `OAI.StronglyRationalVOA.SmoothCircleFunction.scale`, `OAI.StronglyRationalVOA.SmoothCircleFunction.toContinuousMap`, `OAI.StronglyRationalVOA.SmoothCircleFunction.translate`, `OAI.StronglyRationalVOA.SymmetricOperator.approximatingFlow`, `OAI.StronglyRationalVOA.SymmetricOperator.conjugation`, `OAI.StronglyRationalVOA.SymmetricOperator.conjugationIntegral`, `OAI.StronglyRationalVOA.SymmetricOperator.flow`, `OAI.StronglyRationalVOA.SymmetricOperator.smoothConjugate`, `OAI.StronglyRationalVOA.TimeOrdered.evolution`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/VertexAlgebra, in whole or in part: `VertexAlgebra_ApproximatingFlowDerivative`, `VertexAlgebra_BoundedFlows`, `VertexAlgebra_BoundedMultiplierSingle`, `VertexAlgebra_CoefficientSummableBound`, `VertexAlgebra_EnergyCutoffNorm`, `VertexAlgebra_GraphCommutants`, `VertexAlgebra_GraphEquiv`, `VertexAlgebra_GraphInvariantOf`, `VertexAlgebra_HighFieldGraph`, `VertexAlgebra_HilbertCore`, `VertexAlgebra_HilbertRegularization`, `VertexAlgebra_InverseEnergySelf`, `VertexAlgebra_LocalNormalMap`, `VertexAlgebra_Locality`, `VertexAlgebra_ObservableScalars`, `VertexAlgebra_RegularizerFactorAdd`, `VertexAlgebra_SmoothConjugateInner`, `VertexAlgebra_SmoothConjugatePrimary`, `VertexAlgebra_SmoothEnergyPower`, `VertexAlgebra_StressCutoffNormalized`, `VertexAlgebra_StressCutoffNormalized2`, `VertexAlgebra_StressEvolution`, `VertexAlgebra_StressPropagatorDerivative`, `VertexAlgebra_StressSmoothness`, `VertexAlgebra_SummableNormSobolev`, `VertexAlgebra_SymmetricWeakCommute`, `VertexAlgebra_TimeAverageGraph`.
--
--   **Imports.** It imports the published bundle `Def_VertexAlgebraNet`; the bundles `OAIQ3Vx000` and `OAIQ3Vx001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ3Vx006`, `OAIQ3Vx007` and `OAIQ3Vx008`.
-- source:
--   OpenAI, Strongly rational unitary vertex operator algebras and conformal nets, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 280; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/VertexAlgebra at commit adc7f12

import Mathlib
import Definitions.Def_VertexAlgebraNet
import Definitions.Def_OAIQ3Vx000
import Definitions.Def_OAIQ3Vx001

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_HilbertCore
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
open Filter

open scoped ContDiff



namespace CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)



theorem closedSmoothField_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction) :
    ((U.closedSmoothField hc a d f).graph : Set (Completion V × Completion V)) =
      closure ((U.smoothSmearedField hc a d f).graph : Set (Completion V × Completion V)) := by
  symm
  exact congrArg (fun S : Submodule ℂ (Completion V × Completion V) => (S : Set (Completion V × Completion V)))
    (U.smoothSmearedField_closable hc ha f).graph_closure_eq_closure_graph

end CFTTypeVOA.UnitaryStructure

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GraphCommutants
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
open Filter
open scoped ContDiff

open scoped ENNReal
namespace HilbertScale
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable [DecidableEq ι]

theorem domain_dense (w : ι → ℂ) : Dense (domain (G := G) w : Set (Space G)) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
  apply Filter.Eventually.of_forall
  intro s
  exact Submodule.sum_mem _ (fun i _ => single_mem_domain w i (x i))

variable [∀ i, CompleteSpace (G i)]

omit [DecidableEq ι] [∀ i, CompleteSpace (G i)] in
 

theorem diagonal_formalAdjoint (w : ι → ℂ) :
    (diagonal (G := G) w).IsFormalAdjoint (diagonal (fun i => star (w i))) := by
  intro x y
  rw [← (lp.hasSum_inner (diagonal w x) (y : Space G)).tsum_eq,
    ← (lp.hasSum_inner (x : Space G) (diagonal (fun i => star (w i)) y)).tsum_eq]
  apply tsum_congr
  intro i
  simp only [diagonal_apply, inner_smul_left, inner_smul_right, starRingEnd_apply]

theorem adjoint_coordinate (w : ι → ℂ) (y : (diagonal (G := G) w).adjoint.domain)
    (i : ι) : (diagonal (G := G) w).adjoint y i = star (w i) • (y : Space G) i := by
  apply ext_inner_right ℂ
  intro v
  have h : inner ℂ ((diagonal (G := G) w).adjoint y) (lp.single 2 i v) =
      inner ℂ (y : Space G) (lp.single 2 i (w i • v)) := by
    have hh := (LinearPMap.adjoint_isFormalAdjoint (domain_dense (G := G) w)) y
      ⟨lp.single 2 i v, single_mem_domain (G := G) w i v⟩
    rw [diagonal_single] at hh
    exact hh
  rw [lp.inner_single_right, lp.inner_single_right] at h
  simpa only [inner_smul_right, inner_smul_left, star_star, starRingEnd_apply] using h

 

theorem adjoint_le_diagonal (w : ι → ℂ) :
    (diagonal (G := G) w).adjoint ≤ diagonal (G := G) (fun i => star (w i)) := by
  apply LinearPMap.le_graph_iff.mp
  intro z hz
  obtain ⟨y,hy,hTy⟩ := ((diagonal (G := G) w).adjoint).mem_graph_iff.mp hz
  apply (mem_graph_iff (G := G) _ _ _).mpr
  intro i
  have h1 : (y : Space G) = z.1 := hy
  have h2 : (diagonal (G := G) w).adjoint y = z.2 := hTy
  have hi := adjoint_coordinate w y i
  rw [h1, h2] at hi
  exact hi

theorem adjoint_diagonal (w : ι → ℂ) :
    (diagonal (G := G) w).adjoint = diagonal (fun i => star (w i)) := by
  apply le_antisymm (adjoint_le_diagonal w)
  have hf : (diagonal (G := G) w).IsFormalAdjoint (diagonal (fun i => star (w i))) :=
    diagonal_formalAdjoint w
  exact hf.le_adjoint (domain_dense w)



theorem real_diagonal_selfAdjoint (w : ι → ℝ) :
    (diagonal (G := G) (fun i => (w i : ℂ))).adjoint = diagonal (fun i => (w i : ℂ)) := by
  rw [adjoint_diagonal]
  simp only [Complex.star_def, Complex.conj_ofReal]

end HilbertScale

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GraphEquiv
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
open Filter
open scoped ContDiff
open scoped ENNReal
namespace OperatorTransport
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem dense (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K}
    (hT : Dense (T.domain : Set K)) : Dense ((transport E T).domain : Set H) :=
  hT.preimage E.toHomeomorph.isOpenMap

variable [CompleteSpace H] [CompleteSpace K]

theorem adjoint (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K}
    (hT : Dense (T.domain : Set K)) :
    (transport E T).adjoint = transport E T.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (dense E hT)]
  ext z
  rw [mem_graph_iff,LinearPMap.adjoint_graph_eq_graph_adjoint hT]
  simp only [Submodule.mem_adjoint_iff]
  constructor
  · intro hz a b hab
    have hh := hz (E.symm a) (E.symm b) ((mem_graph_iff E T _ _).mpr (by simpa using hab))
    rw [← E.inner_map_map (E.symm b) z.1, ← E.inner_map_map (E.symm a) z.2,
      E.apply_symm_apply,E.apply_symm_apply] at hh
    exact hh
  · intro hz a b hab
    have hh := hz (E a) (E b) ((mem_graph_iff E T _ _).mp hab)
    simpa only [E.inner_map_map] using hh

theorem selfAdjoint (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (transport E T) := by
  rw [LinearPMap.isSelfAdjoint_def,adjoint E hT.dense_domain,
    (LinearPMap.isSelfAdjoint_def.mp hT)]

end OperatorTransport

namespace CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)

theorem energyOperator_selfAdjoint (w : ℕ → ℝ) : IsSelfAdjoint (U.energyOperator w) := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  exact OperatorTransport.selfAdjoint _ (HilbertScale.real_diagonal_selfAdjoint w)



def conformalHamiltonian : Completion V →ₗ.[ℂ] Completion V :=
  U.energyOperator (fun d => d)


theorem core_le_smoothEnergySpace : HilbertCore.space V ≤ U.smoothEnergySpace := by
  apply le_iInf
  intro k
  exact (U.energyOperator_hasCore _).le_domain

end CFTTypeVOA.UnitaryStructure

end StronglyRationalVOA

open scoped Topology
open Filter

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_BoundedMultiplierSingle
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
universe u
open scoped Topology
open Filter
namespace StronglyRationalVOA

namespace HilbertScale
open scoped ENNReal
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]
theorem boundedMultiplier_single (w : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) (i : ι) (x : G i) :
    boundedMultiplier w hC hw (lp.single 2 i x) = w i • lp.single 2 i x := by
  ext j
  simp only [boundedMultiplier_apply,lp.coeFn_smul,Pi.smul_apply]
  by_cases hj : j = i
  · subst j; simp
  · simp [lp.single_apply,hj]

end HilbertScale

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_HilbertRegularization
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u

noncomputable section
open scoped Topology
open Filter

open scoped Topology
open Filter

namespace StronglyRationalVOA.SmoothCircleFunction

def IsReal (f : SmoothCircleFunction) : Prop := ∀ t, star (f t) = f t

end StronglyRationalVOA.SmoothCircleFunction

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SummableNormSobolev
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u v

noncomputable section
open scoped Topology
open Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace Filter
open scoped Topology
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)



theorem smearedMap_energyGraph {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f)
    (r : ℕ) (v : V) :
    (A.smearedMap a d he f hf v,
      ∑' n : ℤ, f n • ((A.energyShift^r) (A.physicalMode a d n v) : Completion V)) ∈
        (U.energyPower r).graph := by
  have hs := (A.summable_norm_physicalSmear he d hf v).of_norm.hasSum.prodMk
    (U.summable_norm_sobolevSmear ha he hf r v).of_norm.hasSum
  apply (U.energyOperator_closed _).mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro n _
  have hbase : ((A.physicalMode a d n v : Completion V),
      ((A.energyShift^r) (A.physicalMode a d n v) : Completion V)) ∈ (U.energyPower r).graph :=
    (U.energyPower r).mem_graph_iff.mpr
      ⟨⟨_,U.coe_mem_energyOperator _ _⟩,rfl,U.energyPower_coe _ _⟩
  exact (U.energyPower r).graph.smul_mem (f n) hbase


include U in
theorem smearedMap_sobolev_bound {a : V} {d k p : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) (v : V) :
    ‖∑' n : ℤ, f n • ((A.energyShift^r) (A.physicalMode a d n v) : Completion V)‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^(p+r))*C)*‖(A.energyShift^(k+r)) v‖ := by
  apply (norm_tsum_le_tsum_norm (U.summable_norm_sobolevSmear ha he hf r v)).trans
  calc
    _ ≤ ∑' n : ℤ, (‖f n‖*(1+|(n : ℝ)|)^(p+r))*(C*‖(A.energyShift^(k+r)) v‖) := by
      apply Summable.tsum_le_tsum _ (U.summable_norm_sobolevSmear ha he hf r v)
        ((hf (p+r)).mul_right _)
      intro n
      simp only [norm_smul,Completion.norm_coe]
      calc
        _ ≤ ‖f n‖*(C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(k+r)) v‖) :=
          mul_le_mul_of_nonneg_left (U.physicalMode_sobolev_bound ha hC hb r n v) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [tsum_mul_right]; ring

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.HilbertScale
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

 

theorem energyExtension_graph (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M N : finiteCore (G := G) →ₗ[ℂ] Space G) {C D : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hN : ∀ x, ‖N x‖ ≤ D * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (T : Space G →ₗ.[ℂ] Space G) (hc : T.IsClosed)
    (ht : ∀ x, (M x,N x) ∈ T.graph) (x : Space G) :
    (energyExtension h M x,energyExtension h N x) ∈ T.graph := by
  have hclosed : IsClosed {z : Space G |
      (energyExtension h M z,energyExtension h N z) ∈ T.graph} :=
    hc.preimage ((energyExtension h M).continuous.prodMk (energyExtension h N).continuous)
  have hin : (finiteCore (G := G) : Set (Space G)) ⊆
      {z | (energyExtension h M z,energyExtension h N z) ∈ T.graph} := by
    intro z hz
    change (energyExtension h M z,energyExtension h N z) ∈ T.graph
    rw [energyExtension_core h hh M hM ⟨z,hz⟩,energyExtension_core h hh N hN ⟨z,hz⟩]
    exact ht _
  exact closure_minimal hin hclosed (finiteCore_dense x)

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

include U in
theorem energyPower_domain_le_coreClosure (k : ℕ) (T : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hT : ∀ v, ‖T v‖ ≤ C*‖(A.energyShift^k) v‖)
    (hc : (HilbertCore.operator T).IsClosable) :
    (U.energyPower k).domain ≤ (HilbertCore.operator T).closure.domain := by
  intro x hx
  obtain ⟨y,hy,_⟩ := (HilbertCore.operator T).closure.mem_graph_iff.mp
    (U.sobolevExtension_energyGraph k T hT hc ⟨x,hx⟩)
  change (y : Completion V) = x at hy
  rw [← hy]
  exact y.property

 
attribute [local instance] OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.instFiniteDimensionalComplexSubtypeMemSubmoduleGrade
theorem sobolevExtension_graph (k : ℕ) (M N : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^k) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^k) v‖)
    (T : Completion V →ₗ.[ℂ] Completion V) (hc : T.IsClosed)
    (ht : ∀ v, (M v,N v) ∈ T.graph) (x : Completion V) :
    (U.sobolevExtension k M x,U.sobolevExtension k N x) ∈ T.graph := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  have hh (d : ℕ) : 1 ≤ (1+(d : ℝ))^k :=
    one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  have ht' : ∀ v, (U.spectralCoreMap M v,U.spectralCoreMap N v) ∈
      (OperatorTransport.transport U.energyCoordinates.symm T).graph := by
    intro v
    obtain ⟨a,rfl⟩ := U.coreEnergyCoordinates.surjective v
    rw [OperatorTransport.mem_graph_iff,U.spectralCoreMap_apply,U.spectralCoreMap_apply,
      U.energyCoordinates.symm_apply_apply,U.energyCoordinates.symm_apply_apply]
    exact ht a
  have h := HilbertScale.energyExtension_graph _ hh _ _
    (U.spectralCoreMap_bound k M hM) (U.spectralCoreMap_bound k N hN)
    _ (OperatorTransport.closed U.energyCoordinates.symm hc) ht' (U.energyCoordinates x)
  exact (OperatorTransport.mem_graph_iff U.energyCoordinates.symm T _ _).mp h

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)



theorem smoothEnergySpace_le_closedSmearedDomain (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    U.smoothEnergySpace ≤ (U.closedSmearedOperator hc a d f hf).domain := by
  obtain ⟨C,_,p,k,hb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  apply le_trans (iInf_le (fun k => (U.energyPower k).domain) k)
  exact U.energyPower_domain_le_coreClosure k _
    (A.smearedMap_bound (U.polynomialEnergyBounds hc a) hf hb)
    (U.smearedCore_closable hc ha hf)

 

theorem closedSmearedOperator_preserves_smoothEnergySpace (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f)
    (x : (U.closedSmearedOperator hc a d f hf).domain) (hx : x.val ∈ U.smoothEnergySpace) :
    U.closedSmearedOperator hc a d f hf x ∈ U.smoothEnergySpace := by
  obtain ⟨C,hC,p,k,hb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf
  let K : ℝ := (∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^p)*C
  have hK : 0 ≤ K := mul_nonneg
    (tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _)) hC.le
  rw [smoothEnergySpace,Submodule.mem_iInf]
  intro r
  let N := U.weightedSmearedMap ha (U.polynomialEnergyBounds hc a) hf r
  have hm : ∀ v, ‖M v‖ ≤ K*‖(A.energyShift^(k+r)) v‖ := by
    intro v
    exact (A.smearedMap_bound (U.polynomialEnergyBounds hc a) hf hb v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ k+r) v) hK)
  have hn : ∀ v, ‖N v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^(p+r))*C)*‖(A.energyShift^(k+r)) v‖ :=
    U.smearedMap_sobolev_bound ha (U.polynomialEnergyBounds hc a) hC.le hb hf r
  have hx' : x.val ∈ (U.energyPower (k+r)).domain :=
    (iInf_le (fun k => (U.energyPower k).domain) (k+r)) hx
  let y := U.energyPower (k+r) ⟨x.val,hx'⟩
  have hvalue : U.closedSmearedOperator hc a d f hf x = U.sobolevExtension (k+r) M y := by
    have h := U.sobolevExtension_energyGraph (k+r) M hm
      (U.smearedCore_closable hc ha hf) ⟨x.val,hx'⟩
    obtain ⟨z,hz,hz'⟩ := (U.closedSmearedOperator hc a d f hf).mem_graph_iff.mp h
    have hzx : z = x := Subtype.ext hz
    rwa [hzx] at hz'
  have hg := U.sobolevExtension_graph (k+r) M N hm hn (U.energyPower r)
    (U.energyOperator_closed _) (U.smearedMap_energyGraph ha (U.polynomialEnergyBounds hc a) hf r) y
  obtain ⟨z,hz,_⟩ := (U.energyPower r).mem_graph_iff.mp hg
  dsimp only [Prod.fst] at hz
  rw [hvalue,← hz]
  exact z.property

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_InverseEnergySelf
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u

noncomputable section
open scoped Topology
open Filter

namespace StronglyRationalVOA.SmoothCircleFunction
open MeasureTheory
local instance inverseEnergySelfContinuousPeriodPos : Fact (0 < 2*Real.pi) := ⟨period_pos⟩

 
def toContinuousMap (f : SmoothCircleFunction) : C(AddCircle (2*Real.pi),ℂ) :=
  ⟨f.periodic.lift, continuous_coinduced_dom.mpr f.smooth.continuous⟩

@[simp] theorem toContinuousMap_coe (f : SmoothCircleFunction) (t : ℝ) :
    f.toContinuousMap (t : AddCircle (2*Real.pi)) = f t := rfl

@[simp] theorem fourierCoeff_toContinuousMap (f : SmoothCircleFunction) (n : ℤ) :
    fourierCoeff f.toContinuousMap n = f.coefficient n := by
  have hl : (f.toContinuousMap : AddCircle (2*Real.pi) → ℂ) =
      AddCircle.liftIoc (2*Real.pi) 0 f := by
    funext t
    have ht : ((AddCircle.equivIoc (2*Real.pi) 0 t : ℝ) : AddCircle (2*Real.pi)) = t :=
      AddCircle.coe_equivIoc
    rw [← ht,toContinuousMap_coe,AddCircle.liftIoc_coe_apply (AddCircle.equivIoc _ _ t).property]
  rw [hl,fourierCoeff_liftIoc_eq]
  simp only [coefficient,zero_add]

end StronglyRationalVOA.SmoothCircleFunction

namespace StronglyRationalVOA.SmoothCircleFunction


def mul (f g : SmoothCircleFunction) : SmoothCircleFunction :=
  ⟨fun t => f t*g t, fun t => by dsimp only; rw [f.periodic,g.periodic], f.smooth.mul g.smooth⟩

@[simp] theorem mul_apply (f g : SmoothCircleFunction) (t : ℝ) : f.mul g t = f t*g t := rfl

@[simp] theorem toContinuousMap_mul (f g : SmoothCircleFunction) :
    (f.mul g).toContinuousMap = f.toContinuousMap*g.toContinuousMap := by
  ext t
  induction t using QuotientAddGroup.induction_on
  rfl


end StronglyRationalVOA.SmoothCircleFunction

namespace StronglyRationalVOA.SmoothCircleFunction
open scoped ContDiff

 
def differentiated (f : SmoothCircleFunction) (k : ℕ) : SmoothCircleFunction where
  toFun := iteratedDeriv k f
  periodic := f.periodic_iteratedDeriv k
  smooth := by
    rw [iteratedDeriv_eq_iterate]
    exact f.smooth.iterate_deriv k

@[simp] theorem differentiated_apply (f : SmoothCircleFunction) (k : ℕ) (t : ℝ) :
    f.differentiated k t = iteratedDeriv k f t := rfl



end StronglyRationalVOA.SmoothCircleFunction

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_BoundedFlows
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter

open scoped Topology
open Filter

open scoped Topology

open scoped Topology
open Filter
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def approximatingFlow (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (n : ℕ) (t : ℝ) : H →L[ℂ] H :=
  BoundedFlow.flow (Complex.I • boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n)) t

lemma approximatingFlow_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (n : ℕ) (t : ℝ) (x : H) : ‖approximatingFlow T hs n t x‖ = ‖x‖ := by
  apply BoundedFlow.flow_norm
  exact IsSelfAdjoint.smul_mem_skewAdjoint (by simp [skewAdjoint.mem_iff]) (boundedGenerator_selfAdjoint T hs _ _)

lemma approximatingFlow_opNorm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (n : ℕ) (t : ℝ) : ‖approximatingFlow T hs n t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [approximatingFlow_norm,one_mul]

lemma approximatingFlow_difference (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (m n : ℕ) (t : ℝ) (x : H) :
    ‖approximatingFlow T hs m t x-approximatingFlow T hs n t x‖ ≤
      |t| * ‖boundedGenerator T hs (sampleRadius m) (sampleRadius_ge m) x-
        boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x‖ := by
  have hm := boundedGenerator_selfAdjoint T hs (sampleRadius m) (sampleRadius_ge m)
  have hn := boundedGenerator_selfAdjoint T hs (sampleRadius n) (sampleRadius_ge n)
  have h := BoundedFlow.flow_difference
    (IsSelfAdjoint.smul_mem_skewAdjoint (r := Complex.I) (by simp [skewAdjoint.mem_iff]) hm)
    (IsSelfAdjoint.smul_mem_skewAdjoint (r := Complex.I) (by simp [skewAdjoint.mem_iff]) hn)
    (((boundedGenerator_commute T hs _ _ _ _).smul_left Complex.I).smul_right Complex.I) t x
  simpa only [approximatingFlow,sub_apply,smul_apply,← smul_sub,norm_smul,Complex.norm_I,one_mul] using h

lemma approximatingFlow_core_cauchy (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (t : ℝ) (x : T.domain) : CauchySeq (fun n => approximatingFlow T hs n t x) := by
  have hx := (boundedGenerator_strong T hs (T.mem_graph_iff.mpr ⟨x,rfl,rfl⟩)).cauchySeq
  rw [Metric.cauchySeq_iff] at hx ⊢
  intro ε hε
  obtain ⟨N,hN⟩ := hx (ε/(|t|+1)) (div_pos hε (by positivity))
  refine ⟨N,fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  calc
    _ ≤ |t| * ‖boundedGenerator T hs (sampleRadius m) (sampleRadius_ge m) x-
      boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x‖ := approximatingFlow_difference T hs _ _ _ _
    _ ≤ (|t|+1) * ‖boundedGenerator T hs (sampleRadius m) (sampleRadius_ge m) x-
      boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x‖ := by gcongr; linarith
    _ < (|t|+1)*(ε/(|t|+1)) := by
      apply mul_lt_mul_of_pos_left _ (by positivity)
      simpa only [dist_eq_norm] using hN m hm n hn
    _ = ε := by field_simp

lemma exists_flow_limit (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) :
    ∃ L : H →L[ℂ] H, ∀ x, Tendsto (fun n => approximatingFlow T hs n t x) atTop (𝓝 (L x)) :=
  StrongLimit.exists_of_dense_core T.domain hs.dense_domain
    (fun n => approximatingFlow T hs n t) (fun n => approximatingFlow_opNorm T hs n t)
    (approximatingFlow_core_cauchy T hs t)

 
def flow (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) : H →L[ℂ] H :=
  Classical.choose (exists_flow_limit T hs t)

lemma flow_tendsto (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) (x : H) :
    Tendsto (fun n => approximatingFlow T hs n t x) atTop (𝓝 (flow T hs t x)) :=
  Classical.choose_spec (exists_flow_limit T hs t) x

lemma flow_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) (x : H) :
    ‖flow T hs t x‖ = ‖x‖ := by
  apply tendsto_nhds_unique (flow_tendsto T hs t x).norm
  simpa only [approximatingFlow_norm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖x‖) atTop (𝓝 ‖x‖))

lemma flow_zero (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) : flow T hs 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply tendsto_nhds_unique (flow_tendsto T hs 0 x)
  simpa only [approximatingFlow,BoundedFlow.flow_zero,one_apply_eq_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))

lemma flow_add (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (s t : ℝ) :
    flow T hs (s+t) = flow T hs s*flow T hs t := by
  apply ContinuousLinearMap.ext
  intro x
  apply tendsto_nhds_unique (flow_tendsto T hs (s+t) x)
  have h := StrongLimit.mul_tendsto (fun n => approximatingFlow T hs n s)
    (fun n => approximatingFlow T hs n t) (flow T hs s) (flow T hs t)
    (fun n => approximatingFlow_opNorm T hs n s) (flow_tendsto T hs s) (flow_tendsto T hs t) x
  simpa only [approximatingFlow,BoundedFlow.flow_add, mul_apply_eq_comp] using h

lemma flow_initial_bound (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) {x y : H}
    (hxy : (x,y) ∈ T.graph) (t : ℝ) : ‖flow T hs t x-x‖ ≤ |t| *‖y‖ := by
  apply le_of_tendsto_of_tendsto ((flow_tendsto T hs t x).sub_const x).norm
    ((boundedGenerator_strong T hs hxy).norm.const_mul |t|)
  filter_upwards [] with n
  have h := BoundedFlow.flow_initial_bound
    (IsSelfAdjoint.smul_mem_skewAdjoint (r := Complex.I) (by simp [skewAdjoint.mem_iff])
      (boundedGenerator_selfAdjoint T hs (sampleRadius n) (sampleRadius_ge n))) t x
  simpa only [approximatingFlow,smul_apply,norm_smul,Complex.norm_I,one_mul] using h

lemma flow_continuous_zero (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (x : H) :
    Tendsto (fun t : ℝ => flow T hs t x) (𝓝 0) (𝓝 x) := by
  have hn : ∀ t, ‖flow T hs t‖ ≤ 1 := by
    intro t
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    rw [flow_norm, one_mul]
  have hc := (StrongLimit.equicontinuous_of_norm_bound _ hn).isClosed_setOfPred_tendsto
    (l := 𝓝 (0 : ℝ)) (f := id) continuous_id
  apply (closure_minimal (s := (T.domain : Set H)) (t := {x | Tendsto
    (fun t : ℝ => flow T hs t x) (𝓝 0) (𝓝 x)}) ?_ hc) (hs.dense_domain x)
  intro v hv
  let w : T.domain := ⟨v,hv⟩
  change Tendsto _ _ _
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm (a := fun t : ℝ => |t| *‖T w‖)
  · exact flow_initial_bound T hs (T.mem_graph_iff.mpr ⟨w,rfl,rfl⟩)
  · simpa only [abs_zero,zero_mul] using
      (continuous_abs.continuousAt.tendsto.mul_const ‖T w‖ : Tendsto _ (𝓝 (0 : ℝ)) _)

lemma flow_continuous (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (x : H) :
    Continuous (fun t : ℝ => flow T hs t x) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have h := (flow T hs s).continuous.tendsto x |>.comp
    ((flow_continuous_zero T hs x).comp (by simpa only [sub_self] using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 s) (𝓝 s)).sub_const s)))
  change Tendsto (fun t : ℝ => flow T hs t x) (𝓝 s) (𝓝 (flow T hs s x))
  change Tendsto (fun t : ℝ => flow T hs s (flow T hs (t-s) x)) _ _ at h
  have he (t : ℝ) : s+(t-s)=t := by ring
  simpa only [← mul_apply_eq_comp,← flow_add,he] using h

end StronglyRationalVOA.SymmetricOperator

open scoped Topology

open scoped Topology
open Filter MeasureTheory

open scoped Topology
open Filter MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ApproximatingFlowDerivative
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma approximatingFlow_derivative (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (n : ℕ) (t : ℝ) (x : H) :
    HasDerivAt (fun s : ℝ => approximatingFlow T hs n s x)
      (approximatingFlow T hs n t (Complex.I • boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x)) t := by
  exact BoundedFlow.flow_derivative _ t x

lemma approximatingFlow_continuous (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (n : ℕ) (x : H) : Continuous (fun t : ℝ => approximatingFlow T hs n t x) :=
  continuous_iff_continuousAt.mpr (fun t => (approximatingFlow_derivative T hs n t x).continuousAt)

lemma approximatingFlow_derivative_limit (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (t : ℝ) {x y : H} (hxy : (x,y) ∈ T.graph) :
    Tendsto (fun n : ℕ => approximatingFlow T hs n t
      (Complex.I • boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x))
      atTop (𝓝 (flow T hs t (Complex.I • y))) := by
  have hz : Tendsto (fun n : ℕ => approximatingFlow T hs n t
      (Complex.I • (boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x-y))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n : ℕ => ‖boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x-y‖)
    · intro n
      rw [approximatingFlow_norm,norm_smul,Complex.norm_I,one_mul]
    · simpa only [sub_self,norm_zero] using ((boundedGenerator_strong T hs hxy).sub_const y).norm
  have h := hz.add (flow_tendsto T hs t (Complex.I • y))
  simpa only [smul_sub,map_sub,sub_add_cancel,zero_add] using h

lemma flow_integral (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    {x y : H} (hxy : (x,y) ∈ T.graph) (t : ℝ) :
    (∫ s in 0..t, flow T hs s (Complex.I • y)) = flow T hs t x-x := by
  let F (n : ℕ) (s : ℝ) := approximatingFlow T hs n s
    (Complex.I • boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x)
  have hc (n : ℕ) : Continuous (F n) := approximatingFlow_continuous T hs n _
  have hb (n : ℕ) (s : ℝ) : ‖F n s‖ ≤ ‖y‖ := by
    dsimp [F]
    rw [approximatingFlow_norm,norm_smul,Complex.norm_I,one_mul,
      regularizer_on_graph T hs _ _ hxy]
    simpa only [one_mul] using (regularizer T hs (sampleRadius n) (sampleRadius_ge n)).le_of_opNorm_le
      (regularizer_norm_le T hs _ _) y
  have hi := StrongLimit.intervalIntegral_tendsto hc hb
    (fun s => approximatingFlow_derivative_limit T hs s hxy) 0 t
  have he (n : ℕ) : (∫ s in 0..t, F n s) = approximatingFlow T hs n t x-x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => approximatingFlow_derivative T hs n s x) ((hc n).intervalIntegrable 0 t)
    simpa only [F,approximatingFlow,BoundedFlow.flow_zero,one_apply_eq_self] using h
  simp_rw [he] at hi
  exact tendsto_nhds_unique hi ((flow_tendsto T hs t x).sub_const x)

lemma flow_derivative (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    {x y : H} (hxy : (x,y) ∈ T.graph) (t : ℝ) :
    HasDerivAt (fun s : ℝ => flow T hs s x) (flow T hs t (Complex.I • y)) t := by
  have hc := flow_continuous T hs (Complex.I • y)
  have he : (fun s : ℝ => flow T hs s x) =
      (fun s : ℝ => x+∫ r in 0..s, flow T hs r (Complex.I • y)) := by
    funext s
    rw [flow_integral T hs hxy s]
    abel
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt).const_add x

end StronglyRationalVOA.SymmetricOperator

open scoped Topology
open Filter

open scoped Topology
open Filter
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma flow_opNorm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) :
    ‖flow T hs t‖ ≤ 1 := by
  apply (flow T hs t).opNorm_le_bound zero_le_one
  intro x
  simp only [flow_norm,one_mul,le_refl]

lemma flow_adjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) :
    (flow T hs t).adjoint = flow T hs (-t) := by
  have hi := ContinuousLinearMap.norm_map_iff_adjoint_comp_self (flow T hs t) |>.mp (flow_norm T hs t)
  have hi' : (flow T hs t).adjoint * flow T hs t = 1 := hi
  calc
    (flow T hs t).adjoint = (flow T hs t).adjoint * (flow T hs t*flow T hs (-t)) := by
      rw [← flow_add,add_neg_cancel,flow_zero,mul_one]
    _ = flow T hs (-t) := by rw [← mul_assoc,hi',one_mul]

end StronglyRationalVOA.SymmetricOperator

open UniformSpace

open scoped Topology
open Filter MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_RegularizerFactorAdd
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace

open scoped Topology
open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma energyPower_zero_graph (x : Completion V) : (x,x) ∈ (U.energyPower 0).graph := by
  apply (OperatorTransport.mem_graph_iff U.energyCoordinates _ _ _).mpr
  apply (HilbertScale.mem_graph_iff _ _ _).mpr
  intro d
  simp only [pow_zero,Complex.ofReal_one,one_smul]



end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)


def smoothSmear (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    U.smoothEnergySpace →ₗ[ℂ] U.smoothEnergySpace :=
  { toFun := fun x => ⟨U.closedSmearedOperator hc a d f hf
      ⟨x,U.smoothEnergySpace_le_closedSmearedDomain hc ha hf x.property⟩,
        U.closedSmearedOperator_preserves_smoothEnergySpace hc ha hf _ x.property⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      change U.closedSmearedOperator hc a d f hf
        (⟨x,U.smoothEnergySpace_le_closedSmearedDomain hc ha hf x.property⟩+
         ⟨y,U.smoothEnergySpace_le_closedSmearedDomain hc ha hf y.property⟩) = _
      exact map_add (U.closedSmearedOperator hc a d f hf).toFun _ _
    map_smul' := by
      intro c x
      apply Subtype.ext
      change U.closedSmearedOperator hc a d f hf
        (c • ⟨x,U.smoothEnergySpace_le_closedSmearedDomain hc ha hf x.property⟩) = _
      exact map_smul (U.closedSmearedOperator hc a d f hf).toFun c _ }

lemma smoothSmear_graph (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) (x : U.smoothEnergySpace) :
    ((x : Completion V),(U.smoothSmear hc ha hf x : Completion V)) ∈
      (U.closedSmearedOperator hc a d f hf).graph := by
  exact (U.closedSmearedOperator hc a d f hf).mem_graph_iff.mpr ⟨_,rfl,rfl⟩

lemma smoothSmear_eq_extension (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d r : ℕ}
    (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) {C : ℝ}
    (hM : ∀ v, ‖A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf v‖ ≤ C*‖(A.energyShift^r) v‖)
    (x : U.smoothEnergySpace) {y : Completion V} (hxy : ((x : Completion V),y) ∈ (U.energyPower r).graph) :
    (U.smoothSmear hc ha hf x : Completion V) =
      U.sobolevExtension r (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf) y := by
  have hg := U.sobolevExtension_inverse_graph r _ hM (U.smearedCore_closable hc ha hf) y
  rw [U.inverseSobolev_on_graph r hxy] at hg
  exact (U.closedSmearedOperator hc a d f hf).mem_graph_snd_inj (U.smoothSmear_graph hc ha hf x) hg rfl

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

def smoothEnergyPower (r : ℕ) (x : U.smoothEnergySpace) : Completion V :=
  U.energyPower r ⟨x,(iInf_le (fun k => (U.energyPower k).domain) r) x.property⟩

lemma smoothEnergyPower_graph (r : ℕ) (x : U.smoothEnergySpace) :
    ((x : Completion V),U.smoothEnergyPower r x) ∈ (U.energyPower r).graph :=
  (U.energyPower r).mem_graph_iff.mpr ⟨_,rfl,rfl⟩

lemma smoothSmear_coe (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) (v : V) :
    (U.smoothSmear hc ha hf ⟨(v : Completion V),U.core_le_smoothEnergySpace
      (HilbertCore.equiv V v).property⟩ : Completion V) =
      A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf v := by
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf
  have h : ((v : Completion V),M v) ∈ (HilbertCore.operator M).graph :=
    (HilbertCore.operator M).mem_graph_iff.mpr ⟨HilbertCore.equiv V v,rfl,HilbertCore.operator_apply M v⟩
  exact (U.closedSmearedOperator hc a d f hf).mem_graph_snd_inj
    (U.smoothSmear_graph hc ha hf _) (LinearPMap.le_graph_of_le (HilbertCore.operator M).le_closure h) rfl
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_HighFieldGraph
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace

open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction

 
def power (f : SmoothCircleFunction) (k : ℕ) : SmoothCircleFunction :=
  ⟨fun t => f t^k,fun t => by dsimp only; rw [f.periodic],f.smooth.pow k⟩

@[simp] lemma power_apply (f : SmoothCircleFunction) (k : ℕ) (t : ℝ) : f.power k t = f t^k := rfl

end StronglyRationalVOA.SmoothCircleFunction

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_TimeAverageGraph
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory

open Filter
open scoped Topology

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma smoothSmear_core (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc ha hf)).closure =
      U.closedSmearedOperator hc a d f hf := by
  apply SymmetricOperator.closure_eq_of_intermediate _ _ (U.smearedCore_closable hc ha hf)
  · apply LinearPMap.le_of_le_graph
    intro p hp
    obtain ⟨x,hx,hMx⟩ := (HilbertCore.operator
      (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf)).mem_graph_iff.mp hp
    obtain ⟨v,rfl⟩ := (HilbertCore.equiv V).surjective x
    let z : U.smoothEnergySpace := ⟨(v:Completion V),U.core_le_smoothEnergySpace
      (HilbertCore.equiv V v).property⟩
    have h := SymmetricOperator.onSubmodule_mem_graph U.smoothEnergySpace (U.smoothSmear hc ha hf) z
    have he : (U.smoothSmear hc ha hf z:Completion V) =
        A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf v := U.smoothSmear_coe hc ha hf v
    rw [he] at h
    have hxe : (v:Completion V) = p.1 := hx
    have hye : A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf v = p.2 := by
      simpa only [HilbertCore.operator_apply] using hMx
    simpa only [z,hxe,hye,Prod.mk.eta] using h
  · apply LinearPMap.le_of_le_graph
    intro p hp
    obtain ⟨x,hx,hy⟩ := (LinearPMap.mem_graph_iff _).mp hp
    have he : ((x:Completion V),(U.smoothSmear hc ha hf x:Completion V)) = p := Prod.ext hx hy
    rw [← he]
    exact U.smoothSmear_graph hc ha hf x
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter MeasureTheory
open scoped Topology

open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SymmetricWeakCommute
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory

open UniformSpace

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma smoothSmear_core_closable (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc ha hf)).IsClosable := by
  apply (U.smearedCore_closable hc ha hf).closure_isClosed.isClosable.leIsClosable
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨x,hx,hy⟩ := (LinearPMap.mem_graph_iff _).mp hp
  have he : ((x : Completion V),(U.smoothSmear hc ha hf x : Completion V)) = p := Prod.ext hx hy
  rw [← he]
  exact U.smoothSmear_graph hc ha hf x



end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open MeasureTheory Set
open scoped ContDiff

open MeasureTheory Set Filter
open scoped Topology Interval

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressEvolution
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
namespace StronglyRationalVOA.TimeOrdered
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
lemma term_continuous {K : ℝ → A} (hK : Continuous K) (n : ℕ) : Continuous (term K n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact continuous_iff_continuousAt.mpr fun t =>
      (intervalIntegral.integral_hasDerivAt_right ((hK.mul ih).intervalIntegrable 0 t)
       (hK.mul ih).stronglyMeasurable.stronglyMeasurableAtFilter (hK.mul ih).continuousAt).continuousAt

lemma term_derivative {K : ℝ → A} (hK : Continuous K) (n : ℕ) (t : ℝ) :
    HasDerivAt (term K (n+1)) (K t*term K n t) t := by
  have hc := hK.mul (term_continuous hK n)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

variable [NormOneClass A]

lemma term_bound {K : ℝ → A} (hK : Continuous K) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t, ‖K t‖ ≤ M) (n : ℕ) (t : ℝ) :
    ‖term K n t‖ ≤ (M*|t|)^n/(n.factorial : ℝ) := by
  induction n generalizing t with
  | zero => simp [term]
  | succ n ih =>
    let g (s : ℝ) := (M^(n+1)/(n.factorial : ℝ))*|s|^n
    have hi : IntervalIntegrable g volume 0 t :=
      (continuous_const.mul (continuous_abs.pow n)).intervalIntegrable 0 t
    have he (s : ℝ) : ‖K s*term K n s‖ ≤ g s := by
      calc
        _ ≤ ‖K s‖*‖term K n s‖ := norm_mul_le _ _
        _ ≤ M*((M*|s|)^n/(n.factorial : ℝ)) := mul_le_mul (hb s) (ih s) (norm_nonneg _) hM
        _ = g s := by dsimp [g]; rw [mul_pow,pow_succ]; ring
    calc
      ‖term K (n+1) t‖ ≤ ∫ s in Ι (0:ℝ) t, ‖K s*term K n s‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ s in Ι (0:ℝ) t, g s := integral_mono_ae
        ((hK.mul (term_continuous hK n)).intervalIntegrable 0 t).norm.def'
        hi.def' (Filter.Eventually.of_forall he)
      _ = (M*|t|)^(n+1)/((n+1).factorial : ℝ) := by
        dsimp only [g]
        rw [integral_const_mul]
        have hx := integral_pow_abs_sub_uIoc (a := (0:ℝ)) (b := t) (n := n)
        simp only [sub_zero] at hx
        rw [hx,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_pow]
        field_simp

lemma term_summable {K : ℝ → A} (hK : Continuous K) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t, ‖K t‖ ≤ M) (t : ℝ) : Summable (fun n => term K n t) :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial (M*|t|)) (fun n => term_bound hK hM hb n t)

def evolution (K : ℝ → A) (t : ℝ) : A := ∑' n, term K n t

omit [CompleteSpace A] [NormOneClass A] in
lemma evolution_zero (K : ℝ → A) : evolution K 0 = 1 := by
  rw [evolution,tsum_eq_single 0]
  · rfl
  · intro n hn
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [term]

lemma evolution_derivative {K : ℝ → A} (hK : Continuous K) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t, ‖K t‖ ≤ M) (t : ℝ) :
    HasDerivAt (evolution K) (K t*evolution K t) t := by
  let R := |t|+1
  have hR : 0 < R := by dsimp [R]; positivity
  let u (n : ℕ) := M*((M*R)^n/(n.factorial : ℝ))
  have hu : Summable u := (Real.summable_pow_div_factorial (M*R)).mul_left M
  have hd := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    (fun n s _ => term_derivative hK n s)
    (fun n s (hs : s ∈ Ioo (-R) R) => by
      calc
        ‖K s*term K n s‖ ≤ ‖K s‖*‖term K n s‖ := norm_mul_le _ _
        _ ≤ M*((M*|s|)^n/(n.factorial : ℝ)) := mul_le_mul (hb s) (term_bound hK hM hb n s) (norm_nonneg _) hM
        _ ≤ u n := by
          dsimp [u]
          gcongr
          exact (abs_lt.mpr hs).le)
    (show (0:ℝ) ∈ Ioo (-R) R from ⟨neg_neg_of_pos hR,hR⟩)
    (by simp only [term,intervalIntegral.integral_same]; exact summable_zero)
    (show t ∈ Ioo (-R) R by dsimp [R]; constructor <;> linarith [le_abs_self t,neg_abs_le t])
  have he (s : ℝ) : evolution K s = 1+∑' n,term K (n+1) s := by
    rw [evolution,(term_summable hK hM hb s).tsum_eq_zero_add]
    rfl
  have hd' := hd.const_add (1:A)
  convert hd' using 1 <;> first | rfl | exact funext he | exact (Summable.tsum_mul_left (K t) (term_summable hK hM hb t)).symm
end StronglyRationalVOA.TimeOrdered

namespace StronglyRationalVOA.TimeOrdered
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]
  [StarRing A] [NormedStarGroup A] [StarModule ℝ A]

lemma evolution_unitary {K : ℝ → A} (hK : Continuous K) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t) (t : ℝ) :
    star (evolution K t)*evolution K t = 1 ∧ evolution K t*star (evolution K t) = 1 := by
  have hd := evolution_derivative hK hM hb
  have hleft (s : ℝ) : HasDerivAt (fun r => star (evolution K r)*evolution K r) 0 s := by
    convert (hd s).star.mul (hd s) using 1
    all_goals try with_reducible_and_instances rfl
    rw [star_mul,hk]
    noncomm_ring
  have hl := is_const_of_deriv_eq_zero (fun s => (hleft s).differentiableAt)
    (fun s => (hleft s).deriv) t 0
  simp only [evolution_zero,star_one,mul_one] at hl
  refine ⟨hl,?_⟩
  let z (s : ℝ) := evolution K s*star (evolution K s)-1
  let z' (s : ℝ) := K s*z s-z s*K s
  have hz (s : ℝ) : HasDerivAt z (z' s) s := by
    convert ((hd s).mul (hd s).star).sub_const (1:A) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [z,z']
    rw [star_mul,hk]
    noncomm_ring
  have hzb (s : ℝ) : ‖z' s‖ ≤ (2*M)*‖z s‖ := by
    calc
      _ ≤ ‖K s*z s‖+‖z s*K s‖ := norm_sub_le _ _
      _ ≤ ‖K s‖*‖z s‖+‖z s‖*‖K s‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ M*‖z s‖+‖z s‖*M := by gcongr <;> exact hb s
      _ = _ := by ring
  have hzero := zero_of_derivative_bound hz hzb (by simp [z,evolution_zero]) t
  exact sub_eq_zero.mp hzero
end StronglyRationalVOA.TimeOrdered

namespace StronglyRationalVOA.TimeOrdered
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

lemma evolution_mem_unitary {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t) (t : ℝ) :
    evolution K t ∈ unitary (H →L[ℂ] H) := evolution_unitary hK hM hb hk t

lemma evolution_norm {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t) (t : ℝ) (x : H) :
    ‖evolution K t x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (evolution_mem_unitary hK hM hb hk t) x

lemma evolution_star_norm {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t) (t : ℝ) (x : H) :
    ‖star (evolution K t) x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem (evolution_mem_unitary hK hM hb hk t)) x



lemma evolution_energy_bound {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M D : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t)
    (S : H →L[ℂ] H) (G : ℝ → H →L[ℂ] H) (hg : ∀ t, S*K t-K t*S = G t*S)
    (hG : ∀ t, ‖G t‖ ≤ D) (t : ℝ) (x : H) :
    ‖S (evolution K t x)‖ ≤ Real.exp (D*|t|)*‖S x‖ := by
  let q (s : ℝ) := star (evolution K s) (S (evolution K s x))
  let q' (s : ℝ) := star (evolution K s) (G s (S (evolution K s x)))
  have hd := evolution_derivative hK hM hb
  have hq (s : ℝ) : HasDerivAt q (q' s) s := by
    have hh := (((hd s).star.mul_const S).mul (hd s))
    have he : (star (K s*evolution K s)*S)*evolution K s +
        (star (evolution K s)*S)*(K s*evolution K s) =
        star (evolution K s)*(G s*S)*evolution K s := by
      rw [star_mul,hk,← hg]
      noncomm_ring
    rw [he] at hh
    exact ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hh
  have hqb (s : ℝ) : ‖q' s‖ ≤ D*‖q s‖ := by
    dsimp [q,q']
    rw [evolution_star_norm hK hM hb hk,evolution_star_norm hK hM hb hk]
    exact (G s).le_of_opNorm_le (hG s) _
  have hh := norm_growth hq hqb t
  dsimp [q] at hh
  rw [evolution_star_norm hK hM hb hk,evolution_zero] at hh
  simpa only [star_one,one_apply_eq_self,mul_comm] using hh

 

lemma duhamel_bound {K L : ℝ → H →L[ℂ] H} (hK : Continuous K) (hL : Continuous L)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hb : ∀ t, ‖K t‖ ≤ M) (hc : ∀ t, ‖L t‖ ≤ N)
    (hk : ∀ t, star (K t) = -K t)
    (t : ℝ) (x : H) {δ : ℝ}
    (hδ : ∀ s ∈ uIcc (0:ℝ) t, ‖(L s-K s) (evolution L s x)‖ ≤ δ) :
    ‖evolution L t x-evolution K t x‖ ≤ δ*|t| := by
  let q (s : ℝ) := star (evolution K s) (evolution L s x)
  let q' (s : ℝ) := star (evolution K s) ((L s-K s) (evolution L s x))
  have hq (s : ℝ) : HasDerivAt q (q' s) s := by
    have hh := (evolution_derivative hK hM hb s).star.mul (evolution_derivative hL hN hc s)
    have he : star (K s*evolution K s)*evolution L s +
        star (evolution K s)*(L s*evolution L s) =
        star (evolution K s)*(L s-K s)*evolution L s := by
      rw [star_mul,hk]
      noncomm_ring
    rw [he] at hh
    exact ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hh
  have hh := (convex_uIcc (0:ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hq s).hasDerivWithinAt)
    (fun s hs => by simpa only [q',evolution_star_norm hK hM hb hk] using hδ s hs)
    (left_mem_uIcc) (right_mem_uIcc)
  have he : q t-q 0 = star (evolution K t) (evolution L t x-evolution K t x) := by
    dsimp [q]
    rw [evolution_zero,evolution_zero,star_one,one_apply_eq_self,
      one_apply_eq_self,map_sub]
    have hunit := congrArg (fun T : H →L[ℂ] H => T x) (evolution_unitary hK hM hb hk t).1
    change star (evolution K t) (evolution K t x) = x at hunit
    rw [hunit]
  rw [he,evolution_star_norm hK hM hb hk] at hh
  simpa only [sub_zero,Real.norm_eq_abs] using hh
end StronglyRationalVOA.TimeOrdered

namespace StronglyRationalVOA.TimeOrdered
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

variable [CompleteSpace A] [NormOneClass A] [StarRing A] [NormedStarGroup A] [StarModule ℝ A]

lemma evolution_reverse {K : ℝ → A} (hK : Continuous K) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t) (t s : ℝ) :
    evolution (fun r => -K (t-r)) s = evolution K (t-s)*star (evolution K t) := by
  have hKr : Continuous (fun r => -K (t-r)) := (hK.comp (continuous_const.sub continuous_id)).neg
  have hbr (r : ℝ) : ‖-K (t-r)‖ ≤ M := by simpa only [norm_neg] using hb (t-r)
  have hr (r : ℝ) : HasDerivAt (fun q => evolution K (t-q)*star (evolution K t))
      (-K (t-r)*(evolution K (t-r)*star (evolution K t))) r := by
    have hh := ((evolution_derivative hK hM hb (t-r)).scomp r
      ((hasDerivAt_id r).const_sub t)).mul_const (star (evolution K t))
    simpa only [Function.comp_def,neg_one_smul,neg_mul,mul_assoc] using hh
  apply linear_ode_unique hbr (evolution_derivative hKr hM hbr) hr _ s
  rw [evolution_zero,sub_zero]
  exact (evolution_unitary hK hM hb hk t).2.symm
end StronglyRationalVOA.TimeOrdered

namespace StronglyRationalVOA.TimeOrdered
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

lemma evolution_star_energy_bound {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M D : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t)
    (S : H →L[ℂ] H) (G : ℝ → H →L[ℂ] H) (hg : ∀ t, S*K t-K t*S = G t*S)
    (hG : ∀ t, ‖G t‖ ≤ D) (t : ℝ) (x : H) :
    ‖S (star (evolution K t) x)‖ ≤ Real.exp (D*|t|)*‖S x‖ := by
  have hKr : Continuous (fun r => -K (t-r)) := (hK.comp (continuous_const.sub continuous_id)).neg
  have hbr (r : ℝ) : ‖-K (t-r)‖ ≤ M := by simpa only [norm_neg] using hb (t-r)
  have hkr (r : ℝ) : star (-K (t-r)) = -(-K (t-r)) := by rw [star_neg,hk]
  have hgr (r : ℝ) : S*(-K (t-r))-(-K (t-r))*S = (-G (t-r))*S := by
    calc
      _ = -(S*K (t-r)-K (t-r)*S) := by noncomm_ring
      _ = _ := by rw [hg,neg_mul]
  have hGr (r : ℝ) : ‖-G (t-r)‖ ≤ D := by simpa only [norm_neg] using hG (t-r)
  have h := evolution_energy_bound hKr hM hbr hkr S (fun r => -G (t-r)) hgr hGr t x
  rw [evolution_reverse hK hM hb hk,sub_self,evolution_zero,one_mul] at h
  exact h

 

lemma evolution_regularizer_factor {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M D : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (G : ℝ → H →L[ℂ] H) (hg : ∀ t, S*K t-K t*S = G t*S)
    (hG : ∀ t, ‖G t‖ ≤ D) (t : ℝ) :
    ∃ B : H →L[ℂ] H, (evolution K t).comp S = S.comp B ∧ ‖B‖ ≤ Real.exp (D*|t|) := by
  let L := (S.comp (star (evolution K t))).toLinearMap
  let Q := L.extendOfNorm S.toLinearMap
  have hb' (x : H) : ‖L x‖ ≤ Real.exp (D*|t|)*‖S.toLinearMap x‖ :=
    evolution_star_energy_bound hK hM hb hk S G hg hG t x
  have hQ : Q.comp S = S.comp (star (evolution K t)) := by
    ext x
    exact L.extendOfNorm_eq hSd ⟨_,hb'⟩ x
  have hQa : S.comp Q.adjoint = (evolution K t).comp S := by
    have h := congrArg ContinuousLinearMap.adjoint hQ
    simpa only [ContinuousLinearMap.adjoint_comp,show S.adjoint=S from hS,
      ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint] using h
  refine ⟨Q.adjoint,hQa.symm,?_⟩
  rw [LinearIsometryEquiv.norm_map]
  exact L.opNorm_extendOfNorm_le hSd (Real.exp_pos _).le hb'
end StronglyRationalVOA.TimeOrdered

open MeasureTheory Set Filter
open scoped Topology Interval
namespace StronglyRationalVOA.TimeOrdered
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

lemma evolution_opNorm {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t) (t : ℝ) :
    ‖evolution K t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [evolution_norm hK hM hb hk,one_mul]

lemma evolution_difference_regularized
    {K L : ℝ → H →L[ℂ] H} (hK : Continuous K) (hL : Continuous L)
    {M N D : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hb : ∀ t, ‖K t‖ ≤ M) (hc : ∀ t, ‖L t‖ ≤ N)
    (hk : ∀ t, star (K t) = -K t) (hl : ∀ t, star (L t) = -L t)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (G : ℝ → H →L[ℂ] H) (hg : ∀ t, S*L t-L t*S = G t*S)
    (hG : ∀ t, ‖G t‖ ≤ D) (hD : 0 ≤ D)
    {δ : ℝ} (hδ : ∀ t, ‖(L t-K t)*S‖ ≤ δ) (t : ℝ) (x : H) :
    ‖evolution L t (S x)-evolution K t (S x)‖ ≤ δ*Real.exp (D*|t|)*‖x‖*|t| := by
  have hd : 0 ≤ δ := (norm_nonneg _).trans (hδ 0)
  apply duhamel_bound hK hL hM hN hb hc hk
  intro s hs
  obtain ⟨B,hB,hBn⟩ := evolution_regularizer_factor hL hN hc hl S hS hSd G hg hG s
  have he : evolution L s (S x) = S (B x) := congrArg (fun A : H →L[ℂ] H => A x) hB
  rw [he]
  calc
    _ ≤ δ*‖B x‖ := ((L s-K s)*S).le_of_opNorm_le (hδ s) _
    _ ≤ δ*(Real.exp (D*|s|)*‖x‖) := mul_le_mul_of_nonneg_left (B.le_of_opNorm_le hBn x) hd
    _ ≤ δ*(Real.exp (D*|t|)*‖x‖) := by
      have hab : |s| ≤ |t| := by
        rcases mem_uIcc.mp hs with hs' | hs' <;> rw [abs_le] <;> constructor <;>
          nlinarith [neg_abs_le t,le_abs_self t]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hD)) (norm_nonneg x)) hd
    _ = _ := by ring

lemma exists_evolution_limit
    (K : ℕ → ℝ → H →L[ℂ] H) (hK : ∀ n, Continuous (K n))
    (M : ℕ → ℝ) (hM : ∀ n, 0 ≤ M n) (hb : ∀ n t, ‖K n t‖ ≤ M n)
    (hk : ∀ n t, star (K n t) = -K n t)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (G : ℕ → ℝ → H →L[ℂ] H) (hg : ∀ n t, S*K n t-K n t*S = G n t*S)
    {D : ℝ} (hG : ∀ n t, ‖G n t‖ ≤ D) (hD : 0 ≤ D)
    (e : ℕ → ℝ) (he : Antitone e) (he0 : Tendsto e atTop (𝓝 0))
    (hδ : ∀ n m t, ‖(K n t-K m t)*S‖ ≤ e n+e m) (t : ℝ) :
    ∃ L : H →L[ℂ] H, ∀ x, Tendsto (fun n => evolution (K n) t x) atTop (𝓝 (L x)) := by
  apply StrongLimit.exists_of_dense_core S.range (by change Dense (Set.range S); exact hSd)
    (fun n => evolution (K n) t) (fun n => evolution_opNorm (hK n) (hM n) (hb n) (hk n) t)
  intro x
  obtain ⟨v,hv⟩ := x.property
  have hx : (x : H)=S v := hv.symm
  rw [hx]
  apply cauchySeq_of_le_tendsto_0 (fun n => (2*e n)*Real.exp (D*|t|)*‖v‖*|t|)
  · intro n m N hn hm
    rw [dist_eq_norm]
    calc
      _ ≤ (e n+e m)*Real.exp (D*|t|)*‖v‖*|t| :=
        evolution_difference_regularized (hK m) (hK n) (hM m) (hM n) (hb m) (hb n)
          (hk m) (hk n) S hS hSd (G n) (hg n) (hG n) hD (hδ n m) t v
      _ ≤ _ := by
        gcongr
        have h1 := he hn
        have h2 := he hm
        linarith
  · simpa only [mul_zero,zero_mul] using
      (((he0.const_mul 2).mul_const (Real.exp (D*|t|))).mul_const ‖v‖).mul_const |t|

end StronglyRationalVOA.TimeOrdered

namespace StronglyRationalVOA.TimeOrdered
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

 

lemma exists_unitary_evolution_limit
    (K : ℕ → ℝ → H →L[ℂ] H) (hK : ∀ n, Continuous (K n))
    (M : ℕ → ℝ) (hM : ∀ n, 0 ≤ M n) (hb : ∀ n t, ‖K n t‖ ≤ M n)
    (hk : ∀ n t, star (K n t) = -K n t)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (G : ℕ → ℝ → H →L[ℂ] H) (hg : ∀ n t, S*K n t-K n t*S = G n t*S)
    {D : ℝ} (hG : ∀ n t, ‖G n t‖ ≤ D) (hD : 0 ≤ D)
    (e : ℕ → ℝ) (he : Antitone e) (he0 : Tendsto e atTop (𝓝 0))
    (hδ : ∀ n m t, ‖(K n t-K m t)*S‖ ≤ e n+e m) (t : ℝ) :
    ∃ L : H →L[ℂ] H, L ∈ unitary (H →L[ℂ] H) ∧
      (∀ x, Tendsto (fun n => evolution (K n) t x) atTop (𝓝 (L x))) ∧
      (∀ x, Tendsto (fun n => star (evolution (K n) t) x) atTop (𝓝 (star L x))) := by
  obtain ⟨L,hL⟩ := exists_evolution_limit K hK M hM hb hk S hS hSd G hg hG hD e he he0 hδ t
  let Kr (n : ℕ) (s : ℝ) := -K n (t-s)
  let Gr (n : ℕ) (s : ℝ) := -G n (t-s)
  have hKr (n : ℕ) : Continuous (Kr n) := ((hK n).comp (continuous_const.sub continuous_id)).neg
  have hbr (n : ℕ) (s : ℝ) : ‖Kr n s‖ ≤ M n := by simpa only [Kr,norm_neg] using hb n (t-s)
  have hkr (n : ℕ) (s : ℝ) : star (Kr n s) = -Kr n s := by simp only [Kr,star_neg,hk]
  have hgr (n : ℕ) (s : ℝ) : S*Kr n s-Kr n s*S=Gr n s*S := by
    dsimp [Kr,Gr]
    calc
      _ = -(S*K n (t-s)-K n (t-s)*S) := by noncomm_ring
      _ = _ := by rw [hg,neg_mul]
  have hGr (n : ℕ) (s : ℝ) : ‖Gr n s‖ ≤ D := by simpa only [Gr,norm_neg] using hG n (t-s)
  have hδr (n m : ℕ) (s : ℝ) : ‖(Kr n s-Kr m s)*S‖ ≤ e n+e m := by
    have heq : (Kr n s-Kr m s)*S = -((K n (t-s)-K m (t-s))*S) := by dsimp [Kr]; noncomm_ring
    rw [heq,norm_neg]
    exact hδ n m (t-s)
  obtain ⟨R,hR⟩ := exists_evolution_limit Kr hKr M hM hbr hkr S hS hSd Gr hgr hGr hD e he he0 hδr t
  have hre (n : ℕ) : evolution (Kr n) t=star (evolution (K n) t) := by
    dsimp [Kr]
    rw [evolution_reverse (hK n) (hM n) (hb n) (hk n),sub_self,evolution_zero,one_mul]
  have hr : ∀ x, Tendsto (fun n => star (evolution (K n) t) x) atTop (𝓝 (R x)) := by
    simpa only [hre] using hR
  obtain ⟨hu,hs⟩ := unitary_of_strong_and_star_limit (fun n => evolution (K n) t)
    (fun n => evolution_mem_unitary (hK n) (hM n) (hb n) (hk n) t) L R hL hr
  refine ⟨L,hu,hL,?_⟩
  rwa [hs]

end StronglyRationalVOA.TimeOrdered

open Set Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_EnergyCutoffNorm
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
namespace StronglyRationalVOA.HilbertScale
variable {G : ℕ → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]

lemma energyCutoff_tail_inverse (n : ℕ) :
    ‖(1-energyCutoff (G := G) n)*inverseEnergy (fun i : ℕ => 1+(i:ℝ)) (fun i => le_add_of_nonneg_right (Nat.cast_nonneg i))‖ ≤
      (1+(n:ℝ))⁻¹ := by
  let q (i : ℕ) : ℂ := if i ≤ n then 0 else (1+(i:ℂ))⁻¹
  have hb (i : ℕ) : ‖q i‖ ≤ (1+(n:ℝ))⁻¹ := by
    dsimp [q]
    split_ifs with hi
    · simpa using inv_nonneg.mpr (show (0:ℝ) ≤ 1+(n:ℝ) by positivity)
    · rw [norm_inv]
      have hn : ‖(1:ℂ)+(i:ℂ)‖ = 1+(i:ℝ) := by
        rw [show (1:ℂ)+(i:ℂ)=((1+(i:ℝ):ℝ):ℂ) by push_cast; rfl,
          Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      rw [hn]
      apply inv_anti₀ (by positivity)
      exact_mod_cast Nat.add_le_add_left (Nat.le_of_lt (Nat.lt_of_not_ge hi)) 1
  have he : (1-energyCutoff (G := G) n)*inverseEnergy (fun i : ℕ => 1+(i:ℝ)) (fun i => le_add_of_nonneg_right (Nat.cast_nonneg i)) =
      boundedMultiplier q (by positivity) hb := by
    ext x i
    change inverseEnergy (fun i : ℕ => 1+(i:ℝ)) (fun i => le_add_of_nonneg_right (Nat.cast_nonneg i)) x i-energyCutoff n (inverseEnergy (fun i : ℕ => 1+(i:ℝ)) (fun i => le_add_of_nonneg_right (Nat.cast_nonneg i)) x) i = _
    simp only [energyCutoff_apply,inverseEnergy_apply,boundedMultiplier_apply,q]
    split_ifs <;> simp
  rw [he]
  exact boundedMultiplier_norm _ _ _
end StronglyRationalVOA.HilbertScale

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma inverseSobolev_mul (r s : ℕ) : U.inverseSobolev r*U.inverseSobolev s=U.inverseSobolev (r+s) := by
  ext x
  apply U.energyCoordinates.injective
  simp only [mul_apply_eq_comp,U.inverseSobolev_apply,U.energyCoordinates.apply_symm_apply]
  ext i
  simp only [HilbertScale.inverseEnergy_apply,smul_smul]
  congr 1
  push_cast
  rw [pow_add,mul_inv]

lemma sobolevExtension_lower (r s : ℕ) (M : V →ₗ[ℂ] Completion V) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hc : (HilbertCore.operator M).IsClosable) :
    U.sobolevExtension (r+s) M=U.sobolevExtension r M*U.inverseSobolev s := by
  have hM' (v : V) : ‖M v‖ ≤ C*‖(A.energyShift^(r+s)) v‖ :=
    (hM v).trans (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (Nat.le_add_right r s) v) hC)
  ext x
  have h1 := U.sobolevExtension_inverse_graph (r+s) M hM' hc x
  have h2 := U.sobolevExtension_inverse_graph r M hM hc (U.inverseSobolev s x)
  apply (HilbertCore.operator M).closure.mem_graph_snd_inj h1 h2
  exact congrArg (fun B : Completion V →L[ℂ] Completion V => B x) (U.inverseSobolev_mul r s).symm

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

attribute [local instance] OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.instFiniteDimensionalComplexSubtypeMemSubmoduleGrade_2
lemma energyCutoff_tail_inverse (n : ℕ) :
    ‖(1-U.energyCutoff n)*U.inverseSobolev 1‖ ≤ (1+(n:ℝ))⁻¹ := by
  change ‖(1-U.energyCoordinates.symm.conjStarAlgEquiv _)*U.energyCoordinates.symm.conjStarAlgEquiv _‖ ≤ _
  rw [← map_one U.energyCoordinates.symm.conjStarAlgEquiv,← map_sub,← map_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.norm_map]
  have h : ‖(1-HilbertScale.energyCutoff (G := fun d => A.grade d) n)*HilbertScale.inverseEnergy (fun d : ℕ => (1+(d:ℝ))^1) (fun d => one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg d)))‖ ≤ (1+(n:ℝ))⁻¹ := by
    simpa only [pow_one] using (HilbertScale.energyCutoff_tail_inverse (G := fun d => A.grade d) n)
  simpa only [LinearIsometryEquiv.symm_symm,LinearIsometryEquiv.norm_map] using ContinuousLinearMap.le_of_opNorm_le _ h (U.energyCoordinates x)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma stressNormalized_two_factor (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) :
    ∃ B : Completion V →L[ℂ] Completion V,
      U.stressNormalized hc hf 2=U.inverseSobolev 1*B ∧
      ‖B‖ ≤ coefficientSeminorm f 3*(1+A.centralCharge.re) ∧
      U.stressNormalized hc hf 2=U.stressNormalized hc hf 1*U.inverseSobolev 1 := by
  let N := U.weightedSmearedMap A.conformal_mem (U.polynomialEnergyBounds hc A.conformalVector) hf 1
  have hN (v : V) : ‖N v‖ ≤ (coefficientSeminorm f 3*(1+A.centralCharge.re))*‖(A.energyShift^2) v‖ := by
    exact U.smearedMap_sobolev_bound A.conformal_mem (U.polynomialEnergyBounds hc _)
      (k := 1) (by linarith [U.centralCharge_nonneg])
      (by simpa only [pow_one] using U.stress_physical_bound) hf 1 v
  refine ⟨U.sobolevExtension 2 N,?_,U.sobolevExtension_norm 2 N
      (mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg])) hN,?_⟩
  · ext x
    have h := U.sobolevExtension_graph 2 (U.stressCore hc hf) N
      (U.stressCore_bound hc hf (by norm_num : 1 ≤ 2)) hN (U.energyPower 1)
      (U.energyOperator_closed _) (U.smearedMap_energyGraph A.conformal_mem (U.polynomialEnergyBounds hc _) hf 1) x
    exact (U.inverseSobolev_on_graph 1 h).symm
  · exact U.sobolevExtension_lower 1 1 (U.stressCore hc hf)
      (mul_nonneg (coefficientSeminorm_nonneg _ _) (by linarith [U.centralCharge_nonneg]))
      (U.stressCore_bound hc hf le_rfl) (U.smearedCore_closable hc A.conformal_mem hf)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressCutoffNormalized
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma stressCutoff_normalized (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) {r : ℕ} (hr : 1 ≤ r) :
    U.stressCutoff hc n hf*U.inverseSobolev r =
      Complex.I • (U.energyCutoff n*U.stressNormalized hc hf r*U.energyCutoff n) := by
  rw [stressCutoff,smul_mul_assoc]
  congr 1
  exact SymmetricOperator.cutoff_normalized (U.closedSmearedOperator hc A.conformalVector 2 f hf)
    _ _ _ _ (U.energyCutoff_graph 1 (U.stressCore hc hf) (U.stressCore_bound hc hf le_rfl)
      (U.smearedCore_closable hc A.conformal_mem hf) n)
    (U.stressNormalized_graph hc hf hr) (U.energyCutoff_inverseSobolev n r)

lemma stressCutoff_commutator (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) (hr : ∀ m, star (f m)=f (-m)) {r : ℕ} (hr' : 1 ≤ r) :
    ∃ G : Completion V →L[ℂ] Completion V,
      U.inverseSobolev r*U.stressCutoff hc n hf-U.stressCutoff hc n hf*U.inverseSobolev r = G*U.inverseSobolev r ∧
      ‖G‖ ≤ coefficientSeminorm f (2+r)*((1+A.centralCharge.re)*r) := by
  obtain ⟨F,hF,hFn⟩ := U.stressNormalized_defect hc hf hr hr'
  refine ⟨Complex.I • (U.energyCutoff n*F.adjoint*U.energyCutoff n),?_,
    (SymmetricOperator.cutoff_commutator_bound _ _ (U.energyCutoff_norm n)).trans hFn⟩
  exact SymmetricOperator.cutoff_commutator (U.closedSmearedOperator hc A.conformalVector 2 f hf)
    (U.stressCore_formalAdjoint hc hf hr) _ _ _ _ _ (U.energyCutoff_selfAdjoint n)
    (U.inverseSobolev_selfAdjoint r)
    (U.energyCutoff_graph 1 (U.stressCore hc hf) (U.stressCore_bound hc hf le_rfl)
      (U.smearedCore_closable hc A.conformal_mem hf) n)
    (U.stressNormalized_graph hc hf hr') (U.energyCutoff_inverseSobolev n r) hF

lemma stressCutoff_error (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) :
    ‖U.stressCutoff hc n hf*U.inverseSobolev 2-Complex.I • U.stressNormalized hc hf 2‖ ≤
      (1+(n:ℝ))⁻¹*((coefficientSeminorm f 3+coefficientSeminorm f 2)*(1+A.centralCharge.re)) := by
  obtain ⟨B,hB,hBn,hE⟩ := U.stressNormalized_two_factor hc hf
  rw [U.stressCutoff_normalized hc n hf (by norm_num : 1 ≤ 2),← smul_sub,norm_smul,Complex.norm_I,one_mul]
  exact (SymmetricOperator.cutoff_error (U.energyCutoff n) (U.inverseSobolev 1)
    (U.stressNormalized hc hf 2) B (U.stressNormalized hc hf 1) (U.energyCutoff_norm n) hB hE
    (U.energyCutoff_inverseSobolev n 1) (U.energyCutoff_tail_inverse n)).trans (by
      have hn := U.stressNormalized_norm hc hf le_rfl
      have hc' : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
      calc
        _ ≤ (1+(n:ℝ))⁻¹*(coefficientSeminorm f 3*(1+A.centralCharge.re)+
            coefficientSeminorm f 2*(1+A.centralCharge.re)) := by gcongr
        _ = _ := by ring)

lemma stressCutoff_difference (hc : A.toVertexAlgebra.C2Cofinite) (n m : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) :
    ‖(U.stressCutoff hc n hf-U.stressCutoff hc m hf)*U.inverseSobolev 2‖ ≤
      ((1+(n:ℝ))⁻¹+(1+(m:ℝ))⁻¹)*((coefficientSeminorm f 3+coefficientSeminorm f 2)*(1+A.centralCharge.re)) := by
  have he : (U.stressCutoff hc n hf-U.stressCutoff hc m hf)*U.inverseSobolev 2 =
      (U.stressCutoff hc n hf*U.inverseSobolev 2-Complex.I • U.stressNormalized hc hf 2)-
      (U.stressCutoff hc m hf*U.inverseSobolev 2-Complex.I • U.stressNormalized hc hf 2) := by noncomm_ring
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add (U.stressCutoff_error hc n hf)
    (U.stressCutoff_error hc m hf)).trans_eq (by ring))
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)



lemma stressPath_cutoff_commutator (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {r : ℕ} (hr : 1 ≤ r) :
    ∃ G : ℕ → ℝ → Completion V →L[ℂ] Completion V,
      (∀ n t, U.inverseSobolev r*U.stressCutoff hc n (f.rapid t)-
        U.stressCutoff hc n (f.rapid t)*U.inverseSobolev r = G n t*U.inverseSobolev r) ∧
      ∀ n t, ‖G n t‖ ≤ f.bound (2+r)*((1+A.centralCharge.re)*r) := by
  choose G hG hGn using fun n t => U.stressCutoff_commutator hc n (f.rapid t) (f.real t) hr
  refine ⟨G,hG,fun n t => (hGn n t).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (f.seminorm_bound t (2+r))
    (mul_nonneg (by linarith [U.centralCharge_nonneg]) (Nat.cast_nonneg r))

lemma stressPath_cutoff_difference (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n m : ℕ) (t : ℝ) :
    ‖(U.stressCutoff hc n (f.rapid t)-U.stressCutoff hc m (f.rapid t))*U.inverseSobolev 2‖ ≤
      (1+(n:ℝ))⁻¹*((f.bound 3+f.bound 2)*(1+A.centralCharge.re))+
      (1+(m:ℝ))⁻¹*((f.bound 3+f.bound 2)*(1+A.centralCharge.re)) := by
  apply (U.stressCutoff_difference hc n m (f.rapid t)).trans
  calc
    _ ≤ ((1+(n:ℝ))⁻¹+(1+(m:ℝ))⁻¹)*((f.bound 3+f.bound 2)*(1+A.centralCharge.re)) := by
      gcongr
      · linarith [U.centralCharge_nonneg]
      · exact f.seminorm_bound t 3
      · exact f.seminorm_bound t 2
    _ = _ := by ring

 

lemma exists_stressPropagator (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) :
    ∃ L : Completion V →L[ℂ] Completion V, L ∈ unitary (Completion V →L[ℂ] Completion V) ∧
      (∀ x, Tendsto (fun n => TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x)
        atTop (𝓝 (L x))) ∧
      (∀ x, Tendsto (fun n => star (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t) x)
        atTop (𝓝 (star L x))) := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  obtain ⟨G,hG,hGn⟩ := U.stressPath_cutoff_commutator hc f (by norm_num : 1 ≤ 2)
  let C := (f.bound 3+f.bound 2)*(1+A.centralCharge.re)
  have hC : 0 ≤ C := mul_nonneg (add_nonneg (f.bound_nonneg 3) (f.bound_nonneg 2))
    (by linarith [U.centralCharge_nonneg])
  apply TimeOrdered.exists_unitary_evolution_limit
    (fun n s => U.stressCutoff hc n (f.rapid s))
    (fun n => U.stressCutoff_continuous hc n f.rapid f.continuous)
    (fun n => (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)))
    (fun n => mul_nonneg (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (by positivity))
    (U.stressPath_cutoff_bound hc f) (fun n s => U.stressCutoff_skew hc n (f.rapid s) (f.real s))
    (U.inverseSobolev 2) (U.inverseSobolev_selfAdjoint 2) (U.inverseSobolev_dense 2)
    G hG hGn (mul_nonneg (f.bound_nonneg _) (mul_nonneg (by linarith [U.centralCharge_nonneg]) (by norm_num)))
    (fun n => (1+(n:ℝ))⁻¹*C) _ _ (U.stressPath_cutoff_difference hc f) t
  · intro n m hnm
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_left hnm 1)) hC
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [one_div,add_comm,zero_mul] using h.mul_const C

 def stressPropagator (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) :
    Completion V →L[ℂ] Completion V := (U.exists_stressPropagator hc f t).choose

lemma stressPropagator_limit (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) (x : Completion V) :
    Tendsto (fun n => TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x)
      atTop (𝓝 (U.stressPropagator hc f t x)) := (U.exists_stressPropagator hc f t).choose_spec.2.1 x

lemma stressPropagator_star_limit (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) (x : Completion V) :
    Tendsto (fun n => star (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t) x)
      atTop (𝓝 (star (U.stressPropagator hc f t) x)) := (U.exists_stressPropagator hc f t).choose_spec.2.2 x

lemma stressPropagator_factor (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {r : ℕ} (hr : 1 ≤ r) (t : ℝ) :
    ∃ B : Completion V →L[ℂ] Completion V,
      U.stressPropagator hc f t*U.inverseSobolev r=U.inverseSobolev r*B ∧
      ‖B‖ ≤ Real.exp ((f.bound (2+r)*((1+A.centralCharge.re)*r))*|t|) := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  obtain ⟨G,hG,hGn⟩ := U.stressPath_cutoff_commutator hc f hr
  exact TimeOrdered.regularizer_factor_of_limits _ _ (U.stressPropagator_star_limit hc f t)
    (U.inverseSobolev r) (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)
    (Real.exp_pos _).le (fun n x => TimeOrdered.evolution_star_energy_bound
      (U.stressCutoff_continuous hc n f.rapid f.continuous)
      (show 0 ≤ (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) by
        exact mul_nonneg (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (by positivity))
      (U.stressPath_cutoff_bound hc f n) (fun s => U.stressCutoff_skew hc n (f.rapid s) (f.real s))
      (U.inverseSobolev r) (G n) (hG n) (hGn n) t x)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma inverseSobolev_injective (r : ℕ) : Function.Injective (U.inverseSobolev r) :=
  SymmetricOperator.selfAdjoint_injective_of_denseRange _
    (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma preserves_smoothEnergySpace_of_factor (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ r : ℕ, 1 ≤ r → ∃ B : Completion V →L[ℂ] Completion V,
      Q*U.inverseSobolev r=U.inverseSobolev r*B)
    {x : Completion V} (hx : x ∈ U.smoothEnergySpace) : Q x ∈ U.smoothEnergySpace := by
  rw [smoothEnergySpace,Submodule.mem_iInf] at hx ⊢
  intro r
  have hg : ∃ y, (Q x,y) ∈ (U.energyPower r).graph := by
    by_cases hr : r=0
    · subst r
      exact ⟨Q x,U.energyPower_zero_graph (Q x)⟩
    · obtain ⟨B,hB⟩ := hQ r (by omega)
      let y := U.energyPower r ⟨x,hx r⟩
      have hy : (x,y) ∈ (U.energyPower r).graph := (U.energyPower r).mem_graph_iff.mpr ⟨_,rfl,rfl⟩
      have he := congrArg (fun Q : Completion V →L[ℂ] Completion V => Q y) hB
      change Q (U.inverseSobolev r y)=U.inverseSobolev r (B y) at he
      rw [U.inverseSobolev_on_graph r hy] at he
      exact ⟨B y,he.symm ▸ U.inverseSobolev_graph r (B y)⟩
  obtain ⟨y,hy⟩ := hg
  obtain ⟨z,hz,_⟩ := (U.energyPower r).mem_graph_iff.mp hy
  dsimp only [Prod.fst] at hz
  rw [← hz]
  exact z.property

lemma stressPropagator_smooth (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    U.stressPropagator hc f t x ∈ U.smoothEnergySpace := by
  apply U.preserves_smoothEnergySpace_of_factor _ _ hx
  intro r hr
  obtain ⟨B,hB,_⟩ := U.stressPropagator_factor hc f hr t
  exact ⟨B,hB⟩

 def stressPropagatorSmooth (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) :
    U.smoothEnergySpace →ₗ[ℂ] U.smoothEnergySpace :=
  ((U.stressPropagator hc f t).toLinearMap.comp U.smoothEnergySpace.subtype).codRestrict
    U.smoothEnergySpace (fun x => U.stressPropagator_smooth hc f t x.property)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter Set
open scoped Topology

open UniformSpace Filter Set MeasureTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressCutoffNormalized2
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory

open Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma sobolevExtension_smul (r : ℕ) (M : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖) (c : ℂ) :
    U.sobolevExtension r (c • M)=c • U.sobolevExtension r M := by
  have hcM (v : V) : ‖(c • M) v‖ ≤ (‖c‖*C)*‖(A.energyShift^r) v‖ := by
    simpa only [LinearMap.smul_apply,norm_smul,mul_assoc] using mul_le_mul_of_nonneg_left (hM v) (norm_nonneg c)
  ext x
  have hd : DenseRange (fun v : V => (v : Completion V)) := Completion.denseRange_coe
  apply hd.induction_on (p := fun x => U.sobolevExtension r (c • M) x=(c • U.sobolevExtension r M) x) x
    (isClosed_eq (U.sobolevExtension r _).continuous (ContinuousLinearMap.continuous _))
  intro v
  simp only [smul_apply,U.sobolevExtension_coe r _ hcM,
    U.sobolevExtension_coe r _ hM,LinearMap.smul_apply]

 def normalizedField (hc : A.toVertexAlgebra.C2Cofinite) (a : V) (d k : ℕ)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) : Completion V →L[ℂ] Completion V :=
  U.sobolevExtension k (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology

open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction

def add (f g : SmoothCircleFunction) : SmoothCircleFunction :=
  ⟨fun t => f t+g t,fun t => by dsimp only; rw [f.periodic,g.periodic],f.smooth.add g.smooth⟩
def scale (f : SmoothCircleFunction) (c : ℂ) : SmoothCircleFunction :=
  ⟨fun t => c*f t,fun t => by dsimp only; rw [f.periodic],contDiff_const.mul f.smooth⟩
@[simp] lemma add_apply (f g : SmoothCircleFunction) (t : ℝ) : f.add g t=f t+g t := rfl
@[simp] lemma scale_apply (f : SmoothCircleFunction) (c : ℂ) (t : ℝ) : f.scale c t=c*f t := rfl
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressPropagatorDerivative
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma stressPropagator_zero (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) :
    U.stressPropagator hc f 0=1 := by
  ext x
  apply tendsto_nhds_unique (U.stressPropagator_limit hc f 0 x)
  simpa only [TimeOrdered.evolution_zero,one_apply_eq_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter
open scoped Topology ContDiff

open Filter
open scoped Topology ContDiff

open Filter
open scoped Topology ContDiff

open Filter MeasureTheory Set
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_CoefficientSummableBound
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
namespace StronglyRationalVOA


structure SmoothCircleFamily where
  toFun : ℝ → SmoothCircleFunction
  smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => toFun p.1 p.2)
namespace SmoothCircleFamily
instance instCoeFunForallRealSmoothCircleFunction : CoeFun SmoothCircleFamily (fun _ => ℝ → SmoothCircleFunction) := ⟨SmoothCircleFamily.toFun⟩
end SmoothCircleFamily
end StronglyRationalVOA

open Filter Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
@[ext] lemma ext {f g : SmoothCircleFunction} (h : ∀ x, f x=g x) : f=g := by
  cases f
  cases g
  congr
  exact funext h
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Filter
open scoped Topology ContDiff

open Filter MeasureTheory Set
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressSmoothness
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set

open Filter MeasureTheory Set
open scoped Topology ContDiff

open Filter MeasureTheory Set
open scoped Topology ContDiff

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
def constant (c : ℂ) : SmoothCircleFunction where
  toFun := fun _ => c
  periodic := fun _ => rfl
  smooth := contDiff_const
@[simp] lemma constant_apply (c : ℂ) (x : ℝ) : constant c x=c := rfl
end StronglyRationalVOA.SmoothCircleFunction

open Filter UniformSpace
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
@[simp] lemma stressPropagatorSmooth_zero (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (y : U.smoothEnergySpace) : U.stressPropagatorSmooth hc f 0 y=y := by
  apply Subtype.ext
  change U.stressPropagator hc f 0 y=(y:Completion V)
  rw [U.stressPropagator_zero hc f,one_apply_eq_self]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothEnergyPower
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.Field
variable (f : Field (2*Real.pi))
def smoothCircle : SmoothCircleFunction where
  toFun := fun x => (f x:ℂ)
  periodic := fun x => congrArg Complex.ofReal (f.periodic x)
  smooth := Complex.ofRealCLM.contDiff.comp f.smooth
@[simp] lemma smoothCircle_apply (x : ℝ) : f.smoothCircle x=(f x:ℂ) := rfl
end StronglyRationalVOA.PositiveCircleGeometry.Field

open Set MeasureTheory
open scoped ContDiff

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
def ofRealPeriodic (g : ℝ → ℝ) (hp : Function.Periodic g (2*Real.pi)) (hs : ContDiff ℝ ∞ g) : SmoothCircleFunction where
  toFun := fun x => (g x:ℂ)
  periodic := fun x => congrArg Complex.ofReal (hp x)
  smooth := Complex.ofRealCLM.contDiff.comp hs
@[simp] lemma ofRealPeriodic_apply (g : ℝ → ℝ) (hp : Function.Periodic g (2*Real.pi)) (hs : ContDiff ℝ ∞ g) (x : ℝ) :
    ofRealPeriodic g hp hs x=(g x:ℂ) := rfl
def quadraticFamily (g : SmoothCircleFunction) : SmoothCircleFamily where
  toFun t := (g.power 2).add (constant (t:ℂ))
  smooth := (g.smooth.comp contDiff_snd).pow 2 |>.add (Complex.ofRealCLM.contDiff.comp contDiff_fst)
@[simp] lemma quadraticFamily_zero (g : SmoothCircleFunction) : quadraticFamily g 0=g.power 2 := by
  apply ext
  intro x
  simp only [quadraticFamily,add_apply,power_apply,constant_apply,Complex.ofReal_zero,add_zero]
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Filter Set
open scoped Topology ContDiff

open UniformSpace Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)


structure PrimaryTestField where
  state : V
  weight : ℕ
  homogeneous : state ∈ A.grade weight
  quasiPrimary : A.IsQuasiPrimary state
  hermitian : U.IsHermitian weight state
  test : SmoothCircleFunction
  real : test.IsReal
  kind : weight = 1 ∨ (weight = 2 ∧ state = A.conformalVector) ∨
    (A.IsPrimary state ∧ 2 ≤ weight ∧ ∃ base : SmoothCircleFunction,
      base.IsReal ∧ test = (base.power 2).power (weight-1))
namespace PrimaryTestField
variable {U}
def field (F : U.PrimaryTestField) (hc : A.toVertexAlgebra.C2Cofinite) :=
  U.closedSmoothField hc F.state F.weight F.test
lemma closed (F : U.PrimaryTestField) (hc : A.toVertexAlgebra.C2Cofinite) :
    (F.field hc).IsClosed := U.closedSmoothField_isClosed hc F.homogeneous F.test
end PrimaryTestField
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_Locality
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

def primaryGraphData (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : Set (Completion V →L[ℂ] Completion V) :=
  {x | ∃ F : U.PrimaryTestField, tsupport F.test.onCircle ⊆ O ∧ ∃ i j : Bool,
    x = ClosedGraphData.entry (F.field hc) (F.closed hc) i j}


def primaryAlgebra (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : VonNeumannAlgebra (Completion V) :=
  LocalOperatorAlgebra.generated (U.primaryGraphData hc O)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set
open scoped Topology ContDiff

open Filter
open scoped Topology
namespace StronglyRationalVOA.HilbertScale
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]
 
def rotation (w : ι → ℝ) (t : ℝ) : Space G →L[ℂ] Space G :=
  boundedMultiplier (fun i => Complex.exp ((t*w i : ℝ)*Complex.I)) zero_le_one
    (fun _ => (Complex.norm_exp_ofReal_mul_I _).le)
@[simp] lemma rotation_apply (w : ι → ℝ) (t : ℝ) (x : Space G) (i : ι) :
    rotation w t x i = Complex.exp ((t*w i : ℝ)*Complex.I) • x i := rfl
variable [DecidableEq ι]
lemma rotation_single (w : ι → ℝ) (t : ℝ) (i : ι) (x : G i) :
    rotation w t (lp.single 2 i x) = Complex.exp ((t*w i : ℝ)*Complex.I) • lp.single 2 i x :=
  boundedMultiplier_single _ _ _ _ _
end StronglyRationalVOA.HilbertScale

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
local instance gradeFinite (d : ℕ) : FiniteDimensional ℂ (A.grade d) := A.grade_finite d
 
def rotation (t : ℝ) : Completion V →L[ℂ] Completion V :=
  U.energyCoordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((HilbertScale.rotation (fun d : ℕ => (d : ℝ)) t).comp
      U.energyCoordinates.toContinuousLinearEquiv.toContinuousLinearMap)
lemma rotation_coordinates (t : ℝ) (x : Completion V) :
    U.energyCoordinates (U.rotation t x) =
      HilbertScale.rotation (fun d : ℕ => (d : ℝ)) t (U.energyCoordinates x) := by
  simp only [rotation,ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.apply_symm_apply]
lemma rotation_grade (t : ℝ) {d : ℕ} (a : A.grade d) :
    U.rotation t (a.val : Completion V) = Complex.exp ((t*d : ℝ)*Complex.I) • (a.val : Completion V) := by
  apply U.energyCoordinates.injective
  rw [U.rotation_coordinates,map_smul,U.energyCoordinates_grade,HilbertScale.rotation_single]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.SmoothCircleFunction
open MeasureTheory AddCircle
local instance instFactLtRealOfNatHMulPi_1 : Fact (0 < 2*Real.pi) := ⟨period_pos⟩
 
def translate (f : SmoothCircleFunction) (t : ℝ) : SmoothCircleFunction :=
  ⟨fun s => f (s-t),fun s => by dsimp only; rw [show s+2*Real.pi-t=(s-t)+2*Real.pi by ring,f.periodic],
    f.smooth.comp (contDiff_id.sub contDiff_const)⟩
@[simp] lemma translate_apply (f : SmoothCircleFunction) (t s : ℝ) :
    f.translate t s = f (s-t) := rfl
lemma translate_onCircle (f : SmoothCircleFunction) (t : ℝ) (s : AddCircle (2*Real.pi)) :
    (f.translate t).onCircle s = f.onCircle (s-(t : AddCircle (2*Real.pi))) := by
  induction s using QuotientAddGroup.induction_on
  rename_i s
  change f (s-t) = f.onCircle ((s : AddCircle (2*Real.pi))-(t : AddCircle (2*Real.pi)))
  rw [← QuotientAddGroup.mk_sub]
  rfl
lemma translate_coefficient (f : SmoothCircleFunction) (t : ℝ) (n : ℤ) :
    (f.translate t).coefficient n = Complex.exp (-((t*(n : ℝ) : ℝ)*Complex.I))*f.coefficient n := by
  rw [← fourierCoeff_toContinuousMap,← fourierCoeff_toContinuousMap]
  unfold fourierCoeff
  have ht := integral_add_right_eq_self (μ := (haarAddCircle : Measure (AddCircle (2*Real.pi))))
    (fun s : AddCircle (2*Real.pi) => fourier (-n) s • (f.translate t).toContinuousMap s)
    (t : AddCircle (2*Real.pi))
  rw [← ht]
  have hchar (s : AddCircle (2*Real.pi)) : fourier (-n) (s+(t : AddCircle (2*Real.pi))) =
      Complex.exp (-((t*(n : ℝ) : ℝ)*Complex.I))*fourier (-n) s := by
    rw [fourier_apply,smul_add,toCircle_add,Circle.coe_mul,← fourier_apply,← fourier_apply,
      fourier_coe_apply]
    have hpi : (2*(Real.pi : ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt period_pos)
    rw [mul_comm]
    congr 1
    congr 1
    push_cast
    field_simp
  calc
    _ = ∫ s : AddCircle (2*Real.pi),
        Complex.exp (-((t*(n : ℝ) : ℝ)*Complex.I))*(fourier (-n) s • f.toContinuousMap s) ∂haarAddCircle := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro s
      dsimp only
      rw [hchar]
      change (Complex.exp _*fourier (-n) s)*(f.translate t).onCircle (s+(t : AddCircle (2*Real.pi))) = _
      rw [translate_onCircle,add_sub_cancel_right]
      simp only [smul_eq_mul,mul_assoc]
      rfl
    _ = _ := integral_const_mul _ _
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma rotation_physicalMode_grade {a v : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hv : v ∈ A.grade e) (m : ℤ) (t : ℝ) :
    U.rotation t (A.physicalMode a d m v : Completion V) =
      Complex.exp ((t*((e : ℝ)-(m : ℝ)) : ℝ)*Complex.I) • (A.physicalMode a d m v : Completion V) := by
  by_cases hm : (e : ℤ) < m
  · have hz : A.physicalMode a d m v = 0 := A.mode_eq_zero_of_negative_energy ha hv _ (by omega)
    rw [hz,Completion.coe_zero,map_zero,smul_zero]
  · have hmode : A.physicalMode a d m v ∈ A.grade ((e : ℤ)-m).toNat :=
      A.mode_mem_grade ha hv _ (by omega)
    rw [U.rotation_grade t ⟨_,hmode⟩]
    have he : (((e : ℤ)-m).toNat : ℝ) = (e : ℝ)-(m : ℝ) := by
      have he0 : (((e : ℤ)-m).toNat : ℤ) = (e : ℤ)-m := Int.toNat_of_nonneg (by omega)
      exact_mod_cast he0
    rw [he]
lemma rotation_smearedMap_grade (hc : A.toVertexAlgebra.C2Cofinite) {a v : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hv : v ∈ A.grade e) (f : SmoothCircleFunction) (t : ℝ) :
    U.rotation t (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients v) =
      Complex.exp ((t*(e : ℝ) : ℝ)*Complex.I) •
        A.smearedMap a d (U.polynomialEnergyBounds hc a) (f.translate t).coefficient
          (f.translate t).rapid_coefficients v := by
  rw [A.smearedMap_apply,A.smearedMap_apply,
    (U.rotation t).map_tsum (A.summable_norm_physicalSmear (U.polynomialEnergyBounds hc a) d f.rapid_coefficients v).of_norm,
    ← tsum_const_smul'']
  apply tsum_congr
  intro m
  rw [map_smul,U.rotation_physicalMode_grade ha hv, SmoothCircleFunction.translate_coefficient,smul_smul,smul_smul]
  congr 1
  have he : Complex.exp ((t*((e : ℝ)-(m : ℝ)) : ℝ)*Complex.I) =
      Complex.exp ((t*(e : ℝ) : ℝ)*Complex.I)*Complex.exp (-((t*(m : ℝ) : ℝ)*Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring
lemma rotation_smearedCore_graph (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f : SmoothCircleFunction) (t : ℝ) (v : V) :
    (U.rotation t (v : Completion V),
      U.rotation t (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients v)) ∈
      (U.closedSmoothField hc a d (f.translate t)).graph := by
  apply A.homogeneous_induction (P := fun v =>
    (U.rotation t (v : Completion V),
      U.rotation t (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients v)) ∈
      (U.closedSmoothField hc a d (f.translate t)).graph)
  · simp only [Completion.coe_zero,map_zero]
    exact (U.closedSmoothField hc a d (f.translate t)).graph.zero_mem
  · intro e v hv
    rw [U.rotation_grade t ⟨v,hv⟩,U.rotation_smearedMap_grade hc ha hv]
    have hg : ((v : Completion V),A.smearedMap a d (U.polynomialEnergyBounds hc a)
        (f.translate t).coefficient (f.translate t).rapid_coefficients v) ∈
        (U.closedSmoothField hc a d (f.translate t)).graph := by
      apply LinearPMap.le_graph_of_le (U.smoothSmearedField hc a d (f.translate t)).le_closure
      exact (U.smoothSmearedField hc a d (f.translate t)).mem_graph_iff.mpr
        ⟨HilbertCore.equiv V v,rfl,HilbertCore.operator_apply _ v⟩
    exact (U.closedSmoothField hc a d (f.translate t)).graph.smul_mem _ hg
  · intro x y hx hy
    simp only [Completion.coe_add,map_add]
    exact (U.closedSmoothField hc a d (f.translate t)).graph.add_mem hx hy
 
lemma rotation_closedSmoothField_graph (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f : SmoothCircleFunction) (t : ℝ) {x y : Completion V}
    (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (U.rotation t x,U.rotation t y) ∈ (U.closedSmoothField hc a d (f.translate t)).graph := by
  have hclosed : IsClosed {p : Completion V × Completion V |
      (U.rotation t p.1,U.rotation t p.2) ∈ (U.closedSmoothField hc a d (f.translate t)).graph} :=
    (U.closedSmoothField_isClosed hc ha (f.translate t)).preimage
      (((U.rotation t).continuous.comp continuous_fst).prodMk
        ((U.rotation t).continuous.comp continuous_snd))
  change (x,y) ∈ ((U.closedSmoothField hc a d f).graph : Set _) at hxy
  rw [U.closedSmoothField_graph hc ha f] at hxy
  apply (closure_minimal (s := ((U.smoothSmearedField hc a d f).graph : Set _)) ?_ hclosed) hxy
  rintro p hp
  obtain ⟨v,hv,hy⟩ := (U.smoothSmearedField hc a d f).mem_graph_iff.mp hp
  obtain ⟨v,rfl⟩ := (HilbertCore.equiv V).surjective v
  obtain rfl : p = ((v : Completion V),A.smearedMap a d (U.polynomialEnergyBounds hc a)
      f.coefficient f.rapid_coefficients v) := by
    ext
    · exact hv.symm
    · exact hy.symm.trans (HilbertCore.operator_apply _ v)
  exact U.rotation_smearedCore_graph hc ha f t v
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
namespace StronglyRationalVOA.SmoothCircleFunction
@[simp] lemma translate_zero (f : SmoothCircleFunction) : f.translate 0 = f := by
  ext s
  simp only [translate_apply,sub_zero]
lemma translate_add (f : SmoothCircleFunction) (s t : ℝ) :
    (f.translate s).translate t = f.translate (s+t) := by
  ext r
  simp only [translate_apply]
  congr 1
  ring
end StronglyRationalVOA.SmoothCircleFunction

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GraphInvariantOf
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma flow_eigenvector (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) {x : H} (μ : ℝ)
    (hg : (x,(μ : ℂ) • x) ∈ T.graph) (t : ℝ) :
    flow T hs t x = Complex.exp ((t*μ : ℝ)*Complex.I) • x := by
  let z : ℂ := (μ : ℂ)*Complex.I
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => Complex.exp (-(r : ℂ)*z) • flow T hs r x) 0 s := by
    have he : HasDerivAt (fun r : ℝ => Complex.exp (-(r : ℂ)*z))
        (Complex.exp (-(s : ℂ)*z)*(-z)) s := by
      convert (((hasDerivAt_id s).ofReal_comp.neg).mul_const z).cexp using 1 <;> simp
    have h := he.smul (flow_derivative T hs hg s)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [map_smul,map_smul,smul_smul,smul_smul,← add_smul]
    dsimp only [z]
    convert (zero_smul ℂ (flow T hs s x)).symm using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simp only [Complex.ofReal_zero,neg_zero,zero_mul,Complex.exp_zero,flow_zero,
    one_apply_eq_self,one_smul] at he
  have h := congrArg (fun v : H => Complex.exp ((t : ℂ)*z) • v) he
  have hm : Complex.exp ((t : ℂ)*z)*Complex.exp (-(t : ℂ)*z)=1 := by
    rw [← Complex.exp_add,← add_mul,add_neg_cancel,zero_mul,Complex.exp_zero]
  rw [smul_smul,hm,one_smul] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [z]
  push_cast
  ring_nf
end StronglyRationalVOA.SymmetricOperator
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma rotation_eq_hamiltonianFlow (t : ℝ) : U.rotation t =
    SymmetricOperator.flow U.conformalHamiltonian (U.energyOperator_selfAdjoint (fun d => d)) t := by
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.denseRange_coe.induction_on x ?_ ?_
  · exact isClosed_eq (U.rotation t).continuous (SymmetricOperator.flow _ _ t).continuous
  · intro v
    apply A.homogeneous_induction (P := fun v => U.rotation t (v : Completion V) =
      SymmetricOperator.flow U.conformalHamiltonian (U.energyOperator_selfAdjoint (fun d => d)) t (v : Completion V))
    · simp only [Completion.coe_zero,map_zero]
    · intro e v hv
      rw [U.rotation_grade t ⟨v,hv⟩]
      symm
      apply SymmetricOperator.flow_eigenvector
      exact U.conformalHamiltonian.mem_graph_iff.mpr
        ⟨⟨(v : Completion V),U.coe_mem_energyOperator (fun d => d) v⟩,rfl,U.energyOperator_grade _ ⟨v,hv⟩⟩
    · intro a b ha hb
      simp only [Completion.coe_add,map_add,ha,hb]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma energyOperator_graph_iff (w : ℕ → ℝ) (x y : Completion V) :
    (x,y) ∈ (U.energyOperator w).graph ↔
      ∀ d, U.energyCoordinates y d = (w d : ℂ) • U.energyCoordinates x d := by
  rw [energyOperator,OperatorTransport.mem_graph_iff,HilbertScale.mem_graph_iff]
lemma energyPower_graph_iff_inverse (k : ℕ) (x y : Completion V) :
    (x,y) ∈ (U.energyPower k).graph ↔ U.inverseSobolev k y=x := by
  constructor
  · exact U.inverseSobolev_on_graph k
  · intro h
    simpa only [h] using U.inverseSobolev_graph k y
lemma energyPower_add_graph (k l : ℕ) (x z : Completion V) :
    (x,z) ∈ (U.energyPower (k+l)).graph ↔
      ∃ y, (x,y) ∈ (U.energyPower k).graph ∧ (y,z) ∈ (U.energyPower l).graph := by
  simp_rw [U.energyPower_graph_iff_inverse]
  constructor
  · intro h
    refine ⟨U.inverseSobolev l z,?_,rfl⟩
    change (U.inverseSobolev k*U.inverseSobolev l) z=x
    rwa [U.inverseSobolev_mul]
  · rintro ⟨y,hxy,hyz⟩
    rw [← U.inverseSobolev_mul]
    change U.inverseSobolev k (U.inverseSobolev l z)=x
    rw [hyz,hxy]
lemma energyPower_domain_le {k l : ℕ} (hkl : k ≤ l) :
    (U.energyPower l).domain ≤ (U.energyPower k).domain := by
  intro x hx
  have h : (x,(U.energyPower l) ⟨x,hx⟩) ∈ (U.energyPower l).graph :=
    (U.energyPower l).mem_graph_iff.mpr ⟨⟨x,hx⟩,rfl,rfl⟩
  have h' : (x,(U.energyPower l) ⟨x,hx⟩) ∈ (U.energyPower (k+(l-k))).graph := by
    simpa only [Nat.add_sub_of_le hkl] using h
  rw [U.energyPower_add_graph] at h'
  obtain ⟨y,hy,_⟩ := h'
  exact LinearPMap.mem_domain_of_mem_graph hy
lemma energyOne_graph_iff (x y : Completion V) :
    (x,y) ∈ (U.energyPower 1).graph ↔ (x,y-x) ∈ U.conformalHamiltonian.graph := by
  change (x,y) ∈ (U.energyOperator (fun d => (1+(d:ℝ))^1)).graph ↔
    (x,y-x) ∈ (U.energyOperator (fun d => d)).graph
  rw [U.energyOperator_graph_iff,U.energyOperator_graph_iff]
  simp only [pow_one,map_sub,lp.coeFn_sub,Pi.sub_apply,Complex.ofReal_add,
    Complex.ofReal_one,Complex.ofReal_natCast]
  constructor
  · intro h d
    rw [h d,add_smul,one_smul]
    abel
  · intro h d
    have hh := h d
    rw [add_smul,one_smul]
    exact eq_add_of_sub_eq' hh
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter MeasureTheory
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def conjugation (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  flow T hs t * Q * flow T hs (-t)
lemma conjugation_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H) (t : ℝ) (x : H) :
    ‖conjugation T hs Q t x‖ ≤ ‖Q‖*‖x‖ := by
  change ‖flow T hs t (Q (flow T hs (-t) x))‖ ≤ _
  rw [flow_norm]
  simpa only [flow_norm] using Q.le_opNorm (flow T hs (-t) x)
lemma conjugation_continuous (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H) (x : H) :
    Continuous (fun t : ℝ => conjugation T hs Q t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact StrongLimit.apply_tendsto (fun s => flow T hs s) (flow T hs t)
    (flow_opNorm T hs) (fun x => (flow_continuous T hs x).tendsto t)
    (Q.continuous.tendsto _ |>.comp (((flow_continuous T hs x).comp continuous_neg).tendsto t))
lemma conjugation_inner (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H) (t : ℝ) (x y : H) :
    inner ℂ x (conjugation T hs Q t y) = inner ℂ (flow T hs (-t) x) (Q (flow T hs (-t) y)) := by
  change inner ℂ x (flow T hs t (Q (flow T hs (-t) y))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left,flow_adjoint]
lemma conjugation_matrix_derivative (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    {u v x y : H} (huv : (u,v) ∈ T.graph) (hxy : (x,y) ∈ T.graph) (t : ℝ) :
    HasDerivAt (fun s : ℝ => inner ℂ u (conjugation T hs Q s x))
      (Complex.I*inner ℂ v (conjugation T hs Q t x) -
        Complex.I*inner ℂ u (conjugation T hs Q t y)) t := by
  have hv := (flow_derivative T hs huv (-t)).scomp t (hasDerivAt_neg t)
  have hx := (flow_derivative T hs hxy (-t)).scomp t (hasDerivAt_neg t)
  have h := HasDerivAt.inner ℂ hv ((Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hx)
  change HasDerivAt (fun s : ℝ => inner ℂ (flow T hs (-s) u) (Q (flow T hs (-s) x)))
    (inner ℂ (flow T hs (-t) u) (Q ((-1 : ℝ) • flow T hs (-t) (Complex.I • y))) +
      inner ℂ ((-1 : ℝ) • flow T hs (-t) (Complex.I • v)) (Q (flow T hs (-t) x))) t at h
  simp only [neg_one_smul,map_neg,map_smul,inner_neg_left,inner_neg_right,
    inner_smul_left,inner_smul_right,Complex.conj_I,neg_mul,neg_neg] at h
  simpa only [conjugation_inner,sub_eq_add_neg,add_comm] using h
 

def conjugationIntegral (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (a b : ℝ) (f : ℝ → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => ∫ t in a..b, f t • conjugation T hs Q t x
      map_add' := fun x y => by
        simp only [map_add,smul_add]
        exact intervalIntegral.integral_add
          ((hf.smul (conjugation_continuous T hs Q x)).intervalIntegrable a b)
          ((hf.smul (conjugation_continuous T hs Q y)).intervalIntegrable a b)
      map_smul' := fun c x => by
        simp only [map_smul,smul_comm (f _) c]
        exact intervalIntegral.integral_smul c _ }
    (C*‖Q‖*|b-a|) (fun x => by
      change ‖∫ t in a..b, f t • conjugation T hs Q t x‖ ≤ _
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
      calc
        _ ≤ (C*‖Q‖*‖x‖)*|b-a| := intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => by
          rw [norm_smul]
          calc
            _ ≤ C*(‖Q‖*‖x‖) := mul_le_mul (hC t) (conjugation_norm T hs Q t x) (norm_nonneg _) hC0
            _ = _ := by ring)
        _ = _ := by ring)
lemma inner_conjugationIntegral (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (a b : ℝ) (f : ℝ → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C) (u x : H) :
    inner ℂ u (conjugationIntegral T hs Q a b f hf C hC x) =
      ∫ t in a..b, f t * inner ℂ u (conjugation T hs Q t x) := by
  have h := (innerSL ℂ u).intervalIntegral_comp_comm (μ := volume)
    ((hf.smul (conjugation_continuous T hs Q x)).intervalIntegrable a b)
  change (∫ t in a..b, inner ℂ u (f t • conjugation T hs Q t x)) =
    inner ℂ u (conjugationIntegral T hs Q a b f hf C hC x) at h
  simpa only [inner_smul_right] using h.symm
 

lemma conjugationIntegral_generator_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (a b : ℝ) (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (Cf Cg : ℝ) (hCf : ∀ t, ‖f t‖ ≤ Cf) (hCg : ∀ t, ‖g t‖ ≤ Cg)
    (hd : ∀ t, HasDerivAt f (g t) t) (hfa : f a=0) (hfb : f b=0)
    {x y : H} (hxy : (x,y) ∈ T.graph) :
    (conjugationIntegral T hs Q a b f hf Cf hCf x,
      conjugationIntegral T hs Q a b f hf Cf hCf y +
        Complex.I • conjugationIntegral T hs Q a b g hg Cg hCg x) ∈ T.graph := by
  rw [show T.graph = T.adjoint.graph from congrArg LinearPMap.graph hs.symm,
    LinearPMap.adjoint_graph_eq_graph_adjoint hs.dense_domain]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro u v huv
  have hh (t : ℝ) := (hd t).mul (conjugation_matrix_derivative T hs Q huv hxy t)
  let D : ℝ → ℂ := fun t => Complex.I*(f t * inner ℂ v (conjugation T hs Q t x)) -
    Complex.I*(f t * inner ℂ u (conjugation T hs Q t y)) + g t*inner ℂ u (conjugation T hs Q t x)
  have he (t : ℝ) : HasDerivAt (fun s => f s * inner ℂ u (conjugation T hs Q s x)) (D t) t := by
    exact (hh t).congr_deriv (by dsimp only [D]; ring)
  have hc1 : Continuous (fun t => f t*inner ℂ v (conjugation T hs Q t x)) :=
    hf.mul (continuous_const.inner (conjugation_continuous T hs Q x))
  have hc2 : Continuous (fun t => f t*inner ℂ u (conjugation T hs Q t y)) :=
    hf.mul (continuous_const.inner (conjugation_continuous T hs Q y))
  have hc3 : Continuous (fun t => g t*inner ℂ u (conjugation T hs Q t x)) :=
    hg.mul (continuous_const.inner (conjugation_continuous T hs Q x))
  have hdc : Continuous D := ((continuous_const.mul hc1).sub (continuous_const.mul hc2)).add hc3
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => he t) (hdc.intervalIntegrable a b)
  simp only [hfa,hfb,zero_mul,sub_zero] at h
  dsimp only [D] at h
  have hi1 : IntervalIntegrable (fun t => Complex.I*(f t*inner ℂ v (conjugation T hs Q t x))) volume a b :=
    (continuous_const.mul hc1).intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun t => Complex.I*(f t*inner ℂ u (conjugation T hs Q t y))) volume a b :=
    (continuous_const.mul hc2).intervalIntegrable a b
  rw [intervalIntegral.integral_add (hi1.sub hi2) (hc3.intervalIntegrable a b),
    intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    ← inner_conjugationIntegral T hs Q a b f hf Cf hCf v x,
    ← inner_conjugationIntegral T hs Q a b f hf Cf hCf u y,
    ← inner_conjugationIntegral T hs Q a b g hg Cg hCg u x] at h
  simp only [inner_add_right,inner_smul_right]
  linear_combination (norm := (ring_nf; simp [Complex.I_sq])) (-Complex.I) * h
 

lemma conjugationIntegral_preserves_graph (T S : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (hS : S.IsClosed) (Q : H →L[ℂ] H) (a b : ℝ) (f : ℝ → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C)
    (hi : ∀ t, f t ≠ 0 → ∀ x y, (x,y) ∈ S.graph →
      (conjugation T hs Q t x,conjugation T hs Q t y) ∈ S.graph)
    {x y : H} (hxy : (x,y) ∈ S.graph) :
    (conjugationIntegral T hs Q a b f hf C hC x,
      conjugationIntegral T hs Q a b f hf C hC y) ∈ S.graph := by
  have hfc : Continuous (fun t => (f t • conjugation T hs Q t x,f t • conjugation T hs Q t y)) :=
    (hf.smul (conjugation_continuous T hs Q x)).prodMk (hf.smul (conjugation_continuous T hs Q y))
  have h := intervalIntegral_mem_closedSubmodule S.graph hS (hfc.intervalIntegrable a b) (fun t => ?_)
  · have he : (∫ t in a..b,(f t • conjugation T hs Q t x,f t • conjugation T hs Q t y)) =
        (conjugationIntegral T hs Q a b f hf C hC x,
          conjugationIntegral T hs Q a b f hf C hC y) := by
      apply Prod.ext
      · exact ((ContinuousLinearMap.fst ℂ H H).intervalIntegral_comp_comm (hfc.intervalIntegrable a b)).symm
      · exact ((ContinuousLinearMap.snd ℂ H H).intervalIntegral_comp_comm (hfc.intervalIntegrable a b)).symm
    rwa [he] at h
  · by_cases ht : f t=0
    · simp only [ht,zero_smul]
      exact S.graph.zero_mem
    · exact S.graph.smul_mem (f t) (hi t ht x y hxy)
end StronglyRationalVOA.SymmetricOperator

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma conjugationIntegral_energy_domain (Q : Completion V →L[ℂ] Completion V)
    (a b : ℝ) (f : ℕ → ℝ → ℂ) (hf : ∀ j, Continuous (f j))
    (C : ℕ → ℝ) (hC : ∀ j t, ‖f j t‖ ≤ C j)
    (hd : ∀ j t, HasDerivAt (f j) (f (j+1) t) t)
    (ha : ∀ j, f j a=0) (hb : ∀ j, f j b=0) :
    ∀ k j (x : Completion V), x ∈ (U.energyPower k).domain →
      SymmetricOperator.conjugationIntegral U.conformalHamiltonian
        (U.energyOperator_selfAdjoint (fun d => d)) Q a b (f j) (hf j) (C j) (hC j) x ∈
          (U.energyPower k).domain := by
  let F (j : ℕ) := SymmetricOperator.conjugationIntegral U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q a b (f j) (hf j) (C j) (hC j)
  intro k
  induction k with
  | zero =>
      intro j x _
      exact LinearPMap.mem_domain_of_mem_graph (U.energyPower_zero_graph (F j x))
  | succ k ih =>
      intro j x hx
      change F j x ∈ (U.energyPower (k+1)).domain
      obtain ⟨z,hxz⟩ := LinearPMap.mem_domain_iff.mp hx
      have hsplit : (x,z) ∈ (U.energyPower (1+k)).graph := by
        simpa only [Nat.add_comm] using hxz
      rw [U.energyPower_add_graph] at hsplit
      obtain ⟨y,hxy,hyz⟩ := hsplit
      have hxk := U.energyPower_domain_le (Nat.le_succ k) hx
      have hyk : y ∈ (U.energyPower k).domain := LinearPMap.mem_domain_of_mem_graph hyz
      have hcomm := SymmetricOperator.conjugationIntegral_generator_graph U.conformalHamiltonian
        (U.energyOperator_selfAdjoint (fun d => d)) Q a b (f j) (f (j+1))
        (hf j) (hf (j+1)) (C j) (C (j+1)) (hC j) (hC (j+1))
        (hd j) (ha j) (hb j) ((U.energyOne_graph_iff x y).mp hxy)
      change (F j x,F j (y-x)+Complex.I • F (j+1) x) ∈ U.conformalHamiltonian.graph at hcomm
      have h1 : (F j x,F j y+Complex.I • F (j+1) x) ∈ (U.energyPower 1).graph := by
        rw [U.energyOne_graph_iff]
        simpa only [map_sub,sub_add_eq_add_sub] using hcomm
      have hu : F j y+Complex.I • F (j+1) x ∈ (U.energyPower k).domain :=
        (U.energyPower k).domain.add_mem (ih j y hyk)
          ((U.energyPower k).domain.smul_mem Complex.I (ih (j+1) x hxk))
      obtain ⟨w,huw⟩ := LinearPMap.mem_domain_iff.mp hu
      have hfull := (U.energyPower_add_graph 1 k (F j x) w).mpr ⟨_,h1,huw⟩
      apply LinearPMap.mem_domain_of_mem_graph
      simpa only [Nat.add_comm] using hfull
lemma conjugationIntegral_smooth (Q : Completion V →L[ℂ] Completion V)
    (a b : ℝ) (f : ℕ → ℝ → ℂ) (hf : ∀ j, Continuous (f j))
    (C : ℕ → ℝ) (hC : ∀ j t, ‖f j t‖ ≤ C j)
    (hd : ∀ j t, HasDerivAt (f j) (f (j+1) t) t)
    (ha : ∀ j, f j a=0) (hb : ∀ j, f j b=0)
    (j : ℕ) {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    SymmetricOperator.conjugationIntegral U.conformalHamiltonian
      (U.energyOperator_selfAdjoint (fun d => d)) Q a b (f j) (hf j) (C j) (hC j) x ∈
        U.smoothEnergySpace := by
  rw [smoothEnergySpace,Submodule.mem_iInf] at hx ⊢
  exact fun k => U.conjugationIntegral_energy_domain Q a b f hf C hC hd ha hb k j x (hx k)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open MeasureTheory Filter
open scoped Topology ContDiff

open MeasureTheory Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open SmoothRotationKernel
 
def smoothConjugate (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (ε : ℝ) (hε : 0 < ε) : H →L[ℂ] H :=
  conjugationIntegral T hs Q (-2*ε) (2*ε) (jet ε hε 0)
    (jet_continuous ε hε 0) (bound ε hε 0) (norm_le_bound ε hε 0)
lemma smoothConjugate_apply (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (ε : ℝ) (hε : 0 < ε) (x : H) :
    smoothConjugate T hs Q ε hε x = ∫ t, kernel ε hε t • conjugation T hs Q t x := by
  change (∫ t in (-2*ε)..(2*ε), (kernel ε hε t : ℂ) • conjugation T hs Q t x)=_
  simp_rw [Complex.coe_smul]
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro t ht
  have hk : kernel ε hε t ≠ 0 := fun h => ht (by simp only [h,zero_smul])
  have hb := (support ε hε).le hk
  simp only [Metric.mem_ball,Real.dist_eq,sub_zero] at hb
  exact ⟨by linarith [(abs_lt.mp hb).1],by linarith [(abs_lt.mp hb).2]⟩
lemma smoothConjugate_strong (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hl : Tendsto r atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => smoothConjugate T hs Q (r n) (hr n) x) atTop (𝓝 (Q x)) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (φ := fun n => bump (r n) (hr n)) hl
    ((conjugation_continuous T hs Q x).comp continuous_neg) (0 : ℝ)
  simp only [convolution_def,Function.comp_apply,zero_sub,neg_neg,ContinuousLinearMap.lsmul_apply] at h
  simpa only [smoothConjugate_apply,kernel,conjugation,neg_zero,flow_zero,mul_one,one_mul] using h
end StronglyRationalVOA.SymmetricOperator
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace SmoothRotationKernel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothConjugate_smooth (Q : Completion V →L[ℂ] Completion V) (ε : ℝ) (hε : 0 < ε)
    {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    SymmetricOperator.smoothConjugate U.conformalHamiltonian
      (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε x ∈ U.smoothEnergySpace := by
  exact U.conjugationIntegral_smooth Q (-2*ε) (2*ε) (jet ε hε)
    (jet_continuous ε hε) (bound ε hε) (norm_le_bound ε hε) (jet_derivative ε hε)
    (fun j => jet_vanish ε hε j (by rw [abs_mul,abs_of_pos hε]; norm_num; linarith))
    (fun j => jet_vanish ε hε j (by rw [abs_mul,abs_of_pos hε]; norm_num; linarith)) 0 hx
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open MeasureTheory Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothConjugateInner
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter

open Set MeasureTheory Filter UniformSpace
open scoped Topology
namespace StronglyRationalVOA.SmoothCircleFunction
local instance smoothConjugateInnerPeriodPos : Fact (0 < 2*Real.pi) := ⟨period_pos⟩
lemma translate_tsupport_subset (f : SmoothCircleFunction) (t : ℝ) :
    tsupport (f.translate t).onCircle ⊆
      (fun x : AddCircle (2*Real.pi) => x-(t : AddCircle (2*Real.pi))) ⁻¹' tsupport f.onCircle := by
  apply closure_minimal
  · intro x hx
    exact subset_closure (by simpa only [Function.mem_support,translate_onCircle] using hx)
  · exact isClosed_closure.preimage (continuous_id.sub continuous_const)
 

lemma exists_translation_radius (f : SmoothCircleFunction) {O : Set (AddCircle (2*Real.pi))}
    (hO : IsOpen O) (hf : tsupport f.onCircle ⊆ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → tsupport (f.translate t).onCircle ⊆ O := by
  let N : Set (ℝ × AddCircle (2*Real.pi)) :=
    (fun z => z.2+(z.1 : AddCircle (2*Real.pi))) ⁻¹' O
  have hc : Continuous (fun t : ℝ => (t : AddCircle (2*Real.pi))) := continuous_quotient_mk'
  have hN : IsOpen N := hO.preimage (continuous_snd.add (hc.comp continuous_fst))
  have hsub : ({0} : Set ℝ) ×ˢ tsupport f.onCircle ⊆ N := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    have ht0 : t=0 := ht
    subst t
    change x+(0 : AddCircle (2*Real.pi)) ∈ O
    simpa only [add_zero] using hf hx
  obtain ⟨u,v,hu,_,h0,hf',huv⟩ := generalized_tube_lemma isCompact_singleton
    isClosed_closure.isCompact hN hsub
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds (h0 (by rfl)))
  refine ⟨ε,hε,fun t ht x hx => ?_⟩
  have ht' : t ∈ u := he (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)
  have hx' := f.translate_tsupport_subset t hx
  have h : (t,x-(t : AddCircle (2*Real.pi))) ∈ N := huv ⟨ht',hf' hx'⟩
  change x-(t : AddCircle (2*Real.pi))+(t : AddCircle (2*Real.pi)) ∈ O at h
  simpa only [sub_add_cancel] using h
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma conjugation_preserves_field_graph (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f : SmoothCircleFunction) (t : ℝ)
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d (f.translate (-t))).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d (f.translate (-t))).graph)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (SymmetricOperator.conjugation U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q t x,
     SymmetricOperator.conjugation U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q t y) ∈
      (U.closedSmoothField hc a d f).graph := by
  have h := U.rotation_closedSmoothField_graph hc ha (f.translate (-t)) t
    (hQ _ _ (U.rotation_closedSmoothField_graph hc ha f (-t) hxy))
  simpa only [SmoothCircleFunction.translate_add,neg_add_cancel,SmoothCircleFunction.translate_zero,
    SymmetricOperator.conjugation,← U.rotation_eq_hamiltonianFlow,mul_apply_eq_comp] using h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace

open Set UniformSpace Filter
open scoped Topology

open Set MeasureTheory Filter
open scoped Topology ContDiff

open Set UniformSpace
open scoped Topology

open Set UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothConjugatePrimary
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
lemma smearedMap_add_state {a b : V} (ha : A.PolynomialEnergyBound a)
    (hb : A.PolynomialEnergyBound b) (hab : A.PolynomialEnergyBound (a+b))
    (d : ℕ) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    A.smearedMap (a+b) d hab f hf=A.smearedMap a d ha f hf+A.smearedMap b d hb f hf := by
  ext v
  simp only [smearedMap_apply,physicalMode,mode_add,LinearMap.add_apply,Completion.coe_add,smul_add]
  exact (A.summable_norm_physicalSmear ha d hf v).of_norm.tsum_add
    (A.summable_norm_physicalSmear hb d hf v).of_norm
lemma smearedMap_smul_state {a : V} (ha : A.PolynomialEnergyBound a) (c : ℂ)
    (hca : A.PolynomialEnergyBound (c • a)) (d : ℕ) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    A.smearedMap (c • a) d hca f hf=c • A.smearedMap a d ha f hf := by
  ext v
  simp only [smearedMap_apply,physicalMode,mode_smul,LinearMap.smul_apply,Completion.coe_smul,
    smul_comm (f _) c,tsum_const_smul'']
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
lemma sobolevExtension_add (r : ℕ) (M N : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^r) v‖) :
    U.sobolevExtension r (M+N)=U.sobolevExtension r M+U.sobolevExtension r N := by
  have hMN (v : V) : ‖(M+N) v‖ ≤ (C+D)*‖(A.energyShift^r) v‖ := by
    exact (norm_add_le (M v) (N v)).trans ((add_le_add (hM v) (hN v)).trans_eq (add_mul ..).symm)
  ext x
  have hd : DenseRange (fun v : V => (v : Completion V)) := Completion.denseRange_coe
  apply hd.induction_on (p := fun x => U.sobolevExtension r (M+N) x=(U.sobolevExtension r M+U.sobolevExtension r N) x) x
    (isClosed_eq (U.sobolevExtension r _).continuous (ContinuousLinearMap.continuous _))
  intro v
  simp only [add_apply,U.sobolevExtension_coe r _ hMN,
    U.sobolevExtension_coe r _ hM,U.sobolevExtension_coe r _ hN,LinearMap.add_apply]
lemma smoothSmear_add_state (hc : A.toVertexAlgebra.C2Cofinite) {a b : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    U.smoothSmear hc ((A.grade d).add_mem ha hb) hf=
      U.smoothSmear hc ha hf+U.smoothSmear hc hb hf := by
  obtain ⟨C,hC,p,k,hM⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hN⟩ := (U.polynomialEnergyBounds hc b).physical A d
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf
  let N := A.smearedMap b d (U.polynomialEnergyBounds hc b) f hf
  have hm (v : V) : ‖M v‖ ≤ (coefficientSeminorm f p*C)*‖(A.energyShift^(k+l)) v‖ :=
    (A.smearedMap_bound _ hf hM v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ k+l) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hC.le))
  have hn (v : V) : ‖N v‖ ≤ (coefficientSeminorm f q*D)*‖(A.energyShift^(k+l)) v‖ :=
    (A.smearedMap_bound _ hf hN v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : l ≤ k+l) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hD.le))
  have hmn (v : V) : ‖A.smearedMap (a+b) d (U.polynomialEnergyBounds hc (a+b)) f hf v‖ ≤
      (coefficientSeminorm f p*C+coefficientSeminorm f q*D)*‖(A.energyShift^(k+l)) v‖ := by
    rw [A.smearedMap_add_state (U.polynomialEnergyBounds hc a) (U.polynomialEnergyBounds hc b)]
    exact (norm_add_le (M v) (N v)).trans ((add_le_add (hm v) (hn v)).trans_eq (add_mul ..).symm)
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (U.smoothSmear hc _ hf x:Completion V)=
    (U.smoothSmear hc ha hf x:Completion V)+(U.smoothSmear hc hb hf x:Completion V)
  rw [U.smoothSmear_eq_extension hc _ hf hmn x (U.smoothEnergyPower_graph (k+l) x),
    U.smoothSmear_eq_extension hc ha hf hm x (U.smoothEnergyPower_graph (k+l) x),
    U.smoothSmear_eq_extension hc hb hf hn x (U.smoothEnergyPower_graph (k+l) x),
    A.smearedMap_add_state (U.polynomialEnergyBounds hc a) (U.polynomialEnergyBounds hc b),U.sobolevExtension_add (k+l) M N hm hn]
  rfl
lemma smoothSmear_smul_state (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (c : ℂ) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    U.smoothSmear hc ((A.grade d).smul_mem c ha) hf=c • U.smoothSmear hc ha hf := by
  obtain ⟨C,hC,p,k,hM⟩ := (U.polynomialEnergyBounds hc a).physical A d
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf
  have hm (v : V) : ‖M v‖ ≤ (coefficientSeminorm f p*C)*‖(A.energyShift^k) v‖ := A.smearedMap_bound _ hf hM v
  have hcm (v : V) : ‖A.smearedMap (c • a) d (U.polynomialEnergyBounds hc (c • a)) f hf v‖ ≤
      (‖c‖*(coefficientSeminorm f p*C))*‖(A.energyShift^k) v‖ := by
    rw [A.smearedMap_smul_state (U.polynomialEnergyBounds hc a)]
    simpa only [LinearMap.smul_apply,norm_smul,mul_assoc] using mul_le_mul_of_nonneg_left (hm v) (norm_nonneg c)
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (U.smoothSmear hc _ hf x:Completion V)=c • (U.smoothSmear hc ha hf x:Completion V)
  rw [U.smoothSmear_eq_extension hc _ hf hcm x (U.smoothEnergyPower_graph k x),
    U.smoothSmear_eq_extension hc ha hf hm x (U.smoothEnergyPower_graph k x),
    A.smearedMap_smul_state (U.polynomialEnergyBounds hc a),U.sobolevExtension_smul k M hm c]
  rfl
end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothSmear_zero_state (hc : A.toVertexAlgebra.C2Cofinite) (d : ℕ)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    U.smoothSmear hc ((A.grade d).zero_mem) hf=0 := by
  simpa only [zero_smul] using U.smoothSmear_smul_state hc ((A.grade d).zero_mem) (0:ℂ) hf
 
def stateCommutant (hc : A.toVertexAlgebra.C2Cofinite) (d : ℕ)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (R : Module.End ℂ U.smoothEnergySpace) : Submodule ℂ V where
  carrier := {a | ∃ ha : a ∈ A.grade d, U.smoothSmear hc ha hf*R=R*U.smoothSmear hc ha hf}
  zero_mem' := ⟨(A.grade d).zero_mem,by rw [U.smoothSmear_zero_state,zero_mul,mul_zero]⟩
  add_mem' := by
    rintro a b ⟨ha,hac⟩ ⟨hb,hbc⟩
    refine ⟨(A.grade d).add_mem ha hb,?_⟩
    rw [U.smoothSmear_add_state,add_mul,mul_add,hac,hbc]
  smul_mem' := by
    rintro c a ⟨ha,hac⟩
    refine ⟨(A.grade d).smul_mem c ha,?_⟩
    rw [U.smoothSmear_smul_state,smul_mul_assoc,mul_smul_comm,hac]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA
namespace RapidCoefficients
lemma shift {f : ℤ → ℂ} (hf : RapidCoefficients f) (j : ℤ) :
    RapidCoefficients (fun n => f (n-j)) := by
  intro p
  have hs : Summable (fun n : ℤ => ‖f (n-j)‖*(1+|((n-j:ℤ):ℝ)|)^p) :=
    (hf p).comp_injective (fun x y h => by omega)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hs.mul_right ((1+|(j:ℝ)|)^p))
  intro n
  calc
    _ ≤ ‖f (n-j)‖*((1+|((n-j:ℤ):ℝ)|)*(1+|(j:ℝ)|))^p := by
      gcongr
      exact frequency_weight_shift n j
    _ = _ := by rw [mul_pow]; ring
end RapidCoefficients
namespace CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
include U in
lemma physicalMode_bound_of_homogeneous {a : V} {d k : ℕ}
    (ha : a ∈ A.grade d) (n : ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h (v : V), v ∈ A.grade h →
      ‖A.physicalMode a d n v‖ ≤ C*(1+(h:ℝ))^k*‖v‖) (v : V) :
    ‖A.physicalMode a d n v‖ ≤ C*‖(A.energyShift^k) v‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [physicalMode,U.mode_norm_sq_eq_sum_grades ha]
  calc
    _ ≤ ∑ h ∈ A.gradeSupport v, (C*(1+(h:ℝ))^k*‖A.gradeComponent h v‖)^2 := by
      apply Finset.sum_le_sum
      intro h _
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        (hb h _ (A.gradeComponent_mem h v))
    _ = C^2*∑ h ∈ A.gradeSupport v, ((1+(h:ℝ))^k*‖A.gradeComponent h v‖)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by rw [← U.energy_norm_sq_eq_sum_grades]; ring
include U in
 

lemma physicalMode_positive_shift_bound {a : V} {d k p : ℕ}
    (ha : a ∈ A.grade d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    (R j : ℕ) (n : ℤ) (v : V) :
    ‖A.physicalMode a d n v‖ ≤
      (C*(1+|((n-(j:ℤ):ℤ):ℝ)|)^(p+R)*(1+(j:ℝ))^p/(1+(j:ℝ))^R)*
        ‖(A.energyShift^(k+R)) v‖ := by
  apply U.physicalMode_bound_of_homogeneous ha n (by positivity)
  intro h w hw
  by_cases hnh : (h:ℤ) < n
  · rw [show A.physicalMode a d n w=0 from A.mode_eq_zero_of_negative_energy ha hw _ (by omega),norm_zero]
    positivity
  have hjw : 1+(j:ℝ) ≤ (1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(h:ℝ)) := by
    have hh : (n:ℝ) ≤ h := by exact_mod_cast le_of_not_gt hnh
    have hab := neg_le_abs ((n:ℝ)-(j:ℝ))
    have hp := mul_nonneg (abs_nonneg ((n:ℝ)-(j:ℝ))) (Nat.cast_nonneg (α := ℝ) h)
    push_cast
    nlinarith
  have hnw : 1+|(n:ℝ)| ≤ (1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(j:ℝ)) := by
    simpa only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] using frequency_weight_shift n j
  have hjpos : 0 < (1+(j:ℝ))^R := pow_pos (by positivity) _
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
  apply (le_div_iff₀ hjpos).mpr
  have hz := hb n w
  rw [A.energyShift_pow_norm_on_grade hw] at hz
  calc
    ‖A.physicalMode a d n w‖*(1+(j:ℝ))^R ≤
        (C*(1+|(n:ℝ)|)^p*((1+(h:ℝ))^k*‖w‖))*
          ((1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(h:ℝ)))^R := by
      gcongr
    _ ≤ (C*((1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(j:ℝ)))^p*((1+(h:ℝ))^k*‖w‖))*
          ((1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(h:ℝ)))^R := by gcongr
    _ = _ := by simp only [mul_pow,pow_add]; ring
end CFTTypeVOA.UnitaryStructure
end StronglyRationalVOA

open UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_LocalNormalMap
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter

open Set

open Set

open UniformSpace

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

def LocalState (hc : A.toVertexAlgebra.C2Cofinite) (a : V) (d : ℕ) : Prop :=
  ∀ (O : Set (AddCircle (2*Real.pi))), IsOpen O → ∀ f : SmoothCircleFunction,
    tsupport f.onCircle ⊆ O → ∀ Q : Completion V →L[ℂ] Completion V,
    Q ∈ (U.primaryAlgebra hc O).commutant → ∀ x y,
    (x,y) ∈ (U.closedSmoothField hc a d f).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph
lemma smoothConjugate_localState_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hL : U.LocalState hc a d)
    (f : SmoothCircleFunction) {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (Q : Completion V →L[ℂ] Completion V) (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    (ε : ℝ) (hε : 0 < ε)
    (hs : ∀ t : ℝ, |t| < ε → tsupport (f.translate t).onCircle ⊆ O)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε x,
     SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε y) ∈
       (U.closedSmoothField hc a d f).graph := by
  apply SymmetricOperator.conjugationIntegral_preserves_graph _ _ _ (U.closedSmoothField_isClosed hc ha f)
    Q _ _ _ _ _ _ _ hxy
  intro t ht x y hxy
  have ht' : |t| < ε := by
    have hk : SmoothRotationKernel.kernel ε hε t ≠ 0 := by
      intro h
      exact ht (by simp only [SmoothRotationKernel.jet_zero,h,Complex.ofReal_zero])
    have h := (SmoothRotationKernel.support ε hε).le hk
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using h
  apply U.conjugation_preserves_field_graph hc ha f t Q _ hxy
  intro u v huv
  exact hL O hO (f.translate (-t)) (hs (-t) (by simpa only [abs_neg] using ht')) Q hQ u v huv
lemma LocalState.span (hc : A.toVertexAlgebra.C2Cofinite) (d : ℕ) {S : Set V}
    (hS : ∀ a ∈ S, a ∈ A.grade d ∧ U.LocalState hc a d)
    {a : V} (ha : a ∈ Submodule.span ℂ S) : U.LocalState hc a d := by
  have hgrade : Submodule.span ℂ S ≤ A.grade d := Submodule.span_le.mpr (fun a h => (hS a h).1)
  intro O hO f hf Q hQ x y hxy
  obtain ⟨ε,hε,hεF⟩ := f.exists_translation_radius hO hf
  let r : ℕ → ℝ := fun n => ε/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := div_pos hε (by positivity)
  have hrle (n : ℕ) : r n ≤ ε := div_le_self hε.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hl : Tendsto r atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
  let R (n : ℕ) := SymmetricOperator.smoothConjugate U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q (r n) (hr n)
  have hRn (n : ℕ) : (R n x,R n y) ∈ (U.closedSmoothField hc a d f).graph := by
    have hRs (z : U.smoothEnergySpace) : R n z ∈ U.smoothEnergySpace :=
      U.smoothConjugate_smooth Q (r n) (hr n) z.property
    let R' := SymmetricOperator.restricted U.smoothEnergySpace (R n) hRs
    have hSP : Submodule.span ℂ S ≤ U.stateCommutant hc d f.rapid_coefficients R' := by
      apply Submodule.span_le.mpr
      intro b hb
      obtain ⟨hbd,hLb⟩ := hS b hb
      refine ⟨hbd,?_⟩
      apply SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
        (U.smoothSmear hc hbd f.rapid_coefficients) (R n) hRs (U.closedSmoothField hc b d f)
        (U.smoothSmear_graph hc hbd f.rapid_coefficients)
      intro u v huv
      exact U.smoothConjugate_localState_graph hc hbd hLb f hO Q hQ (r n) (hr n)
        (fun t ht => hεF t (ht.trans_le (hrle n))) huv
    obtain ⟨_,hac⟩ := hSP ha
    have hce := U.smoothSmear_core hc (hgrade ha) f.rapid_coefficients
    change (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc (hgrade ha) f.rapid_coefficients)).closure =
      U.closedSmoothField hc a d f at hce
    rw [← hce] at hxy ⊢
    exact SymmetricOperator.onSubmodule_closure_graph_invariant _ _
      (U.smoothSmear_core_closable hc (hgrade ha) f.rapid_coefficients) (R n) hRs hac hxy
  exact (U.closedSmoothField_isClosed hc (hgrade ha) f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace

open UniformSpace Set Filter
open scoped Topology

open UniformSpace Set
open scoped Topology

open UniformSpace Set

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ObservableScalars
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
open UniformSpace Set Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma LocalState.add (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade d)
    (hLa : U.LocalState hc a d) (hLb : U.LocalState hc b d) :
    U.LocalState hc (a+b) d := by
  apply LocalState.span U hc d (S := {a,b})
  · intro c hc
    rcases Set.mem_insert_iff.mp hc with rfl | hc
    · exact ⟨ha,hLa⟩
    · rcases Set.mem_singleton_iff.mp hc with rfl
      exact ⟨hb,hLb⟩
  · exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set

open UniformSpace Set

open UniformSpace Set

open Set
open scoped Topology ContDiff

open UniformSpace Set Filter
open scoped Topology

open UniformSpace Set

end

end OAI
end


