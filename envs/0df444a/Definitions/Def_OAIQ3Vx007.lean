-- Prove2me | Definitions.Def_OAIQ3Vx007
-- name    : OAIQ3Vx007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:37:33.949805+00:00
-- url     : https://prove2.me/theorems/09dee62e-5a7e-498b-b52a-b651fdd74e81
-- title:
--   Definitions bundle OAIQ3Vx007 of the split of OpenAI, Strongly rational unitary vertex operator algebras and conformal nets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinimalVertex.main`, carved from OpenAI's openai/math development (OpenAI, *Strongly rational unitary vertex operator algebras and conformal nets*, OpenAI Math Release, September 25, 2026, result family 280, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 191 declarations of OpenAI's Lean: 27 definitions and 164 theorems. The definitions and types are `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.PrimaryTestField.translate`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.diffeomorphismDefect`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.diffeomorphismImplementer`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.diffeomorphismSmoothDefect`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.diffeomorphismSmoothImplementer`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.mobiusVacuumPhase`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.stressCutoffEvolutionSmooth`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.stressPropagatorDerivative`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.stressPropagatorEquiv`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.stressPropagatorSmoothEquiv`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.angularDensity`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.angularStressPath`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.angularVelocity`, `OAI.StronglyRationalVOA.SmoothCircleFamily.timeDerivative`, `OAI.StronglyRationalVOA.SmoothCircleFamily.toStressPath`, `OAI.StronglyRationalVOA.SmoothCircleFunction.cocycleDensity`, `OAI.StronglyRationalVOA.SmoothCircleFunction.imPart`, `OAI.StronglyRationalVOA.SmoothCircleFunction.powerFamily`, `OAI.StronglyRationalVOA.SmoothCircleFunction.primaryTransport`, `OAI.StronglyRationalVOA.SmoothCircleFunction.rePart`, `OAI.StronglyRationalVOA.SmoothCircleFunction.reciprocal`, `OAI.StronglyRationalVOA.SmoothCircleFunction.sumTests`, `OAI.StronglyRationalVOA.SmoothCircleLift.pushTest`, `OAI.StronglyRationalVOA.SmoothCircleLift.pushedTest`, `OAI.StronglyRationalVOA.SymmetricOperator.timeAverage`, `OAI.StronglyRationalVOA.SymmetricOperator.timeDifference`, `OAI.StronglyRationalVOA.SymmetricOperator.timeIntegral`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/VertexAlgebra, in whole or in part: `VertexAlgebra_ApproximatingFlowDerivative`, `VertexAlgebra_BoundedFlows`, `VertexAlgebra_BoundedMultiplierSingle`, `VertexAlgebra_CoefficientSummableBound`, `VertexAlgebra_CovarianceContinuation`, `VertexAlgebra_DiffeomorphismStressSmooth`, `VertexAlgebra_GeometryContinuation`, `VertexAlgebra_GraphCommutants`, `VertexAlgebra_GraphEquiv`, `VertexAlgebra_HighFieldGraph`, `VertexAlgebra_HilbertRegularization`, `VertexAlgebra_LocalImplementer`, `VertexAlgebra_LocalNormalMap`, `VertexAlgebra_Locality`, `VertexAlgebra_MobiusContinuity`, `VertexAlgebra_MobiusRepresentation`, `VertexAlgebra_MobiusStandardTopology`, `VertexAlgebra_MobiusVacuum`, `VertexAlgebra_NetVacuum`, `VertexAlgebra_ObservableScalars`, `VertexAlgebra_PrimaryStressWeak`, `VertexAlgebra_RegularizerFactorAdd`, `VertexAlgebra_RotationConjugateCommutant`, `VertexAlgebra_RotationImplementer`, `VertexAlgebra_SmoothConjugateInner`, `VertexAlgebra_SmoothConjugatePrimary`, `VertexAlgebra_SmoothEnergyPower`, `VertexAlgebra_SmoothTopology`, `VertexAlgebra_StressCutoffNormalized`, `VertexAlgebra_StressCutoffNormalized2`, `VertexAlgebra_StressEvolution`, `VertexAlgebra_StressPropagatorDerivative`, `VertexAlgebra_StressSmoothness`, `VertexAlgebra_StrongContinuity`, `VertexAlgebra_SymmetricWeakCommute`, `VertexAlgebra_TimeAverageGraph`.
--
--   **Imports.** It imports the published bundle `Def_VertexAlgebraNet`; the bundles `OAIQ3Vx003`, `OAIQ3Vx004` and `OAIQ3Vx005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ3Vx009` and `OAIQ3Vx010`.
-- source:
--   OpenAI, Strongly rational unitary vertex operator algebras and conformal nets, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 280; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/VertexAlgebra at commit adc7f12

import Mathlib
import Definitions.Def_VertexAlgebraNet
import Definitions.Def_OAIQ3Vx003
import Definitions.Def_OAIQ3Vx004
import Definitions.Def_OAIQ3Vx005

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GraphCommutants
attribute [-instance] _root_.OAI.StronglyRationalVOA.SmoothCircleFamily.instCoeFunForallRealSmoothCircleFunction _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
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



theorem localAlgebra_isotone (hc : A.toVertexAlgebra.C2Cofinite)
    {O P : Set (AddCircle (2*Real.pi))} (hOP : O ⊆ P) :
    U.localAlgebra hc O ≤ U.localAlgebra hc P := by
  apply LocalOperatorAlgebra.generated_mono
  rintro x ⟨a,d,ha,f,hf,i,j,rfl⟩
  exact ⟨a,d,ha,f,hf.trans hOP,i,j,rfl⟩



end CFTTypeVOA.UnitaryStructure

open scoped ENNReal
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

namespace CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)

theorem smoothEnergySpace_dense : Dense (U.smoothEnergySpace : Set (Completion V)) :=
  HilbertCore.dense.mono U.core_le_smoothEnergySpace

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
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

 
theorem boundedMultiplier_strong_zero (w : ℕ → ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ n i, ‖w n i‖ ≤ C)
    (hlim : ∀ i, Tendsto (fun n => w n i) atTop (𝓝 0)) (x : Space G) :
    Tendsto (fun n => boundedMultiplier (w n) hC (hw n) x) atTop (𝓝 0) := by
  refine StrongOperatorLimit.zero_of_dense (S := finiteCore (G := G)) finiteCore_dense
    (fun n => boundedMultiplier (w n) hC (hw n)) hC
    (fun n => boundedMultiplier_norm (G := G) (w n) hC (hw n)) ?_ x
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i,v,rfl⟩ := hy
    simp only [boundedMultiplier_single]
    simpa only [zero_smul] using (hlim i).smul (tendsto_const_nhds (x := lp.single 2 i v))
  | zero => simpa only [map_zero] using (tendsto_const_nhds (x := (0 : Space G)))
  | add y z _ _ hy hz => simpa only [map_add,zero_add] using hy.add hz
  | smul c y _ hy => simpa only [map_smul,smul_zero] using hy.const_smul c

end HilbertScale
end StronglyRationalVOA

namespace StronglyRationalVOA.HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [instDec : DecidableEq ι]

variable [∀ i, CompleteSpace (G i)]

omit [DecidableEq ι]

include instDec in
theorem complement_strong_zero (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (x : Space G) :
    Tendsto (fun n => complement h hh n x) atTop (𝓝 0) := by
  apply boundedMultiplier_strong_zero
  intro i
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp (complementWeight_tendsto_zero h i)

include instDec in
theorem resolvent_strong_one (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (x : Space G) :
    Tendsto (fun n => resolvent h hh n x) atTop (𝓝 x) := by
  have he : ∀ n, resolvent h hh n x = x - complement h hh n x := fun n => by
    have heq := resolvent_add_complement h hh n x
    exact eq_sub_iff_add_eq.mpr heq
  simp_rw [he]
  simpa using tendsto_const_nhds.sub (complement_strong_zero h hh x)

end StronglyRationalVOA.HilbertScale

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_HilbertRegularization
attribute [-instance] _root_.OAI.StronglyRationalVOA.SmoothCircleFamily.instCoeFunForallRealSmoothCircleFunction _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
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

namespace StronglyRationalVOA.HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]



theorem coreOperator_essentialSelfAdjoint (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M K : finiteCore (G := G) →ₗ[ℂ] Space G) {C D : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hK : ∀ x, ‖K x‖ ≤ D * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hs : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (y : Space G) = inner ℂ (x : Space G) (M y))
    (hk : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (coreDiagonal (fun i => (h i : ℂ)) y) -
        inner ℂ (coreDiagonal (fun i => (h i : ℂ)) x) (M y) = inner ℂ (K x) (y : Space G)) :
    IsSelfAdjoint (coreOperator M).closure := by
  have hc := coreOperator_closable M hs
  have hd : Dense ((coreOperator M).closure.domain : Set (Space G)) :=
    finiteCore_dense.mono (LinearPMap.domain_mono.monotone (coreOperator M).le_closure)
  apply SymmetricOperator.selfAdjoint_of_regularizers hd hc.closure_isClosed
    (SymmetricOperator.formalAdjoint_closure hc hc (coreOperator_formalAdjoint M hs))
    (resolvent h hh) (regularized h hh M) (resolvent_selfAdjoint h hh)
    (regularized_graph_closure h hh M hM hc) (resolvent_strong_one h hh)
  intro x
  simp_rw [regularized_defect h hh M K hM hK hs hk]
  have hk0 : Tendsto (fun n => energyExtension h K (complement h hh n x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,map_zero] using (energyExtension h K).continuous.continuousAt.tendsto.comp
      (complement_strong_zero h hh x)
  change Tendsto (fun n => resolvent h hh n (energyExtension h K (complement h hh n x))) atTop (𝓝 0)
  apply squeeze_zero_norm
    (a := fun n => ‖energyExtension h K (complement h hh n x)‖)
  · intro n
    simpa only [one_mul] using
      (resolvent (G := G) h hh n).le_of_opNorm_le (resolvent_norm (G := G) h hh n)
        (energyExtension h K (complement h hh n x))
  · simpa only [norm_zero] using hk0.norm

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

include U in
 

theorem firstOrder_essentialSelfAdjoint (T K : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hT : ∀ a, ‖T a‖ ≤ C*‖A.energyShift a‖)
    (hK : ∀ a, ‖K a‖ ≤ D*‖A.energyShift a‖)
    (hs : ∀ x y : V, inner ℂ (T x) (y : Completion V) = inner ℂ (x : Completion V) (T y))
    (hk : ∀ x y : V,
      inner ℂ (T x) (A.energyShift y : Completion V)-
        inner ℂ (A.energyShift x : Completion V) (T y) = inner ℂ (K x) (y : Completion V)) :
    IsSelfAdjoint (HilbertCore.operator T).closure := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  have hT' : ∀ x, ‖U.spectralCoreMap T x‖ ≤
      C*‖HilbertScale.coreDiagonal (fun d : ℕ => ((1+(d : ℝ) : ℝ) : ℂ)) x‖ := by
    intro x
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_energyShift,
      U.energyCoordinates.norm_map,Completion.norm_coe] using hT v
  have hK' : ∀ x, ‖U.spectralCoreMap K x‖ ≤
      D*‖HilbertScale.coreDiagonal (fun d : ℕ => ((1+(d : ℝ) : ℝ) : ℂ)) x‖ := by
    intro x
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_energyShift,
      U.energyCoordinates.norm_map,Completion.norm_coe] using hK v
  have hs' : ∀ x y : HilbertScale.finiteCore (G := fun d => A.grade d),
      inner ℂ (U.spectralCoreMap T x) y = inner ℂ (x : HilbertScale.Space _) (U.spectralCoreMap T y) := by
    intro x y
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    obtain ⟨w,rfl⟩ := U.coreEnergyCoordinates.surjective y
    simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_coe,U.energyCoordinates.inner_map_map] using hs v w
  have hk' : ∀ x y : HilbertScale.finiteCore (G := fun d => A.grade d),
      inner ℂ (U.spectralCoreMap T x)
          (HilbertScale.coreDiagonal (fun d : ℕ => ((1+(d : ℝ) : ℝ) : ℂ)) y)-
        inner ℂ (HilbertScale.coreDiagonal (fun d : ℕ => ((1+(d : ℝ) : ℝ) : ℂ)) x)
          (U.spectralCoreMap T y) = inner ℂ (U.spectralCoreMap K x) y := by
    intro x y
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    obtain ⟨w,rfl⟩ := U.coreEnergyCoordinates.surjective y
    simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_coe,
      U.coreEnergyCoordinates_energyShift,U.energyCoordinates.inner_map_map] using hk v w
  have hsa := HilbertScale.coreOperator_essentialSelfAdjoint (fun d : ℕ => 1+(d : ℝ))
    (fun d => by have := Nat.cast_nonneg (α := ℝ) d; linarith) (U.spectralCoreMap T) (U.spectralCoreMap K) hT' hK' hs' hk'
  have hcl := HilbertScale.coreOperator_closable (U.spectralCoreMap T) hs'
  have h := OperatorTransport.selfAdjoint U.energyCoordinates hsa
  rwa [← OperatorTransport.closure U.energyCoordinates hcl,U.spectralCoreOperator_transport] at h

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

include U in
 

theorem smearedCore_essentialSelfAdjoint {a : V} {d p : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (he : A.PolynomialEnergyBound a) {C : ℝ}
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n)) :
    IsSelfAdjoint (HilbertCore.operator (A.smearedMap a d he f hf)).closure := by
  have hf' : RapidCoefficients (fun n => -(n : ℂ)*f n) := by
    simpa only [neg_mul,one_mul] using hf.int_mul.smul (-1)
  apply U.firstOrder_essentialSelfAdjoint (A.smearedMap a d he f hf)
    (A.smearedMap a d he (fun n => -(n : ℂ)*f n) hf')
  · intro v
    simpa only [pow_one] using A.smearedMap_bound (k := 1) he hf
      (by simpa only [pow_one] using hb) v
  · intro v
    simpa only [pow_one] using A.smearedMap_bound (k := 1) he hf'
      (by simpa only [pow_one] using hb) v
  · exact U.smearedMap_symmetric ha hq hh he hf hr
  · exact U.smearedMap_energy_commutator ha hq hh he hf hr



theorem stress_closedSmearedOperator_selfAdjoint (hc : A.toVertexAlgebra.C2Cofinite)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n)) :
    IsSelfAdjoint (U.closedSmearedOperator hc A.conformalVector 2 f hf) := by
  have hh : U.IsHermitian 2 A.conformalVector := by
    simp [IsHermitian,U.pct_conformal]
  apply U.smearedCore_essentialSelfAdjoint A.conformal_mem A.conformal_quasiPrimary hh
    (U.polynomialEnergyBounds hc A.conformalVector)
    (C := 1+A.centralCharge.re) (p := 2) ?_ hf hr
  intro n v
  simpa only [A.physicalMode_conformal] using U.virasoro_linear_energy n v

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.SmoothCircleFunction

theorem coefficient_real {f : SmoothCircleFunction} (hf : f.IsReal) (n : ℤ) :
    star (f.coefficient n) = f.coefficient (-n) := by
  rw [coefficient,coefficient,fourierCoeffOn_eq_integral,fourierCoeffOn_eq_integral]
  simp only [star_smul,star_trivial]
  have hc : star (∫ x in (0 : ℝ)..2*Real.pi,
      fourier (-n) (x : AddCircle (2*Real.pi-0)) • f x) =
      ∫ x in (0 : ℝ)..2*Real.pi,
        star (fourier (-n) (x : AddCircle (2*Real.pi-0)) • f x) := by
    exact (Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm _).symm
  rw [hc]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [smul_eq_mul,star_mul,neg_neg]
  rw [hf t, mul_comm]
  rw [show star (fourier (-n) (t : AddCircle (2*Real.pi-0))) =
      fourier n (t : AddCircle (2*Real.pi-0)) from by
        rw [fourier_neg]; exact star_star _]

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

lemma approximatingFlow_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (n : ℕ) (t : ℝ) {x y : H} (hxy : (x,y) ∈ T.graph) :
    (approximatingFlow T hs n t x,approximatingFlow T hs n t y) ∈ T.graph := by
  let r := sampleRadius n
  have hr : 1 ≤ r := sampleRadius_ge n
  let z : ℂ := (r : ℂ)*Complex.I
  have hz : 1 ≤ |z.im| := by rw [imaginary_modulus,abs_of_pos (show 0 < r by linarith)]; exact hr
  have hz' : 1 ≤ |(-z).im| := by simpa using hz
  have hc : Commute (boundedGenerator T hs r hr) (resolvent T hs Complex.I (by simp)) := by
    exact ((resolvent_commute T hs z Complex.I hz (by simp)).add_left
      (resolvent_commute T hs (-z) Complex.I hz' (by simp))).smul_left ((r : ℂ)^2/2)
  have hf : Commute (approximatingFlow T hs n t) (resolvent T hs Complex.I (by simp)) :=
    (((hc.smul_left Complex.I).smul_left t).symm.exp_right).symm
  exact graph_invariant_of_commutes_resolvent T hs Complex.I (by simp) _ hf.eq x y hxy

lemma flow_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ)
    {x y : H} (hxy : (x,y) ∈ T.graph) : (flow T hs t x,flow T hs t y) ∈ T.graph := by
  exact hs.isClosed.mem_of_tendsto ((flow_tendsto T hs t x).prodMk_nhds (flow_tendsto T hs t y))
    (Filter.Eventually.of_forall (fun n => approximatingFlow_graph T hs n t hxy))

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

open scoped Topology
open Filter

open scoped Topology
open Filter
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma regularizer_flow_bound (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S E F : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (hg : ∀ x, (S x,E x) ∈ T.graph) (hdef : E-E.adjoint = S.comp F)
    (t : ℝ) (x : H) :
    ‖S (flow T hs t x)‖ ≤ Real.exp (‖F‖*|t|)*‖S x‖ := by
  have hSa : S.adjoint = S := hS
  have hd : S.comp F = -(F.adjoint.comp S) := by
    have ha := congrArg ContinuousLinearMap.adjoint hdef
    rw [map_sub,ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.adjoint_comp,hSa] at ha
    rw [← ha,← hdef]
    abel
  have hx (x y : H) (hxy : (x,y) ∈ T.graph) :
      ‖S (flow T hs t x)‖ ≤ Real.exp (‖F‖*|t|)*‖S x‖ := by
    let q (s : ℝ) := flow T hs (-s) (S (flow T hs s x))
    let dq (s : ℝ) := Complex.I • flow T hs (-s) (F.adjoint (S (flow T hs s x)))
    have hder (s : ℝ) : HasDerivAt q (dq s) s := by
      have hg' := (S.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s (flow_derivative T hs hxy s)
      have hz : HasDerivAt (fun r : ℝ => flow T hs (-r) (S (flow T hs s x)))
          (-(flow T hs (-s) (Complex.I • E (flow T hs s x)))) s := by
        simpa only [neg_one_smul,Function.comp_def] using
          (flow_derivative T hs (hg (flow T hs s x)) (-s)).scomp s (hasDerivAt_neg s)
      have hp := StrongLimit.hasDerivAt_apply (F := fun r => flow T hs (-r))
        (fun r => flow_opNorm T hs (-r))
        (fun v => ((flow_continuous T hs v).comp continuous_neg).continuousAt) hg' hz
      have hgxy := flow_graph T hs s hxy
      have he : E.adjoint (flow T hs s x) = S (flow T hs s y) :=
        regularizer_adjoint hs.dense_domain S E hS hg (by rwa [show T.adjoint=T from hs])
      have hval := congrArg (fun A : H →L[ℂ] H => A (flow T hs s x)) hdef
      change E (flow T hs s x)-E.adjoint (flow T hs s x) = S (F (flow T hs s x)) at hval
      have hval' := congrArg (fun A : H →L[ℂ] H => A (flow T hs s x)) hd
      change S (F (flow T hs s x)) = -F.adjoint (S (flow T hs s x)) at hval'
      have heq : S (flow T hs s y)-E (flow T hs s x) = F.adjoint (S (flow T hs s x)) := by
        rw [he] at hval
        rw [hval'] at hval
        simpa only [neg_sub,neg_neg] using congrArg Neg.neg hval
      convert hp using 1
      · rfl
      · change Complex.I • flow T hs (-s) (F.adjoint (S (flow T hs s x))) =
          flow T hs (-s) (S (flow T hs s (Complex.I • y))) +
            -flow T hs (-s) (Complex.I • E (flow T hs s x))
        simp only [map_smul]
        rw [← sub_eq_add_neg,← smul_sub,← map_sub,heq]
    have hb (s : ℝ) : ‖dq s‖ ≤ ‖F‖*‖q s‖ := by
      dsimp only [dq,q]
      rw [norm_smul,Complex.norm_I,one_mul,flow_norm,flow_norm]
      simpa only [LinearIsometryEquiv.norm_map] using F.adjoint.le_opNorm (S (flow T hs s x))
    have hb' := norm_le_exp_of_derivative_bound hder hb t
    dsimp only [q] at hb'
    simpa only [flow_norm,neg_zero,flow_zero,one_apply_eq_self,mul_comm] using hb'
  have hdense : DenseRange T.domain.subtype := by simpa [DenseRange] using hs.dense_domain
  apply hdense.induction_on (p := fun x => ‖S (flow T hs t x)‖ ≤ Real.exp (‖F‖*|t|)*‖S x‖)
  · exact isClosed_le (S.continuous.comp (flow T hs t).continuous).norm
      (continuous_const.mul S.continuous.norm)
  · intro u
    exact hx u (T u) (T.mem_graph_iff.mpr ⟨u,rfl,rfl⟩)

end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

lemma flow_regularizer_factor (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S E F : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (hg : ∀ x, (S x,E x) ∈ T.graph) (hdef : E-E.adjoint = S.comp F) (t : ℝ) :
    ∃ B : H →L[ℂ] H, (flow T hs t).comp S = S.comp B ∧ ‖B‖ ≤ Real.exp (‖F‖*|t|) := by
  let L := (S.comp (flow T hs (-t))).toLinearMap
  let Q := L.extendOfNorm S.toLinearMap
  have hb (x : H) : ‖L x‖ ≤ Real.exp (‖F‖*|t|)*‖S.toLinearMap x‖ := by
    simpa only [L,ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,abs_neg] using
      regularizer_flow_bound T hs S E F hS hg hdef (-t) x
  have hQ : Q.comp S = S.comp (flow T hs (-t)) := by
    ext x
    exact L.extendOfNorm_eq hSd ⟨_,hb⟩ x
  have hQa : S.comp Q.adjoint = (flow T hs t).comp S := by
    have h := congrArg ContinuousLinearMap.adjoint hQ
    simpa only [ContinuousLinearMap.adjoint_comp,show S.adjoint=S from hS,flow_adjoint,neg_neg] using h
  refine ⟨Q.adjoint,hQa.symm,?_⟩
  rw [LinearIsometryEquiv.norm_map]
  exact L.opNorm_extendOfNorm_le hSd (Real.exp_pos _).le hb

end StronglyRationalVOA.SymmetricOperator

open UniformSpace

open scoped Topology
open Filter MeasureTheory

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



lemma regularizer_factor_continuous_zero (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|)) (x : H) :
    Tendsto (fun t => B t x) (𝓝 0) (𝓝 x) := by
  have ha (t : ℝ) : (B t).adjoint.comp S = S.comp (flow T hs (-t)) := by
    have h := congrArg ContinuousLinearMap.adjoint (hB t)
    rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,
      show S.adjoint = S from hS,flow_adjoint] at h
    exact h.symm
  have hbound : ∀ᶠ t in 𝓝 (0 : ℝ), ‖(B t).adjoint‖ ≤ Real.exp K := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ)<0 by norm_num) (show (0 : ℝ)<1 by norm_num)] with t ht
    rw [LinearIsometryEquiv.norm_map]
    apply (hb t).trans
    apply Real.exp_le_exp.mpr
    have ht' : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le,ht.2.le⟩
    nlinarith
  have hc (v : H) : Tendsto (fun t => (B t).adjoint (S v)) (𝓝 0) (𝓝 (S v)) := by
    have he (t : ℝ) : (B t).adjoint (S v) = S (flow T hs (-t) v) :=
      congrArg (fun Q : H →L[ℂ] H => Q v) (ha t)
    simp_rw [he]
    have h := S.continuous.continuousAt.tendsto.comp
      (((flow_continuous T hs v).comp continuous_neg).tendsto 0)
    simpa only [Function.comp_def,neg_zero,flow_zero,one_apply_eq_self] using h
  have hc' (v : H) : Tendsto (fun t => (B t).adjoint v) (𝓝 0) (𝓝 v) := by
    exact StrongLimit.tendsto_of_denseRange S hSd (fun t => (B t).adjoint) 1
      (Real.exp_pos K).le hbound (by simpa only [one_apply_eq_self] using hc) v
  have hip : Tendsto (fun t => (inner ℂ (B t x) x).re) (𝓝 0) (𝓝 (‖x‖^2)) := by
    have h : Tendsto (fun t => inner ℂ x ((B t).adjoint x)) (𝓝 0) (𝓝 (inner ℂ x x)) :=
      tendsto_const_nhds.inner (hc' x)
    have h' := Complex.continuous_re.continuousAt.tendsto.comp h
    have heq : (inner ℂ x x).re = ‖x‖^2 := by
      exact inner_self_eq_norm_sq (𝕜 := ℂ) x
    simpa only [Function.comp_def,ContinuousLinearMap.adjoint_inner_right,heq] using h'
  have hupper : Tendsto (fun t : ℝ => (Real.exp (K*|t|)*‖x‖)^2+‖x‖^2-
      2*(inner ℂ (B t x) x).re) (𝓝 0) (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => (Real.exp (K*|t|)*‖x‖)^2) (𝓝 0) (𝓝 (‖x‖^2)) := by
      have hec : Continuous (fun t : ℝ => (Real.exp (K*|t|)*‖x‖)^2) := by fun_prop
      simpa only [abs_zero,mul_zero,Real.exp_zero,one_mul] using hec.tendsto (0 : ℝ)
    have hh := (he.add_const (‖x‖^2)).sub (hip.const_mul 2)
    have hz : ‖x‖^2+‖x‖^2-2*‖x‖^2 = 0 := by ring
    simpa only [hz] using hh
  have hsquare : Tendsto (fun t => ‖B t x-x‖^2) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero (fun t => sq_nonneg _) _ hupper
    intro t
    rw [norm_sub_sq (𝕜 := ℂ)]
    change ‖B t x‖^2-2*(inner ℂ (B t x) x).re+‖x‖^2 ≤ _
    have hn := (B t).le_of_opNorm_le (hb t) x
    nlinarith [norm_nonneg (B t x), show 0 ≤ Real.exp (K*|t|)*‖x‖ by positivity]
  have hn : Tendsto (fun t => ‖B t x-x‖) (𝓝 0) (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn
end StronglyRationalVOA.SymmetricOperator

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
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma regularizer_factor_add (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S : H →L[ℂ] H) (hSi : Function.Injective S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    (s t : ℝ) : B (s+t) = B s * B t := by
  have he (r : ℝ) (v : H) : S (B r v) = flow T hs r (S v) :=
    (congrArg (fun Q : H →L[ℂ] H => Q v) (hB r)).symm
  ext x
  apply hSi
  rw [he,mul_apply_eq_comp,he,he,flow_add,mul_apply_eq_comp]

lemma regularizer_factor_continuous (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|)) (x : H) :
    Continuous (fun t => B t x) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have h := (B s).continuous.tendsto x |>.comp
    ((regularizer_factor_continuous_zero T hs S hS hSd B hB hK hb x).comp
      (by simpa only [sub_self] using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 s) (𝓝 s)).sub_const s)))
  change Tendsto (fun t : ℝ => B t x) (𝓝 s) (𝓝 (B s x))
  change Tendsto (fun t : ℝ => B s (B (t-s) x)) _ _ at h
  have he (t : ℝ) : s+(t-s)=t := by ring
  simpa only [← mul_apply_eq_comp,← regularizer_factor_add T hs S
    (selfAdjoint_injective_of_denseRange S hS hSd) B hB,he] using h

lemma regularizer_factor_integral (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|))
    {x y : H} (hxy : (S x,S y) ∈ T.graph) (t : ℝ) :
    (∫ s in 0..t, B s (Complex.I • y)) = B t x-x := by
  apply selfAdjoint_injective_of_denseRange S hS hSd
  have he (r : ℝ) (v : H) : S (B r v) = flow T hs r (S v) :=
    (congrArg (fun Q : H →L[ℂ] H => Q v) (hB r)).symm
  rw [← S.intervalIntegral_comp_comm ((regularizer_factor_continuous T hs S hS hSd B hB hK hb _).intervalIntegrable 0 t),
    map_sub,he]
  simp_rw [he,map_smul]
  simpa only [map_smul] using flow_integral T hs hxy t

lemma regularizer_factor_derivative (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|))
    {x y : H} (hxy : (S x,S y) ∈ T.graph) (t : ℝ) :
    HasDerivAt (fun s => B s x) (B t (Complex.I • y)) t := by
  have hc := regularizer_factor_continuous T hs S hS hSd B hB hK hb (Complex.I • y)
  have he : (fun s : ℝ => B s x) = (fun s : ℝ => x+∫ r in 0..s, B r (Complex.I • y)) := by
    funext s
    rw [regularizer_factor_integral T hs S hS hSd B hB hK hb hxy s]
    abel
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt).const_add x

end StronglyRationalVOA.SymmetricOperator

open scoped Topology
open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)



lemma core_flow_energyGraph (r : ℕ) (M K : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hK : ∀ v, ‖K v‖ ≤ D*‖(A.energyShift^r) v‖)
    (hk : ∀ x y : V, inner ℂ (M x) ((A.energyShift^r) y : Completion V)-
      inner ℂ ((A.energyShift^r) x : Completion V) (M y) = inner ℂ (K x) (y : Completion V))
    (hc : (HilbertCore.operator M).IsClosable) (hs : IsSelfAdjoint (HilbertCore.operator M).closure)
    (t : ℝ) {x y : Completion V} (hxy : (x,y) ∈ (U.energyPower r).graph) :
    ∃ z, (SymmetricOperator.flow (HilbertCore.operator M).closure hs t x,z) ∈ (U.energyPower r).graph ∧
      ‖z‖ ≤ Real.exp (‖U.sobolevExtension r K‖*|t|)*‖y‖ := by
  obtain ⟨B,hB,hbound⟩ := SymmetricOperator.flow_regularizer_factor _ hs
    (U.inverseSobolev r) (U.sobolevExtension r M) (U.sobolevExtension r K)
    (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)
    (U.sobolevExtension_inverse_graph r M hM hc) (U.sobolevExtension_defect r M K hM hK hk) t
  refine ⟨B y,?_,B.le_of_opNorm_le hbound y⟩
  have he := congrArg (fun Q : Completion V →L[ℂ] Completion V => Q y) hB
  change SymmetricOperator.flow _ hs t (U.inverseSobolev r y) = U.inverseSobolev r (B y) at he
  rw [U.inverseSobolev_on_graph r hxy] at he
  rw [he]
  exact U.inverseSobolev_graph r (B y)



lemma firstOrderSmear_flow_energyGraph {a : V} {d p : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n))
    {r : ℕ} (hrp : 1 ≤ r) (t : ℝ) {x y : Completion V}
    (hxy : (x,y) ∈ (U.energyPower r).graph) :
    ∃ z, (SymmetricOperator.flow (HilbertCore.operator (A.smearedMap a d he f hf)).closure
      (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t x,z) ∈ (U.energyPower r).graph ∧
      ‖z‖ ≤ Real.exp (‖U.sobolevExtension r (U.smearedPowerCommutator ha he hf r)‖*|t|)*‖y‖ := by
  have hM (v : V) : ‖A.smearedMap a d he f hf v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^p)*C)*‖(A.energyShift^r) v‖ := by
    have hb' : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖(A.energyShift^1) v‖ := by
      simpa only [pow_one] using hb
    exact (A.smearedMap_bound he hf hb' v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono hrp v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hC))
  exact U.core_flow_energyGraph r (A.smearedMap a d he f hf)
    (U.smearedPowerCommutator ha he hf r) hM
    (U.smearedPowerCommutator_bound ha he hC hb hf r)
    (U.smearedPowerCommutator_pairing ha hq hh he hf hr r)
    (HilbertCore.closable (U.smearedMap_symmetric ha hq hh he hf hr))
    (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t hxy

lemma firstOrderSmear_flow_smoothEnergySpace {a : V} {d p : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n))
    (t : ℝ) {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    SymmetricOperator.flow (HilbertCore.operator (A.smearedMap a d he f hf)).closure
      (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t x ∈ U.smoothEnergySpace := by
  rw [smoothEnergySpace,Submodule.mem_iInf] at hx ⊢
  intro r
  by_cases hr0 : r = 0
  · subst r
    obtain ⟨v,hv,_⟩ := (U.energyPower 0).mem_graph_iff.mp (U.energyPower_zero_graph
      (SymmetricOperator.flow (HilbertCore.operator (A.smearedMap a d he f hf)).closure
        (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t x))
    dsimp only [Prod.fst] at hv
    rw [← hv]
    exact v.property
  · let v : (U.energyPower r).domain := ⟨x,hx r⟩
    obtain ⟨z,hz,_⟩ := U.firstOrderSmear_flow_energyGraph ha hq hh he hC hb hf hr
      (show 1 ≤ r by omega) t ((U.energyPower r).mem_graph_iff.mpr ⟨v,rfl,rfl⟩)
    obtain ⟨w,hw,_⟩ := (U.energyPower r).mem_graph_iff.mp hz
    dsimp only [Prod.fst] at hw
    rw [← hw]
    exact w.property

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma smoothSmear_symmetric (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n))
    (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc ha hf x : Completion V) (y : Completion V) =
      inner ℂ (x : Completion V) (U.smoothSmear hc ha hf y : Completion V) := by
  have hs := HilbertCore.formalAdjoint (U.smearedMap_symmetric ha hq hh (U.polynomialEnergyBounds hc a) hf hr)
  have hsc := SymmetricOperator.formalAdjoint_closure (U.smearedCore_closable hc ha hf)
    (U.smearedCore_closable hc ha hf) hs
  exact SymmetricOperator.formalAdjoint_graph_pairing hsc
    (U.smoothSmear_graph hc ha hf x) (U.smoothSmear_graph hc ha hf y)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

lemma regularized_heisenberg_pairing (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S E : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|))
    {x y u v : H} (hxy : (S x,S y) ∈ T.graph) (huv : (u,v) ∈ T.graph)
    (hw : ∀ t, inner ℂ (E (B t y)) (flow T hs t u) =
      inner ℂ (E (B t x)) (flow T hs t v)) (t : ℝ) :
    inner ℂ (E (B t x)) (flow T hs t u) = inner ℂ (E x) u := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => inner ℂ (E (B r x)) (flow T hs r u)) 0 s := by
    have h1 := (E.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s
      (regularizer_factor_derivative T hs S hS hSd B hB hK hb hxy s)
    change HasDerivAt (fun r : ℝ => E (B r x)) (E (B s (Complex.I • y))) s at h1
    have h2 := flow_derivative T hs huv s
    have hd0 := HasDerivAt.inner ℂ h1 h2
    have hz : inner ℂ (E (B s x)) (flow T hs s (Complex.I • v)) +
        inner ℂ (E (B s (Complex.I • y))) (flow T hs s u) = 0 := by
      rw [map_smul (flow T hs s),map_smul (B s),map_smul E,
        inner_smul_right,inner_smul_left,starRingEnd_apply,Complex.star_def,Complex.conj_I,hw s]
      ring
    rwa [hz] at hd0
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  have hzero : B 0 = 1 := by
    ext z
    apply selfAdjoint_injective_of_denseRange S hS hSd
    have h := congrArg (fun Q : H →L[ℂ] H => Q z) (hB 0)
    simpa only [flow_zero,ContinuousLinearMap.comp_apply,one_apply_eq_self] using h.symm
  simpa only [flow_zero,one_apply_eq_self,hzero] using he

end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma flow_inner (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) (x y : H) :
    inner ℂ (flow T hs t x) (flow T hs t y) = inner ℂ x y := by
  rw [← ContinuousLinearMap.adjoint_inner_right,flow_adjoint]
  change inner ℂ x ((flow T hs (-t)*flow T hs t) y) = _
  rw [← flow_add,neg_add_cancel,flow_zero,one_apply_eq_self]

lemma flow_inverse (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) (x : H) :
    flow T hs t (flow T hs (-t) x) = x := by
  change (flow T hs t*flow T hs (-t)) x=x
  rw [← flow_add,add_neg_cancel,flow_zero,one_apply_eq_self]
end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

lemma regularized_commutation_on_dense_core
    (A T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (D : Submodule ℂ H) (hDd : Dense (D : Set H)) (a b : D →ₗ[ℂ] D)
    (ha : ∀ x : D, ((x : H),(a x : H)) ∈ A.graph)
    (hb : ∀ x : D, ((x : H),(b x : H)) ∈ T.graph)
    (hasym : ∀ x y : D, inner ℂ (a x : H) (y : H) = inner ℂ (x : H) (a y : H))
    (hw : ∀ x y : D, inner ℂ (a x : H) (b y : H) = inner ℂ (b x : H) (a y : H))
    (S E : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (hDS : ∀ x : D, ∃ y, S y = (x : H)) (hE : ∀ x, (S x,E x) ∈ A.graph)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|))
    (hFD : ∀ t (x : D), flow T hs t x ∈ D) (t : ℝ) (x : D) :
    (flow T hs t x,flow T hs t (a x : H)) ∈ A.graph := by
  classical
  choose R hR using hDS
  let F (s : ℝ) (z : D) : D := ⟨flow T hs s z,hFD s z⟩
  have hF (s : ℝ) (z : D) : (b (F s z) : H) = flow T hs s (b z : H) :=
    T.mem_graph_snd_inj (hb (F s z)) (flow_graph T hs s (hb z)) rfl
  have hEB (s : ℝ) (z : D) : E (B s (R z)) = (a (F s z) : H) := by
    have he := congrArg (fun Q : H →L[ℂ] H => Q (R z)) (hB s)
    change flow T hs s (S (R z)) = S (B s (R z)) at he
    rw [hR] at he
    exact A.mem_graph_snd_inj (hE (B s (R z))) (ha (F s z)) he.symm
  have hp (s : ℝ) (y : D) :
      inner ℂ (a (F s x) : H) (F s y : H) = inner ℂ (a x : H) (y : H) := by
    have hxy : (S (R x),S (R (b x))) ∈ T.graph := by rw [hR,hR]; exact hb x
    have hweak (r : ℝ) : inner ℂ (E (B r (R (b x)))) (flow T hs r y) =
        inner ℂ (E (B r (R x))) (flow T hs r (b y : H)) := by
      rw [hEB,hEB,← hF r y]
      change inner ℂ (a (F r (b x)) : H) (F r y : H) =
        inner ℂ (a (F r x) : H) (b (F r y) : H)
      rw [hasym]
      change inner ℂ (flow T hs r (b x : H)) (a (F r y) : H) = _
      rw [← hF r x]
      exact (hw (F r x) (F r y)).symm
    have hc := regularized_heisenberg_pairing T hs S E hS hSd B hB hK hbound
      hxy (hb y) hweak s
    rw [hEB] at hc
    have he0 : E (R x) = (a x : H) := A.mem_graph_snd_inj (hE (R x)) (ha x) (hR x)
    rwa [he0] at hc
  have heq : (a (F t x) : H) = flow T hs t (a x : H) := by
    apply ext_inner_right ℂ
    intro z
    have hd : DenseRange D.subtype := by simpa [DenseRange] using hDd
    apply hd.induction_on (p := fun z => inner ℂ (a (F t x) : H) z = inner ℂ (flow T hs t (a x : H)) z)
    · exact isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
    · intro y
      have hi : (F t (F (-t) y) : H) = (y : H) := flow_inverse T hs t y
      have hm := hp t (F (-t) y)
      rw [hi] at hm
      have hu := flow_inner T hs t (a x : H) (F (-t) y : H)
      rw [show flow T hs t (F (-t) y : H) = (y : H) from hi] at hu
      exact hm.trans hu.symm
  rw [← heq]
  exact ha (F t x)
end StronglyRationalVOA.SymmetricOperator

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_HighFieldGraph
attribute [-instance] _root_.OAI.StronglyRationalVOA.SmoothCircleFamily.instCoeFunForallRealSmoothCircleFunction _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
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

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

lemma graph_invariant_of_commutes_flow (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (Q : H →L[ℂ] H) (hQ : ∀ t, Q*flow T hs t = flow T hs t*Q)
    {x y : H} (hxy : (x,y) ∈ T.graph) : (Q x,Q y) ∈ T.graph := by
  rw [← show T.adjoint = T from hs,LinearPMap.adjoint_graph_eq_graph_adjoint hs.dense_domain]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro u v huv
  have h1 := flow_derivative T hs huv 0
  have h2 := (Q.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 (flow_derivative T hs hxy 0)
  have hd := HasDerivAt.inner ℂ h1 h2
  have he (s : ℝ) : inner ℂ (flow T hs s u) (Q (flow T hs s x)) = inner ℂ u (Q x) := by
    have hc := congrArg (fun R : H →L[ℂ] H => R x) (hQ s)
    change Q (flow T hs s x) = flow T hs s (Q x) at hc
    rw [hc,← ContinuousLinearMap.adjoint_inner_right,flow_adjoint]
    change inner ℂ u ((flow T hs (-s)*flow T hs s) (Q x)) = _
    rw [← flow_add,neg_add_cancel,flow_zero,one_apply_eq_self]
  simp only [Function.comp_apply, he] at hd
  have hz := hd.unique (hasDerivAt_const (0 : ℝ) (inner ℂ u (Q x)))
  simp only [flow_zero,one_apply_eq_self] at hz
  change inner ℂ u (Q (Complex.I • y)) + inner ℂ (Complex.I • v) (Q x) = 0 at hz
  rw [map_smul Q,inner_smul_right,inner_smul_left,starRingEnd_apply,Complex.star_def,Complex.conj_I] at hz
  have hi : Complex.I * (inner ℂ u (Q y)-inner ℂ v (Q x)) = 0 := by linear_combination hz
  have heq := (mul_eq_zero.mp hi).resolve_left Complex.I_ne_zero
  exact sub_eq_zero.mpr (sub_eq_zero.mp heq).symm

 

lemma graph_entries_commute_of_flow_invariant (A T : H →ₗ.[ℂ] H)
    (hA : A.IsClosed) (hs : IsSelfAdjoint T)
    (hF : ∀ t x y, (x,y) ∈ A.graph → (flow T hs t x,flow T hs t y) ∈ A.graph)
    (i j k l : Bool) :
    ClosedGraphData.entry A hA i j * ClosedGraphData.entry T hs.isClosed k l =
      ClosedGraphData.entry T hs.isClosed k l * ClosedGraphData.entry A hA i j := by
  have hC (i j : Bool) (t : ℝ) := ClosedGraphData.entry_commutes_of_graph_invariant A hA
    (flow T hs t) (hF t) (by rw [flow_adjoint]; exact hF (-t)) i j
  have hG (i j : Bool) : ∀ x y, (x,y) ∈ T.graph →
      (ClosedGraphData.entry A hA i j x,ClosedGraphData.entry A hA i j y) ∈ T.graph := by
    intro x y hxy
    exact graph_invariant_of_commutes_flow T hs _ (fun t => (hC i j t).symm) hxy
  apply ClosedGraphData.entry_commutes_of_graph_invariant T hs.isClosed _ (hG i j) ?_ k l
  change ∀ x y, (x,y) ∈ T.graph →
    (star (ClosedGraphData.entry A hA i j) x,star (ClosedGraphData.entry A hA i j) y) ∈ T.graph
  rw [ClosedGraphData.star_entry]
  exact hG j i
end StronglyRationalVOA.SymmetricOperator

open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction


lemma power_real {f : SmoothCircleFunction} (hf : f.IsReal) (k : ℕ) : (f.power k).IsReal := by
  intro t
  change star (f t^k) = f t^k
  rw [star_pow,hf t]

lemma derivative_power_balance (f : SmoothCircleFunction) (k : ℕ) (t : ℝ) :
    (k : ℂ)*deriv f t*(f.power k t) = f t*deriv (f.power k) t := by
  have hd : DifferentiableAt ℝ (f : ℝ → ℂ) t :=
    (f.smooth.differentiable (by norm_num)).differentiableAt
  change (k : ℂ)*deriv f t*f t^k = f t*deriv ((f : ℝ → ℂ)^k) t
  rw [(hd.hasDerivAt.pow k).deriv]
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.add_sub_cancel,pow_succ]
    ring



end StronglyRationalVOA.SmoothCircleFunction

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma smearedMap_weakCommutation_of_convolution {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hqa : A.IsQuasiPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b)
    (hea : A.PolynomialEnergyBound a) (heb : A.PolynomialEnergyBound b)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hzero : ∀ r : ℤ, ∀ x y : V,
      HasSum (fun m : ℤ => f.coefficient m*g.coefficient (r-m)*
        inner ℂ x (A.physicalMode a d m (A.physicalMode b e (r-m) y)-
          A.physicalMode b e (r-m) (A.physicalMode a d m y))) 0) (x y : V) :
    inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
      (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
    inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
      (A.smearedMap a d hea f.coefficient f.rapid_coefficients y) := by
  have Hhom (D E : ℕ) (x y : V) (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) :
      inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
        (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
      inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
        (A.smearedMap a d hea f.coefficient f.rapid_coefficients y) := by
    let r : ℤ := (E : ℤ)-D
    have H1 := U.hasSum_smeared_inner_homogeneous ha hb hx hy hqa hha hea heb
      f.rapid_coefficients g.rapid_coefficients (SmoothCircleFunction.coefficient_real hf)
    have H2 := U.hasSum_smeared_inner_homogeneous hb ha hx hy hqb hhb heb hea
      g.rapid_coefficients f.rapid_coefficients (SmoothCircleFunction.coefficient_real hg)
    let R : ℤ ≃ ℤ :=
      { toFun := fun m => r-m
        invFun := fun m => r-m
        left_inv := fun m => by dsimp; omega
        right_inv := fun m => by dsimp; omega }
    have H2' := R.hasSum_iff.mpr H2
    have Hdiff := H1.sub H2'
    have Hz := hzero r x y
    apply sub_eq_zero.mp
    apply Hdiff.unique
    convert Hz using 1
    all_goals try with_reducible_and_instances rfl
    ext m
    simp only [Function.comp_def,R,Equiv.coe_fn_mk]
    rw [show (E : ℤ)-D-(r-m) = m by dsimp [r]; omega]
    simp only [inner_sub_right]
    ring
  apply A.homogeneous_induction (P := fun x =>
      inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
        (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
      inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
        (A.smearedMap a d hea f.coefficient f.rapid_coefficients y))
  · simp only [map_zero,inner_zero_left]
  · intro D x hx
    apply A.homogeneous_induction (P := fun y =>
        inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
          (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
        inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
          (A.smearedMap a d hea f.coefficient f.rapid_coefficients y))
    · simp only [map_zero,inner_zero_right]
    · intro E y hy
      exact Hhom D E x y hx hy
    · intro y z hy hz
      simp only [map_add,inner_add_right,hy,hz]
  · intro x z hx hz
    simp only [map_add,inner_add_left,hx,hz]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_PrimaryStressWeak
attribute [-instance] _root_.OAI.StronglyRationalVOA.SmoothCircleFamily.instCoeFunForallRealSmoothCircleFunction _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
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

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma smoothSmear_weakCommutation_of_algebraic (hc : A.toVertexAlgebra.C2Cofinite) {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : SmoothCircleFunction}
    (hweak : ∀ x y : V,
      inner ℂ (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients x)
        (A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients y) =
      inner ℂ (A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients x)
        (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients y))
    (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc ha f.rapid_coefficients x : Completion V)
      (U.smoothSmear hc hb g.rapid_coefficients y : Completion V) =
    inner ℂ (U.smoothSmear hc hb g.rapid_coefficients x : Completion V)
      (U.smoothSmear hc ha f.rapid_coefficients y : Completion V) := by
  obtain ⟨C,hC,p,k,hM⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hN⟩ := (U.polynomialEnergyBounds hc b).physical A e
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients
  let N := A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients
  have hm (v : V) : ‖M v‖ ≤ ((∑' n : ℤ, ‖f.coefficient n‖*(1+|(n : ℝ)|)^p)*C)*‖(A.energyShift^(k+l)) v‖ :=
    (A.smearedMap_bound _ f.rapid_coefficients hM v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ k+l) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hC.le))
  have hn (v : V) : ‖N v‖ ≤ ((∑' n : ℤ, ‖g.coefficient n‖*(1+|(n : ℝ)|)^q)*D)*‖(A.energyShift^(k+l)) v‖ :=
    (A.smearedMap_bound _ g.rapid_coefficients hN v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : l ≤ k+l) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hD.le))
  let xx : (U.energyPower (k+l)).domain := ⟨x,(iInf_le (fun r => (U.energyPower r).domain) (k+l)) x.property⟩
  let yy : (U.energyPower (k+l)).domain := ⟨y,(iInf_le (fun r => (U.energyPower r).domain) (k+l)) y.property⟩
  have hx : ((x : Completion V),U.energyPower (k+l) xx) ∈ (U.energyPower (k+l)).graph :=
    (U.energyPower (k+l)).mem_graph_iff.mpr ⟨xx,rfl,rfl⟩
  have hy : ((y : Completion V),U.energyPower (k+l) yy) ∈ (U.energyPower (k+l)).graph :=
    (U.energyPower (k+l)).mem_graph_iff.mpr ⟨yy,rfl,rfl⟩
  rw [U.smoothSmear_eq_extension hc ha f.rapid_coefficients hm x hx,
    U.smoothSmear_eq_extension hc hb g.rapid_coefficients hn y hy,
    U.smoothSmear_eq_extension hc hb g.rapid_coefficients hn x hx,
    U.smoothSmear_eq_extension hc ha f.rapid_coefficients hm y hy]
  exact U.sobolevExtension_weakCommutation (k+l) M N hm hn
    hweak _ _

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter
open scoped Topology

open Filter MeasureTheory
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

def timeIntegral (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => ∫ t in a..b, flow T hs t x
      map_add' := fun x y => by
        simp only [map_add]
        exact intervalIntegral.integral_add ((flow_continuous T hs x).intervalIntegrable a b)
          ((flow_continuous T hs y).intervalIntegrable a b)
      map_smul' := fun c x => by
        simp only [map_smul]
        exact intervalIntegral.integral_smul c (fun t => flow T hs t x) }
    |b-a| (fun x => by
      change ‖∫ t in a..b, flow T hs t x‖ ≤ |b-a| * ‖x‖
      simpa only [mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const
        (fun t _ => le_of_eq (flow_norm T hs t x)))

lemma timeIntegral_apply (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) (x : H) :
    timeIntegral T hs a b x = ∫ t in a..b, flow T hs t x := rfl

lemma timeIntegral_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) :
    ‖timeIntegral T hs a b‖ ≤ |b-a| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
  intro x
  simpa only [timeIntegral_apply,mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t _ => le_of_eq (flow_norm T hs t x))

lemma flow_matrix_derivative (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    {u v : H} (huv : (u,v) ∈ T.graph) (x : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => inner ℂ u (flow T hs s x))
      (Complex.I*inner ℂ v (flow T hs t x)) t := by
  have h := HasDerivAt.inner ℂ
    ((flow_derivative T hs huv (-t)).scomp t (hasDerivAt_neg t)) (hasDerivAt_const t x)
  have he (s : ℝ) : inner ℂ (flow T hs (-s) u) x = inner ℂ u (flow T hs s x) := by
    rw [← ContinuousLinearMap.adjoint_inner_left,flow_adjoint]
  have hid : inner ℂ ((-1 : ℝ) • flow T hs (-t) (Complex.I • v)) x =
      Complex.I*inner ℂ v (flow T hs t x) := by
    rw [neg_one_smul,map_smul,inner_neg_left,inner_smul_left]
    change -(star Complex.I * inner ℂ (flow T hs (-t) v) x) = _
    rw [Complex.star_def,Complex.conj_I,neg_mul,neg_neg]
    rw [← ContinuousLinearMap.adjoint_inner_left,flow_adjoint]
  simpa only [Function.comp_apply,he,inner_zero_right,zero_add,hid] using h

 

lemma timeIntegral_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) (x : H) :
    (timeIntegral T hs a b x,(-Complex.I) • (flow T hs b x-flow T hs a x)) ∈ T.graph := by
  rw [show T.graph = T.adjoint.graph from congrArg LinearPMap.graph hs.symm,
    LinearPMap.adjoint_graph_eq_graph_adjoint hs.dense_domain]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro u v huv
  have hc : Continuous (fun t => Complex.I*inner ℂ v (flow T hs t x)) :=
    continuous_const.mul (continuous_const.inner (flow_continuous T hs x))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => flow_matrix_derivative T hs huv x t) (hc.intervalIntegrable a b)
  have hi := (innerSL ℂ v).intervalIntegral_comp_comm (μ := volume) ((flow_continuous T hs x).intervalIntegrable a b)
  change (∫ t in a..b, inner ℂ v (flow T hs t x)) = inner ℂ v (timeIntegral T hs a b x) at hi
  rw [intervalIntegral.integral_const_mul,hi] at h
  simp only [inner_smul_right,inner_sub_right]
  linear_combination (norm := (ring_nf; simp [Complex.I_sq])) (-Complex.I) * h

lemma inner_timeIntegral_right (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) (x y : H) :
    inner ℂ x (timeIntegral T hs a b y) = ∫ t in a..b, inner ℂ x (flow T hs t y) := by
  exact ((innerSL ℂ x).intervalIntegral_comp_comm (μ := volume)
    ((flow_continuous T hs y).intervalIntegrable a b)).symm

lemma inner_timeIntegral_left (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) (x y : H) :
    inner ℂ (timeIntegral T hs a b x) y = ∫ t in a..b, inner ℂ (flow T hs t x) y := by
  let L : H →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap.comp ((innerSL ℂ y).restrictScalars ℝ)
  have h := L.intervalIntegral_comp_comm (μ := volume) ((flow_continuous T hs x).intervalIntegrable a b)
  change (∫ t in a..b, (starRingEnd ℂ) (inner ℂ y (flow T hs t x))) =
    (starRingEnd ℂ) (inner ℂ y (∫ t in a..b, flow T hs t x)) at h
  simpa only [inner_conj_symm,timeIntegral_apply] using h.symm

lemma timeIntegral_adjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) :
    (timeIntegral T hs a b).adjoint = timeIntegral T hs (-b) (-a) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_timeIntegral_left,inner_timeIntegral_right]
  simp_rw [← ContinuousLinearMap.adjoint_inner_right,flow_adjoint]
  simpa only [neg_neg] using intervalIntegral.integral_comp_neg
    (fun t => inner ℂ x (flow T hs t y)) (a := -b) (b := -a)

 

def timeAverage (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (r : ℝ) : H →L[ℂ] H :=
  ((2*r)⁻¹ : ℝ) • timeIntegral T hs (-r) r

lemma timeAverage_selfAdjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (r : ℝ) :
    IsSelfAdjoint (timeAverage T hs r) := by
  change star (timeAverage T hs r) = timeAverage T hs r
  rw [timeAverage,star_smul,star_trivial]
  change (2*r)⁻¹ • (timeIntegral T hs (-r) r).adjoint = _
  rw [timeIntegral_adjoint,neg_neg]

lemma timeAverage_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) {r : ℝ} (hr : 0 < r) :
    ‖timeAverage T hs r‖ ≤ 1 := by
  rw [timeAverage,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) hr))]
  calc
    (2*r)⁻¹ * ‖timeIntegral T hs (-r) r‖ ≤ (2*r)⁻¹ * |r-(-r)| :=
      mul_le_mul_of_nonneg_left (timeIntegral_norm T hs (-r) r) (by positivity)
    _ = 1 := by
      rw [show r-(-r)=2*r by ring,abs_of_pos (mul_pos (by norm_num) hr)]
      exact inv_mul_cancel₀ (by positivity)

lemma timeAverage_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (r : ℝ) (x : H) :
    (timeAverage T hs r x,((2*r)⁻¹ : ℝ) • ((-Complex.I) • (flow T hs r x-flow T hs (-r) x))) ∈ T.graph := by
  have h := (T.graph.restrictScalars ℝ).smul_mem ((2*r)⁻¹ : ℝ) (timeIntegral_graph T hs (-r) r x)
  simpa only [Submodule.restrictScalars_mem,timeAverage,smul_apply,Prod.smul_mk] using h

lemma timeAverage_initial_bound (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    {x y : H} (hxy : (x,y) ∈ T.graph) {r : ℝ} (hr : 0 < r) :
    ‖timeAverage T hs r x-x‖ ≤ r*‖y‖ := by
  have he : timeAverage T hs r x-x =
      (2*r)⁻¹ • (∫ t in -r..r, (flow T hs t x-x)) := by
    rw [intervalIntegral.integral_sub ((flow_continuous T hs x).intervalIntegrable (-r) r)
      (continuous_const.intervalIntegrable (-r) r),intervalIntegral.integral_const,
      show r-(-r)=2*r by ring,smul_sub,inv_smul_smul₀ (show 2*r ≠ 0 by positivity)]
    rfl
  have hb : ‖∫ t in -r..r, (flow T hs t x-x)‖ ≤ (r*‖y‖)*(2*r) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -r) (b := r)
      (C := r*‖y‖) (f := fun t => flow T hs t x-x) (fun t ht => ?_)
    · simpa only [show r-(-r)=2*r by ring,abs_of_pos (show 0 < 2*r by positivity)] using h
    · rw [Set.uIoc_of_le (by linarith : -r ≤ r)] at ht
      exact (flow_initial_bound T hs hxy t).trans
        (mul_le_mul_of_nonneg_right (abs_le.mpr ⟨ht.1.le,ht.2⟩) (norm_nonneg y))
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) hr))]
  have h := mul_le_mul_of_nonneg_left hb (show 0 ≤ (2*r)⁻¹ by positivity)
  calc
    (2*r)⁻¹ * ‖∫ t in -r..r, (flow T hs t x-x)‖ ≤ (2*r)⁻¹*((r*‖y‖)*(2*r)) := h
    _ = r*‖y‖ := by field_simp

 

lemma timeAverage_strong_one (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hl : Tendsto r atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => timeAverage T hs (r n) x) atTop (𝓝 x) := by
  have hc := (StrongLimit.equicontinuous_of_norm_bound
    (fun n => timeAverage T hs (r n)) (fun n => timeAverage_norm T hs (hr n))).isClosed_setOfPred_tendsto
    (l := atTop) (f := id) continuous_id
  apply (closure_minimal (s := (T.domain : Set H)) (t := {x | Tendsto
    (fun n => timeAverage T hs (r n) x) atTop (𝓝 x)}) ?_ hc) (hs.dense_domain x)
  intro v hv
  let w : T.domain := ⟨v,hv⟩
  change Tendsto _ _ _
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm (a := fun n => r n*‖T w‖)
  · exact fun n => timeAverage_initial_bound T hs (T.mem_graph_iff.mpr ⟨w,rfl,rfl⟩) (hr n)
  · simpa only [zero_mul] using hl.mul_const ‖T w‖

end StronglyRationalVOA.SymmetricOperator

open MeasureTheory
open scoped Topology
namespace StronglyRationalVOA

namespace SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma timeIntegral_preserves_graph (T A : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (hA : A.IsClosed)
    (hi : ∀ t x y, (x,y) ∈ A.graph → (flow T hs t x,flow T hs t y) ∈ A.graph)
    (a b : ℝ) {x y : H} (hxy : (x,y) ∈ A.graph) :
    (timeIntegral T hs a b x,timeIntegral T hs a b y) ∈ A.graph := by
  have hf : IntervalIntegrable (fun t => (flow T hs t x,flow T hs t y)) volume a b :=
    ((flow_continuous T hs x).prodMk (flow_continuous T hs y)).intervalIntegrable a b
  have h := intervalIntegral_mem_closedSubmodule A.graph hA hf (fun t => hi t x y hxy)
  have he : (∫ t in a..b,(flow T hs t x,flow T hs t y)) =
      (timeIntegral T hs a b x,timeIntegral T hs a b y) := by
    apply Prod.ext
    · exact ((ContinuousLinearMap.fst ℂ H H).intervalIntegral_comp_comm hf).symm
    · exact ((ContinuousLinearMap.snd ℂ H H).intervalIntegral_comp_comm hf).symm
  rwa [he] at h

lemma timeAverage_preserves_graph (T A : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (hA : A.IsClosed)
    (hi : ∀ t x y, (x,y) ∈ A.graph → (flow T hs t x,flow T hs t y) ∈ A.graph)
    (r : ℝ) {x y : H} (hxy : (x,y) ∈ A.graph) :
    (timeAverage T hs r x,timeAverage T hs r y) ∈ A.graph := by
  have h := (A.graph.restrictScalars ℝ).smul_mem ((2*r)⁻¹ : ℝ)
    (timeIntegral_preserves_graph T A hs hA hi (-r) r hxy)
  simpa only [Submodule.restrictScalars_mem,timeAverage,smul_apply,Prod.smul_mk] using h
end SymmetricOperator
end StronglyRationalVOA

open Filter MeasureTheory
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma timeIntegral_commutes (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (Q : H →L[ℂ] H) (hQ : ∀ t, Q*flow T hs t = flow T hs t*Q) (a b : ℝ) :
    Q*timeIntegral T hs a b = timeIntegral T hs a b*Q := by
  ext x
  change Q (∫ t in a..b,flow T hs t x) = ∫ t in a..b,flow T hs t (Q x)
  rw [← Q.intervalIntegral_comp_comm ((flow_continuous T hs x).intervalIntegrable a b)]
  apply intervalIntegral.integral_congr
  intro t _
  exact congrArg (fun R : H →L[ℂ] H => R x) (hQ t)

lemma timeAverage_commutes (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (Q : H →L[ℂ] H) (hQ : ∀ t, Q*flow T hs t = flow T hs t*Q) (r : ℝ) :
    Q*timeAverage T hs r = timeAverage T hs r*Q := by
  rw [timeAverage,mul_smul_comm,smul_mul_assoc,timeIntegral_commutes T hs Q hQ]


def timeDifference (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (r : ℝ) : H →L[ℂ] H :=
  ((2*r)⁻¹ : ℝ) • ((-Complex.I) • (flow T hs r-flow T hs (-r)))

lemma timeAverage_graph' (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (r : ℝ) (x : H) :
    (timeAverage T hs r x,timeDifference T hs r x) ∈ T.graph := by
  exact timeAverage_graph T hs r x
end StronglyRationalVOA.SymmetricOperator

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
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma timeDifference_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) {r : ℝ} (hr : 0 < r) :
    ‖timeDifference T hs r‖ ≤ r⁻¹ := by
  rw [timeDifference,norm_smul,norm_smul,norm_neg,Complex.norm_I,one_mul,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by positivity : 0 < 2*r))]
  calc
    (2*r)⁻¹*‖flow T hs r-flow T hs (-r)‖ ≤ (2*r)⁻¹*(1+1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sub_le _ _).trans (add_le_add (flow_opNorm T hs r) (flow_opNorm T hs (-r)))
    _ = r⁻¹ := by field_simp; ring



lemma timeIntegral_factor (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|))
    (a b : ℝ) (x : H) :
    timeIntegral T hs a b (S x) = S (∫ t in a..b,B t x) := by
  rw [← S.intervalIntegral_comp_comm
    ((regularizer_factor_continuous T hs S hS hSd B hB hK hb x).intervalIntegrable a b)]
  apply intervalIntegral.integral_congr
  intro t _
  exact congrArg (fun Q : H →L[ℂ] H => Q x) (hB t)

lemma timeAverage_pow_strong_one (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hl : Tendsto r atTop (𝓝 0)) (k : ℕ) (x : H) :
    Tendsto (fun n => ((timeAverage T hs (r n))^k) x) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n =>
    contraction_pow_initial_bound _ (timeAverage_norm T hs (hr n)) k x)
  simpa only [mul_zero] using
    (tendsto_iff_norm_sub_tendsto_zero.mp (timeAverage_strong_one T hs r hr hl x)).const_mul (k:ℝ)

end StronglyRationalVOA.SymmetricOperator

open Filter
open scoped Topology

open Filter MeasureTheory
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma timeAverage_inverse_factor (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S E F : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (hg : ∀ x, (S x,E x) ∈ T.graph) (hdef : E-E.adjoint = S.comp F)
    (r : ℝ) (x : H) : ∃ z, timeAverage T hs r (S x) = S z := by
  choose B hB hb using fun t => flow_regularizer_factor T hs S E F hS hSd hg hdef t
  refine ⟨((2*r)⁻¹ : ℝ) • (∫ t in -r..r,B t x),?_⟩
  rw [show S (((2*r)⁻¹ : ℝ) • (∫ t in -r..r,B t x)) =
      ((2*r)⁻¹ : ℝ) • S (∫ t in -r..r,B t x) from
        (S.restrictScalars ℝ).map_smul _ _,
    timeAverage,smul_apply,timeIntegral_factor T hs S hS hSd B hB (norm_nonneg F) hb]
end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma core_timeAverage_energyGraph (r : ℕ) (M K : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hK : ∀ v, ‖K v‖ ≤ D*‖(A.energyShift^r) v‖)
    (hk : ∀ x y : V, inner ℂ (M x) ((A.energyShift^r) y : Completion V)-
      inner ℂ ((A.energyShift^r) x : Completion V) (M y) = inner ℂ (K x) (y : Completion V))
    (hc : (HilbertCore.operator M).IsClosable) (hs : IsSelfAdjoint (HilbertCore.operator M).closure)
    (t : ℝ) {x y : Completion V} (hxy : (x,y) ∈ (U.energyPower r).graph) :
    ∃ z, (SymmetricOperator.timeAverage (HilbertCore.operator M).closure hs t x,z) ∈ (U.energyPower r).graph := by
  obtain ⟨z,hz⟩ := SymmetricOperator.timeAverage_inverse_factor _ hs
    (U.inverseSobolev r) (U.sobolevExtension r M) (U.sobolevExtension r K)
    (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)
    (U.sobolevExtension_inverse_graph r M hM hc) (U.sobolevExtension_defect r M K hM hK hk) t y
  rw [U.inverseSobolev_on_graph r hxy] at hz
  refine ⟨z,?_⟩
  rw [hz]
  exact U.inverseSobolev_graph r z

lemma firstOrderSmear_timeAverage_energyGraph {a : V} {d p : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n))
    {r : ℕ} (hrp : 1 ≤ r) (t : ℝ) {x y : Completion V}
    (hxy : (x,y) ∈ (U.energyPower r).graph) :
    ∃ z, (SymmetricOperator.timeAverage (HilbertCore.operator (A.smearedMap a d he f hf)).closure
      (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t x,z) ∈ (U.energyPower r).graph := by
  have hM (v : V) : ‖A.smearedMap a d he f hf v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^p)*C)*‖(A.energyShift^r) v‖ := by
    have hb' : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖(A.energyShift^1) v‖ := by
      simpa only [pow_one] using hb
    exact (A.smearedMap_bound he hf hb' v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono hrp v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hC))
  exact U.core_timeAverage_energyGraph r (A.smearedMap a d he f hf)
    (U.smearedPowerCommutator ha he hf r) hM
    (U.smearedPowerCommutator_bound ha he hC hb hf r)
    (U.smearedPowerCommutator_pairing ha hq hh he hf hr r)
    (HilbertCore.closable (U.smearedMap_symmetric ha hq hh he hf hr))
    (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t hxy

lemma firstOrderSmear_timeAverage_smoothEnergySpace {a : V} {d p : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n))
    (t : ℝ) {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    SymmetricOperator.timeAverage (HilbertCore.operator (A.smearedMap a d he f hf)).closure
      (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t x ∈ U.smoothEnergySpace := by
  rw [smoothEnergySpace,Submodule.mem_iInf] at hx ⊢
  intro r
  by_cases hr0 : r = 0
  · subst r
    obtain ⟨v,hv,_⟩ := (U.energyPower 0).mem_graph_iff.mp (U.energyPower_zero_graph
      (SymmetricOperator.timeAverage (HilbertCore.operator (A.smearedMap a d he f hf)).closure
        (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t x))
    dsimp only [Prod.fst] at hv
    rw [← hv]
    exact v.property
  · let v : (U.energyPower r).domain := ⟨x,hx r⟩
    obtain ⟨z,hz⟩ := U.firstOrderSmear_timeAverage_energyGraph ha hq hh he hC hb hf hr
      (show 1 ≤ r by omega) t ((U.energyPower r).mem_graph_iff.mpr ⟨v,rfl,rfl⟩)
    obtain ⟨w,hw,_⟩ := (U.energyPower r).mem_graph_iff.mp hz
    dsimp only [Prod.fst] at hw
    rw [← hw]
    exact w.property
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

lemma local_energy_regularization (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (P τ : Module.End ℂ D) (M T : H →ₗ.[ℂ] H) (hM : M.IsClosed)
    (hs : IsSelfAdjoint T)
    (hP : ∀ x : D, ((x:H),(P x:H)) ∈ M.graph)
    (hτ : ∀ x : D, ((x:H),(τ x:H)) ∈ T.graph)
    (hPs : ∀ x y : D, inner ℂ (P x:H) (y:H) = inner ℂ (x:H) (P y:H))
    (hflow : ∀ t x y, (x,y) ∈ M.graph → (flow T hs t x,flow T hs t y) ∈ M.graph)
    (r : ℝ) (hr : 0 < r)
    (hinv : ∀ x : D, timeAverage T hs r x ∈ D)
    (k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : D, ‖(P x:H)‖ ≤ C*∑ j ∈ Finset.range (k+1), ‖((τ^j) x:H)‖) :
    ∃ B : H →L[ℂ] H, IsSelfAdjoint B ∧
      (∀ x : D, B x = (P (((restricted D (timeAverage T hs r) hinv)^k) x):H)) ∧
      ∀ x : H, (((timeAverage T hs r)^k) x,B x) ∈ M.graph := by
  let R := timeAverage T hs r
  let q := restricted D R hinv
  have hRq : ∀ x : D, (q x:H) = R x := fun _ => rfl
  have hqτ : τ*q = q*τ := restricted_commutes_of_graph D τ R hinv T hτ
    (fun _ _ hxy => timeAverage_preserves_graph T T hs hs.isClosed (fun t _ _ h => flow_graph T hs t h) r hxy)
  have hqP : P*q = q*P := restricted_commutes_of_graph D P R hinv M hP
    (fun _ _ hxy => timeAverage_preserves_graph T M hs hM hflow r hxy)
  have hqnorm (x : D) : ‖q x‖ ≤ ‖x‖ := by
    change ‖R x‖ ≤ ‖(x:H)‖
    simpa only [one_mul] using R.le_of_opNorm_le (timeAverage_norm T hs hr) (x:H)
  have htq (x : D) : ‖τ (q x)‖ ≤ r⁻¹*‖x‖ := by
    have he : (τ (q x):H) = timeDifference T hs r x :=
      T.mem_graph_snd_inj (hτ (q x)) (timeAverage_graph' T hs r x) rfl
    change ‖(τ (q x):H)‖ ≤ r⁻¹*‖(x:H)‖
    rw [he]
    exact (timeDifference T hs r).le_of_opNorm_le (timeDifference_norm T hs hr) (x:H)
  have hb' (x : D) : ‖(P ((q^k) x):H)‖ ≤
      (C*(∑ j ∈ Finset.range (k+1), (r⁻¹)^j))*‖(x:H)‖ := by
    calc
      ‖(P ((q^k) x):H)‖ ≤ C*∑ j ∈ Finset.range (k+1), ‖((τ^j) ((q^k) x):H)‖ := hb _
      _ ≤ C*∑ j ∈ Finset.range (k+1), (r⁻¹)^j*‖(x:H)‖ := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Finset.sum_le_sum
        intro j hj
        exact commuting_core_power_bound τ q hqτ (inv_nonneg.mpr hr.le) hqnorm htq
          (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj) x
      _ = (C*(∑ j ∈ Finset.range (k+1), (r⁻¹)^j))*‖(x:H)‖ := by
        rw [← Finset.sum_mul,mul_assoc]
  have hqpow (x : D) : ((q^k) x:H) = (R^k) x := restricted_pow_coe D R hinv k x
  obtain ⟨B,hB,hg⟩ := bounded_regularization D hD M hM P (q^k) (R^k) hP hqpow hb'
  refine ⟨B,?_,hB,hg⟩
  apply regularization_selfAdjoint D hD P (q^k) (R^k) B (IsSelfAdjoint.pow (timeAverage_selfAdjoint T hs r) k)
    hqpow hB hPs
  exact Commute.pow_right hqP k

 

lemma selfAdjoint_of_local_energy (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (P τ : Module.End ℂ D) (M T : H →ₗ.[ℂ] H) (hM : M.IsClosed)
    (hMs : M.IsFormalAdjoint M) (hs : IsSelfAdjoint T)
    (hP : ∀ x : D, ((x:H),(P x:H)) ∈ M.graph)
    (hτ : ∀ x : D, ((x:H),(τ x:H)) ∈ T.graph)
    (hflow : ∀ t x y, (x,y) ∈ M.graph → (flow T hs t x,flow T hs t y) ∈ M.graph)
    (hinv : ∀ r, 0 < r → ∀ x : D, timeAverage T hs r x ∈ D)
    (k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : D, ‖(P x:H)‖ ≤ C*∑ j ∈ Finset.range (k+1), ‖((τ^j) x:H)‖) :
    IsSelfAdjoint M := by
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  have hl : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hPs (x y : D) : inner ℂ (P x:H) (y:H) = inner ℂ (x:H) (P y:H) :=
    formalAdjoint_graph_pairing hMs (hP x) (hP y)
  choose B hB hc hg using fun n => local_energy_regularization D hD P τ M T hM hs hP hτ hPs
    hflow (r n) (hr n) (hinv (r n) (hr n)) k hC hb
  have hdM : Dense (M.domain : Set H) := by
    apply hD.mono
    intro x hx
    obtain ⟨z,hz,_⟩ := M.mem_graph_iff.mp (hP ⟨x,hx⟩)
    change (z:H) = x at hz
    rw [← hz]
    exact z.property
  exact selfAdjoint_of_selfAdjoint_regularizers hdM hM hMs
    (fun n => (timeAverage T hs (r n))^k) B
    (fun n => (timeAverage_selfAdjoint T hs (r n)).pow k) hB hg
    (timeAverage_pow_strong_one T hs r hr hl k)

end StronglyRationalVOA.SymmetricOperator

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SymmetricWeakCommute
attribute [-instance] _root_.OAI.StronglyRationalVOA.SmoothCircleFamily.instCoeFunForallRealSmoothCircleFunction _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
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
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



lemma graph_entries_commute_of_local_energy
    (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (P Q τ : Module.End ℂ D) (M T N : H →ₗ.[ℂ] H) (hM : M.IsClosed)
    (hMs : M.IsFormalAdjoint M) (hs : IsSelfAdjoint T) (hN : N.IsClosable)
    (hP : ∀ x : D, ((x:H),(P x:H)) ∈ M.graph)
    (hτ : ∀ x : D, ((x:H),(τ x:H)) ∈ T.graph)
    (hNcore : N.graph = (D.subtype.prod (D.subtype.comp Q)).range)
    (hPQ : P*Q = Q*P)
    (hflowM : ∀ t x y, (x,y) ∈ M.graph → (flow T hs t x,flow T hs t y) ∈ M.graph)
    (hflowN : ∀ t x y, (x,y) ∈ N.closure.graph →
      (flow T hs t x,flow T hs t y) ∈ N.closure.graph)
    (hinv : ∀ r, 0 < r → ∀ x : D, timeAverage T hs r x ∈ D)
    (k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : D, ‖(P x:H)‖ ≤ C*∑ j ∈ Finset.range (k+1), ‖((τ^j) x:H)‖)
    (i j a b : Bool) :
    ClosedGraphData.entry M hM i j * ClosedGraphData.entry N.closure hN.closure_isClosed a b =
      ClosedGraphData.entry N.closure hN.closure_isClosed a b * ClosedGraphData.entry M hM i j := by
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  have hl : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hPs (x y : D) : inner ℂ (P x:H) (y:H) = inner ℂ (x:H) (P y:H) :=
    formalAdjoint_graph_pairing hMs (hP x) (hP y)
  choose B hB hc hg using fun n => local_energy_regularization D hD P τ M T hM hs hP hτ hPs
    hflowM (r n) (hr n) (hinv (r n) (hr n)) k hC hb
  have hself : IsSelfAdjoint M := selfAdjoint_of_local_energy D hD P τ M T hM hMs hs hP hτ
    hflowM hinv k hC hb
  have hQ (x : D) : ((x:H),(Q x:H)) ∈ N.closure.graph := by
    apply LinearPMap.le_graph_of_le (LinearPMap.le_closure N)
    rw [hNcore]
    exact ⟨x,rfl⟩
  have hreg (n : ℕ) (x y : H) (hxy : (x,y) ∈ M.graph) :
      B n x = ((timeAverage T hs (r n))^k) y := by
    have h := regularizer_adjoint hself.dense_domain _ (B n)
      ((timeAverage_selfAdjoint T hs (r n)).pow k) (hg n)
      (by rwa [show M.adjoint = M from hself])
    rwa [show (B n).adjoint = B n from hB n] at h
  have hBc (n : ℕ) (a b : Bool) :
      ClosedGraphData.entry N.closure hN.closure_isClosed a b * B n =
        B n * ClosedGraphData.entry N.closure hN.closure_isClosed a b := by
    symm
    apply ClosedGraphData.entry_commutes_of_graph_invariant N.closure hN.closure_isClosed (B n) ?_ ?_ a b
    · apply regularization_preserves_closure D P Q
        ((restricted D (timeAverage T hs (r n)) (hinv (r n) (hr n)))^k) (B n)
        (hc n) hPQ
      · apply Commute.pow_left
        exact (restricted_commutes_of_graph D Q _ _ N.closure hQ
          (fun _ _ hxy => timeAverage_preserves_graph T N.closure hs hN.closure_isClosed hflowN (r n) hxy)).symm
      · exact hN
      · exact hNcore
    · rw [show (B n).adjoint = B n from hB n]
      apply regularization_preserves_closure D P Q
        ((restricted D (timeAverage T hs (r n)) (hinv (r n) (hr n)))^k) (B n)
        (hc n) hPQ
      · apply Commute.pow_left
        exact (restricted_commutes_of_graph D Q _ _ N.closure hQ
          (fun _ _ hxy => timeAverage_preserves_graph T N.closure hs hN.closure_isClosed hflowN (r n) hxy)).symm
      · exact hN
      · exact hNcore
  have hRc (n : ℕ) (a b : Bool) :
      ClosedGraphData.entry N.closure hN.closure_isClosed a b * (timeAverage T hs (r n))^k =
        (timeAverage T hs (r n))^k * ClosedGraphData.entry N.closure hN.closure_isClosed a b := by
    apply Commute.pow_right
    apply timeAverage_commutes T hs
    intro t
    symm
    apply ClosedGraphData.entry_commutes_of_graph_invariant N.closure hN.closure_isClosed (flow T hs t)
      (hflowN t) ?_ a b
    rw [flow_adjoint]
    exact hflowN (-t)
  exact graph_entries_commute_of_regularizers M N.closure hM hN.closure_isClosed
    (fun n => (timeAverage T hs (r n))^k) B hg
    (timeAverage_pow_strong_one T hs r hr hl k) hreg hRc hBc i j a b

end StronglyRationalVOA.SymmetricOperator

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)



lemma stress_selfAdjoint (hc : A.toVertexAlgebra.C2Cofinite)
    {f : SmoothCircleFunction} (hf : f.IsReal) :
    IsSelfAdjoint (U.closedSmoothField hc A.conformalVector 2 f) :=
  U.smearedCore_essentialSelfAdjoint A.conformal_mem A.conformal_quasiPrimary U.stress_hermitian
    (U.polynomialEnergyBounds hc A.conformalVector) U.stress_physical_bound f.rapid_coefficients
    (SmoothCircleFunction.coefficient_real hf)

lemma closedSmoothField_symmetric (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hh : U.IsHermitian d a) {f : SmoothCircleFunction} (hf : f.IsReal) :
    (U.closedSmoothField hc a d f).IsFormalAdjoint (U.closedSmoothField hc a d f) := by
  exact SymmetricOperator.formalAdjoint_closure (U.smoothSmearedField_closable hc ha f)
    (U.smoothSmearedField_closable hc ha f)
    (HilbertCore.formalAdjoint (U.smearedMap_symmetric ha hq hh
      (U.polynomialEnergyBounds hc a) f.rapid_coefficients (SmoothCircleFunction.coefficient_real hf)))

lemma stress_timeAverage_smooth (hc : A.toVertexAlgebra.C2Cofinite)
    {f : SmoothCircleFunction} (hf : f.IsReal) (r : ℝ) {x : Completion V}
    (hx : x ∈ U.smoothEnergySpace) :
    SymmetricOperator.timeAverage (U.closedSmoothField hc A.conformalVector 2 f)
      (U.stress_selfAdjoint hc hf) r x ∈ U.smoothEnergySpace := by
  exact U.firstOrderSmear_timeAverage_smoothEnergySpace A.conformal_mem
    A.conformal_quasiPrimary U.stress_hermitian (U.polynomialEnergyBounds hc A.conformalVector)
    (by linarith [U.centralCharge_nonneg]) U.stress_physical_bound f.rapid_coefficients
    (SmoothCircleFunction.coefficient_real hf) r hx



end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.SmoothCircleFunction
lemma power_tsupport_subset (f : SmoothCircleFunction) {k : ℕ} (hk : k ≠ 0) :
    tsupport (f.power k) ⊆ tsupport f := by
  apply closure_mono
  intro t ht
  contrapose! ht
  simp only [Function.mem_support, ne_eq, not_not] at ht ⊢
  simpa only [power_apply,ht] using zero_pow hk
end StronglyRationalVOA.SmoothCircleFunction

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

lemma evolution_apply_derivative {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (t : ℝ) (x : H) :
    HasDerivAt (fun s => evolution K s x) (K t (evolution K t x)) t :=
  ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (evolution_derivative hK hM hb t)



end StronglyRationalVOA.TimeOrdered

open MeasureTheory Set Filter
open scoped Topology Interval

open Set Filter
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

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)



lemma stressPropagator_unitary (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) :
    U.stressPropagator hc f t ∈ unitary (Completion V →L[ℂ] Completion V) :=
  (U.exists_stressPropagator hc f t).choose_spec.1

lemma stressPropagator_star_factor (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {r : ℕ} (hr : 1 ≤ r) (t : ℝ) :
    ∃ B : Completion V →L[ℂ] Completion V,
      star (U.stressPropagator hc f t)*U.inverseSobolev r=U.inverseSobolev r*B ∧
      ‖B‖ ≤ Real.exp ((f.bound (2+r)*((1+A.centralCharge.re)*r))*|t|) := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  obtain ⟨G,hG,hGn⟩ := U.stressPath_cutoff_commutator hc f hr
  apply TimeOrdered.regularizer_factor_of_limits
    (fun n => star (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t)) _
    (by simpa only [star_star] using U.stressPropagator_limit hc f t)
    (U.inverseSobolev r) (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r) (Real.exp_pos _).le
  intro n x
  simp only [star_star]
  exact TimeOrdered.evolution_energy_bound (U.stressCutoff_continuous hc n f.rapid f.continuous)
    (show 0 ≤ (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) by
      exact mul_nonneg (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (by positivity))
    (U.stressPath_cutoff_bound hc f n) (fun s => U.stressCutoff_skew hc n (f.rapid s) (f.real s))
    (U.inverseSobolev r) (G n) (hG n) (hGn n) t x
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma inverseSobolev_zero : U.inverseSobolev 0=1 := by
  ext x
  exact U.inverseSobolev_on_graph 0 (U.energyPower_zero_graph x)

lemma sobolev_interpolation_bound (r n : ℕ) {x p q : Completion V}
    (hp : U.inverseSobolev r p=x) (hq : U.inverseSobolev 1 q=p) :
    ‖p‖ ≤ (1+(n:ℝ))^r*‖x‖+(1+(n:ℝ))⁻¹*‖q‖ := by
  have he : U.energyCutoff n p=U.truncatedEnergyPower n r x := by
    apply U.inverseSobolev_injective r
    calc
      _ = U.energyCutoff n (U.inverseSobolev r p) :=
        congrArg (fun B : Completion V →L[ℂ] Completion V => B p) (U.energyCutoff_inverseSobolev n r).eq.symm
      _ = U.energyCutoff n x := by rw [hp]
      _ = _ := (congrArg (fun B : Completion V →L[ℂ] Completion V => B x) (U.inverseSobolev_truncated n r)).symm
  calc
    ‖p‖ ≤ ‖U.energyCutoff n p‖+‖p-U.energyCutoff n p‖ := by
      simpa only [add_sub_cancel] using norm_add_le (U.energyCutoff n p) (p-U.energyCutoff n p)
    _ ≤ (1+(n:ℝ))^r*‖x‖+(1+(n:ℝ))⁻¹*‖q‖ := by
      apply add_le_add
      · rw [he]
        exact (U.truncatedEnergyPower n r).le_of_opNorm_le (U.truncatedEnergyPower_norm n r) x
      · simpa only [mul_apply_eq_comp,sub_apply,one_apply_eq_self,hq] using
          ((1-U.energyCutoff n)*U.inverseSobolev 1).le_of_opNorm_le (U.energyCutoff_tail_inverse n) q

 

lemma tendsto_sobolev_of_extra_bound {ι : Type*} {l : Filter ι}
    (r : ℕ) (x p q : ι → Completion V)
    (hp : ∀ i, U.inverseSobolev r (p i)=x i)
    (hq : ∀ i, U.inverseSobolev 1 (q i)=p i)
    (hx : Tendsto x l (𝓝 0)) {C : ℝ} (hb : ∀ᶠ i in l, ‖q i‖ ≤ C) :
    Tendsto p l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht : Tendsto (fun n : ℕ => (1+(n:ℝ))⁻¹*C) atTop (𝓝 0) := by
    simpa only [one_div,add_comm,zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2))).exists
  have ht' : Tendsto (fun i => (1+(n:ℝ))^r*‖x i‖) l (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using hx.norm.const_mul ((1+(n:ℝ))^r)
  filter_upwards [hb,ht'.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2))] with i hi hi'
  rw [dist_zero_right]
  have h := U.sobolev_interpolation_bound r n (hp i) (hq i)
  have h2 := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (1+(n:ℝ))⁻¹)
  linarith

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma stressPropagator_star_smooth (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    star (U.stressPropagator hc f t) x ∈ U.smoothEnergySpace := by
  apply U.preserves_smoothEnergySpace_of_factor _ _ hx
  intro r hr
  obtain ⟨B,hB,_⟩ := U.stressPropagator_star_factor hc f hr t
  exact ⟨B,hB⟩

lemma stressCutoff_evolution_factor (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {r : ℕ} (hr : 1 ≤ r) (n : ℕ) (t : ℝ) :
    ∃ B : Completion V →L[ℂ] Completion V,
      TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t*U.inverseSobolev r=U.inverseSobolev r*B ∧
      ‖B‖ ≤ Real.exp ((f.bound (2+r)*((1+A.centralCharge.re)*r))*|t|) := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  obtain ⟨G,hG,hGn⟩ := U.stressPath_cutoff_commutator hc f hr
  exact TimeOrdered.evolution_regularizer_factor (U.stressCutoff_continuous hc n f.rapid f.continuous)
    (show 0 ≤ (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) by
      exact mul_nonneg (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (by positivity))
    (U.stressPath_cutoff_bound hc f n) (fun s => U.stressCutoff_skew hc n (f.rapid s) (f.real s))
    (U.inverseSobolev r) (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r) (G n) (hG n) (hGn n) t

lemma stressCutoff_evolution_smooth (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) (t : ℝ) {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x ∈ U.smoothEnergySpace := by
  apply U.preserves_smoothEnergySpace_of_factor _ _ hx
  intro r hr
  obtain ⟨B,hB,_⟩ := U.stressCutoff_evolution_factor hc f hr n t
  exact ⟨B,hB⟩

 def stressCutoffEvolutionSmooth (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) (t : ℝ) : U.smoothEnergySpace →ₗ[ℂ] U.smoothEnergySpace :=
  ((TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t).toLinearMap.comp
    U.smoothEnergySpace.subtype).codRestrict U.smoothEnergySpace
      (fun x => U.stressCutoff_evolution_smooth hc f n t x.property)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter Set
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma stressCutoff_normalized_norm (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) {r : ℕ} (hr : 1 ≤ r) :
    ‖U.stressCutoff hc n hf*U.inverseSobolev r‖ ≤ coefficientSeminorm f 2*(1+A.centralCharge.re) := by
  rw [U.stressCutoff_normalized hc n hf hr,norm_smul,Complex.norm_I,one_mul]
  calc
    _ ≤ (‖U.energyCutoff n‖*‖U.stressNormalized hc hf r‖)*‖U.energyCutoff n‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖U.stressNormalized hc hf r‖)*1 := by
      gcongr <;> exact U.energyCutoff_norm n
    _ ≤ _ := by simpa only [one_mul,mul_one] using U.stressNormalized_norm hc hf hr

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter Set MeasureTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressCutoffNormalized2
attribute [-instance] _root_.OAI.StronglyRationalVOA.SmoothCircleFamily.instCoeFunForallRealSmoothCircleFunction _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
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
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma stressCutoff_normalized_limit (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) :
    Tendsto (fun n => U.stressCutoff hc n hf*U.inverseSobolev 2) atTop
      (𝓝 (Complex.I • U.stressNormalized hc hf 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => U.stressCutoff_error hc n hf)
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa only [one_div,add_comm,zero_mul] using
    h.mul_const ((coefficientSeminorm f 3+coefficientSeminorm f 2)*(1+A.centralCharge.re))

 def stressPropagatorDerivative (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) (x : U.smoothEnergySpace) : Completion V :=
  Complex.I • U.stressNormalized hc (f.rapid t) 2
    (U.smoothEnergyPower 2 (U.stressPropagatorSmooth hc f t x))

lemma stressCutoff_evolution_derivative (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) (t : ℝ) (x : Completion V) :
    HasDerivAt (fun s => TimeOrdered.evolution (fun q => U.stressCutoff hc n (f.rapid q)) s x)
      (U.stressCutoff hc n (f.rapid t)
        (TimeOrdered.evolution (fun q => U.stressCutoff hc n (f.rapid q)) t x)) t := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  exact TimeOrdered.evolution_apply_derivative (U.stressCutoff_continuous hc n f.rapid f.continuous)
    (show 0 ≤ (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) by
      exact mul_nonneg (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (by positivity))
    (U.stressPath_cutoff_bound hc f n) t x

lemma stressCutoff_evolution_continuous (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) (x : Completion V) :
    Continuous (fun t => TimeOrdered.evolution (fun q => U.stressCutoff hc n (f.rapid q)) t x) :=
  continuous_iff_continuousAt.mpr (fun t => (U.stressCutoff_evolution_derivative hc f n t x).continuousAt)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology

open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction



def primaryTransport (f g : SmoothCircleFunction) (d : ℕ) : SmoothCircleFunction :=
  (((f.differentiated 1).mul g).scale ((d:ℂ)-1)).add
    ((f.mul (g.differentiated 1)).scale (-1))
lemma primaryTransport_apply (f g : SmoothCircleFunction) (d : ℕ) (t : ℝ) :
    f.primaryTransport g d t=((d:ℂ)-1)*deriv f t*g t-f t*deriv g t := by
  simp only [primaryTransport,add_apply,scale_apply,mul_apply,differentiated_apply,iteratedDeriv_one]
  ring

end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressPropagatorDerivative
attribute [-instance] _root_.OAI.StronglyRationalVOA.SmoothCircleFamily.instCoeFunForallRealSmoothCircleFunction _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
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

def stressPropagatorEquiv (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) :
    Completion V ≃ₗᵢ[ℂ] Completion V :=
  Unitary.linearIsometryEquiv ⟨U.stressPropagator hc f t,U.stressPropagator_unitary hc f t⟩

lemma stressPropagatorEquiv_apply (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) (x : Completion V) :
    U.stressPropagatorEquiv hc f t x=U.stressPropagator hc f t x := rfl


lemma primary_transport_smooth_covariance (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (f : StressPath) {g h : ℤ → ℂ} (hg : RapidCoefficients g) (hh : RapidCoefficients h) (t : ℝ)
    (he : ∀ x y : U.smoothEnergySpace,
      inner ℂ (U.stressPropagator hc f t x)
        (U.smoothSmear hc ha hh (U.stressPropagatorSmooth hc f t y) : Completion V)=
      inner ℂ (x:Completion V) (U.smoothSmear hc ha hg y : Completion V))
    (y : U.smoothEnergySpace) :
    (U.smoothSmear hc ha hh (U.stressPropagatorSmooth hc f t y) : Completion V)=
      U.stressPropagator hc f t (U.smoothSmear hc ha hg y : Completion V) := by
  let E := U.stressPropagatorEquiv hc f t
  apply E.symm.injective
  apply ext_inner_left ℂ
  intro z
  refine U.smoothEnergySpace_dense.denseRange_val.induction_on z ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · intro w
    have h := he w y
    have hi := E.inner_map_map (w:Completion V)
      (E.symm (U.smoothSmear hc ha hh (U.stressPropagatorSmooth hc f t y)))
    rw [E.apply_symm_apply] at hi
    change inner ℂ (w:Completion V) (E.symm (U.smoothSmear hc ha hh (U.stressPropagatorSmooth hc f t y))) =
      inner ℂ (w:Completion V) (E.symm (E (U.smoothSmear hc ha hg y)))
    rw [E.symm_apply_apply]
    exact hi.symm.trans h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter
open scoped Topology ContDiff

open Filter
open scoped Topology ContDiff

open Filter
open scoped Topology ContDiff

open Filter MeasureTheory Set
open scoped Topology ContDiff
namespace StronglyRationalVOA

namespace SmoothCircleFunction
lemma coefficient_weighted_bound (f : SmoothCircleFunction) (k : ℕ) {M : ℝ}
    (hM : 0 ≤ M) (h0 : ∀ x ∈ Icc 0 (2*Real.pi), ‖f x‖ ≤ M)
    (hk : ∀ x ∈ Icc 0 (2*Real.pi), ‖iteratedDeriv k f x‖ ≤ M) (n : ℤ) :
    ‖f.coefficient n‖*(1+|(n:ℝ)|)^k ≤ 2^k*M := by
  by_cases hn : n=0
  · subst n
    simp only [Int.cast_zero,abs_zero,add_zero,one_pow,mul_one]
    exact (coefficient_norm_le h0 0).trans (le_mul_of_one_le_left hM (one_le_pow₀ (by norm_num)))
  · have hx : 1 ≤ |(n:ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have he := congrArg norm (f.coefficient_iteratedDeriv k hn)
    have hn' : ‖(n:ℂ)‖=|(n:ℝ)| := by rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
    simp only [norm_mul,norm_pow,Complex.norm_I,one_mul,hn'] at he
    have hb : |(n:ℝ)|^k*‖f.coefficient n‖ ≤ M := he.trans_le (coefficient_norm_le hk n)
    calc
      _ ≤ ‖f.coefficient n‖*(2*|(n:ℝ)|)^k := by gcongr; linarith
      _ = 2^k*(|(n:ℝ)|^k*‖f.coefficient n‖) := by rw [mul_pow]; ring
      _ ≤ 2^k*M := mul_le_mul_of_nonneg_left hb (by positivity)
end SmoothCircleFunction
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_CoefficientSummableBound
attribute [-instance] _root_.OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
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

namespace SmoothCircleFunction

lemma coefficient_summable_bound (f : SmoothCircleFunction) (r : ℕ) {M : ℝ}
    (hM : 0 ≤ M) (h0 : ∀ x ∈ Icc 0 (2*Real.pi), ‖f x‖ ≤ M)
    (hk : ∀ x ∈ Icc 0 (2*Real.pi), ‖iteratedDeriv (r+2) f x‖ ≤ M) (n : ℤ) :
    ‖f.coefficient n‖*(1+|(n:ℝ)|)^r ≤ (2^(r+2)*M)*((1+|(n:ℝ)|)^2)⁻¹ := by
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+|(n:ℝ)|) _)).mpr
  convert f.coefficient_weighted_bound (r+2) hM h0 hk n using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | (rw [pow_add]; ring)
end SmoothCircleFunction

namespace SmoothCircleFamily
variable (f : SmoothCircleFamily)
lemma time_smooth (x : ℝ) : ContDiff ℝ ∞ (fun t => f t x) :=
  f.smooth.comp (contDiff_id.prodMk contDiff_const)
lemma space_iterated_smooth (k : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv k (f p.1) p.2) :=
  joint_iterated_space_deriv_smooth f.smooth k
lemma time_derivative_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1) := by
  have h := joint_space_deriv_smooth (f.smooth.comp (contDiff_snd.prodMk contDiff_fst))
  exact h.comp (contDiff_snd.prodMk contDiff_fst)

def timeDerivative : SmoothCircleFamily where
  toFun t := {
    toFun := fun x => deriv (fun s => f s x) t
    periodic := fun x => by
      have he : (fun s => f s (x+2*Real.pi))=(fun s => f s x) := funext fun s => (f s).periodic x
      exact congrArg (fun g : ℝ → ℂ => deriv g t) he
    smooth := f.time_derivative_smooth.comp (contDiff_const.prodMk contDiff_id) }
  smooth := f.time_derivative_smooth

lemma coefficient_derivative (t : ℝ) (n : ℤ) :
    HasDerivAt (fun s => (f s).coefficient n) ((f.timeDerivative t).coefficient n) t := by
  let K (x : ℝ) : ℂ := fourier (-n) (x : AddCircle (2*Real.pi))
  have hK : Continuous K := by unfold K; fun_prop
  let F (s x : ℝ) := K x*f s x
  let G (s x : ℝ) := K x*f.timeDerivative s x
  have hF (s : ℝ) : Continuous (F s) := hK.mul (f s).smooth.continuous
  have hG : Continuous (Function.uncurry G) :=
    (hK.comp continuous_snd).mul f.timeDerivative.smooth.continuous
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    hG.continuousOn (s := Icc (t-1) (t+1) ×ˢ Icc 0 (2*Real.pi))
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := G) (μ := volume) (a := 0) (b := 2*Real.pi)
    (s := Icc (t-1) (t+1)) (bound := fun _ => M)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun s => (hF s).aestronglyMeasurable))
    ((hF t).intervalIntegrable _ _)
    ((hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x hx s hs => hM (s,x) ⟨hs, by
      rw [uIoc_of_le SmoothCircleFunction.period_pos.le] at hx
      exact ⟨hx.1.le,hx.2⟩⟩))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun x _ s _ => by
      exact ((f.time_smooth x).differentiable (by simp) s).hasDerivAt.const_mul (K x)))
  have he (s : ℝ) : (f s).coefficient n = (1/(2*Real.pi):ℝ) • ∫ x in 0..2*Real.pi, F s x := by
    rw [SmoothCircleFunction.coefficient,fourierCoeffOn_eq_integral]
    simp only [sub_zero,smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    simp only [F,K,fourier_coe_apply,sub_zero]
  have he' : (f.timeDerivative t).coefficient n = (1/(2*Real.pi):ℝ) • ∫ x in 0..2*Real.pi, G t x := by
    rw [SmoothCircleFunction.coefficient,fourierCoeffOn_eq_integral]
    simp only [sub_zero,smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    simp only [G,K,fourier_coe_apply,sub_zero]
  simp_rw [he,he']
  exact hd.2.const_smul ((1/(2*Real.pi):ℝ))
end SmoothCircleFamily
end StronglyRationalVOA
namespace StronglyRationalVOA.SmoothCircleFamily
lemma coefficient_bound_compact (f : SmoothCircleFamily) (a b : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ n : ℤ,
      ‖(f t).coefficient n‖*(1+|(n:ℝ)|)^r ≤ C*((1+|(n:ℝ)|)^2)⁻¹ := by
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    f.smooth.continuous.continuousOn (s := Icc a b ×ˢ Icc 0 (2*Real.pi))
  obtain ⟨N,hN⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (f.space_iterated_smooth (r+2)).continuous.continuousOn (s := Icc a b ×ˢ Icc 0 (2*Real.pi))
  let B := max 0 (max M N)
  have hB : 0 ≤ B := le_max_left _ _
  refine ⟨2^(r+2)*B,by positivity,fun t ht n => (f t).coefficient_summable_bound r hB ?_ ?_ n⟩
  · intro x hx
    exact (hM (t,x) ⟨ht,hx⟩).trans ((le_max_left M N).trans (le_max_right 0 _))
  · intro x hx
    exact (hN (t,x) ⟨ht,hx⟩).trans ((le_max_right M N).trans (le_max_right 0 _))

lemma seminorm_continuous (f : SmoothCircleFamily) (t : ℝ) (r : ℕ) :
    Tendsto (fun s => coefficientSeminorm (fun n => (f s).coefficient n-(f t).coefficient n) r)
      (𝓝 t) (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := f.coefficient_bound_compact (t-1) (t+1) r
  have ht : t ∈ Icc (t-1) (t+1) := ⟨by linarith,by linarith⟩
  apply coefficientSeminorm_tendsto_zero r (C := 2*C)
  · intro n
    simpa only [sub_self] using ((f.coefficient_derivative t n).continuousAt.tendsto.sub_const ((f t).coefficient n))
  · filter_upwards [Icc_mem_nhds (show t-1<t by linarith) (show t<t+1 by linarith)] with s hs
    intro n
    calc
      _ ≤ (‖(f s).coefficient n‖+‖(f t).coefficient n‖)*(1+|(n:ℝ)|)^r := by gcongr; exact norm_sub_le _ _
      _ = ‖(f s).coefficient n‖*(1+|(n:ℝ)|)^r+‖(f t).coefficient n‖*(1+|(n:ℝ)|)^r := by ring
      _ ≤ C*((1+|(n:ℝ)|)^2)⁻¹+C*((1+|(n:ℝ)|)^2)⁻¹ := add_le_add (hb s hs n) (hb t ht n)
      _ = _ := by ring
end StronglyRationalVOA.SmoothCircleFamily
namespace StronglyRationalVOA.SmoothCircleFamily
lemma seminorm_derivative (f : SmoothCircleFamily) (t : ℝ) (r : ℕ) :
    Tendsto (fun s => coefficientSeminorm
      (fun n => (((s-t)⁻¹:ℝ):ℂ)*((f s).coefficient n-(f t).coefficient n)-
        (f.timeDerivative t).coefficient n) r) (𝓝[≠] t) (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := f.timeDerivative.coefficient_bound_compact (t-1) (t+1) r
  have ht : t ∈ Icc (t-1) (t+1) := ⟨by linarith,by linarith⟩
  apply coefficientSeminorm_tendsto_zero r (C := 2*C)
  · intro n
    have h := (hasDerivAt_iff_tendsto_slope.mp (f.coefficient_derivative t n)).sub_const
      ((f.timeDerivative t).coefficient n)
    simpa only [slope,vsub_eq_sub,sub_self,Complex.real_smul] using h
  · have hnh : Icc (t-1) (t+1) ∈ 𝓝[≠] t := nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith))
    filter_upwards [hnh,self_mem_nhdsWithin] with s hs hst
    have hne : s-t ≠ 0 := sub_ne_zero.mpr hst
    intro n
    let W : ℝ := (1+|(n:ℝ)|)^r
    have hW : 0 < W := pow_pos (by positivity) _
    have hder (u : ℝ) (_hu : u ∈ Icc (t-1) (t+1)) :
        HasDerivWithinAt (fun q => (W:ℂ)*(f q).coefficient n)
          ((W:ℂ)*(f.timeDerivative u).coefficient n) (Icc (t-1) (t+1)) u :=
      ((f.coefficient_derivative u n).const_mul (W:ℂ)).hasDerivWithinAt
    have hbd (u : ℝ) (hu : u ∈ Icc (t-1) (t+1)) :
        ‖(W:ℂ)*(f.timeDerivative u).coefficient n‖ ≤ C*((1+|(n:ℝ)|)^2)⁻¹ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hW,mul_comm]
      exact hb u hu n
    have hd := (convex_Icc (t-1) (t+1)).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd ht hs
    rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hW] at hd
    have hsl : ‖(((s-t)⁻¹:ℝ):ℂ)*((f s).coefficient n-(f t).coefficient n)‖*W ≤
        C*((1+|(n:ℝ)|)^2)⁻¹ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_inv]
      calc
        _ = (W*‖(f s).coefficient n-(f t).coefficient n‖)*|s-t|⁻¹ := by ring
        _ ≤ (C*((1+|(n:ℝ)|)^2)⁻¹*‖s-t‖)*|s-t|⁻¹ := mul_le_mul_of_nonneg_right hd (inv_nonneg.mpr (abs_nonneg _))
        _ = _ := by rw [Real.norm_eq_abs,mul_assoc,mul_inv_cancel₀ (abs_ne_zero.mpr hne),mul_one]
    calc
      _ ≤ (‖(((s-t)⁻¹:ℝ):ℂ)*((f s).coefficient n-(f t).coefficient n)‖+
        ‖(f.timeDerivative t).coefficient n‖)*W := by gcongr; exact norm_sub_le _ _
      _ = _ := add_mul _ _ _
      _ ≤ C*((1+|(n:ℝ)|)^2)⁻¹+C*((1+|(n:ℝ)|)^2)⁻¹ := add_le_add hsl (hb t ht n)
      _ = _ := by ring
end StronglyRationalVOA.SmoothCircleFamily
namespace StronglyRationalVOA.SmoothCircleFamily
lemma seminorm_bound_stationary (f : SmoothCircleFamily) (a b : ℝ)
    (hz : ∀ t ∉ Icc a b, ∀ x, f t x=0) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, coefficientSeminorm (f t).coefficient r ≤ C := by
  obtain ⟨C,hC,hb⟩ := f.coefficient_bound_compact a b r
  let D := ∑' n : ℤ, C*((1+|(n:ℝ)|)^2)⁻¹
  have hD : 0 ≤ D := tsum_nonneg (fun n => by positivity)
  refine ⟨D,hD,fun t => ?_⟩
  by_cases ht : t ∈ Icc a b
  · exact Summable.tsum_le_tsum (hb t ht) ((f t).rapid_coefficients r) (summable_circle_decay.mul_left C)
  · have he (n : ℤ) : (f t).coefficient n=0 := by
      rw [SmoothCircleFunction.coefficient,fourierCoeffOn_eq_integral]
      simp only [hz t ht,smul_zero,intervalIntegral.integral_zero]
    simpa only [coefficientSeminorm,he,norm_zero,zero_mul,tsum_zero] using hD

def toStressPath (f : SmoothCircleFamily) (hr : ∀ t, (f t).IsReal) (a b : ℝ)
    (hz : ∀ t ∉ Icc a b, ∀ x, f t x=0) : CFTTypeVOA.UnitaryStructure.StressPath where
  coefficients t := (f t).coefficient
  rapid t := (f t).rapid_coefficients
  real t := SmoothCircleFunction.coefficient_real (hr t)
  continuous t := f.seminorm_continuous t 2
  bound r := (f.seminorm_bound_stationary a b hz r).choose
  bound_nonneg r := (f.seminorm_bound_stationary a b hz r).choose_spec.1
  seminorm_bound t r := (f.seminorm_bound_stationary a b hz r).choose_spec.2 t
end StronglyRationalVOA.SmoothCircleFamily

open Filter Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)

def angularVelocity : SmoothCircleFamily where
  toFun t := {
    toFun := fun x => (2*Real.pi*φ.velocity t (x/(2*Real.pi)) : ℝ)
    periodic := fun x => by
      dsimp only
      rw [angular_shift,φ.velocity_periodic]
    smooth := Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul ((φ.velocity_smooth.comp (contDiff_const.prodMk (contDiff_id.div_const _))))) }
  smooth := Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (φ.velocity_smooth.comp (contDiff_fst.prodMk (contDiff_snd.div_const _))))
lemma angularVelocity_real (t : ℝ) : (φ.angularVelocity t).IsReal := fun x => by
  change star ((2*Real.pi*φ.velocity t (x/(2*Real.pi)):ℝ):ℂ)=_
  exact Complex.conj_ofReal _
lemma angularVelocity_stationary (t : ℝ) (ht : t ∉ Icc 0 1) (x : ℝ) : φ.angularVelocity t x=0 := by
  change ((2*Real.pi*φ.velocity t (x/(2*Real.pi)):ℝ):ℂ)=0
  simp only [φ.velocity_stationary ht,Pi.zero_apply,mul_zero,Complex.ofReal_zero]
def angularStressPath : CFTTypeVOA.UnitaryStructure.StressPath :=
  φ.angularVelocity.toStressPath φ.angularVelocity_real 0 1 φ.angularVelocity_stationary

def angularDensity (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1) (k : ℕ) :
    SmoothCircleFamily where
  toFun t := {
    toFun := fun x => (φ.density g k t (x/(2*Real.pi)) : ℝ)
    periodic := fun x => by dsimp only; rw [angular_shift,φ.density_periodic hp]
    smooth := Complex.ofRealCLM.contDiff.comp ((φ.density_smooth hg k).comp
      (contDiff_const.prodMk (contDiff_id.div_const _))) }
  smooth := Complex.ofRealCLM.contDiff.comp ((φ.density_smooth hg k).comp
    (contDiff_fst.prodMk (contDiff_snd.div_const _)))
lemma angularDensity_real (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (k : ℕ) (t : ℝ) : (φ.angularDensity g hg hp k t).IsReal := fun _ => Complex.conj_ofReal _
lemma angularVelocity_space_derivative (t x : ℝ) :
    HasDerivAt (φ.angularVelocity t) (deriv (φ.velocity t) (x/(2*Real.pi)):ℝ) x := by
  have hv := (((φ.velocity_smooth.comp ((contDiff_const (c := t)).prodMk contDiff_id)).differentiable
    (by simp) (x/(2*Real.pi))).hasDerivAt).comp x ((hasDerivAt_id x).div_const (2*Real.pi))
  have hd := (hv.const_mul (2*Real.pi)).ofReal_comp
  convert hd using 1 <;> first | rfl | (congr 1; dsimp only [Function.comp_def,id_eq]; field_simp [Real.pi_ne_zero])
lemma angularDensity_space_derivative (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (k : ℕ) (t x : ℝ) :
    HasDerivAt (φ.angularDensity g hg hp k t)
      ((deriv (φ.density g k t) (x/(2*Real.pi))/(2*Real.pi):ℝ):ℂ) x := by
  have hv := (((φ.density_smooth hg k).comp ((contDiff_const (c := t)).prodMk contDiff_id)).differentiable
    (by simp) (x/(2*Real.pi))).hasDerivAt.comp x ((hasDerivAt_id x).div_const (2*Real.pi))
  convert hv.ofReal_comp using 1 <;> first | rfl | (congr 1; dsimp only [Function.comp_def,id_eq]; ring)
lemma angularDensity_transport (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (k : ℕ) (t : ℝ) :
    (φ.angularDensity g hg hp k).timeDerivative t =
      (φ.angularVelocity t).primaryTransport (φ.angularDensity g hg hp k t) (k+1) := by
  apply SmoothCircleFunction.ext
  intro x
  change deriv (fun s => ((φ.density g k s (x/(2*Real.pi)):ℝ):ℂ)) t=_
  rw [(φ.density_time_derivative hg k t (x/(2*Real.pi))).ofReal_comp.deriv,
    SmoothCircleFunction.primaryTransport_apply,(φ.angularVelocity_space_derivative t x).deriv,
    (φ.angularDensity_space_derivative g hg hp k t x).deriv]
  change _ = ((↑(k+1):ℂ)-1)*(deriv (φ.velocity t) (x/(2*Real.pi)):ℝ)*
      (φ.density g k t (x/(2*Real.pi)):ℝ)-
      (2*Real.pi*φ.velocity t (x/(2*Real.pi)):ℝ)*
      (deriv (φ.density g k t) (x/(2*Real.pi))/(2*Real.pi):ℝ)
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
 
def cocycleDensity (f g : SmoothCircleFunction) : SmoothCircleFunction :=
  ((f.differentiated 3).add (f.differentiated 1)).mul g
end StronglyRationalVOA.SmoothCircleFunction

open Filter MeasureTheory Set
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressSmoothness
attribute [-instance] _root_.OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
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
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)
lemma realAngularVelocity_periodic (t : ℝ) :
    Function.Periodic (fun x => φ.realAngularVelocity (t,x)) (2*Real.pi) := by
  intro x
  exact Complex.ofReal_injective ((φ.angularVelocity t).periodic x)
lemma realAngularDensity_periodic {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (k : ℕ) (t : ℝ) : Function.Periodic (fun x => φ.realAngularDensity g k (t,x)) (2*Real.pi) := by
  intro x
  exact Complex.ofReal_injective ((φ.angularDensity g hg hp k t).periodic x)
lemma realAngularDensity_PDE {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (t x : ℝ) :
    deriv (fun s => φ.realAngularDensity g 1 (s,x)) t=
      deriv (fun y => φ.realAngularVelocity (t,y)) x*φ.realAngularDensity g 1 (t,x)-
      φ.realAngularVelocity (t,x)*deriv (fun y => φ.realAngularDensity g 1 (t,y)) x := by
  have hD : ContDiff ℝ ∞ (φ.realAngularDensity g 1) := φ.realAngularDensity_smooth hg 1
  have hV := φ.realAngularVelocity_smooth
  have he := congrArg (fun f : SmoothCircleFunction => f x) (φ.angularDensity_transport g hg hp 1 t)
  change deriv (fun s => ((φ.realAngularDensity g 1 (s,x)):ℂ)) t=_ at he
  rw [SmoothCircleFunction.primaryTransport_apply] at he
  change _ = ((2:ℂ)-1)*deriv (fun y => ((φ.realAngularVelocity (t,y)):ℂ)) x*
      ((φ.realAngularDensity g 1 (t,x)):ℂ)-
      ((φ.realAngularVelocity (t,x)):ℂ)*deriv (fun y => ((φ.realAngularDensity g 1 (t,y)):ℂ)) x at he
  rw [RealCircleCalculus.deriv_ofReal (g := fun s => φ.realAngularDensity g 1 (s,x)) ((hD.comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp)),
    RealCircleCalculus.deriv_ofReal (g := fun y => φ.realAngularVelocity (t,y)) ((hV.comp ((contDiff_const (c := t)).prodMk contDiff_id)).differentiable (by simp)),
    RealCircleCalculus.deriv_ofReal (g := fun y => φ.realAngularDensity g 1 (t,y)) ((hD.comp ((contDiff_const (c := t)).prodMk contDiff_id)).differentiable (by simp))] at he
  apply Complex.ofReal_injective
  push_cast
  norm_num only [show (2:ℂ)-1=1 from by norm_num,one_mul] at he
  exact he
lemma angular_cocycle_coefficient {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (t : ℝ) :
    ((φ.angularVelocity t).cocycleDensity (φ.angularDensity g hg hp 1 t)).coefficient 0 =
      ((2*Real.pi)⁻¹*(∫ x in 0..2*Real.pi,
        (deriv (deriv (deriv (fun y => φ.realAngularVelocity (t,y)))) x+
          deriv (fun y => φ.realAngularVelocity (t,y)) x)*φ.realAngularDensity g 1 (t,x)):ℝ) := by
  let v : ℝ → ℝ := fun x => φ.realAngularVelocity (t,x)
  let G : ℝ → ℝ := fun x => φ.realAngularDensity g 1 (t,x)
  have hv : ContDiff ℝ ∞ v := φ.realAngularVelocity_smooth.comp (contDiff_const.prodMk contDiff_id)
  have he : (fun x => (φ.angularVelocity t).cocycleDensity (φ.angularDensity g hg hp 1 t) x)=
      fun x => (((deriv (deriv (deriv v)) x+deriv v x)*G x:ℝ):ℂ) := by
    funext x
    simp only [SmoothCircleFunction.cocycleDensity,SmoothCircleFunction.mul_apply,
      SmoothCircleFunction.add_apply,SmoothCircleFunction.differentiated_apply]
    change (iteratedDeriv 3 (fun x => (v x:ℂ)) x+iteratedDeriv 1 (fun x => (v x:ℂ)) x)*(G x:ℂ)=_
    rw [RealCircleCalculus.iteratedDeriv_ofReal hv,RealCircleCalculus.iteratedDeriv_ofReal hv]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero,Complex.ofReal_add,Complex.ofReal_mul]
  rw [SmoothCircleFunction.coefficient,fourierCoeffOn_eq_integral]
  simp only [neg_zero,fourier_zero,one_smul]
  rw [he]
  rw [intervalIntegral.integral_ofReal]
  simp [Complex.real_smul,v,G,one_div]


lemma anomalyShift_derivative {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g 1)
    (hpos : ∀ x, 0 < g x) (c : ℂ) (t : ℝ) :
    HasDerivAt (φ.anomalyShift g c)
      (c/12*((φ.angularVelocity t).cocycleDensity (φ.angularDensity g hg hp 1 t)).coefficient 0) t := by
  have hd := RealCircleCalculus.anomaly_energy_derivative (φ.realAngularDensity_smooth hg 1)
    φ.realAngularVelocity_smooth (fun t x => ne_of_gt (φ.realAngularDensity_pos hpos 1 t x))
    (φ.realAngularDensity_periodic hg hp 1) φ.realAngularVelocity_periodic
    (φ.realAngularDensity_PDE hg hp) t
  have he := (((hd.const_mul ((2*Real.pi)⁻¹)).sub_const (φ.normalizedAnomaly g 0)).ofReal_comp).const_mul (c/24)
  rw [φ.angular_cocycle_coefficient hg hp t]
  convert he using 1 <;> try rfl
  push_cast
  ring
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

open Filter MeasureTheory Set
open scoped Topology ContDiff

open UniformSpace Filter
open scoped Topology ContDiff

open Filter UniformSpace
open scoped Topology ContDiff

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
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
def stressPropagatorSmoothEquiv (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) :
    U.smoothEnergySpace ≃ₗᵢ[ℂ] U.smoothEnergySpace where
  toLinearEquiv :=
    { toLinearMap := U.stressPropagatorSmooth hc f t
      invFun := fun x => ⟨star (U.stressPropagator hc f t) x,U.stressPropagator_star_smooth hc f t x.property⟩
      left_inv := fun x => Subtype.ext ((U.stressPropagatorEquiv hc f t).symm_apply_apply x)
      right_inv := fun x => Subtype.ext ((U.stressPropagatorEquiv hc f t).apply_symm_apply x) }
  norm_map' := fun x => (U.stressPropagatorEquiv hc f t).norm_map x
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.Field
variable (f : Field (2*Real.pi))
lemma flattening_angular_zero :
    f.flattening.angularDensity f.unitParameter f.unitParameter_smooth f.unitParameter_periodic 1 0=f.smoothCircle := by
  apply SmoothCircleFunction.ext
  intro x
  exact congrArg Complex.ofReal (f.flattening_realDensity_zero x)
lemma flattening_angular_one :
    f.flattening.angularDensity f.unitParameter f.unitParameter_smooth f.unitParameter_periodic 1 1=
      SmoothCircleFunction.constant f.frequency := by
  apply SmoothCircleFunction.ext
  intro x
  exact congrArg Complex.ofReal (f.flattening_realDensity_one x)
lemma flattening_primary_zero (k : ℕ) :
    f.flattening.angularDensity (fun x => f.unitParameter x^k) (f.unitParameter_smooth.pow k)
      (fun x => congrArg (fun y : ℝ => y^k) (f.unitParameter_periodic x)) k 0=f.smoothCircle.power k := by
  apply SmoothCircleFunction.ext
  intro x
  change (f.flattening.density (fun x => f.unitParameter x^k) k 0 (x/(2*Real.pi)):ℂ)=(f x:ℂ)^k
  rw [SmoothLift.density_power]
  rw [show f.flattening.density f.unitParameter 1 0 (x/(2*Real.pi))=f x from f.flattening_realDensity_zero x]
  exact Complex.ofReal_pow _ _
lemma flattening_primary_one (k : ℕ) :
    f.flattening.angularDensity (fun x => f.unitParameter x^k) (f.unitParameter_smooth.pow k)
      (fun x => congrArg (fun y : ℝ => y^k) (f.unitParameter_periodic x)) k 1=
        SmoothCircleFunction.constant ((f.frequency:ℂ)^k) := by
  apply SmoothCircleFunction.ext
  intro x
  change (f.flattening.density (fun x => f.unitParameter x^k) k 1 (x/(2*Real.pi)):ℂ)=(f.frequency:ℂ)^k
  rw [SmoothLift.density_power,f.flattening_density_one]
  exact Complex.ofReal_pow _ _
end StronglyRationalVOA.PositiveCircleGeometry.Field

open Set MeasureTheory
open scoped ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.Field
variable {T : ℝ} (f : Field T)
lemma frequency_sub_stressScalar_bound (hT : 0 < T) {K D : ℝ} (hK : 0 < K)
    (hf : ∀ x ∈ Icc 0 T, f x ≤ K) (hd : ∀ x ∈ Icc 0 T, (deriv f x)^2/f x ≤ D) (c : ℝ) :
    |f.frequency-f.stressScalar c| ≤ K+|c|/24*(2*K+D) := by
  have ha := RealCircleCalculus.average_bounds hT f.smooth.continuous
    (fun x hx => ⟨(f.positive x).le,hf x hx⟩)
  have hb := RealCircleCalculus.average_bounds hT
    (((contDiff_infty_iff_deriv.mp f.smooth).2.continuous.pow 2).div f.smooth.continuous
      (fun x => ne_of_gt (f.positive x)))
    (fun x hx => ⟨div_nonneg (sq_nonneg _) (f.positive x).le,hd x hx⟩)
  change 0 ≤ T⁻¹*(∫ x in 0..T,(deriv f x)^2/f x) ∧
    T⁻¹*(∫ x in 0..T,(deriv f x)^2/f x) ≤ D at hb
  rcases ha with ⟨ha0,ha1⟩
  rcases hb with ⟨hb0,hb1⟩
  have hfreq := f.frequency_le hT hK hf
  have hfreq0 := (f.frequency_pos hT).le
  have hinner : |T⁻¹*(∫ x in 0..T,f x)-f.frequency-T⁻¹*(∫ x in 0..T,(deriv f x)^2/f x)| ≤ 2*K+D :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  rw [stressScalar]
  calc
    _ ≤ |f.frequency|+|c/24*(T⁻¹*(∫ x in 0..T,f x)-f.frequency-T⁻¹*(∫ x in 0..T,(deriv f x)^2/f x))| :=
      abs_sub _ _
    _ ≤ K+|c|/24*(2*K+D) := by
      rw [abs_of_nonneg hfreq0,abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<24)]
      exact add_le_add hfreq (mul_le_mul_of_nonneg_left hinner (by positivity))
end StronglyRationalVOA.PositiveCircleGeometry.Field
namespace StronglyRationalVOA.PositiveCircleGeometry
lemma quadratic_uniform_anomaly {T : ℝ} {g : ℝ → ℝ} (hp : Function.Periodic g T)
    (hs : ContDiff ℝ ∞ g) (hT : 0 < T) {M N : ℝ}
    (hM : ∀ x ∈ Icc 0 T, ‖g x‖ ≤ M) (hN : ∀ x ∈ Icc 0 T, ‖deriv g x‖ ≤ N)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (c : ℝ) :
    |(quadraticField hp hs hε).frequency-(quadraticField hp hs hε).stressScalar c| ≤
      (M^2+1)+|c|/24*(2*(M^2+1)+4*N^2) := by
  apply Field.frequency_sub_stressScalar_bound _ hT (by positivity)
  · intro x hx
    have hh := hM x hx
    rw [Real.norm_eq_abs] at hh
    have hsq := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hh)).mpr hh
    simp only [sq_abs] at hsq
    change g x^2+ε ≤ M^2+1
    linarith
  · intro x hx
    apply (quadratic_logDerivative_bound hp hs hε x).trans
    have hh := hN x hx
    rw [Real.norm_eq_abs] at hh
    have hsq := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hh)).mpr hh
    simp only [sq_abs] at hsq
    linarith
end StronglyRationalVOA.PositiveCircleGeometry

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
def powerFamily (f : SmoothCircleFamily) (k : ℕ) : SmoothCircleFamily where
  toFun t := (f t).power k
  smooth := f.smooth.pow k
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.PositiveCircleGeometry
lemma quadratic_smoothCircle {g : ℝ → ℝ} (hp : Function.Periodic g (2*Real.pi))
    (hs : ContDiff ℝ ∞ g) {ε : ℝ} (hε : 0 < ε) :
    (quadraticField hp hs hε).smoothCircle=(SmoothCircleFunction.ofRealPeriodic g hp hs).quadraticFamily ε := by
  apply SmoothCircleFunction.ext
  intro x
  change ((g x^2+ε:ℝ):ℂ)=(g x:ℂ)^2+(ε:ℂ)
  push_cast
  rfl
end StronglyRationalVOA.PositiveCircleGeometry

open UniformSpace Filter Set
open scoped Topology ContDiff

open UniformSpace Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
lemma real_reconstruct (f : SmoothCircleFunction) (hf : f.IsReal) :
    ofRealPeriodic (fun t => (f t).re)
      (fun t => congrArg Complex.re (f.periodic t)) (Complex.reCLM.contDiff.comp f.smooth) = f := by
  ext t
  apply Complex.ext
  · rfl
  · have h := congrArg Complex.im (hf t)
    change 0 = (f t).im
    simp only [Complex.star_def,Complex.conj_im] at h
    linarith
lemma power_tsupport_eq (f : SmoothCircleFunction) {k : ℕ} (hk : 0 < k) :
    tsupport (f.power k) = tsupport f := by
  unfold tsupport
  congr 1
  ext t
  simp only [Function.mem_support,power_apply,ne_eq,pow_eq_zero_iff hk.ne']
end StronglyRationalVOA.SmoothCircleFunction

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


lemma primaryGraphData_subset (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : U.primaryGraphData hc O ⊆ U.localGraphData hc O := by
  rintro x ⟨F,hF,i,j,rfl⟩
  exact ⟨F.state,F.weight,F.homogeneous,F.test,hF,i,j,rfl⟩


lemma primaryAlgebra_le_localAlgebra (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : U.primaryAlgebra hc O ≤ U.localAlgebra hc O :=
  LocalOperatorAlgebra.generated_mono (U.primaryGraphData_subset hc O)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set
open scoped Topology ContDiff

open Filter
open scoped Topology
namespace StronglyRationalVOA.HilbertScale
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]

lemma rotation_zero (w : ι → ℝ) : rotation (G := G) w 0 = 1 := by
  ext x i
  simp [rotation_apply]
lemma rotation_add (w : ι → ℝ) (s t : ℝ) :
    rotation (G := G) w (s+t) = rotation w s * rotation w t := by
  ext x i
  simp only [mul_apply_eq_comp,rotation_apply,smul_smul]
  congr 1
  rw [add_mul,Complex.ofReal_add,add_mul,Complex.exp_add]
lemma rotation_adjoint (w : ι → ℝ) (t : ℝ) :
    (rotation (G := G) w t).adjoint = rotation w (-t) := by
  rw [rotation,boundedMultiplier_adjoint]
  ext x i
  simp only [boundedMultiplier_apply,rotation_apply,Complex.star_def,← Complex.exp_conj,
    map_mul,Complex.conj_ofReal,Complex.conj_I,neg_mul,Complex.ofReal_neg,mul_neg]
end StronglyRationalVOA.HilbertScale

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
attribute [local instance] OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.gradeFinite
lemma rotation_zero : U.rotation 0 = 1 := by
  ext x
  apply U.energyCoordinates.injective
  rw [U.rotation_coordinates,HilbertScale.rotation_zero]
  rfl
lemma rotation_add (s t : ℝ) : U.rotation (s+t) = U.rotation s * U.rotation t := by
  ext x
  apply U.energyCoordinates.injective
  simp only [mul_apply_eq_comp,U.rotation_coordinates,HilbertScale.rotation_add]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.SmoothCircleFunction
open MeasureTheory AddCircle
lemma translate_real {f : SmoothCircleFunction} (hf : f.IsReal) (t : ℝ) :
    (f.translate t).IsReal := fun s => hf (s-t)
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma rotation_inner (t : ℝ) (x y : Completion V) :
    inner ℂ (U.rotation t x) (U.rotation t y) = inner ℂ x y := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  rw [← U.energyCoordinates.inner_map_map (U.rotation t x) (U.rotation t y),
    U.rotation_coordinates,U.rotation_coordinates,← ContinuousLinearMap.adjoint_inner_right,
    HilbertScale.rotation_adjoint,← mul_apply_eq_comp,← HilbertScale.rotation_add,neg_add_cancel,
    HilbertScale.rotation_zero,one_apply_eq_self,U.energyCoordinates.inner_map_map]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

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
lemma translate_power (f : SmoothCircleFunction) (k : ℕ) (t : ℝ) :
    (f.power k).translate t = (f.translate t).power k := by
  ext s
  rfl
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
namespace PrimaryTestField
variable {U}
def translate (F : U.PrimaryTestField) (t : ℝ) : U.PrimaryTestField where
  state := F.state
  weight := F.weight
  homogeneous := F.homogeneous
  quasiPrimary := F.quasiPrimary
  hermitian := F.hermitian
  test := F.test.translate t
  real := SmoothCircleFunction.translate_real F.real t
  kind := by
    rcases F.kind with h | h | ⟨hp,hd,b,hb,he⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hp,hd,b.translate t,SmoothCircleFunction.translate_real hb t,
        by rw [he,SmoothCircleFunction.translate_power,SmoothCircleFunction.translate_power]⟩)
lemma commutant_preserves_graph (F : U.PrimaryTestField) (hc : A.toVertexAlgebra.C2Cofinite)
    {O : Set (AddCircle (2*Real.pi))} (hF : tsupport F.test.onCircle ⊆ O)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (F.field hc).graph) :
    (Q x,Q y) ∈ (F.field hc).graph := by
  apply ClosedGraphData.graph_invariant_of_entry_commutes (F.field hc) (F.closed hc) Q _ hxy
  intro i j
  rw [← SetLike.mem_coe,primaryAlgebra,LocalOperatorAlgebra.coe_generated_commutant] at hQ
  exact (hQ _ (Or.inl ⟨F,hF,i,j,rfl⟩)).symm
end PrimaryTestField

lemma smoothConjugate_preserves_primary_graph (hc : A.toVertexAlgebra.C2Cofinite)
    (F : U.PrimaryTestField) {O : Set (AddCircle (2*Real.pi))}
    (Q : Completion V →L[ℂ] Completion V) (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    (ε : ℝ) (hε : 0 < ε)
    (hF : ∀ t : ℝ, |t| < ε → tsupport (F.test.translate t).onCircle ⊆ O)
    {x y : Completion V} (hxy : (x,y) ∈ (F.field hc).graph) :
    (SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε x,
     SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε y) ∈ (F.field hc).graph := by
  apply SymmetricOperator.conjugationIntegral_preserves_graph _ _ _ (F.closed hc) Q _ _ _ _ _ _ _ hxy
  intro t ht x y hxy
  have ht' : |t| < ε := by
    have hk : SmoothRotationKernel.kernel ε hε t ≠ 0 := by
      intro h
      exact ht (by simp only [SmoothRotationKernel.jet_zero,h,Complex.ofReal_zero])
    have h := (SmoothRotationKernel.support ε hε).le hk
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using h
  apply U.conjugation_preserves_field_graph hc F.homogeneous F.test t Q _ hxy
  intro u v huv
  exact (F.translate (-t)).commutant_preserves_graph hc (hF (-t) (by simpa only [abs_neg] using ht')) hQ huv
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace

open Set UniformSpace Filter
open scoped Topology

open Set MeasureTheory Filter
open scoped Topology ContDiff

open Set UniformSpace
open scoped Topology
namespace StronglyRationalVOA.SmoothCircleFunction
lemma power_tsupport_circle_subset (f : SmoothCircleFunction) {k : ℕ} (hk : 0 < k) :
    tsupport (f.power k).onCircle ⊆ tsupport f.onCircle := by
  apply closure_mono
  intro x hx
  induction x using Quotient.inductionOn with | h t =>
  change f t ^ k ≠ 0 at hx
  change f t ≠ 0
  exact fun h => hx (by rw [h,zero_pow (by omega)])
end StronglyRationalVOA.SmoothCircleFunction

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.SmoothCircleFunction
open scoped ContDiff in
def rePart (f : SmoothCircleFunction) : SmoothCircleFunction :=
  ofRealPeriodic (fun t => (f t).re) (fun t => congrArg Complex.re (f.periodic t))
    (Complex.reCLM.contDiff.comp f.smooth)
open scoped ContDiff in
def imPart (f : SmoothCircleFunction) : SmoothCircleFunction :=
  ofRealPeriodic (fun t => (f t).im) (fun t => congrArg Complex.im (f.periodic t))
    (Complex.imCLM.contDiff.comp f.smooth)
lemma rePart_support (f : SmoothCircleFunction) : tsupport f.rePart.onCircle ⊆ tsupport f.onCircle := by
  apply closure_mono
  intro x hx
  induction x using Quotient.inductionOn with | h t =>
  change ((f t).re:ℂ) ≠ 0 at hx
  change f t ≠ 0
  intro h
  exact hx (by simp only [h,Complex.zero_re,Complex.ofReal_zero])
lemma imPart_support (f : SmoothCircleFunction) : tsupport f.imPart.onCircle ⊆ tsupport f.onCircle := by
  apply closure_mono
  intro x hx
  induction x using Quotient.inductionOn with | h t =>
  change ((f t).im:ℂ) ≠ 0 at hx
  change f t ≠ 0
  intro h
  exact hx (by simp only [h,Complex.zero_im,Complex.ofReal_zero])
lemma rePart_add_imPart (f : SmoothCircleFunction) (t : ℝ) :
    f t=f.rePart t+Complex.I*f.imPart t := by
  change f t=((f t).re:ℂ)+Complex.I*((f t).im:ℂ)
  simpa only [mul_comm] using (Complex.re_add_im (f t)).symm
end StronglyRationalVOA.SmoothCircleFunction

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
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma primary_graph_invariant_of_hermitian (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (f : SmoothCircleFunction)
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hH : ∀ b : V, b ∈ A.grade d → A.IsPrimary b → U.IsHermitian d b →
      ∀ x y, (x,y) ∈ (U.closedSmoothField hc b d f).graph →
        (Q x,Q y) ∈ (U.closedSmoothField hc b d f).graph)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  let R := SymmetricOperator.restricted U.smoothEnergySpace Q hQ
  obtain ⟨S,hS,hspan⟩ := U.exists_hermitian_primary_spanning d
  have hSP : Submodule.span ℂ (S : Set V) ≤ U.stateCommutant hc d f.rapid_coefficients R := by
    apply Submodule.span_le.mpr
    intro b hb
    obtain ⟨hbd,hbp,hbh⟩ := hS b hb
    refine ⟨hbd,?_⟩
    exact SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
      (U.smoothSmear hc hbd f.rapid_coefficients) Q hQ (U.closedSmoothField hc b d f)
      (U.smoothSmear_graph hc hbd f.rapid_coefficients) (hH b hbd hbp hbh)
  obtain ⟨_,hac⟩ := hSP (hspan a ha hp)
  have hce := U.smoothSmear_core hc ha f.rapid_coefficients
  change (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc ha f.rapid_coefficients)).closure =
    U.closedSmoothField hc a d f at hce
  rw [← hce] at hxy ⊢
  exact SymmetricOperator.onSubmodule_closure_graph_invariant _ _
    (U.smoothSmear_core_closable hc ha f.rapid_coefficients) Q hQ hac hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace Filter
open scoped Topology

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

open Set UniformSpace

open UniformSpace Set Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothConjugate_realLocal_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hL : ∀ (O : Set (AddCircle (2*Real.pi))), IsOpen O → ∀ f : SmoothCircleFunction,
      f.IsReal → tsupport f.onCircle ⊆ O → ∀ Q : Completion V →L[ℂ] Completion V,
      Q ∈ (U.primaryAlgebra hc O).commutant → ∀ x y,
      (x,y) ∈ (U.closedSmoothField hc a d f).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph)
    (f : SmoothCircleFunction) (hf : f.IsReal)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
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
  exact hL O hO (f.translate (-t)) (SmoothCircleFunction.translate_real hf (-t))
    (hs (-t) (by simpa only [abs_neg] using ht')) Q hQ u v huv


end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma vacuum_smearedMap (hc : A.toVertexAlgebra.C2Cofinite) (f : SmoothCircleFunction) (v : V) :
    A.smearedMap A.vacuum 0 (U.polynomialEnergyBounds hc _) f.coefficient f.rapid_coefficients v=
      f.coefficient 0 • (v : Completion V) := by
  have hm (n : ℤ) : A.physicalMode A.vacuum 0 n=if n=0 then 1 else 0 := by
    by_cases h : n=0
    · subst n
      simp [physicalMode,A.vacuum_mode]
    · have h' : n-1 ≠ -1 := by omega
      simp [physicalMode,A.vacuum_mode,h,h']
  rw [A.smearedMap_apply,tsum_eq_single 0]
  · simp [hm]
  · intro n hn
    simp [hm,hn]
lemma vacuum_closed_graph (hc : A.toVertexAlgebra.C2Cofinite) (f : SmoothCircleFunction)
    (x y : Completion V) :
    (x,y) ∈ (U.closedSmoothField hc A.vacuum 0 f).graph ↔ y=f.coefficient 0 • x := by
  have hv : A.vacuum ∈ A.grade 0 := by rw [A.grade_zero]; exact Submodule.mem_span_singleton_self _
  let c := f.coefficient 0
  let g : Completion V → Completion V × Completion V := fun x => (x,c • x)
  have hg : Continuous g := continuous_id.prodMk (continuous_id.const_smul c)
  have hcore : ((U.smoothSmearedField hc A.vacuum 0 f).graph : Set (Completion V × Completion V))=
      Set.range (fun v : V => g (v : Completion V)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨z,hz,hp⟩ := (U.smoothSmearedField hc A.vacuum 0 f).mem_graph_iff.mp hp
      obtain ⟨v,rfl⟩ := (HilbertCore.equiv V).surjective z
      refine ⟨v,?_⟩
      have he := U.vacuum_smearedMap hc f v
      change HilbertCore.operator (A.smearedMap A.vacuum 0 (U.polynomialEnergyBounds hc _) f.coefficient f.rapid_coefficients) (HilbertCore.equiv V v)=p.2 at hp
      rw [HilbertCore.operator_apply] at hp
      exact Prod.ext hz (he.symm.trans hp)
    · rintro ⟨v,rfl⟩
      apply (U.smoothSmearedField hc A.vacuum 0 f).mem_graph_iff.mpr
      refine ⟨HilbertCore.equiv V v,rfl,?_⟩
      change HilbertCore.operator (A.smearedMap A.vacuum 0 (U.polynomialEnergyBounds hc _) f.coefficient f.rapid_coefficients) (HilbertCore.equiv V v)=_
      rw [HilbertCore.operator_apply]
      exact U.vacuum_smearedMap hc f v
  change (x,y) ∈ ((U.closedSmoothField hc A.vacuum 0 f).graph : Set (Completion V × Completion V)) ↔ _
  rw [U.closedSmoothField_graph hc hv f,hcore]
  constructor
  · intro h
    have hs : closure (Set.range (fun v : V => g (v : Completion V))) ⊆
        {p : Completion V × Completion V | p.2=c • p.1} := by
      apply closure_minimal _ (isClosed_eq continuous_snd (continuous_fst.const_smul c))
      rintro _ ⟨v,rfl⟩
      rfl
    exact hs h
  · intro h
    rw [h]
    have H := mem_closure_image hg.continuousAt (Completion.denseRange_coe x)
    have hr : g '' Set.range (Completion.coe' : V → Completion V) =
        Set.range (fun v : V => g (v : Completion V)) := by
      ext p
      constructor
      · rintro ⟨_,⟨v,rfl⟩,rfl⟩
        exact ⟨v,rfl⟩
      · rintro ⟨v,rfl⟩
        exact ⟨(v : Completion V),⟨v,rfl⟩,rfl⟩
    rw [hr] at H
    exact H
lemma vacuum_localState (hc : A.toVertexAlgebra.C2Cofinite) : U.LocalState hc A.vacuum 0 := by
  intro O _ f _ Q _ x y hxy
  rw [U.vacuum_closed_graph] at hxy ⊢
  rw [hxy,map_smul]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

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
lemma localState_zero (hc : A.toVertexAlgebra.C2Cofinite) (d : ℕ) : U.LocalState hc (0:V) d := by
  apply LocalState.span U hc d (S := ∅) (by simp)
  exact Submodule.zero_mem _
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma hamiltonian_kernel {x : Completion V} (hx : (x,0) ∈ U.conformalHamiltonian.graph) :
    ∃ c : ℂ, x=c • (A.vacuum : Completion V) := by
  have h := (OperatorTransport.mem_graph_iff U.energyCoordinates _ x 0).mp hx
  rw [map_zero,HilbertScale.mem_graph_iff] at h
  let a : A.grade 0 := U.energyCoordinates x 0
  have he : U.energyCoordinates x=lp.single 2 0 a := by
    ext d
    by_cases hd : d=0
    · subst d
      simp [a]
    · have H := h d
      simp only [lp.coeFn_zero,Pi.zero_apply] at H
      have hz : U.energyCoordinates x d=0 := by
        exact (smul_eq_zero.mp H.symm).resolve_left (by exact_mod_cast hd)
      simp [lp.single_apply,hd,hz]
  have ha : (a : V) ∈ Submodule.span ℂ {A.vacuum} := by
    rw [← A.grade_zero]
    exact a.property
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp ha
  refine ⟨c,?_⟩
  apply U.energyCoordinates.injective
  rw [he,← U.energyCoordinates_grade a]
  congr 1
  rw [← hc,Completion.coe_smul]
lemma local_commutant_preserves_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {O : Set (AddCircle (2*Real.pi))} {Q : Completion V →L[ℂ] Completion V}
    (hQ : Q ∈ (U.localAlgebra hc O).commutant) {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (f : SmoothCircleFunction) (hf : tsupport f.onCircle ⊆ O)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  apply ClosedGraphData.graph_invariant_of_entry_commutes _ (U.closedSmoothField_isClosed hc ha f) Q _ hxy
  intro i j
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hQ _ (U.closedSmoothField_graphData_mem hc ha f hf i j)).symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma closedSmoothField_core_graph (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) (v : V) :
    ((v : Completion V),A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients v) ∈
      (U.closedSmoothField hc a d f).graph := by
  apply LinearPMap.le_graph_of_le (U.smoothSmearedField hc a d f).le_closure
  exact (U.smoothSmearedField hc a d f).mem_graph_iff.mpr
    ⟨HilbertCore.equiv V v,rfl,HilbertCore.operator_apply _ v⟩
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
def sumTests {ι : Type*} (s : Finset ι) (f : ι → SmoothCircleFunction) : SmoothCircleFunction where
  toFun := fun t => ∑ i ∈ s, f i t
  periodic := fun t => Finset.sum_congr rfl (fun i _ => (f i).periodic t)
  smooth := ContDiff.sum (fun i _ => (f i).smooth)
@[simp] lemma sumTests_apply {ι : Type*} (s : Finset ι) (f : ι → SmoothCircleFunction) (t : ℝ) :
    sumTests s f t=∑ i ∈ s, f i t := rfl
def reciprocal (f : SmoothCircleFunction) (hf : ∀ t, f t ≠ 0) : SmoothCircleFunction where
  toFun := fun t => (f t)⁻¹
  periodic := fun t => by dsimp only; rw [f.periodic]
  smooth := f.smooth.inv hf
@[simp] lemma reciprocal_apply (f : SmoothCircleFunction) (hf : ∀ t, f t ≠ 0) (t : ℝ) :
    reciprocal f hf t=(f t)⁻¹ := rfl
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Set Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothConjugate_interval_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction) (I : ProperCircleArc)
    (hf : tsupport f.onCircle ⊆ I.carrier) (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ J : ProperCircleArc, Q ∈ (U.intervalAlgebra hc J).commutant)
    (ε : ℝ) (hε : 0 < ε) {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε x,
     SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε y) ∈
       (U.closedSmoothField hc a d f).graph := by
  apply SymmetricOperator.conjugationIntegral_preserves_graph _ _ _ (U.closedSmoothField_isClosed hc ha f)
    Q _ _ _ _ _ _ _ hxy
  intro t _ x y hxy
  apply U.conjugation_preserves_field_graph hc ha f t Q _ hxy
  intro u v huv
  apply U.local_commutant_preserves_graph hc (hQ (I.translate (-t))) ha (f.translate (-t)) _ huv
  intro z hz
  exact I.translate_contains (-t) (hf (f.translate_tsupport_subset (-t) hz))
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma rotation_vacuum (t : ℝ) : U.rotation t (A.vacuum : Completion V)=(A.vacuum : Completion V) := by
  have h := U.rotation_grade t (⟨A.vacuum,by rw [A.grade_zero]; exact Submodule.subset_span (Set.mem_singleton _)⟩ : A.grade 0)
  simpa only [Nat.cast_zero,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_smul] using h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_RotationConjugateCommutant
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup _root_.OAI.StronglyRationalVOA.SmoothCircleLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
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

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma rotation_fixed_scalar {x : Completion V} (hx : ∀ t : ℝ, U.rotation t x=x) :
    ∃ c : ℂ, x=c • (A.vacuum : Completion V) := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  apply U.hamiltonian_kernel
  rw [conformalHamiltonian,U.energyOperator_graph_iff]
  intro d
  by_cases hd : d=0
  · subst d
    simp
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have H := congrArg (fun y => U.energyCoordinates y d) (hx (Real.pi/d))
  rw [U.rotation_coordinates,HilbertScale.rotation_apply,div_mul_cancel₀ _ hd',Complex.exp_pi_mul_I] at H
  have hz : U.energyCoordinates x d=0 := by
    have H' : (-2 : ℂ) • U.energyCoordinates x d=0 := by
      rw [show (-2:ℂ)=(-1)-1 by norm_num,sub_smul,one_smul,H,sub_self]
    exact (smul_eq_zero.mp H').resolve_left (by norm_num)
  simp [hz]

lemma conformalHamiltonian_nonnegative {x y : Completion V}
    (hxy : (x,y) ∈ U.conformalHamiltonian.graph) : 0 ≤ (inner ℂ x y).re := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  have H := (U.energyOperator_graph_iff (fun d => d) x y).mp hxy
  rw [← U.energyCoordinates.inner_map_map x y,
    ← (lp.hasSum_inner (U.energyCoordinates x) (U.energyCoordinates y)).tsum_eq,
    Complex.re_tsum (lp.hasSum_inner (U.energyCoordinates x) (U.energyCoordinates y)).summable]
  apply tsum_nonneg
  intro d
  rw [H d,inner_smul_right,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg (Nat.cast_nonneg d) (inner_self_nonneg (𝕜 := ℂ))
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set

open scoped ContDiff

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

def diffeomorphismImplementer (hc : A.toVertexAlgebra.C2Cofinite) (F : SmoothCircleLift) :
    Completion V ≃ₗᵢ[ℂ] Completion V :=
  U.stressPropagatorEquiv hc F.unitLift.angularStressPath 1
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped ContDiff

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleLift
variable (F : SmoothCircleLift) (g : ℝ → ℝ)
def pushedTest (k : ℕ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)) : SmoothCircleFunction :=
  SmoothCircleFunction.ofRealPeriodic (F.pushDensity k g) (F.pushDensity_periodic k hp) (F.pushDensity_smooth k hg)
lemma angularTest_zero (k : ℕ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)) :
    F.unitLift.angularDensity (unitTest g) (unitTest_smooth g hg) (unitTest_periodic g hp) k 0=
      SmoothCircleFunction.ofRealPeriodic g hp hg := by
  ext x
  change (F.unitLift.density (unitTest g) k 0 (x/(2*Real.pi)):ℂ)=(g x:ℂ)
  rw [PositiveCircleGeometry.SmoothLift.density_zero]
  dsimp only [unitTest]
  rw [mul_div_cancel₀ _ (by positivity : (2*Real.pi:ℝ) ≠ 0)]
lemma angularTest_one (k : ℕ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)) :
    F.unitLift.angularDensity (unitTest g) (unitTest_smooth g hg) (unitTest_periodic g hp) k 1=
      F.pushedTest g k hg hp := by
  ext x
  exact congrArg Complex.ofReal (F.unitLift_density_one g k x)
end StronglyRationalVOA.SmoothCircleLift
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
def diffeomorphismSmoothImplementer (hc : A.toVertexAlgebra.C2Cofinite) (F : SmoothCircleLift) :
    U.smoothEnergySpace ≃ₗᵢ[ℂ] U.smoothEnergySpace :=
  U.stressPropagatorSmoothEquiv hc F.unitLift.angularStressPath 1
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_DiffeomorphismStressSmooth
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup _root_.OAI.StronglyRationalVOA.SmoothCircleLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
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

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleLift
lemma pushedTest_mul (F G : SmoothCircleLift) (k : ℕ) (g : ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)) :
    F.pushedTest (G.pushDensity k g) k (G.pushDensity_smooth k hg) (G.pushDensity_periodic k hp)=
      (F*G).pushedTest g k hg hp := by
  ext x
  exact congrArg (fun f : ℝ → ℝ => (f x:ℂ)) (F.pushDensity_mul G k g).symm
end StronglyRationalVOA.SmoothCircleLift
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 
def diffeomorphismDefect (hc : A.toVertexAlgebra.C2Cofinite) (F G : SmoothCircleLift) :
    Completion V ≃ₗᵢ[ℂ] Completion V :=
  ((U.diffeomorphismImplementer hc G).trans (U.diffeomorphismImplementer hc F)).trans
    (U.diffeomorphismImplementer hc (F*G)).symm
def diffeomorphismSmoothDefect (hc : A.toVertexAlgebra.C2Cofinite) (F G : SmoothCircleLift) :
    U.smoothEnergySpace ≃ₗᵢ[ℂ] U.smoothEnergySpace :=
  ((U.diffeomorphismSmoothImplementer hc G).trans (U.diffeomorphismSmoothImplementer hc F)).trans
    (U.diffeomorphismSmoothImplementer hc (F*G)).symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
open scoped ContDiff

open UniformSpace Set

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
include U in
lemma scalarUnitary_norm (E : Completion V ≃ₗᵢ[ℂ] Completion V) {c : ℂ}
    (h : E.toContinuousLinearEquiv.toContinuousLinearMap=c • (1 : Completion V →L[ℂ] Completion V)) :
    ‖c‖=1 := by
  have hv : ‖(A.vacuum : Completion V)‖=1 := by simpa only [Completion.norm_coe] using U.vacuum_norm
  have H := congrArg (fun Q : Completion V →L[ℂ] Completion V => ‖Q (A.vacuum : Completion V)‖) h
  change ‖E (A.vacuum : Completion V)‖=‖c • (A.vacuum : Completion V)‖ at H
  rw [E.norm_map,norm_smul,hv,mul_one] at H
  exact H.symm


end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace

open UniformSpace
open scoped ContDiff

open UniformSpace Set

open UniformSpace Filter Set
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GeometryContinuation
attribute [-instance] _root_.OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)

lemma angularVelocity_iteratedDeriv (t x : ℝ) (k : ℕ) :
    iteratedDeriv k (φ.angularVelocity t) x =
      ((2*Real.pi)*((2*Real.pi)⁻¹)^k *
        iteratedDeriv k (φ.velocity t) (x/(2*Real.pi)) : ℝ) := by
  have hv : ContDiff ℝ ∞ (φ.velocity t) :=
    φ.velocity_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hs : ContDiff ℝ ∞ (fun z => (2*Real.pi)*φ.velocity t (z/(2*Real.pi))) :=
    contDiff_const.mul (hv.comp (contDiff_id.div_const _))
  change iteratedDeriv k (fun z => (((2*Real.pi)*φ.velocity t (z/(2*Real.pi)) : ℝ) : ℂ)) x = _
  rw [RealCircleCalculus.iteratedDeriv_ofReal hs]
  dsimp only
  congr 1
  rw [iteratedDeriv_const_mul_field]
  have he : (fun z => φ.velocity t (z/(2*Real.pi))) =
      (fun z => φ.velocity t ((2*Real.pi)⁻¹*z)) := by funext z; congr 1; ring
  rw [he, iteratedDeriv_comp_const_mul (hv.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))]
  dsimp only
  rw [← mul_assoc]
  congr 2
  ring



theorem angularStressPath_small_near_identity :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : SmoothLift) (ε : ℝ), 0 ≤ ε → ε ≤ 1/2 →
      (∀ x, |φ x-x| ≤ ε) → (∀ x, |deriv φ x-1| ≤ ε) →
      (∀ k ∈ Finset.Icc 2 4, ∀ x, |iteratedDeriv k φ x| ≤ ε) →
      ∀ t, coefficientSeminorm (φ.angularStressPath.coefficients t) 2 ≤ C*ε := by
  obtain ⟨B, hB, hβ⟩ := smoothTransition_deriv_bounded
  let K : ℝ := (2*Real.pi)*2592*B
  let S : ℝ := ∑' n : ℤ, ((1+|(n:ℝ)|)^2)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  have hS : 0 ≤ S := tsum_nonneg (fun n => by positivity)
  refine ⟨16*K*(1+S), by positivity, fun φ ε hε hε1 h0 h1 hk t => ?_⟩
  have hv (x : ℝ) : |φ.velocity t x| ≤ B*ε := by
    dsimp only [velocity]
    rw [abs_mul]
    exact mul_le_mul (hβ t) (h0 _) (abs_nonneg _) hB.le
  have h0' (x : ℝ) : ‖φ.angularVelocity t x‖ ≤ K*ε := by
    change ‖(((2*Real.pi)*φ.velocity t (x/(2*Real.pi)) : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
    calc _ ≤ (2*Real.pi)*(B*ε) := mul_le_mul_of_nonneg_left (hv _) (by positivity)
         _ ≤ K*ε := by dsimp only [K]; nlinarith [mul_nonneg hB.le hε, Real.pi_pos]
  have h4' (x : ℝ) : ‖iteratedDeriv 4 (φ.angularVelocity t) x‖ ≤ K*ε := by
    rw [φ.angularVelocity_iteratedDeriv, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi), abs_pow,
      abs_of_pos (by positivity : (0:ℝ) < (2*Real.pi)⁻¹)]
    have hpi : (2*Real.pi)⁻¹ ≤ (1:ℝ) := by
      apply (inv_le_one₀ (by positivity)).mpr
      linarith [Real.pi_gt_three]
    calc
      _ ≤ (2*Real.pi)*1*(2592*B*ε) := by
        gcongr
        · exact pow_le_one₀ (by positivity) hpi
        · exact (φ.velocity_fourth_bound hε hε1 h1 hk _ _).trans (by gcongr; exact hβ t)
      _ = K*ε := by dsimp [K]; ring
  have hc (n : ℤ) := (φ.angularVelocity t).coefficient_summable_bound 2
    (mul_nonneg hK.le hε) (fun x _ => h0' x) (fun x _ => h4' x) n
  change (∑' n : ℤ, ‖(φ.angularVelocity t).coefficient n‖*(1+|(n:ℝ)|)^2) ≤ _
  calc
    _ ≤ ∑' n : ℤ, (2^(2+2)*(K*ε))*((1+|(n:ℝ)|)^2)⁻¹ :=
      Summable.tsum_le_tsum hc ((φ.angularVelocity t).rapid_coefficients 2)
        (summable_circle_decay.mul_left _)
    _ = 16*K*S*ε := by rw [tsum_mul_left]; dsimp only [S]; ring
    _ ≤ 16*K*(1+S)*ε := by gcongr; linarith

end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothTopology
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace StronglyRationalVOA.SmoothCircleLift

lemma continuous_unitLift : Continuous (fun F : SmoothCircleLift => F.unitLift) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro k
  simp only [Function.comp_apply,unitLift_jet]
  exact continuous_const.mul ((ContinuousMap.continuous_precomp _).comp (continuous_jet k))



lemma continuous_mul_right (G : SmoothCircleLift) : Continuous (fun F : SmoothCircleLift => F*G) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro k
  simp only [Function.comp_apply,jet_mul]
  apply continuous_finsetSum
  intro c _
  exact ((ContinuousMap.continuous_precomp _).comp (continuous_jet c.length)).mul continuous_const
end StronglyRationalVOA.SmoothCircleLift

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StrongContinuity
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

lemma identity_angularVelocity (t : ℝ) :
    identity.angularVelocity t=SmoothCircleFunction.constant 0 := by
  ext x
  change ((2*Real.pi*(deriv Real.smoothTransition t *
    (identity (identity.inverse t (x/(2*Real.pi)))-identity.inverse t (x/(2*Real.pi)))) : ℝ) : ℂ)=0
  simp
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_CovarianceContinuation
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
open scoped ContDiff Topology
namespace StronglyRationalVOA.SmoothCircleLift
 
def pushTest (F : SmoothCircleLift) (k : ℕ) (f : SmoothCircleFunction) : SmoothCircleFunction where
  toFun x := (deriv F (F⁻¹ x)^k : ℝ) * f (F⁻¹ x)
  periodic x := by
    dsimp only
    rw [(F⁻¹).period,F.derivative_periodic,f.periodic]
  smooth := (Complex.ofRealCLM.contDiff.comp
    (((contDiff_infty_iff_deriv.mp F.smooth).2.comp (F⁻¹).smooth).pow k)).mul
      (f.smooth.comp (F⁻¹).smooth)
lemma pushTest_realPeriodic (F : SmoothCircleLift) (k : ℕ) (g : ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)) :
    F.pushTest k (SmoothCircleFunction.ofRealPeriodic g hp hg)=F.pushedTest g k hg hp := by
  ext x
  exact (Complex.ofReal_mul _ _).symm
lemma pushTest_add (F : SmoothCircleLift) (k : ℕ) (f g : SmoothCircleFunction) :
    F.pushTest k (f.add g)=(F.pushTest k f).add (F.pushTest k g) := by
  ext x
  exact mul_add _ _ _
lemma pushTest_support (F : SmoothCircleLift) (k : ℕ) (f : SmoothCircleFunction) :
    tsupport (F.pushTest k f).onCircle ⊆ F.onCircle '' tsupport f.onCircle := by
  have he : F.onCircle '' tsupport f.onCircle =
      F⁻¹.onCircle ⁻¹' tsupport f.onCircle := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [Set.mem_preimage,F.onCircle_inverse] using hy
    · intro hx
      refine ⟨F⁻¹.onCircle x,hx,?_⟩
      simpa using F⁻¹.onCircle_inverse x
  rw [he]
  apply closure_minimal _ (isClosed_closure.preimage F⁻¹.continuous_onCircle)
  intro x hx
  apply subset_closure
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    change f.onCircle ((F⁻¹ x : ℝ) : AddCircle (2*Real.pi)) ≠ 0
    change ((deriv F (F⁻¹ x)^k : ℝ) : ℂ)*f (F⁻¹ x) ≠ 0 at hx
    exact fun hz => hx (by rw [show f (F⁻¹ x)=0 from hz,mul_zero])

end StronglyRationalVOA.SmoothCircleLift

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_LocalImplementer
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
open scoped Topology

namespace StronglyRationalVOA.SmoothCircleLift
lemma angularVelocity_zero_of_fixed (F : SmoothCircleLift) (t x : ℝ) (hx : F x=x) :
    F.unitLift.angularVelocity t x=0 := by
  have hu : F.unitLift (x/(2*Real.pi))=x/(2*Real.pi) := by
    change F (2*Real.pi*(x/(2*Real.pi)))/(2*Real.pi)=_
    rw [mul_div_cancel₀ _ (by positivity : (2*Real.pi:ℝ)≠0),hx]
  change ((2*Real.pi*F.unitLift.velocity t (x/(2*Real.pi)) : ℝ):ℂ)=0
  rw [F.unitLift.velocity_zero_of_fixed t _ hu,mul_zero,Complex.ofReal_zero]
lemma angularVelocity_support_of_fixed (F : SmoothCircleLift)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (hfixed : ∀ x : ℝ, (x : AddCircle (2*Real.pi)) ∈ O → F x=x) (t : ℝ) :
    tsupport (F.unitLift.angularVelocity t).onCircle ⊆ Oᶜ := by
  apply closure_minimal _ hO.isClosed_compl
  intro z hz hmem
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective z
  exact hz (F.angularVelocity_zero_of_fixed t x (hfixed x hmem))
end StronglyRationalVOA.SmoothCircleLift

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusVacuum
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
open scoped ContDiff MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma pushed_constant_mobius_equation (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) :
    ((F.pushedTest (fun _ => 1) 1 contDiff_const (fun _ => rfl)).differentiated 3).add
      ((F.pushedTest (fun _ => 1) 1 contDiff_const (fun _ => rfl)).differentiated 1)=
    SmoothCircleFunction.constant 0 := by
  ext x
  simp only [SmoothCircleFunction.add_apply,SmoothCircleFunction.differentiated_apply,
    SmoothCircleFunction.constant_apply]
  have he : (F.pushedTest (fun _ => 1) 1 contDiff_const (fun _ => rfl) : ℝ → ℂ)=
      fun x => (density M x : ℂ) := by
    funext x
    exact congrArg (fun g : ℝ → ℝ => (g x:ℂ)) (push_constant M F hF)
  rw [he,RealCircleCalculus.iteratedDeriv_ofReal (density_smooth M),
    RealCircleCalculus.iteratedDeriv_ofReal (density_smooth M)]
  dsimp only
  rw [density_third,iteratedDeriv_one]
  simp
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusRepresentation
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology MatrixGroups
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
include U in
lemma completion_vacuum_norm : ‖(A.vacuum:Completion V)‖=1 := by
  simpa only [Completion.norm_coe] using U.vacuum_norm
include U in
lemma completion_vacuum_ne_zero : (A.vacuum:Completion V) ≠ 0 := by
  intro h
  have hh := U.completion_vacuum_norm
  rw [h,norm_zero] at hh
  exact zero_ne_one hh
 
def mobiusVacuumPhase (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) : ℂ :=
  inner ℂ (A.vacuum:Completion V) (U.diffeomorphismImplementer hc F (A.vacuum:Completion V))
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusContinuity
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma continuous_mul_right (F : lifts) : Continuous (fun G : lifts => G*F) := by
  apply Continuous.subtype_mk
  exact (SmoothCircleLift.continuous_mul_right (F:SmoothCircleLift)).comp continuous_subtype_val
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusStandardTopology
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped MatrixGroups Topology ContDiff
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma group_continuous_mul_right (G : Group) : Continuous (fun F : Group => F*G) := by
  induction G using QuotientGroup.induction_on with
  | H G =>
    apply (QuotientGroup.isQuotientMap_mk (SmoothCircleLift.circleAction.comp lifts.subtype).ker).continuous_iff.mpr
    exact (QuotientGroup.isQuotientMap_mk (SmoothCircleLift.circleAction.comp lifts.subtype).ker).continuous.comp
      (((SmoothCircleLift.continuous_mul_right (G:SmoothCircleLift)).comp continuous_subtype_val).subtype_mk _)
 

lemma standardAction_continuous : Continuous standardAction := by
  apply continuous_iff_continuousAt.mpr
  intro M
  have hnear : Tendsto (fun N : SL(2,ℝ) => N*M⁻¹) (𝓝 M) (𝓝 1) := by
    simpa using (continuous_mul_const M⁻¹).tendsto M
  have h := standardAction_continuousAt_one.tendsto.comp hnear
  have hpost := (group_continuous_mul_right (standardAction M)).tendsto (standardAction 1)
  have H := hpost.comp h
  change Tendsto standardAction (𝓝 M) (𝓝 (standardAction M))
  simpa only [Function.comp_def,map_mul,map_inv,map_one,one_mul,mul_assoc,inv_mul_cancel,mul_one] using H
lemma projectiveStandardAction_continuous : Continuous projectiveStandardAction := by
  apply (QuotientGroup.isQuotientMap_mk (Subgroup.center (SL(2,ℝ)))).continuous_iff.mpr
  exact standardAction_continuous
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_NetVacuum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set TopologicalSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma hilbertCompletion_separable (_U : A.UnitaryStructure) : SeparableSpace (Completion V) := by
  have hv : SeparableSpace V := by
    have hg (d : ℕ) : IsSeparable (A.grade d : Set V) := by
      let : FiniteDimensional ℂ (A.grade d) := A.grade_finite d
      exact IsSeparable.of_subtype _
    have hs := (IsSeparable.iUnion hg).span (R := ℂ)
    have he : Submodule.span ℂ (⋃ d, (A.grade d : Set V))=⊤ := by
      apply top_unique
      intro x _
      apply A.homogeneous_induction (P := fun x => x ∈ Submodule.span ℂ (⋃ d, (A.grade d : Set V)))
      · exact (Submodule.span ℂ _).zero_mem
      · intro d x hx; exact Submodule.subset_span (mem_iUnion.mpr ⟨d,hx⟩)
      · intro x y hx hy; exact Submodule.add_mem _ hx hy
    rw [he,Submodule.top_coe] at hs
    exact isSeparable_univ_iff.mp hs
  let := hv
  exact Completion.denseRange_coe.separableSpace (Completion.continuous_coe V)


end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_RotationImplementer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleLift
lemma rotation_angularVelocity (s t : ℝ) :
    (rotation s).unitLift.angularVelocity t=
      SmoothCircleFunction.constant ((s*deriv Real.smoothTransition t:ℝ):ℂ) := by
  ext x
  let y := (rotation s).unitLift.inverse t (x/(2*Real.pi))
  change ((2*Real.pi*(deriv Real.smoothTransition t*
    (((2*Real.pi*y+s)/(2*Real.pi))-y)):ℝ):ℂ)=((s*deriv Real.smoothTransition t:ℝ):ℂ)
  congr 1
  field_simp [Real.pi_ne_zero]
  ring
end StronglyRationalVOA.SmoothCircleLift

end

end OAI
end


