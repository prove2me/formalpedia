-- Prove2me | Definitions.Def_OAIQ3Vx011
-- name    : OAIQ3Vx011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:43:59.375156+00:00
-- url     : https://prove2.me/theorems/bdd78c6f-01e7-4e53-b715-b0dc441fc3f8
-- title:
--   Definitions bundle OAIQ3Vx011 of the split of OpenAI, Strongly rational unitary vertex operator algebras and conformal nets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinimalVertex.main`, carved from OpenAI's openai/math development (OpenAI, *Strongly rational unitary vertex operator algebras and conformal nets*, OpenAI Math Release, September 25, 2026, result family 280, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 5 definitions and 55 theorems. The definitions and types are `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.diffeomorphismProjectiveRepresentation`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.liftProjectiveRepresentation`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.mobiusLiftRepresentation`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.mobiusLiftUnitary`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.mobiusRepresentation`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/VertexAlgebra, in whole or in part: `VertexAlgebra_AlgebraCovariance`, `VertexAlgebra_CovarianceContinuation`, `VertexAlgebra_DiffeomorphismContinuity`, `VertexAlgebra_DiffeomorphismStressSmooth`, `VertexAlgebra_FixedArc`, `VertexAlgebra_GraphCovariance`, `VertexAlgebra_LocalImplementer`, `VertexAlgebra_MobiusContinuity`, `VertexAlgebra_MobiusRepresentation`, `VertexAlgebra_MobiusVacuum`, `VertexAlgebra_NetVacuum`, `VertexAlgebra_ObservableScalars`, `VertexAlgebra_PropagatorContinuation`, `VertexAlgebra_RotationConjugateCommutant`, `VertexAlgebra_RotationImplementer`, `VertexAlgebra_StressPropagatorPath`, `VertexAlgebra_StrongContinuity`.
--
--   **Imports.** It imports the published bundle `Def_VertexAlgebraNet`; the bundles `OAIQ3Vx009` and `OAIQ3Vx010` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ3Vx012`.
-- source:
--   OpenAI, Strongly rational unitary vertex operator algebras and conformal nets, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 280; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/VertexAlgebra at commit adc7f12

import Mathlib
import Definitions.Def_VertexAlgebraNet
import Definitions.Def_OAIQ3Vx009
import Definitions.Def_OAIQ3Vx010

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

open UniformSpace Set

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma stress_graph_le_hamiltonian (hc : A.toVertexAlgebra.C2Cofinite) :
    (U.closedSmoothField hc A.conformalVector 2 (SmoothCircleFunction.constant 1)).graph ≤
      U.conformalHamiltonian.graph := by
  intro p hp
  have hcore (v : V) : ((v : Completion V),(A.virasoroMode 0 v : Completion V)) ∈
      U.conformalHamiltonian.graph := by
    apply A.homogeneous_induction (P := fun v => ((v : Completion V),(A.virasoroMode 0 v : Completion V)) ∈ U.conformalHamiltonian.graph)
    · simpa only [map_zero,Completion.coe_zero,Prod.zero_eq_mk] using U.conformalHamiltonian.graph.zero_mem
    · intro d a ha
      have H : ((a : Completion V),(d : ℂ) • (a : Completion V)) ∈ (U.energyOperator (fun d => d)).graph := (U.energyOperator (fun d => d)).mem_graph_iff.mpr
        ⟨⟨(a : Completion V),U.coe_mem_energyOperator (fun d => d) a⟩,rfl,
          by simpa only [Complex.ofReal_natCast] using U.energyOperator_grade (fun d => d) ⟨a,ha⟩⟩
      simpa only [conformalHamiltonian,virasoroMode,zero_add,A.conformal_energy d a ha,Completion.coe_smul,Complex.ofReal_natCast] using H
    · intro a b ha hb
      simpa only [map_add,Completion.coe_add,Prod.mk_add_mk] using U.conformalHamiltonian.graph.add_mem ha hb
  change p ∈ ((U.closedSmoothField hc A.conformalVector 2 (SmoothCircleFunction.constant 1)).graph : Set (Completion V × Completion V)) at hp
  rw [U.closedSmoothField_graph hc A.conformal_mem] at hp
  apply closure_minimal (fun p hp => ?_) (U.energyOperator_closed (fun d => d)) hp
  obtain ⟨z,hz,hp⟩ := (U.smoothSmearedField hc A.conformalVector 2 (SmoothCircleFunction.constant 1)).mem_graph_iff.mp hp
  obtain ⟨v,rfl⟩ := (HilbertCore.equiv V).surjective z
  change HilbertCore.operator _ (HilbertCore.equiv V v)=p.2 at hp
  rw [HilbertCore.operator_apply,U.constant_stress_core hc] at hp
  have he : p=((v : Completion V),(A.virasoroMode 0 v : Completion V)) := Prod.ext hz.symm hp.symm
  rw [he]
  exact hcore v
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma global_commutant_vacuum (hc : A.toVertexAlgebra.C2Cofinite)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ (U.localAlgebra hc Set.univ).commutant) :
    ∃ c : ℂ, Q (A.vacuum : Completion V)=c • (A.vacuum : Completion V) := by
  apply U.hamiltonian_kernel
  have h := U.closedSmoothField_core_graph hc A.conformalVector 2 (SmoothCircleFunction.constant 1) A.vacuum
  rw [U.constant_stress_core hc,A.virasoro_vacuum 0 (by omega),Completion.coe_zero] at h
  have H := U.local_commutant_preserves_graph hc hQ A.conformal_mem _ (Set.subset_univ _) h
  rw [map_zero] at H
  exact U.stress_graph_le_hamiltonian hc H
 

lemma global_commutant_scalar (hc : A.toVertexAlgebra.C2Cofinite)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ (U.localAlgebra hc Set.univ).commutant) :
    ∃ c : ℂ, Q=c • (1 : Completion V →L[ℂ] Completion V) := by
  obtain ⟨c,hcQ⟩ := U.global_commutant_vacuum hc hQ
  refine ⟨c,?_⟩
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.denseRange_coe.induction_on x (isClosed_eq Q.continuous (c • (1 : Completion V →L[ℂ] Completion V)).continuous) ?_
  intro v
  change Q (v : Completion V)=c • (v : Completion V)
  apply A.homogeneous_induction (P := fun v => Q (v : Completion V)=c • (v : Completion V))
  · simp only [Completion.coe_zero,map_zero,smul_zero]
  · intro d a ha
    let f := (SmoothCircleFunction.constant 1).modulate (-(d : ℤ))
    have h : ((A.vacuum : Completion V),(a : Completion V)) ∈ (U.closedSmoothField hc a d f).graph := by
      have H := U.closedSmoothField_core_graph hc a d f A.vacuum
      change ((A.vacuum:Completion V),A.smearedMap a d (U.polynomialEnergyBounds hc a) ((SmoothCircleFunction.constant 1).modulate (-(d:ℤ))).coefficient ((SmoothCircleFunction.constant 1).modulate (-(d:ℤ))).rapid_coefficients A.vacuum) ∈ _ at H
      rw [U.smearedMap_character hc] at H
      have he : A.physicalMode a d (-(d:ℤ)) A.vacuum=a := by
        simpa only [physicalMode,neg_add_cancel,zero_sub] using A.creation a
      rwa [he] at H
    have H := U.local_commutant_preserves_graph hc hQ ha f (Set.subset_univ _) h
    apply (U.closedSmoothField hc a d f).mem_graph_snd_inj H ((U.closedSmoothField hc a d f).graph.smul_mem c h)
    exact hcQ
  · intro a b ha hb
    simp only [Completion.coe_add,map_add,ha,hb,smul_add]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set
open scoped Topology ContDiff

open UniformSpace Set Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothSmear_sumTests (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {ι : Type*} (s : Finset ι) (f : ι → SmoothCircleFunction) :
    U.smoothSmear hc ha (SmoothCircleFunction.sumTests s f).rapid_coefficients=
      ∑ i ∈ s, U.smoothSmear hc ha (f i).rapid_coefficients := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : SmoothCircleFunction.sumTests ∅ f=SmoothCircleFunction.constant 0 := by ext; simp
    rw [he,U.smoothSmear_constant]
    simp
  | @insert i s hi ih =>
    have he : SmoothCircleFunction.sumTests (insert i s) f=(f i).add (SmoothCircleFunction.sumTests s f) := by
      ext t
      simp only [SmoothCircleFunction.sumTests_apply,Finset.sum_insert hi,SmoothCircleFunction.add_apply]
    rw [he,U.smoothSmear_add_functions,ih,Finset.sum_insert hi]
lemma finite_test_graph_invariant (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {ι : Type*} (s : Finset ι) (f : ι → SmoothCircleFunction)
    (Q : Completion V →L[ℂ] Completion V) (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hF : ∀ i ∈ s, ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d (f i)).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d (f i)).graph)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d (SmoothCircleFunction.sumTests s f)).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d (SmoothCircleFunction.sumTests s f)).graph := by
  let R := SymmetricOperator.restricted U.smoothEnergySpace Q hQ
  have hcomm : U.smoothSmear hc ha (SmoothCircleFunction.sumTests s f).rapid_coefficients*R=
      R*U.smoothSmear hc ha (SmoothCircleFunction.sumTests s f).rapid_coefficients := by
    rw [U.smoothSmear_sumTests,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
      (U.smoothSmear hc ha (f i).rapid_coefficients) Q hQ (U.closedSmoothField hc a d (f i))
      (U.smoothSmear_graph hc ha (f i).rapid_coefficients) (hF i hi)
  have he := U.smoothSmear_core hc ha (SmoothCircleFunction.sumTests s f).rapid_coefficients
  change (SymmetricOperator.onSubmodule U.smoothEnergySpace
    (U.smoothSmear hc ha (SmoothCircleFunction.sumTests s f).rapid_coefficients)).closure=
      U.closedSmoothField hc a d (SmoothCircleFunction.sumTests s f) at he
  rw [← he] at hxy ⊢
  exact SymmetricOperator.onSubmodule_closure_graph_invariant U.smoothEnergySpace _
    (U.smoothSmear_core_closable hc ha _) Q hQ hcomm hxy
lemma interval_commutant_all_graphs (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction)
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ I : ProperCircleArc, Q ∈ (U.intervalAlgebra hc I).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  obtain ⟨s,g,I,hg,hfg⟩ := f.finite_arc_partition
  have he : f=SmoothCircleFunction.sumTests s g := SmoothCircleFunction.ext (congrFun hfg)
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hl : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let R (n : ℕ) := SymmetricOperator.smoothConjugate U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q (r n) (hr n)
  have hRn (n : ℕ) : (R n x,R n y) ∈ (U.closedSmoothField hc a d f).graph := by
    rw [he] at hxy ⊢
    apply U.finite_test_graph_invariant hc ha s g (R n) (fun z => U.smoothConjugate_smooth Q _ _ z.property) _ hxy
    intro i _ u v huv
    exact U.smoothConjugate_interval_graph hc ha (g i) (I i) (hg i) Q hQ _ _ huv
  exact (U.closedSmoothField_isClosed hc ha f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
 

theorem interval_commutant_scalar (hc : A.toVertexAlgebra.C2Cofinite)
    {Q : Completion V →L[ℂ] Completion V}
    (hQ : ∀ I : ProperCircleArc, Q ∈ (U.intervalAlgebra hc I).commutant) :
    ∃ c : ℂ, Q=c • (1 : Completion V →L[ℂ] Completion V) := by
  apply U.global_commutant_scalar hc
  rw [← SetLike.mem_coe,localAlgebra,LocalOperatorAlgebra.coe_generated_commutant]
  intro B hB
  have hdata : ∀ B ∈ U.localGraphData hc Set.univ, Q*B=B*Q := by
    rintro B ⟨a,d,ha,f,_,i,j,rfl⟩
    apply ClosedGraphData.entry_commutes_of_graph_invariant
    · intro x y hxy
      exact U.interval_commutant_all_graphs hc ha f Q hQ hxy
    · intro x y hxy
      exact U.interval_commutant_all_graphs hc ha f Q.adjoint (fun I => star_mem (hQ I)) hxy
  rcases hB with hB | hB
  · exact (hdata B hB).symm
  · apply (hdata B ?_).symm
    obtain ⟨a,d,ha,f,hf,i,j,he⟩ := hB
    refine ⟨a,d,ha,f,hf,j,i,?_⟩
    have H := congrArg star he
    rw [star_star,ClosedGraphData.star_entry] at H
    exact H
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_RotationConjugateCommutant
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

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma interval_invariant_subspace (hc : A.toVertexAlgebra.C2Cofinite)
    (S : Submodule ℂ (Completion V)) (hclosed : IsClosed (S : Set (Completion V)))
    (hS : ∀ I : ProperCircleArc, ∀ B ∈ U.intervalAlgebra hc I, ∀ x ∈ S, B x ∈ S) :
    S=⊥ ∨ S=⊤ := by
  let : IsClosed (S : Set (Completion V)) := hclosed
  have hcomm : ∀ I : ProperCircleArc, S.starProjection ∈ (U.intervalAlgebra hc I).commutant := by
    intro I
    rw [VonNeumannAlgebra.mem_commutant_iff]
    intro B hB
    exact ClosedGraphData.commutes_projection_of_reduces S B (hS I B hB)
      (hS I B.adjoint (star_mem hB))
  obtain ⟨c,he⟩ := U.interval_commutant_scalar hc hcomm
  by_cases hbot : S=⊥
  · exact Or.inl hbot
  right
  have hex : ∃ x ∈ S, x ≠ 0 := by
    by_contra! h
    apply hbot
    exact le_antisymm (fun x hx => (Submodule.mem_bot _).mpr (h x hx)) bot_le
  obtain ⟨x,hx,hxn⟩ := hex
  have hcx : c • x=x := by
    have H := S.starProjection_eq_self_iff.mpr hx
    rwa [he,smul_apply,one_apply_eq_self] at H
  have hc1 : c=1 := smul_left_injective ℂ hxn (hcx.trans (one_smul ℂ x).symm)
  apply top_unique
  intro y _
  have hy := S.starProjection_apply_mem y
  simpa only [he,hc1,one_smul,one_apply_eq_self] using hy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set

open scoped ContDiff

open UniformSpace
open scoped ContDiff

open scoped ContDiff

open UniformSpace
open scoped ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_DiffeomorphismStressSmooth
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup _root_.OAI.StronglyRationalVOA.SmoothCircleLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.instTopologicalSpaceSmoothCircleDiffeomorphism _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
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
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma diffeomorphism_defect_primary (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {k : ℕ} (ha : a ∈ A.grade (k+1)) (hpa : A.IsPrimary a) (hh : U.IsHermitian (k+1) a)
    (F G : SmoothCircleLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2*Real.pi)) (y : U.smoothEnergySpace) :
    U.smoothSmear hc ha (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients
      (U.diffeomorphismSmoothDefect hc F G y)=
    U.diffeomorphismSmoothDefect hc F G
      (U.smoothSmear hc ha (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y) := by
  let Ef := U.diffeomorphismSmoothImplementer hc F
  let Eg := U.diffeomorphismSmoothImplementer hc G
  let E := U.diffeomorphismSmoothImplementer hc (F*G)
  let T := U.smoothSmear hc ha (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients
  let Tp := U.smoothSmear hc ha ((F*G).pushedTest g k hg hp).rapid_coefficients
  have hprod : Tp (Ef (Eg y))=Ef (Eg (T y)) := by
    have h := U.diffeomorphism_primary_smooth hc ha hpa hh F (G.pushDensity k g)
      (G.pushDensity_smooth k hg) (G.pushDensity_periodic k hp) (Eg y)
    dsimp only [Eg] at h
    rw [F.pushedTest_mul] at h
    change Tp (Ef (Eg y))=Ef (U.smoothSmear hc ha (G.pushedTest g k hg hp).rapid_coefficients (Eg y)) at h
    have hG := U.diffeomorphism_primary_smooth hc ha hpa hh G g hg hp y
    change U.smoothSmear hc ha (G.pushedTest g k hg hp).rapid_coefficients (Eg y)=Eg (T y) at hG
    rw [hG] at h
    exact h
  have hE := U.diffeomorphism_primary_smooth hc ha hpa hh (F*G) g hg hp
    (E.symm (Ef (Eg y)))
  change Tp (E (E.symm (Ef (Eg y))))=E (T (E.symm (Ef (Eg y)))) at hE
  rw [E.apply_symm_apply,hprod] at hE
  apply E.injective
  change E (T (E.symm (Ef (Eg y))))=E (E.symm (Ef (Eg (T y))))
  rw [E.apply_symm_apply]
  exact hE.symm
lemma diffeomorphism_defect_positive_stress (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2*Real.pi)) (hpos : ∀ x, 0 < g x) (y : U.smoothEnergySpace) :
    U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients
      (U.diffeomorphismSmoothDefect hc F G y)=
    U.diffeomorphismSmoothDefect hc F G
      (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y) := by
  let Ef := U.diffeomorphismSmoothImplementer hc F
  let Eg := U.diffeomorphismSmoothImplementer hc G
  let E := U.diffeomorphismSmoothImplementer hc (F*G)
  let T := U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients
  let Tp := U.smoothSmear hc A.conformal_mem ((F*G).pushedTest g 1 hg hp).rapid_coefficients
  have hprod : Tp (Ef (Eg y))=Ef (Eg (T y))+(F*G).anomaly g A.centralCharge • Ef (Eg y) := by
    have h := U.diffeomorphism_stress_smooth hc F (G.pushDensity 1 g)
      (G.pushDensity_smooth 1 hg) (G.pushDensity_periodic 1 hp) (G.pushDensity_pos 1 hpos) (Eg y)
    dsimp only [Eg] at h
    rw [F.pushedTest_mul] at h
    change Tp (Ef (Eg y))=Ef (U.smoothSmear hc A.conformal_mem (G.pushedTest g 1 hg hp).rapid_coefficients (Eg y))+
      F.anomaly (G.pushDensity 1 g) A.centralCharge • Ef (Eg y) at h
    have hG := U.diffeomorphism_stress_smooth hc G g hg hp hpos y
    change U.smoothSmear hc A.conformal_mem (G.pushedTest g 1 hg hp).rapid_coefficients (Eg y)=Eg (T y)+
      G.anomaly g A.centralCharge • Eg y at hG
    rw [hG,map_add,map_smul] at h
    rw [F.anomaly_mul]
    rw [add_smul]
    exact h.trans (by abel)
  have hE := U.diffeomorphism_stress_smooth hc (F*G) g hg hp hpos
    (E.symm (Ef (Eg y)))
  change Tp (E (E.symm (Ef (Eg y))))=E (T (E.symm (Ef (Eg y))))+
    (F*G).anomaly g A.centralCharge • E (E.symm (Ef (Eg y))) at hE
  rw [E.apply_symm_apply,hprod] at hE
  have hcancel := add_right_cancel hE
  apply E.injective
  change E (T (E.symm (Ef (Eg y))))=E (E.symm (Ef (Eg (T y))))
  rw [E.apply_symm_apply]
  exact hcancel.symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_defect_stress (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2*Real.pi)) (y : U.smoothEnergySpace) :
    U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients
      (U.diffeomorphismSmoothDefect hc F G y)=
    U.diffeomorphismSmoothDefect hc F G
      (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y) := by
  obtain ⟨M,hM,hb⟩ := (hp.isBounded_of_continuous (by positivity) hg.continuous).exists_pos_norm_le
  have hpos (x : ℝ) : 0 < g x+(M+1) := by
    have H := hb (g x) ⟨x,rfl⟩
    rw [Real.norm_eq_abs] at H
    have := (abs_le.mp H).1
    linarith
  have hp' : Function.Periodic (fun x => g x+(M+1)) (2*Real.pi) := by
    intro x; exact congrArg (fun z : ℝ => z+(M+1)) (hp x)
  have hpM : Function.Periodic (fun _ : ℝ => M+1) (2*Real.pi) := fun _ => rfl
  have h := U.diffeomorphism_defect_positive_stress hc F G (fun x => g x+(M+1))
    (hg.add contDiff_const) hp' hpos y
  have hM' := U.diffeomorphism_defect_positive_stress hc F G (fun _ => M+1)
    contDiff_const hpM (fun _ => by linarith) y
  have he : SmoothCircleFunction.ofRealPeriodic (fun x => g x+(M+1)) hp' (hg.add contDiff_const)=
      (SmoothCircleFunction.ofRealPeriodic g hp hg).add
        (SmoothCircleFunction.ofRealPeriodic (fun _ => M+1) hpM contDiff_const) := by
    ext x
    exact Complex.ofReal_add _ _
  rw [he,U.smoothSmear_add_functions,LinearMap.add_apply,LinearMap.add_apply,map_add,hM'] at h
  exact add_right_cancel h
lemma diffeomorphism_defect_primary_test (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    (hd : 0 < d) (F G : SmoothCircleLift) (f : SmoothCircleFunction) (hf : f.IsReal)
    (y : U.smoothEnergySpace) :
    U.smoothSmear hc ha f.rapid_coefficients (U.diffeomorphismSmoothDefect hc F G y)=
      U.diffeomorphismSmoothDefect hc F G (U.smoothSmear hc ha f.rapid_coefficients y) := by
  cases d with
  | zero => omega
  | succ k =>
    have h := U.diffeomorphism_defect_primary hc ha hp hh F G (fun x => (f x).re)
      (Complex.reCLM.contDiff.comp f.smooth) (fun x => congrArg Complex.re (f.periodic x)) y
    rwa [f.real_reconstruct hf] at h
lemma diffeomorphism_defect_test (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) (T : U.PrimaryTestField) (y : U.smoothEnergySpace) :
    U.smoothSmear hc T.homogeneous T.test.rapid_coefficients
      (U.diffeomorphismSmoothDefect hc F G y)=
      U.diffeomorphismSmoothDefect hc F G (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients y) := by
  rcases T.kind with hw | ⟨hw,ha⟩ | ⟨hp,hd,_⟩
  · have hp : A.IsPrimary T.state := by
      intro n hn
      by_cases h : n=1
      · subst n; exact T.quasiPrimary
      · exact A.virasoro_eq_zero_of_lt (hw ▸ T.homogeneous) n (by omega)
    exact U.diffeomorphism_defect_primary_test hc T.homogeneous hp T.hermitian
      (by omega) F G T.test T.real y
  · have h := U.diffeomorphism_defect_stress hc F G (fun x => (T.test x).re)
      (Complex.reCLM.contDiff.comp T.test.smooth) (fun x => congrArg Complex.re (T.test.periodic x)) y
    rw [T.test.real_reconstruct T.real] at h
    simpa only [hw,ha] using h
  · exact U.diffeomorphism_defect_primary_test hc T.homogeneous hp T.hermitian
      (by omega) F G T.test T.real y
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_defect_closed (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) (T : U.PrimaryTestField) :
    OperatorTransport.transport (U.diffeomorphismDefect hc F G) (T.field hc)=T.field hc := by
  let E := U.diffeomorphismDefect hc F G
  let e := U.diffeomorphismSmoothDefect hc F G
  have hE (x : Completion V) (hx : x ∈ U.smoothEnergySpace) : E x ∈ U.smoothEnergySpace :=
    (e ⟨x,hx⟩).property
  have hI (x : Completion V) (hx : x ∈ U.smoothEnergySpace) : E.symm x ∈ U.smoothEnergySpace :=
    (e.symm ⟨x,hx⟩).property
  have h := OperatorTransport.onSubmodule E U.smoothEnergySpace
    (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients)
    (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients) hE hI
    (fun x => congrArg Subtype.val (U.diffeomorphism_defect_test hc F G T x))
  have H := congrArg LinearPMap.closure h
  rw [OperatorTransport.closure E (U.smoothSmear_core_closable hc T.homogeneous T.test.rapid_coefficients),
    U.smoothSmear_core hc T.homogeneous] at H
  exact H
 

theorem diffeomorphism_defect_scalar (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) : ∃ c : ℂ,
    (U.diffeomorphismDefect hc F G).toContinuousLinearEquiv.toContinuousLinearMap=c • (1 : Completion V →L[ℂ] Completion V) := by
  apply U.global_commutant_scalar hc
  rw [U.localAlgebra_eq_primaryAlgebra hc isOpen_univ,← SetLike.mem_coe,
    primaryAlgebra,LocalOperatorAlgebra.coe_generated_commutant]
  have hdata : ∀ B ∈ U.primaryGraphData hc Set.univ,
      B*(U.diffeomorphismDefect hc F G).toContinuousLinearEquiv.toContinuousLinearMap=
        (U.diffeomorphismDefect hc F G).toContinuousLinearEquiv.toContinuousLinearMap*B := by
    rintro B ⟨T,_,i,j,rfl⟩
    apply ContinuousLinearMap.ext
    intro x
    have h := ClosedGraphData.entry_transport (U.diffeomorphismDefect hc F G) (T.field hc) (T.closed hc) i j x
    simp only [U.diffeomorphism_defect_closed hc F G T] at h
    have H := congrArg (U.diffeomorphismDefect hc F G) h
    rw [LinearIsometryEquiv.apply_symm_apply] at H
    exact H.symm
  intro B hB
  rcases hB with hB | hB
  · exact hdata B hB
  · apply hdata B
    obtain ⟨T,hT,i,j,he⟩ := hB
    refine ⟨T,hT,j,i,?_⟩
    have H := congrArg star he
    rw [star_star,ClosedGraphData.star_entry] at H
    exact H
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace

open UniformSpace
namespace StronglyRationalVOA

namespace CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

def liftProjectiveRepresentation (hc : A.toVertexAlgebra.C2Cofinite) :
    SmoothCircleLift →* ProjectiveUnitaryGroup (Completion V) :=
  MonoidHom.mk' (fun F => QuotientGroup.mk (U.diffeomorphismImplementer hc F)) (by
    intro F G
    change QuotientGroup.mk (U.diffeomorphismImplementer hc (F*G))=
      QuotientGroup.mk (U.diffeomorphismImplementer hc F)*QuotientGroup.mk (U.diffeomorphismImplementer hc G)
    rw [← QuotientGroup.mk_mul]
    apply QuotientGroup.eq.mpr
    obtain ⟨c,h⟩ := U.diffeomorphism_defect_scalar hc F G
    refine ⟨c,U.scalarUnitary_norm _ h,?_⟩
    intro x
    exact congrArg (fun Q : Completion V →L[ℂ] Completion V => Q x) h)
end CFTTypeVOA.UnitaryStructure
end StronglyRationalVOA

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma positiveStress_commutation_extend (hc : A.toVertexAlgebra.C2Cofinite)
    (e : U.smoothEnergySpace ≃ₗᵢ[ℂ] U.smoothEnergySpace)
    (he : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi)),
      (∀ x, 0 < g x) → ∀ y : U.smoothEnergySpace,
      U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients (e y)=
        e (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y))
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi))
    (y : U.smoothEnergySpace) :
    U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients (e y)=
        e (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y) := by
  obtain ⟨M,hM,hb⟩ := (hp.isBounded_of_continuous (by positivity) hg.continuous).exists_pos_norm_le
  have hpos (x : ℝ) : 0 < g x+(M+1) := by
    have H := hb (g x) ⟨x,rfl⟩
    rw [Real.norm_eq_abs] at H
    have := (abs_le.mp H).1
    linarith
  have hp' : Function.Periodic (fun x => g x+(M+1)) (2*Real.pi) := by
    intro x; exact congrArg (fun z : ℝ => z+(M+1)) (hp x)
  have hpM : Function.Periodic (fun _ : ℝ => M+1) (2*Real.pi) := fun _ => rfl
  have h := he (fun x => g x+(M+1)) (hg.add contDiff_const) hp' hpos y
  have hM' := he (fun _ => M+1) contDiff_const hpM (fun _ => by linarith) y
  have hsum : SmoothCircleFunction.ofRealPeriodic (fun x => g x+(M+1)) hp' (hg.add contDiff_const)=
      (SmoothCircleFunction.ofRealPeriodic g hp hg).add
        (SmoothCircleFunction.ofRealPeriodic (fun _ => M+1) hpM contDiff_const) := by
    ext x
    exact Complex.ofReal_add _ _
  rw [hsum,U.smoothSmear_add_functions,LinearMap.add_apply,LinearMap.add_apply,map_add,hM'] at h
  exact add_right_cancel h
lemma diffeomorphism_deck_stress (hc : A.toVertexAlgebra.C2Cofinite)
    (n : ℤ) (f : SmoothCircleFunction) (hf : f.IsReal) (y : U.smoothEnergySpace) :
    U.smoothSmear hc A.conformal_mem f.rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi))) y)=
    U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi)))
      (U.smoothSmear hc A.conformal_mem f.rapid_coefficients y) := by
  have he (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g (2*Real.pi))
      (hpos : ∀ x, 0 < g x) (y : U.smoothEnergySpace) :
      U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients
        (U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi))) y)=
      U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi)))
        (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y) := by
    have h := U.diffeomorphism_stress_smooth hc (SmoothCircleLift.rotation (n*(2*Real.pi))) g hg hp hpos y
    simpa only [SmoothCircleLift.pushedTest,SmoothCircleLift.pushDensity_deck n 1 hp,
      SmoothCircleLift.anomaly_deck n g hp,zero_smul,add_zero] using h
  have h := U.positiveStress_commutation_extend hc _ he (fun x => (f x).re)
    (Complex.reCLM.contDiff.comp f.smooth) (fun x => congrArg Complex.re (f.periodic x)) y
  rwa [f.real_reconstruct hf] at h
lemma diffeomorphism_deck_test (hc : A.toVertexAlgebra.C2Cofinite)
    (n : ℤ) (T : U.PrimaryTestField) (y : U.smoothEnergySpace) :
    U.smoothSmear hc T.homogeneous T.test.rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi))) y)=
    U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi)))
      (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients y) := by
  rcases T.kind with hw | ⟨hw,ha⟩ | ⟨hp,hd,_⟩
  · have hp : A.IsPrimary T.state := by
      intro j hj
      by_cases h : j=1
      · subst j; exact T.quasiPrimary
      · exact A.virasoro_eq_zero_of_lt (hw ▸ T.homogeneous) j (by omega)
    exact U.diffeomorphism_deck_primary hc T.homogeneous hp T.hermitian (by omega) n T.test T.real y
  · have h := U.diffeomorphism_deck_stress hc n T.test T.real y
    simpa only [hw,ha] using h
  · exact U.diffeomorphism_deck_primary hc T.homogeneous hp T.hermitian (by omega) n T.test T.real y
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_deck_closed (hc : A.toVertexAlgebra.C2Cofinite)
    (n : ℤ) (T : U.PrimaryTestField) :
    OperatorTransport.transport (U.diffeomorphismImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi))))
      (T.field hc)=T.field hc := by
  let F := SmoothCircleLift.rotation (n*(2*Real.pi))
  let E := U.diffeomorphismImplementer hc F
  let e := U.diffeomorphismSmoothImplementer hc F
  have hE (x : Completion V) (hx : x ∈ U.smoothEnergySpace) : E x ∈ U.smoothEnergySpace :=
    (e ⟨x,hx⟩).property
  have hI (x : Completion V) (hx : x ∈ U.smoothEnergySpace) : E.symm x ∈ U.smoothEnergySpace :=
    (e.symm ⟨x,hx⟩).property
  have h := OperatorTransport.onSubmodule E U.smoothEnergySpace
    (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients)
    (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients) hE hI
    (fun x => congrArg Subtype.val (U.diffeomorphism_deck_test hc n T x))
  have H := congrArg LinearPMap.closure h
  rw [OperatorTransport.closure E (U.smoothSmear_core_closable hc T.homogeneous T.test.rapid_coefficients),
    U.smoothSmear_core hc T.homogeneous] at H
  exact H
lemma diffeomorphism_deck_scalar (hc : A.toVertexAlgebra.C2Cofinite) (n : ℤ) : ∃ c : ℂ,
    (U.diffeomorphismImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi)))).toContinuousLinearEquiv.toContinuousLinearMap=
      c • (1 : Completion V →L[ℂ] Completion V) := by
  let E := U.diffeomorphismImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi)))
  apply U.global_commutant_scalar hc
  rw [U.localAlgebra_eq_primaryAlgebra hc isOpen_univ,← SetLike.mem_coe,
    primaryAlgebra,LocalOperatorAlgebra.coe_generated_commutant]
  have hdata : ∀ B ∈ U.primaryGraphData hc Set.univ,
      B*E.toContinuousLinearEquiv.toContinuousLinearMap=E.toContinuousLinearEquiv.toContinuousLinearMap*B := by
    rintro B ⟨T,_,i,j,rfl⟩
    apply ContinuousLinearMap.ext
    intro x
    have h := ClosedGraphData.entry_transport E (T.field hc) (T.closed hc) i j x
    dsimp only [E] at h
    simp only [U.diffeomorphism_deck_closed hc n T] at h
    have H := congrArg E h
    rw [LinearIsometryEquiv.apply_symm_apply] at H
    exact H.symm
  intro B hB
  rcases hB with hB | hB
  · exact hdata B hB
  · apply hdata B
    obtain ⟨T,hT,i,j,he⟩ := hB
    refine ⟨T,hT,j,i,?_⟩
    have H := congrArg star he
    rw [star_star,ClosedGraphData.star_entry] at H
    exact H
 

def diffeomorphismProjectiveRepresentation (hc : A.toVertexAlgebra.C2Cofinite) :
    SmoothCircleDiffeomorphism →* ProjectiveUnitaryGroup (Completion V) :=
  QuotientGroup.lift SmoothCircleLift.circleAction.ker (U.liftProjectiveRepresentation hc) (by
    intro F hF
    obtain ⟨n,rfl⟩ := (SmoothCircleLift.circleAction_kernel F).mp hF
    change QuotientGroup.mk (U.diffeomorphismImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi))))=1
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨c,h⟩ := U.diffeomorphism_deck_scalar hc n
    refine ⟨c,U.scalarUnitary_norm _ h,?_⟩
    intro x
    exact congrArg (fun Q : Completion V →L[ℂ] Completion V => Q x) h)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter Set
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressPropagatorPath
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
lemma stressPropagator_path_difference (hc : A.toVertexAlgebra.C2Cofinite)
    (f g : StressPath) (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hd : ∀ s ∈ uIcc (0:ℝ) t,
      coefficientSeminorm (fun k => g.coefficients s k-f.coefficients s k) 2 ≤ ε)
    (x : U.smoothEnergySpace) :
    ‖U.stressPropagator hc g t x-U.stressPropagator hc f t x‖ ≤
      (ε*(1+A.centralCharge.re))*Real.exp ((g.bound 3*(1+A.centralCharge.re))*|t|)*
        ‖U.smoothEnergyPower 1 x‖*|t| := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  have hC : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
  have hB := mul_nonneg hε hC
  have hb (p : StressPath) (n : ℕ) : 0 ≤ (p.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) :=
    mul_nonneg (mul_nonneg (p.bound_nonneg 2) hC) (by positivity)
  apply le_of_tendsto ((U.stressPropagator_limit hc g t x).sub
    (U.stressPropagator_limit hc f t x)).norm
  apply Filter.Eventually.of_forall
  intro n
  apply TimeOrdered.duhamel_bound
    (U.stressCutoff_continuous hc n f.rapid f.continuous)
    (U.stressCutoff_continuous hc n g.rapid g.continuous)
    (hb f n) (hb g n) (U.stressPath_cutoff_bound hc f n)
    (U.stressPath_cutoff_bound hc g n)
    (fun s => U.stressCutoff_skew hc n (f.rapid s) (f.real s))
  intro s hs
  let y := U.stressCutoffEvolutionSmooth hc g n s x
  have hn : ‖(U.stressCutoff hc n (g.rapid s)-U.stressCutoff hc n (f.rapid s))*U.inverseSobolev 1‖ ≤
      ε*(1+A.centralCharge.re) := by
    calc
      _ ≤ coefficientSeminorm (fun k => g.coefficients s k-f.coefficients s k) 2*
          (1+A.centralCharge.re) := by
        rw [sub_mul,U.stressCutoff_normalized hc n (g.rapid s) le_rfl,
          U.stressCutoff_normalized hc n (f.rapid s) le_rfl,
          ← smul_sub,← sub_mul,← mul_sub,norm_smul,Complex.norm_I,one_mul]
        calc
          _ ≤ (‖U.energyCutoff n‖*
              ‖U.stressNormalized hc (g.rapid s) 1-U.stressNormalized hc (f.rapid s) 1‖)*
              ‖U.energyCutoff n‖ :=
            (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ (1*‖U.stressNormalized hc (g.rapid s) 1-
              U.stressNormalized hc (f.rapid s) 1‖)*1 := by
            gcongr <;> exact U.energyCutoff_norm n
          _ ≤ _ := by
            simpa only [one_mul,mul_one] using
              U.stressNormalized_difference hc (g.rapid s) (f.rapid s) le_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_right (hd s hs) hC
  have h1 : ‖(U.stressCutoff hc n (g.rapid s)-U.stressCutoff hc n (f.rapid s)) y‖ ≤
      (ε*(1+A.centralCharge.re))*‖U.smoothEnergyPower 1 y‖ := by
    rw [← U.inverseSobolev_smoothEnergyPower 1 y]
    exact ((U.stressCutoff hc n (g.rapid s)-U.stressCutoff hc n (f.rapid s))*U.inverseSobolev 1).le_of_opNorm_le hn _
  have hst : |s| ≤ |t| := by
    rcases le_total 0 t with ht | ht
    · rw [uIcc_of_le ht] at hs
      rw [abs_of_nonneg hs.1,abs_of_nonneg ht]
      exact hs.2
    · rw [uIcc_of_ge ht] at hs
      rw [abs_of_nonpos hs.2,abs_of_nonpos ht]
      exact neg_le_neg hs.1
  have h2 : ‖U.smoothEnergyPower 1 y‖ ≤
      Real.exp ((g.bound 3*(1+A.centralCharge.re))*|t|)*‖U.smoothEnergyPower 1 x‖ := by
    apply (U.stressCutoffEvolutionSmooth_bound hc g le_rfl n s x).trans
    simp only [Nat.cast_one,mul_one]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hst (mul_nonneg (g.bound_nonneg 3) hC))) (norm_nonneg _)
  exact (h1.trans (mul_le_mul_of_nonneg_left h2 hB)).trans_eq (by ring)


end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure


end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_PropagatorContinuation
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

lemma stressPropagator_path_difference_fixed (hc : A.toVertexAlgebra.C2Cofinite)
    (f g : StressPath) (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hd : ∀ s ∈ uIcc (0:ℝ) t,
      coefficientSeminorm (fun k => g.coefficients s k-f.coefficients s k) 2 ≤ ε)
    (x : U.smoothEnergySpace) :
    ‖U.stressPropagator hc g t x-U.stressPropagator hc f t x‖ ≤
      (ε*(1+A.centralCharge.re))*Real.exp ((f.bound 3*(1+A.centralCharge.re))*|t|)*
        ‖U.smoothEnergyPower 1 x‖*|t| := by
  rw [norm_sub_rev]
  apply U.stressPropagator_path_difference hc g f t hε
  intro s hs
  convert hd s hs using 1
  all_goals try with_reducible_and_instances rfl
  unfold coefficientSeminorm
  congr 1
  funext k
  rw [norm_sub_rev]

 
lemma stressPropagator_path_tendsto_fixed (hc : A.toVertexAlgebra.C2Cofinite)
    {ι : Type*} {l : Filter ι} (f : StressPath) (g : ι → StressPath) (t : ℝ)
    (ε : ι → ℝ) (hε : ∀ i, 0 ≤ ε i) (hε0 : Tendsto ε l (𝓝 0))
    (hd : ∀ᶠ i in l, ∀ s ∈ uIcc (0:ℝ) t,
      coefficientSeminorm (fun k => (g i).coefficients s k-f.coefficients s k) 2 ≤ ε i)
    (x : Completion V) :
    Tendsto (fun i => U.stressPropagator hc (g i) t x) l (𝓝 (U.stressPropagator hc f t x)) := by
  apply StrongLimit.tendsto_of_denseRange (fun y : U.smoothEnergySpace => (y : Completion V))
    U.smoothEnergySpace_dense.denseRange_val (fun i => U.stressPropagator hc (g i) t)
    (U.stressPropagator hc f t) (C := 1) (by norm_num) _ _ x
  · exact Filter.Eventually.of_forall (fun i => (U.stressPropagator hc (g i) t).opNorm_le_bound (by norm_num)
      (fun y => by simpa only [one_mul,U.stressPropagatorEquiv_apply] using (U.stressPropagatorEquiv hc (g i) t).norm_map y |>.le))
  intro y
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hz : Tendsto (fun i => (ε i*(1+A.centralCharge.re))*
      Real.exp ((f.bound 3*(1+A.centralCharge.re))*|t|)*‖U.smoothEnergyPower 1 y‖*|t|) l (𝓝 0) := by
    simpa only [zero_mul] using (((hε0.mul_const (1+A.centralCharge.re)).mul_const
      (Real.exp ((f.bound 3*(1+A.centralCharge.re))*|t|))).mul_const ‖U.smoothEnergyPower 1 y‖).mul_const |t|
  apply squeeze_zero' (Filter.Eventually.of_forall (fun i => norm_nonneg _)) _ hz
  filter_upwards [hd] with i he
  exact U.stressPropagator_path_difference_fixed hc f (g i) t (hε i) he y
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StrongContinuity
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology ContDiff

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

theorem diffeomorphismImplementer_continuousAt_one
    (hc : A.toVertexAlgebra.C2Cofinite) (x : Completion V) :
    ContinuousAt (fun F : SmoothCircleLift => U.diffeomorphismImplementer hc F x) 1 := by
  let e : SmoothCircleLift → ℝ := fun F => F.unitLift.identityError
  have he : Continuous e := PositiveCircleGeometry.SmoothLift.continuous_identityError.comp
    SmoothCircleLift.continuous_unitLift
  have he0 : e 1=0 := by simp [e]
  have he' : Tendsto e (𝓝 1) (𝓝 0) := he0 ▸ he.continuousAt
  obtain ⟨C,hC,hbound⟩ := PositiveCircleGeometry.SmoothLift.angularStressPath_small_near_identity
  have hε : Tendsto (fun F => C*e F) (𝓝 1) (𝓝 0) := by simpa using he'.const_mul C
  have hd : ∀ᶠ F : SmoothCircleLift in 𝓝 1, ∀ t ∈ uIcc (0:ℝ) 1,
      coefficientSeminorm (fun k => F.unitLift.angularStressPath.coefficients t k-
        PositiveCircleGeometry.SmoothLift.identity.angularStressPath.coefficients t k) 2 ≤ C*e F := by
    have hn : ∀ᶠ F in 𝓝 (1 : SmoothCircleLift), e F < 1/2 :=
      he'.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
    filter_upwards [hn] with F hF
    intro t _
    simp only [PositiveCircleGeometry.SmoothLift.identity_path_coefficients,sub_zero]
    exact hbound F.unitLift (e F) F.unitLift.identityError_nonneg hF.le
      F.unitLift.identityError_controls_zero F.unitLift.identityError_controls_one
      F.unitLift.identityError_controls_higher t
  have H := U.stressPropagator_path_tendsto_fixed hc
    PositiveCircleGeometry.SmoothLift.identity.angularStressPath
    (fun F : SmoothCircleLift => F.unitLift.angularStressPath) 1 (fun F => C*e F)
    (fun F => mul_nonneg hC.le F.unitLift.identityError_nonneg) hε hd x
  change Tendsto (fun F : SmoothCircleLift => U.stressPropagator hc F.unitLift.angularStressPath 1 x)
    (𝓝 1) (𝓝 (U.stressPropagator hc (1 : SmoothCircleLift).unitLift.angularStressPath 1 x))
  rw [SmoothCircleLift.unitLift_one]
  exact H
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_DiffeomorphismContinuity
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma liftProjectiveRepresentation_continuousAt_one (hc : A.toVertexAlgebra.C2Cofinite) :
    ContinuousAt (U.liftProjectiveRepresentation hc) 1 := by
  have hi : ContinuousAt (U.diffeomorphismImplementer hc) 1 := by
    apply (unitaryStrong_isInducing (Completion V)).continuousAt_iff.mpr
    exact continuousAt_pi.mpr (fun x => U.diffeomorphismImplementer_continuousAt_one hc x)
  exact (QuotientGroup.isQuotientMap_mk (scalarPhaseSubgroup (Completion V))).continuous.continuousAt.comp hi

 

theorem liftProjectiveRepresentation_continuous (hc : A.toVertexAlgebra.C2Cofinite) :
    Continuous (U.liftProjectiveRepresentation hc) := by
  apply continuous_iff_continuousAt.mpr
  intro F
  have hnear : Tendsto (fun G : SmoothCircleLift => G*F⁻¹) (𝓝 F) (𝓝 1) := by
    simpa only [mul_inv_cancel] using (SmoothCircleLift.continuous_mul_right F⁻¹).tendsto F
  have h := (U.liftProjectiveRepresentation_continuousAt_one hc).tendsto.comp hnear
  have hpost := (projectiveStrong_continuous_mul_right (U.liftProjectiveRepresentation hc F)).tendsto
    (U.liftProjectiveRepresentation hc 1)
  have H := hpost.comp h
  change Tendsto (U.liftProjectiveRepresentation hc) (𝓝 F) (𝓝 (U.liftProjectiveRepresentation hc F))
  simpa only [Function.comp_def,map_mul,map_inv,map_one,one_mul,mul_assoc,inv_mul_cancel,mul_one] using H

 

theorem diffeomorphismProjectiveRepresentation_continuous (hc : A.toVertexAlgebra.C2Cofinite) :
    Continuous (U.diffeomorphismProjectiveRepresentation hc) := by
  apply (QuotientGroup.isQuotientMap_mk SmoothCircleLift.circleAction.ker).continuous_iff.mpr
  exact U.liftProjectiveRepresentation_continuous hc
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

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

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_primary_test_smooth (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    (hd : 0 < d) (F : SmoothCircleLift) (f : SmoothCircleFunction) (hf : f.IsReal)
    (y : U.smoothEnergySpace) :
    U.smoothSmear hc ha (F.pushTest (d-1) f).rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc F y)=
      U.diffeomorphismSmoothImplementer hc F (U.smoothSmear hc ha f.rapid_coefficients y) := by
  cases d with
  | zero => omega
  | succ k =>
    have h := U.diffeomorphism_primary_smooth hc (k := k) ha hp hh F (fun x => (f x).re)
      (Complex.reCLM.contDiff.comp f.smooth) (fun x => congrArg Complex.re (f.periodic x)) y
    have he := F.pushTest_realPeriodic k (fun x => (f x).re)
      (Complex.reCLM.contDiff.comp f.smooth) (fun x => congrArg Complex.re (f.periodic x))
    rw [← he,f.real_reconstruct hf] at h
    exact h
 

lemma diffeomorphism_stress_test_smooth (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) (f : SmoothCircleFunction) (hf : f.IsReal) :
    ∃ c : ℂ, ∀ y : U.smoothEnergySpace,
    U.smoothSmear hc A.conformal_mem (F.pushTest 1 f).rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc F y)=
      U.diffeomorphismSmoothImplementer hc F (U.smoothSmear hc A.conformal_mem f.rapid_coefficients y)+
        c • U.diffeomorphismSmoothImplementer hc F y := by
  let g : ℝ → ℝ := fun x => (f x).re
  have hg : ContDiff ℝ ∞ g := Complex.reCLM.contDiff.comp f.smooth
  have hp : Function.Periodic g (2*Real.pi) := fun x => congrArg Complex.re (f.periodic x)
  obtain ⟨M,hM,hb⟩ := (hp.isBounded_of_continuous (by positivity) hg.continuous).exists_pos_norm_le
  have hpos (x : ℝ) : 0 < g x+(M+1) := by
    have H := hb (g x) ⟨x,rfl⟩
    rw [Real.norm_eq_abs] at H
    have := (abs_le.mp H).1
    linarith
  have hp' : Function.Periodic (fun x => g x+(M+1)) (2*Real.pi) :=
    fun x => congrArg (fun z : ℝ => z+(M+1)) (hp x)
  have hpM : Function.Periodic (fun _ : ℝ => M+1) (2*Real.pi) := fun _ => rfl
  refine ⟨F.anomaly (fun x => g x+(M+1)) A.centralCharge-
    F.anomaly (fun _ => M+1) A.centralCharge,?_⟩
  intro y
  have h := U.diffeomorphism_stress_smooth hc F (fun x => g x+(M+1))
    (hg.add contDiff_const) hp' hpos y
  have H := U.diffeomorphism_stress_smooth hc F (fun _ => M+1)
    contDiff_const hpM (fun _ => by linarith) y
  have he : SmoothCircleFunction.ofRealPeriodic (fun x => g x+(M+1)) hp' (hg.add contDiff_const)=
      f.add (SmoothCircleFunction.ofRealPeriodic (fun _ => M+1) hpM contDiff_const) := by
    rw [← f.real_reconstruct hf]
    ext x
    exact Complex.ofReal_add _ _
  rw [← F.pushTest_realPeriodic,he,F.pushTest_add,
    U.smoothSmear_add_functions,U.smoothSmear_add_functions,
    LinearMap.add_apply,LinearMap.add_apply,map_add] at h
  rw [← F.pushTest_realPeriodic] at H
  rw [H] at h
  rw [sub_smul]
  apply add_right_cancel (b := U.diffeomorphismSmoothImplementer hc F
    (U.smoothSmear hc A.conformal_mem
      (SmoothCircleFunction.ofRealPeriodic (fun _ => M+1) hpM contDiff_const).rapid_coefficients y)+
      F.anomaly (fun _ => M+1) A.centralCharge • U.diffeomorphismSmoothImplementer hc F y)
  exact h.trans (by abel)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GraphCovariance
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma diffeomorphism_primaryTest_graph (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) (T : U.PrimaryTestField) :
    ∃ c : ℂ, ∀ x y : Completion V,
      (x,y) ∈ (T.field hc).graph ↔
      (U.diffeomorphismImplementer hc F x,
        U.diffeomorphismImplementer hc F y+c • U.diffeomorphismImplementer hc F x) ∈
      (U.closedSmoothField hc T.state T.weight (F.pushTest (T.weight-1) T.test)).graph := by
  have hcov : ∃ c : ℂ, ∀ y : U.smoothEnergySpace,
      U.smoothSmear hc T.homogeneous (F.pushTest (T.weight-1) T.test).rapid_coefficients
        (U.diffeomorphismSmoothImplementer hc F y)=
      U.diffeomorphismSmoothImplementer hc F
        (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients y)+
        c • U.diffeomorphismSmoothImplementer hc F y := by
    rcases T.kind with hw | ⟨hw,ha⟩ | ⟨hp,hd,_⟩
    · have hp : A.IsPrimary T.state := by
        intro n hn
        by_cases h : n=1
        · subst n; exact T.quasiPrimary
        · exact A.virasoro_eq_zero_of_lt (hw ▸ T.homogeneous) n (by omega)
      refine ⟨0,fun y => ?_⟩
      simpa only [zero_smul,add_zero] using
        U.diffeomorphism_primary_test_smooth hc T.homogeneous hp T.hermitian (by omega) F T.test T.real y
    · obtain ⟨c,hc'⟩ := U.diffeomorphism_stress_test_smooth hc F T.test T.real
      refine ⟨c,fun y => ?_⟩
      have HH := hc' y
      simpa only [hw,ha,Nat.reduceSub] using HH
    · refine ⟨0,fun y => ?_⟩
      simpa only [zero_smul,add_zero] using
        U.diffeomorphism_primary_test_smooth hc T.homogeneous hp T.hermitian (by omega) F T.test T.real y
  obtain ⟨c,hc'⟩ := hcov
  refine ⟨c,fun x y => ?_⟩
  have h := SymmetricOperator.onSubmodule_affine_graph_iff U.smoothEnergySpace
    (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients)
    (U.smoothSmear hc T.homogeneous (F.pushTest (T.weight-1) T.test).rapid_coefficients)
    (U.diffeomorphismImplementer hc F) (U.diffeomorphismSmoothImplementer hc F)
    (fun _ => rfl) c hc'
    (U.smoothSmear_core_closable hc T.homogeneous _)
    (U.smoothSmear_core_closable hc T.homogeneous _) x y
  rw [U.smoothSmear_core,U.smoothSmear_core] at h
  exact h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_AlgebraCovariance
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_conjugate_primary_graph (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) (T : U.PrimaryTestField) {O : Set (AddCircle (2*Real.pi))}
    (hT : tsupport T.test.onCircle ⊆ O)
    {Q : Completion V →L[ℂ] Completion V}
    (hQ : Q ∈ (U.localAlgebra hc (F.onCircle '' O)).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (T.field hc).graph) :
    (((U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv Q) x,
      ((U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv Q) y) ∈ (T.field hc).graph := by
  obtain ⟨c,hc'⟩ := U.diffeomorphism_primaryTest_graph hc F T
  let E := U.diffeomorphismImplementer hc F
  have H := U.local_commutant_preserves_graph hc hQ T.homogeneous
    (F.pushTest (T.weight-1) T.test)
    ((F.pushTest_support (T.weight-1) T.test).trans (image_mono hT)) ((hc' x y).mp hxy)
  apply (hc' _ _).mpr
  change (E (E.symm (Q (E x))),E (E.symm (Q (E y)))+c • E (E.symm (Q (E x)))) ∈ _
  simpa only [E.apply_symm_apply,map_add,map_smul] using H
lemma diffeomorphism_conjugate_commutant (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    {Q : Completion V →L[ℂ] Completion V}
    (hQ : Q ∈ (U.localAlgebra hc (F.onCircle '' O)).commutant) :
    (U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv Q ∈
      (U.localAlgebra hc O).commutant := by
  rw [U.localAlgebra_eq_primaryAlgebra hc hO,← SetLike.mem_coe,
    primaryAlgebra,LocalOperatorAlgebra.coe_generated_commutant]
  let E := U.diffeomorphismImplementer hc F
  have hdata : ∀ B ∈ U.primaryGraphData hc O,
      E.symm.conjStarAlgEquiv Q*B=B*E.symm.conjStarAlgEquiv Q := by
    rintro B ⟨T,hT,i,j,rfl⟩
    apply ClosedGraphData.entry_commutes_of_graph_invariant
    · intro x y hxy
      exact U.diffeomorphism_conjugate_primary_graph hc F T hT hQ hxy
    · intro x y hxy
      have h := U.diffeomorphism_conjugate_primary_graph hc F T hT (star_mem hQ) hxy
      have hs : (U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv (star Q)=
          star ((U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv Q) :=
        ((U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv).map_star' Q
      rw [hs] at h
      exact h
  intro B hB
  rcases hB with hB | hB
  · exact (hdata B hB).symm
  · apply (hdata B ?_).symm
    obtain ⟨T,hT,i,j,he⟩ := hB
    refine ⟨T,hT,j,i,?_⟩
    have H := congrArg star he
    rw [star_star,ClosedGraphData.star_entry] at H
    exact H
 

lemma localAlgebra_diffeomorphism_mem (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    {B : Completion V →L[ℂ] Completion V} (hB : B ∈ U.localAlgebra hc O) :
    (U.diffeomorphismImplementer hc F).conjStarAlgEquiv B ∈ U.localAlgebra hc (F.onCircle '' O) := by
  rw [← VonNeumannAlgebra.commutant_commutant (U.localAlgebra hc (F.onCircle '' O)),
    VonNeumannAlgebra.mem_commutant_iff]
  intro Q hQ
  have h := (VonNeumannAlgebra.mem_commutant_iff.mp
    (U.diffeomorphism_conjugate_commutant hc F hO hQ)) B hB
  have H := congrArg (U.diffeomorphismImplementer hc F).conjStarAlgEquiv h
  simpa only [map_mul,← LinearIsometryEquiv.symm_conjStarAlgEquiv,StarAlgEquiv.apply_symm_apply] using H.symm
lemma diffeomorphism_inverse_conjugation (hc : A.toVertexAlgebra.C2Cofinite) (F : SmoothCircleLift) :
    (U.diffeomorphismImplementer hc F⁻¹).conjStarAlgEquiv=
      (U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv := by
  apply projective_equality_conjugation
  exact (U.liftProjectiveRepresentation hc).map_inv F
 
lemma localAlgebra_diffeomorphism_iff (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (B : Completion V →L[ℂ] Completion V) :
    (U.diffeomorphismImplementer hc F).conjStarAlgEquiv B ∈ U.localAlgebra hc (F.onCircle '' O) ↔
      B ∈ U.localAlgebra hc O := by
  constructor
  · intro hB
    have H := U.localAlgebra_diffeomorphism_mem hc F⁻¹ (F.circleHomeomorph.isOpenMap O hO) hB
    have hset : F⁻¹.onCircle '' (F.onCircle '' O)=O := by
      rw [← image_comp]
      simp only [Function.comp_def,F.onCircle_inverse,image_id']
    change (U.diffeomorphismImplementer hc F⁻¹).conjStarAlgEquiv
      ((U.diffeomorphismImplementer hc F).conjStarAlgEquiv B) ∈
      U.localAlgebra hc (F⁻¹.onCircle '' (F.onCircle '' O)) at H
    rw [hset,U.diffeomorphism_inverse_conjugation hc F,
      ← LinearIsometryEquiv.symm_conjStarAlgEquiv,StarAlgEquiv.symm_apply_apply] at H
    exact H
  · exact U.localAlgebra_diffeomorphism_mem hc F hO
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

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

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_local_action_of_fixed_lift (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (hfixed : ∀ x : ℝ, (x : AddCircle (2*Real.pi)) ∈ O → F x=x)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ U.localAlgebra hc O) :
    (U.diffeomorphismImplementer hc F).conjStarAlgEquiv Q=Q := by
  have he := U.angularStressPath_local_action hc F.unitLift hO
    (F.angularVelocity_support_of_fixed hO hfixed) hQ 1
  have hx (x : Completion V) := congrArg (fun B : Completion V →L[ℂ] Completion V => B x) he
  ext x
  exact ((hx ((U.diffeomorphismImplementer hc F).symm x)).symm.trans
    (congrArg Q ((U.diffeomorphismImplementer hc F).apply_symm_apply x)))
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_FixedArc
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_conjugation_eq_of_circle (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) (h : F.onCircle=G.onCircle) :
    (U.diffeomorphismImplementer hc F).conjStarAlgEquiv=
      (U.diffeomorphismImplementer hc G).conjStarAlgEquiv := by
  apply projective_equality_conjugation
  change U.diffeomorphismProjectiveRepresentation hc (QuotientGroup.mk F)=
    U.diffeomorphismProjectiveRepresentation hc (QuotientGroup.mk G)
  congr 1
  apply QuotientGroup.eq.mpr
  change SmoothCircleLift.circleAction (F⁻¹*G)=1
  rw [map_mul,map_inv]
  have he : SmoothCircleLift.circleAction F=SmoothCircleLift.circleAction G := by
    ext z; exact congrFun h z
  rw [he,inv_mul_cancel]
 

lemma diffeomorphism_local_action (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) (I : ProperCircleArc)
    (hF : ∀ z ∈ I.carrier, F.onCircle z=z)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ U.intervalAlgebra hc I) :
    (U.diffeomorphismImplementer hc F).conjStarAlgEquiv Q=Q := by
  obtain ⟨G,hG,hfixed⟩ := F.fixed_arc_normalize I hF
  rw [U.diffeomorphism_conjugation_eq_of_circle hc F G hG.symm]
  exact U.diffeomorphism_local_action_of_fixed_lift hc G I.isOpen_carrier hfixed hQ
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

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
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)


lemma diffeomorphism_mobius_vacuum_ray (hc : A.toVertexAlgebra.C2Cofinite)
    (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : CircleMobiusGeometry.Implements M F) :
    ∃ c : ℂ, U.diffeomorphismImplementer hc F (A.vacuum:Completion V)=c • (A.vacuum:Completion V) := by
  let E := U.diffeomorphismSmoothImplementer hc F
  let Ω := U.smoothCoreVector A.vacuum
  let y := E.symm Ω
  have h := U.diffeomorphism_stress_smooth hc F (fun _ => 1) contDiff_const
    (fun _ => rfl) (fun _ => zero_lt_one) y
  have htest : SmoothCircleFunction.ofRealPeriodic (fun _ => 1) (fun _ => rfl) contDiff_const=
      SmoothCircleFunction.constant 1 := by ext; rfl
  change U.smoothSmear hc A.conformal_mem
    (F.pushedTest (fun _ => 1) 1 contDiff_const (fun _ => rfl)).rapid_coefficients (E y)=
    E (U.smoothSmear hc A.conformal_mem
      (SmoothCircleFunction.ofRealPeriodic (fun _ => 1) (fun _ => rfl) contDiff_const).rapid_coefficients y)+
    F.anomaly (fun _ => 1) A.centralCharge • E y at h
  rw [CircleMobiusGeometry.anomaly_constant_zero M F hF,zero_smul,add_zero,htest] at h
  have hey : E y=Ω := E.apply_symm_apply Ω
  rw [hey,U.mobius_stress_vacuum hc _ (CircleMobiusGeometry.pushed_constant_mobius_equation M F hF)] at h
  have hz : U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients y=0 :=
    E.injective (h.symm.trans (map_zero E).symm)
  have hg := U.smoothSmear_graph hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients y
  rw [hz] at hg
  obtain ⟨c,hc'⟩ := U.hamiltonian_kernel (U.stress_graph_le_hamiltonian hc hg)
  have hc0 : c ≠ 0 := by
    intro he
    rw [he,zero_smul] at hc'
    have hy0 : y=0 := Subtype.ext hc'
    have ho : Ω=0 := by rw [← hey,hy0,map_zero]
    have hv : (A.vacuum:Completion V)=0 := congrArg Subtype.val ho
    exact A.vacuum_ne_zero (Completion.coe_injective V (by simpa only [Completion.coe_zero] using hv))
  refine ⟨c⁻¹,?_⟩
  have he : (A.vacuum:Completion V)=c • U.diffeomorphismImplementer hc F (A.vacuum:Completion V) := by
    have H := congrArg (U.diffeomorphismImplementer hc F) hc'
    rw [map_smul] at H
    have HY : U.diffeomorphismImplementer hc F (y:Completion V)=(A.vacuum:Completion V) :=
      congrArg Subtype.val hey
    rwa [HY] at H
  calc
    _ = c⁻¹ • (c • U.diffeomorphismImplementer hc F (A.vacuum:Completion V)) := by
      rw [smul_smul,inv_mul_cancel₀ hc0,one_smul]
    _ = _ := congrArg (fun z : Completion V => c⁻¹ • z) he.symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

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
lemma mobiusVacuumPhase_spec (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) :
    U.diffeomorphismImplementer hc F (A.vacuum:Completion V)=
      U.mobiusVacuumPhase hc F • (A.vacuum:Completion V) := by
  obtain ⟨M,hM⟩ := F.property
  obtain ⟨c,he⟩ := U.diffeomorphism_mobius_vacuum_ray hc M F hM
  dsimp only [mobiusVacuumPhase]
  rw [he,inner_smul_right,inner_self_eq_norm_sq_to_K,U.completion_vacuum_norm]
  simp
lemma mobiusVacuumPhase_norm (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) :
    ‖U.mobiusVacuumPhase hc F‖=1 := by
  have h := congrArg norm (U.mobiusVacuumPhase_spec hc F)
  rw [(U.diffeomorphismImplementer hc F).norm_map,norm_smul,U.completion_vacuum_norm,mul_one] at h
  exact h.symm
lemma mobiusVacuumPhase_ne_zero (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) :
    U.mobiusVacuumPhase hc F ≠ 0 := by
  intro h
  have he := U.mobiusVacuumPhase_norm hc F
  rw [h,norm_zero] at he
  exact zero_ne_one he
 
def mobiusLiftUnitary (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) :
    Completion V ≃ₗᵢ[ℂ] Completion V :=
  (U.diffeomorphismImplementer hc F).trans
    (phaseUnitary (U.mobiusVacuumPhase hc F)⁻¹ (by rw [norm_inv,U.mobiusVacuumPhase_norm,inv_one]))
lemma mobiusLiftUnitary_apply (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts)
    (x : Completion V) : U.mobiusLiftUnitary hc F x=
      (U.mobiusVacuumPhase hc F)⁻¹ • U.diffeomorphismImplementer hc F x := rfl
lemma mobiusLiftUnitary_vacuum (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) :
    U.mobiusLiftUnitary hc F (A.vacuum:Completion V)=(A.vacuum:Completion V) := by
  rw [U.mobiusLiftUnitary_apply,U.mobiusVacuumPhase_spec,smul_smul,
    inv_mul_cancel₀ (U.mobiusVacuumPhase_ne_zero hc F),one_smul]
lemma mobiusLiftUnitary_projective (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.lifts) :
    (QuotientGroup.mk (U.mobiusLiftUnitary hc F) : ProjectiveUnitaryGroup (Completion V))=
      U.liftProjectiveRepresentation hc F := by
  exact (projective_eq_of_phase _ _
    (by rw [norm_inv,U.mobiusVacuumPhase_norm,inv_one]) (U.mobiusLiftUnitary_apply hc F)).symm
lemma mobiusLiftUnitary_mul (hc : A.toVertexAlgebra.C2Cofinite) (F G : CircleMobiusGeometry.lifts) :
    U.mobiusLiftUnitary hc (F*G)=U.mobiusLiftUnitary hc F*U.mobiusLiftUnitary hc G := by
  apply projective_eq_vacuum_unique (A.vacuum:Completion V) U.completion_vacuum_ne_zero
  · rw [QuotientGroup.mk_mul,U.mobiusLiftUnitary_projective,U.mobiusLiftUnitary_projective,
      U.mobiusLiftUnitary_projective]
    exact map_mul (U.liftProjectiveRepresentation hc) (F:SmoothCircleLift) (G:SmoothCircleLift)
  · exact U.mobiusLiftUnitary_vacuum hc (F*G)
  · change U.mobiusLiftUnitary hc F (U.mobiusLiftUnitary hc G (A.vacuum:Completion V))=_
    rw [U.mobiusLiftUnitary_vacuum,U.mobiusLiftUnitary_vacuum]
def mobiusLiftRepresentation (hc : A.toVertexAlgebra.C2Cofinite) :
    CircleMobiusGeometry.lifts →* (Completion V ≃ₗᵢ[ℂ] Completion V) :=
  MonoidHom.mk' (U.mobiusLiftUnitary hc) (U.mobiusLiftUnitary_mul hc)
lemma mobiusLiftRepresentation_kernel (hc : A.toVertexAlgebra.C2Cofinite)
    (F : CircleMobiusGeometry.lifts)
    (hF : F ∈ (SmoothCircleLift.circleAction.comp CircleMobiusGeometry.lifts.subtype).ker) :
    U.mobiusLiftRepresentation hc F=1 := by
  apply projective_eq_vacuum_unique (A.vacuum:Completion V) U.completion_vacuum_ne_zero
  · change (QuotientGroup.mk (U.mobiusLiftUnitary hc F) : ProjectiveUnitaryGroup (Completion V))=1
    rw [U.mobiusLiftUnitary_projective]
    have h : (QuotientGroup.mk (F:SmoothCircleLift) : SmoothCircleDiffeomorphism)=1 :=
      (QuotientGroup.eq_one_iff _).mpr hF
    exact (congrArg (U.diffeomorphismProjectiveRepresentation hc) h).trans (map_one _)
  · exact U.mobiusLiftUnitary_vacuum hc F
  · rfl
 

def mobiusRepresentation (hc : A.toVertexAlgebra.C2Cofinite) :
    CircleMobiusGeometry.Group →* (Completion V ≃ₗᵢ[ℂ] Completion V) :=
  QuotientGroup.lift (SmoothCircleLift.circleAction.comp CircleMobiusGeometry.lifts.subtype).ker
    (U.mobiusLiftRepresentation hc) (by intro F hF; exact U.mobiusLiftRepresentation_kernel hc F hF)
lemma mobiusRepresentation_vacuum (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.Group) :
    U.mobiusRepresentation hc F (A.vacuum:Completion V)=(A.vacuum:Completion V) := by
  induction F using QuotientGroup.induction_on with
  | H F => exact U.mobiusLiftUnitary_vacuum hc F
lemma mobiusRepresentation_projective (hc : A.toVertexAlgebra.C2Cofinite) (F : CircleMobiusGeometry.Group) :
    (QuotientGroup.mk (U.mobiusRepresentation hc F) : ProjectiveUnitaryGroup (Completion V))=
      U.diffeomorphismProjectiveRepresentation hc (CircleMobiusGeometry.inclusion F) := by
  induction F using QuotientGroup.induction_on with
  | H F => exact U.mobiusLiftUnitary_projective hc F
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
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma mobiusVacuumPhase_continuousAt_one (hc : A.toVertexAlgebra.C2Cofinite) :
    ContinuousAt (U.mobiusVacuumPhase hc) 1 := by
  apply ContinuousAt.inner continuousAt_const
  have hval : Tendsto (fun F : CircleMobiusGeometry.lifts => (F:SmoothCircleLift))
      (𝓝 1) (𝓝 (1:SmoothCircleLift)) := continuous_subtype_val.tendsto (1:CircleMobiusGeometry.lifts)
  exact (U.diffeomorphismImplementer_continuousAt_one hc (A.vacuum:Completion V)).tendsto.comp hval
lemma mobiusLiftRepresentation_continuousAt_one (hc : A.toVertexAlgebra.C2Cofinite) :
    ContinuousAt (U.mobiusLiftRepresentation hc) 1 := by
  apply (unitaryStrong_isInducing (Completion V)).continuousAt_iff.mpr
  apply continuousAt_pi.mpr
  intro x
  change ContinuousAt (fun F : CircleMobiusGeometry.lifts => U.mobiusLiftUnitary hc F x) 1
  simp only [U.mobiusLiftUnitary_apply]
  have hval : Tendsto (fun F : CircleMobiusGeometry.lifts => (F:SmoothCircleLift))
      (𝓝 1) (𝓝 (1:SmoothCircleLift)) := continuous_subtype_val.tendsto (1:CircleMobiusGeometry.lifts)
  exact ((U.mobiusVacuumPhase_continuousAt_one hc).inv₀ (U.mobiusVacuumPhase_ne_zero hc 1)).smul
    ((U.diffeomorphismImplementer_continuousAt_one hc x).tendsto.comp hval)
lemma mobiusLiftRepresentation_continuous (hc : A.toVertexAlgebra.C2Cofinite) :
    Continuous (U.mobiusLiftRepresentation hc) := by
  apply continuous_iff_continuousAt.mpr
  intro F
  have hnear : Tendsto (fun G : CircleMobiusGeometry.lifts => G*F⁻¹) (𝓝 F) (𝓝 1) := by
    simpa only [mul_inv_cancel] using (CircleMobiusGeometry.continuous_mul_right F⁻¹).tendsto F
  have h := (U.mobiusLiftRepresentation_continuousAt_one hc).tendsto.comp hnear
  have hpost := (unitaryStrong_continuous_mul_right (U.mobiusLiftRepresentation hc F)).tendsto
    (U.mobiusLiftRepresentation hc 1)
  have H := hpost.comp h
  change Tendsto (U.mobiusLiftRepresentation hc) (𝓝 F) (𝓝 (U.mobiusLiftRepresentation hc F))
  simpa only [Function.comp_def,map_mul,map_inv,map_one,one_mul,mul_assoc,inv_mul_cancel,mul_one] using H
 
theorem mobiusRepresentation_continuous (hc : A.toVertexAlgebra.C2Cofinite) :
    Continuous (U.mobiusRepresentation hc) := by
  apply (QuotientGroup.isQuotientMap_mk
    (SmoothCircleLift.circleAction.comp CircleMobiusGeometry.lifts.subtype).ker).continuous_iff.mpr
  exact U.mobiusLiftRepresentation_continuous hc
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

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


lemma interval_vacuum_cyclic (hc : A.toVertexAlgebra.C2Cofinite) :
    globalCyclicSpace (U.intervalAlgebra hc) (A.vacuum:Completion V)=⊤ := by
  have h := U.interval_invariant_subspace hc
    (globalCyclicSpace (U.intervalAlgebra hc) (A.vacuum:Completion V))
    (Submodule.isClosed_topologicalClosure _) (globalCyclicSpace_invariant _ _)
  rcases h with h | h
  · have hh := globalCyclicSpace_contains (U.intervalAlgebra hc) (A.vacuum:Completion V)
    rw [h,Submodule.mem_bot] at hh
    exact (U.completion_vacuum_ne_zero hh).elim
  · exact h
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
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma rotationPropagatorDerivative (hc : A.toVertexAlgebra.C2Cofinite) (s t : ℝ)
    (x : U.smoothEnergySpace) :
    U.stressPropagatorDerivative hc (SmoothCircleLift.rotation s).unitLift.angularStressPath t x=
      (Complex.I*(s*deriv Real.smoothTransition t:ℝ)) •
      (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients
        (U.stressPropagatorSmooth hc (SmoothCircleLift.rotation s).unitLift.angularStressPath t x):Completion V) := by
  rw [U.stressPropagatorDerivative_smoothSmear]
  change Complex.I • (U.smoothSmear hc A.conformal_mem
    ((SmoothCircleLift.rotation s).unitLift.angularVelocity t).rapid_coefficients _ : Completion V)=_
  rw [SmoothCircleLift.rotation_angularVelocity,U.smoothSmear_constant]
  simp only [LinearMap.smul_apply,Submodule.coe_smul,smul_smul]


end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end


