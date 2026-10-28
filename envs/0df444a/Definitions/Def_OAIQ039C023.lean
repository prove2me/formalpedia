-- Prove2me | Definitions.Def_OAIQ039C023
-- name    : OAIQ039C023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:15:57.809197+00:00
-- url     : https://prove2.me/theorems/763f3865-d603-43b7-8c6c-ff965a7cfc6b
-- title:
--   Definitions bundle OAIQ039C023 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 5 definitions and 18 theorems. The definitions and types are `OAI.Kadison.CyclicSpectral.unitary`, `OAI.Kadison.Decomposable.fiberJoin`, `OAI.Kadison.Decomposable.finiteSumEquiv`, `OAI.Kadison.Decomposable.instNormedAlgebraRatContinuousLinearMapComplexId_solutions`, `OAI.Kadison.OperatorAmplification.matrixUnit`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CountableFieldHom`, `Commutator_CyclicSpectralNorm`, `Commutator_CyclicSpectralUnitary`, `Commutator_DecomposableAlgebra`, `Commutator_DenseFieldClosure`, `Commutator_DiagonalField`, `Commutator_DiagonalVonNeumann`, `Commutator_FactorCorner`, `Commutator_FiberCommutator`, `Commutator_FiberFactorProducer`, `Commutator_FiniteHankel`, `Commutator_L2FiniteSum`, `Commutator_MatrixAlgebraDensity`, `Commutator_MatrixField`, `Commutator_PolarDecomposition`, `Commutator_PolarSupport`.
--
--   **Imports.** It imports the published bundle `Def_UniformCommutator`; the bundles `OAIQ039C002`, `OAIQ039C003`, `OAIQ039C004`, `OAIQ039C005`, `OAIQ039C007` and `OAIQ039C008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C033`, `OAIQ039C034`, `OAIQ039C035` and `OAIQ039C040`; the statement `OAI.Kadison.Decomposable.homomorphisms_ae_of_countable_relations`; the proof of `OAI.Kadison.Decomposable.homomorphisms_ae_of_countable_relations`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C002
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C004
import Definitions.Def_OAIQ039C005
import Definitions.Def_OAIQ039C007
import Definitions.Def_OAIQ039C008

section
-- module Solutions.OAIQ039_CM.Commutator_CountableFieldHom
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace Kadison.Decomposable

variable {Ω H A : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ] [CStarAlgebra A]

attribute [local instance] OAI.Kadison.Decomposable.instNormedAlgebraRat_solutions
local instance instNormedAlgebraRatContinuousLinearMapComplexId_solutions : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)

local instance instStarModuleRat_solutions : StarModule ℚ A where
  star_smul r a := by
    change star ((r:ℂ) • a)=((star r:ℚ):ℂ) • star a
    simp

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicSpectralNorm
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped ComplexOrder InnerProductSpace CompactlySupported ComplexConjugate

namespace Kadison.CyclicSpectral

variable {Ω H : Type*} [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma toLp_norm_eq (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (f : C(Ω,ℂ)) :
    ‖ContinuousMap.toLp 2 (measure ρ ξ) ℂ f‖=‖ρ f ξ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),MeasureTheory.ContinuousMap.inner_toLp]
  simp_rw [Complex.mul_conj]
  rw [integral_complex_ofReal]
  simpa using (representation_norm_integral ρ ξ f).symm

end Kadison.CyclicSpectral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicSpectralUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.CyclicSpectral

variable {Ω H : Type*} [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitary (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hd : DenseRange (orbitMap ρ ξ)) : Lp ℂ 2 (measure ρ ξ) ≃ₗᵢ[ℂ] H :=
  (LinearEquiv.refl ℂ C(Ω,ℂ)).extendOfIsometry
    (ContinuousMap.toLp 2 (measure ρ ξ) ℂ).toLinearMap (orbitMap ρ ξ)
    (ContinuousMap.toLp_denseRange ℂ (measure ρ ξ) ℂ (p:=2) (by norm_num)) hd
    (fun f => (toLp_norm_eq ρ ξ f).symm)

end Kadison.CyclicSpectral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma mul_measurable (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ) (ξ : H) :
    AEStronglyMeasurable (fun a => (T a*S a) ξ) μ := measurable_apply μ T hT (hS ξ)

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DenseFieldClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology InnerProductSpace

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_vonNeumann_of_dense_finite_tests (Q : VonNeumannAlgebra H)
    (v : ℕ → H) (hv : DenseRange v) (T : H →L[ℂ] H) (b : ℝ) (hb : 0≤b)
    (ha : ∀ m : ℕ,∃ A : H →L[ℂ] H,A∈Q ∧ ‖A‖≤b ∧
      ∀ j : Fin m,‖A (v j)-T (v j)‖≤1/((m:ℝ)+1)) : T∈Q := by
  choose A hAQ hAb hA using ha
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ)≤atTop := Ultrafilter.of_le _
  obtain ⟨W,hW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω A b hb hAb
  have hWQ : W∈Q := WeakOperatorLimit.mem_vonNeumann hlim Q (Eventually.of_forall hAQ)
  have htest (j : ℕ) : W (v j)=T (v j) := by
    have hn : Tendsto (fun m => ‖A m (v j)-T (v j)‖) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
        tendsto_one_div_add_atTop_nhds_zero_nat
      filter_upwards [eventually_ge_atTop (j+1)] with m hm
      exact hA m ⟨j,by omega⟩
    have hl : Tendsto (fun m => A m (v j)) atTop (𝓝 (T (v j))) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr hn
    apply ext_inner_right ℂ
    intro y
    exact tendsto_nhds_unique (hlim (v j) y)
      (((continuous_id.inner continuous_const).tendsto (T (v j))).comp (hl.mono_left hω))
  have he : W=T := ContinuousLinearMap.ext (fun x => hv.induction_on x
    (isClosed_eq W.continuous T.continuous) htest)
  rwa [he] at hWQ

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_L2FiniteSum
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def finiteSumEquiv : PiLp 2 (fun _ : ι => Lp H 2 μ) ≃ₗᵢ[ℂ] Lp (PiLp 2 (fun _ : ι => H)) 2 μ :=
  LinearIsometryEquiv.ofSurjective (assembleIsometry μ) (assemble_surjective μ)

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DiagonalField
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma diagonal_field_measurable (h : ℕ) (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    (ξ : PiLp 2 (fun _ : Fin h => H)) :
    AEStronglyMeasurable (fun a => diagonalAmplification h (T a) ξ) μ := by
  classical
  have eqn (a) : diagonalAmplification h (T a) ξ=
      ∑ i,OperatorAmplification.single (Fin h) i (T a (ξ i)) := by
    ext i
    simp [diagonalAmplification_apply,OperatorAmplification.single_apply]
  simp_rw [eqn]
  exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ =>
    (OperatorAmplification.single (Fin h) i).continuous.comp_aestronglyMeasurable (hm (ξ i)))

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DiagonalVonNeumann
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

def matrixUnit (i j : ι) : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι :=
  (single ι i).comp (PiLp.proj 2 (fun _ : ι => H) j)

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma matrixUnit_apply (i j : ι) (x : SumSpace (H:=H) ι) :
    matrixUnit ι i j x=single ι i (x j) := rfl

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarDecomposition
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma partialIsometry_final_projection (T : H →L[ℂ] H) :
    IsStarProjection (partialIsometry T*star (partialIsometry T)) := by
  constructor
  · change (partialIsometry T*star (partialIsometry T))*(partialIsometry T*star (partialIsometry T))=_
    calc
      _=(partialIsometry T*(star (partialIsometry T)*partialIsometry T))*star (partialIsometry T) := by noncomm_ring
      _=partialIsometry T*star (partialIsometry T) := by rw [partialIsometry_initial,partialIsometry_mul_initial]
  · exact IsSelfAdjoint.mul_star_self _

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarSupport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma isProjection_leftSupport (T : H →L[ℂ] H) : IsStarProjection (leftSupport T) :=
  partialIsometry_final_projection T

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FactorCorner
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.FactorCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma projection_commutant (M : VonNeumannAlgebra H) (e : H →L[ℂ] H) :
    (supportSpace M e).starProjection∈Set.centralizer (M : Set (H →L[ℂ] H)) := by
  intro a ha
  exact (projection_commutes_of_invariant _ a (invariant_of_mem M e ha)
    (invariant_of_mem M e (M.star_mem' ha))).symm

lemma projection_mem (M : VonNeumannAlgebra H) {e : H →L[ℂ] H} (he : e∈M) :
    (supportSpace M e).starProjection∈M := by
  change (supportSpace M e).starProjection∈M.carrier
  rw [←M.centralizer_centralizer']
  intro a ha
  have hsa : star a∈Set.centralizer (M : Set (H →L[ℂ] H)) := by
    intro b hb
    simpa only [star_mul,star_star] using congrArg star (ha (star b) (M.star_mem' hb)).symm
  exact (projection_commutes_of_invariant _ a (invariant_of_commutant M he ha)
    (invariant_of_commutant M he hsa)).symm

lemma centralSupport_eq_one (M : VonNeumannAlgebra H) (hf : IsFactor M)
    {e : H →L[ℂ] H} (he : e∈M) (hne : e≠0) :
    (supportSpace M e).starProjection=1 := by
  obtain ⟨c,hc⟩ := hf _ (projection_mem M he) (projection_commutant M e)
  have hex : ∃ ξ : H, e ξ≠0 := by
    by_contra! h
    apply hne
    ext ξ
    exact h ξ
  obtain ⟨ξ,hξ⟩ := hex
  have hg : e ξ∈supportSpace M e := by simpa using generator_mem M e M.one_mem ξ
  have hfix := Submodule.starProjection_eq_self_iff.mpr hg
  rw [hc] at hfix
  change c • e ξ=e ξ at hfix
  have hzero : (c-1) • e ξ=0 := by rw [sub_smul,one_smul,hfix,sub_self]
  have hcone : c=1 := sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hξ)
  rw [hc,hcone,one_smul]

end Kadison.FactorCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiberCommutator
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma commutator_measurable (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ) (ξ : H) :
    AEStronglyMeasurable (fun a => (T a*S a-S a*T a) ξ) μ :=
  (mul_measurable μ T S hT hS ξ).sub (mul_measurable μ S T hS hT ξ)

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixAlgebraDensity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

open CyclicColumns CyclicSpatial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι]

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixAlgebraDensityDecidableEq
variable (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]

attribute [local instance] OAI.Kadison.OperatorAmplification.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
local instance instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiberFactorProducer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

def fiberJoin (Q R : VonNeumannAlgebra H) : VonNeumannAlgebra H :=
  (vonNeumannIntersection Q.commutant R.commutant).commutant

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteHankel
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.FiniteCompression

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
@[simp] lemma average_apply (c : ℝ) (U : I → K →L[ℂ] H) (x : K) :
    average c U x = (c : ℂ) • ∑ i, U i x := by simp [average]

end Kadison.FiniteCompression

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixField
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma vector_norm_le_sum {ι : Type*} [Fintype ι] (v : PiLp 2 (fun _ : ι => H)) :
    ‖v‖≤∑ i,‖v i‖ := by
  classical
  have he : ∑ i,PiLp.single 2 i (v i)=v := by ext i; simp
  rw [←he]
  convert norm_sum_le (Finset.univ) (fun i => PiLp.single 2 i (v i)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [PiLp.norm_single]
  rw [he]

omit [CompleteSpace H] in
lemma matrix_norm_le_sum (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) :
    ‖matrixOperator h X‖≤∑ i,∑ j,‖X i j‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  calc
    ‖matrixOperator h X x‖≤∑ i,‖matrixOperator h X x i‖ := vector_norm_le_sum _
    _≤∑ i,∑ j,‖X i j‖*‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [matrixOperator_apply]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact ((X i j).le_opNorm (x j)).trans
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (norm_nonneg _))
    _=(∑ i,∑ j,‖X i j‖)*‖x‖ := by simp only [Finset.sum_mul]

omit [CompleteSpace H] in
lemma matrix_field_measurable (h : ℕ) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    (hm : ∀ i j ξ,AEStronglyMeasurable (fun a => X i j a ξ) μ)
    (ξ : PiLp 2 (fun _ : Fin h => H)) :
    AEStronglyMeasurable (fun a => matrixOperator h (fun i j => X i j a) ξ) μ := by
  classical
  have eqn (a) : matrixOperator h (fun i j => X i j a) ξ=
      ∑ i,OperatorAmplification.single (Fin h) i (∑ j,X i j a (ξ j)) := by
    ext i
    erw [matrixOperator_apply]
    simp [OperatorAmplification.single_apply]
  simp_rw [eqn]
  apply Finset.aestronglyMeasurable_fun_sum
  intro i _
  exact (OperatorAmplification.single (Fin h) i).continuous.comp_aestronglyMeasurable
    (Finset.aestronglyMeasurable_fun_sum _ (fun j _ => hm i j (ξ j)))

omit [CompleteSpace H] in
lemma matrix_field_bound (h : ℕ) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    {b : Fin h → Fin h → ℝ} (hb : ∀ i j,∀ᵐ a ∂μ,‖X i j a‖≤b i j) :
    ∀ᵐ a ∂μ,‖matrixOperator h (fun i j => X i j a)‖≤∑ i,∑ j,b i j := by
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hb i))] with a ha
  exact (matrix_norm_le_sum h _).trans (Finset.sum_le_sum (fun i _ =>
    Finset.sum_le_sum (fun j _ => ha i j)))

end Kadison.Decomposable

end

end
end

end OAI
end


