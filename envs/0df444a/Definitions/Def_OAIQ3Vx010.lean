-- Prove2me | Definitions.Def_OAIQ3Vx010
-- name    : OAIQ3Vx010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:40:14.214321+00:00
-- url     : https://prove2.me/theorems/89892178-8c03-4625-9983-1397c7851fd1
-- title:
--   Definitions bundle OAIQ3Vx010 of the split of OpenAI, Strongly rational unitary vertex operator algebras and conformal nets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinimalVertex.main`, carved from OpenAI's openai/math development (OpenAI, *Strongly rational unitary vertex operator algebras and conformal nets*, OpenAI Math Release, September 25, 2026, result family 280, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/VertexAlgebra, in whole or in part: [`VertexAlgebra_MobiusVacuum`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/VertexAlgebra/VertexAlgebra/MobiusVacuum.lean), [`VertexAlgebra_ObservableScalars`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/VertexAlgebra/VertexAlgebra/ObservableScalars.lean).
--
--   **Imports.** It imports the published bundle `Def_VertexAlgebraNet`; the bundles `OAIQ3Vx006` and `OAIQ3Vx007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ3Vx011`.
-- source:
--   OpenAI, Strongly rational unitary vertex operator algebras and conformal nets, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 280; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/VertexAlgebra at commit adc7f12

import Mathlib
import Definitions.Def_VertexAlgebraNet
import Definitions.Def_OAIQ3Vx006
import Definitions.Def_OAIQ3Vx007

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

open UniformSpace Set

open Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction

attribute [local instance] OAI.StronglyRationalVOA.SmoothCircleFunction.instFactLtRealOfNatHMulPi_5
lemma finite_arc_cutoffs : ∃ (s : Finset (AddCircle (2*Real.pi)))
    (χ : AddCircle (2*Real.pi) → SmoothCircleFunction) (I : AddCircle (2*Real.pi) → ProperCircleArc),
    (∀ x, (χ x).IsReal ∧ tsupport (χ x).onCircle ⊆ (I x).carrier) ∧
      ∀ t : AddCircle (2*Real.pi), ∃ x ∈ s, (χ x).onCircle t ≠ 0 := by
  classical
  have hex (x : AddCircle (2*Real.pi)) : ∃ I : ProperCircleArc, ∃ χ : SmoothCircleFunction,
      χ.IsReal ∧ χ.onCircle x=1 ∧ tsupport χ.onCircle ⊆ I.carrier := by
    obtain ⟨I,hI⟩ := ProperCircleArc.exists_mem x
    obtain ⟨χ,hχ,hχ1,hχS⟩ := exists_real_cutoff (isCompact_singleton (x := x)) I.isOpen_carrier
      (Set.singleton_subset_iff.mpr hI)
    exact ⟨I,χ,hχ,hχ1 (Set.mem_singleton _),hχS⟩
  choose I χ hχ hχ1 hχS using hex
  have hop (x : AddCircle (2*Real.pi)) : IsOpen {t | (χ x).onCircle t ≠ 0} := by
    exact isOpen_ne_fun (χ x).toContinuousMap.continuous continuous_const
  have hcov : (Set.univ : Set (AddCircle (2*Real.pi))) ⊆ ⋃ x, {t | (χ x).onCircle t ≠ 0} := by
    intro t _
    exact Set.mem_iUnion.mpr ⟨t,by change (χ t).onCircle t ≠ 0; rw [hχ1]; exact one_ne_zero⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover _ hop hcov
  refine ⟨s,χ,I,fun x => ⟨hχ x,hχS x⟩,?_⟩
  intro t
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ t))
  obtain ⟨hxS,hxt⟩ := Set.mem_iUnion.mp hx
  exact ⟨x,hxS,hxt⟩
lemma finite_arc_partition (f : SmoothCircleFunction) : ∃ (s : Finset (AddCircle (2*Real.pi)))
    (g : AddCircle (2*Real.pi) → SmoothCircleFunction) (I : AddCircle (2*Real.pi) → ProperCircleArc),
    (∀ x, tsupport (g x).onCircle ⊆ (I x).carrier) ∧
      (f : ℝ → ℂ)=fun t => ∑ x ∈ s, g x t := by
  classical
  obtain ⟨s,χ,I,hχ,hcov⟩ := finite_arc_cutoffs
  let S := sumTests s (fun x => (χ x).power 2)
  have hSn (t : ℝ) : S t ≠ 0 := by
    have hr (x) : χ x t=((χ x t).re : ℂ) := by
      have H := congrArg Complex.im ((hχ x).1 t)
      apply Complex.ext
      · rfl
      · change -(χ x t).im=(χ x t).im at H
        change (χ x t).im=0
        linarith
    have he : (S t).re=∑ x ∈ s, (χ x t).re^2 := by
      simp only [S,sumTests_apply,power_apply,Complex.re_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [hr,← Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_re]
    have hp : 0 < ∑ x ∈ s, (χ x t).re^2 := by
      apply Finset.sum_pos' (fun x _ => sq_nonneg _)
      obtain ⟨x,hx,hxt⟩ := hcov (t : AddCircle (2*Real.pi))
      refine ⟨x,hx,sq_pos_of_ne_zero ?_⟩
      intro hz
      apply hxt
      change χ x t=0
      rw [hr,hz,Complex.ofReal_zero]
    intro hz
    rw [hz,Complex.zero_re] at he
    linarith
  let R := S.reciprocal hSn
  let g := fun x => ((χ x).power 2).mul (R.mul f)
  refine ⟨s,g,I,?_,?_⟩
  · intro x
    apply Subset.trans _ (hχ x).2
    apply closure_mono
    intro t ht
    have hn : (χ x).onCircle t ≠ 0 := by
      intro hz
      apply ht
      induction t using QuotientAddGroup.induction_on with
      | H t =>
        change (χ x t)^2*(R t*f t)=0
        change χ x t=0 at hz
        rw [hz,zero_pow (by decide),zero_mul]
    exact hn
  · funext t
    change f t=∑ x ∈ s, (χ x t)^2*((S t)⁻¹*f t)
    rw [← Finset.sum_mul]
    change f t=S t*((S t)⁻¹*f t)
    rw [← mul_assoc,mul_inv_cancel₀ (hSn t),one_mul]
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Set Filter
open scoped Topology

open UniformSpace Set

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusVacuum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
open scoped ContDiff MatrixGroups
namespace StronglyRationalVOA.SmoothCircleFunction
lemma coefficient_of_mobius_equation (f : SmoothCircleFunction)
    (hf : (f.differentiated 3).add (f.differentiated 1)=constant 0) (n : ℤ)
    (hn : n ≠ 0) (hn1 : n ≠ 1) (hnm : n ≠ -1) : f.coefficient n=0 := by
  have h := congrArg (fun f : SmoothCircleFunction => f.coefficient n) hf
  rw [coefficient_add,coefficient_differentiated,coefficient_differentiated,
    coefficient_zero_constant] at h
  have hi : (Complex.I*(n:ℂ))^3+Complex.I*(n:ℂ)=
      -Complex.I*(n:ℂ)*((n:ℂ)-1)*((n:ℂ)+1) := by
    calc
      _ = Complex.I^2*Complex.I*(n:ℂ)^3+Complex.I*(n:ℂ) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [pow_one,← add_mul,hi] at h
  have hn' : (n:ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have h1 : (n:ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn1)
  have hm : (n:ℂ)+1 ≠ 0 := by
    intro hh; have he : (n:ℂ)=(-1:ℂ) := by linear_combination hh
    exact hnm (by exact_mod_cast he)
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hn') h1) hm)
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma mobius_stress_vacuum (hc : A.toVertexAlgebra.C2Cofinite) (f : SmoothCircleFunction)
    (hf : (f.differentiated 3).add (f.differentiated 1)=SmoothCircleFunction.constant 0) :
    U.smoothSmear hc A.conformal_mem f.rapid_coefficients (U.smoothCoreVector A.vacuum)=0 := by
  apply Subtype.ext
  rw [smoothCoreVector,U.smoothSmear_coe,A.smearedMap_apply]
  change (∑' n : ℤ, f.coefficient n • (A.physicalMode A.conformalVector 2 n A.vacuum:Completion V))=0
  trans ∑' _ : ℤ, (0 : Completion V)
  · apply tsum_congr
    intro n
    by_cases hn : -1 ≤ n
    · have he : A.physicalMode A.conformalVector 2 n=A.virasoroMode n := by
        simp only [physicalMode,virasoroMode]
        congr 1
        omega
      rw [he,A.virasoro_vacuum n hn,Completion.coe_zero,smul_zero]
    · rw [f.coefficient_of_mobius_equation hf n (by omega) (by omega) (by omega),zero_smul]
  · simp


end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end


