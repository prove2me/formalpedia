-- Prove2me | Definitions.Def_OAIQ039C022
-- name    : OAIQ039C022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:15:04.474554+00:00
-- url     : https://prove2.me/theorems/b8359440-9c28-4796-8380-c712a01127cf
-- title:
--   Definitions bundle OAIQ039C022 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 8 definitions, 1 instance and 14 theorems. The definitions and types are `OAI.Kadison.CyclicColumns.matrixRepresentation`, `OAI.Kadison.Decomposable.act`, `OAI.Kadison.Decomposable.operator`, `OAI.Kadison.NormalSubalgebra.inclusion`, `OAI.Kadison.NormalSubalgebra.trace`, `OAI.Kadison.PointwiseLift.Good`, `OAI.Kadison.TracialGNS.starMap`, `OAI.Kadison.TracialGNS.starPre`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_ColumnModule`, `Commutator_CyclicMatrix`, `Commutator_CyclicSpatialImplementation`, `Commutator_DecomposableOperator`, `Commutator_HankelAlgebra`, `Commutator_NormalGNS`, `Commutator_NormalSubalgebra`, `Commutator_PointwiseLinearLift`, `Commutator_TracialCommutation`, `Commutator_VonNeumannCStar`.
--
--   **Imports.** It imports the bundles `OAIQ039C002`, `OAIQ039C003`, `OAIQ039C004`, `OAIQ039C005`, `OAIQ039C006` and `OAIQ039C007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C032`, `OAIQ039C033`, `OAIQ039C034`, `OAIQ039C035`, `OAIQ039C037`, `OAIQ039C038`, `OAIQ039C039` and `OAIQ039C040`; the statements `OAI.Kadison.CornerSymmetrization.bound_small_projection`, `OAI.Kadison.CornerTransport.finite_small_corner_bound`, `OAI.Kadison.CyclicSpatial.matrixRepresentation_norm_eq`, `OAI.Kadison.Decomposable.commutant_ae_of_dense_commuting_fields`, `OAI.Kadison.Decomposable.exists_common_tests`, `OAI.Kadison.Decomposable.matrix_commutator_bound_of_countable_factor_fields`, `OAI.Kadison.Decomposable.matrix_commutator_bound_of_factor_fields`, `OAI.Kadison.HilbertPadding.amplified_extension_commutator_norm`, `OAI.Kadison.HilbertPadding.matrix_padding_commutator_norm`, `OAI.Kadison.IntertwinerCompression.seminorm_le`, `OAI.Kadison.IrreducibleTowerAveraging.expectation_tendsto`, `OAI.Kadison.LocalQuantization.exists_centered_compression`, `OAI.Kadison.MatrixDiffuse.noMinimal_of_matrix_stages`, `OAI.Kadison.MatrixGNS.flatBalanced_commutator_dominates`, `OAI.Kadison.MatrixGNS.flattenCopies_commutator_norm`, `OAI.Kadison.MatrixGNS.row_corner_commutator_bound`, `OAI.Kadison.NormalGNS.commutant_range_eq_of_commutative`, `OAI.Kadison.NormalGNS.image_bicommutant`, `OAI.Kadison.NormalGNS.separable_gns`, `OAI.Kadison.NormalRepresentation.exists_countable_gns_embedding`, `OAI.Kadison.NormalRepresentation.exists_stable_gns_model`, `OAI.Kadison.NormalRepresentation.finite_standard_compression_bound`, `OAI.Kadison.NormalRepresentation.separable_traced_factor_bound`, `OAI.Kadison.PartialIsometryOrder.finite_factor_unitary_subequivalence`, `OAI.Kadison.RelativeCornerQuantization.exists_polar_cut`, `OAI.Kadison.RelativeCornerQuantization.exists_relative_centered_compression`, `OAI.Kadison.commutator_column_bound` and `OAI.Kadison.matrixOperator_subtype_norm_le`; the proofs of `OAI.Kadison.CyclicColumns.cyclic_matrix_bound`, `OAI.Kadison.CyclicSpatial.matrixRepresentation_norm_eq`, `OAI.Kadison.HilbertPadding.amplified_extension_commutator_norm`, `OAI.Kadison.HilbertPadding.matrix_padding_commutator_norm`, `OAI.Kadison.IntertwinerCompression.seminorm_le`, `OAI.Kadison.MatrixGNS.flatBalanced_commutator_dominates`, `OAI.Kadison.MatrixGNS.flattenCopies_commutator_norm`, `OAI.Kadison.MatrixGNS.row_corner_commutator_bound`, `OAI.Kadison.RelativeCornerQuantization.exists_relative_centered_compression`, `OAI.Kadison.commutator_column_bound`, `OAI.Kadison.isometry_column_error_bound`, `OAI.Kadison.matrixOperator_subtype_norm_le` and `OAI.Kadison.uniform_commutator_finiteDimensional`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C002
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C004
import Definitions.Def_OAIQ039C005
import Definitions.Def_OAIQ039C006
import Definitions.Def_OAIQ039C007

section
-- module Solutions.OAIQ039_CM.Commutator_ColumnModule
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace CStarAlgebra

open Filter Set

namespace Kadison.ColumnModule

variable {A E : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma maxFunctional_one (T : A →L[ℂ] E) (u : unitary A) :
    maxFunctional T u 1=‖T (u:A)‖^2 := by
  simp only [maxFunctional_apply,one_mul]
  exact inner_self_eq_norm_sq (𝕜:=ℂ) _

end Kadison.ColumnModule

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicMatrix
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H F ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

omit [CompleteSpace H] [CompleteSpace F] in
@[simp] lemma matrixAction_apply (X : ι → ι → H →L[ℂ] F)
    (x : PiLp 2 (fun _ : ι => H)) (i : ι) :
    matrixAction X x i=∑ j, X i j (x j) := by
  simp [matrixAction]

def matrixRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    CStarMatrix ι ι A →⋆ₐ[ℂ] (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) where
  toFun X := matrixAction (fun i j => σ (X i j))
  map_zero' := by ext x i; simp
  map_one' := by
    classical
    ext x i
    rw [matrixAction_apply]
    change ∑ j, σ ((1 : CStarMatrix ι ι A) i j) (x j)=x i
    have he (j : ι) : σ ((1 : CStarMatrix ι ι A) i j) (x j)=if i=j then x j else 0 := by
      by_cases h : i=j <;> simp [CStarMatrix.one_apply,h]
    simp_rw [he]
    simp
  map_add' X Y := by
    ext x i
    simp [CStarMatrix.add_apply,Finset.sum_add_distrib]
  map_mul' X Y := by
    ext x i
    simp only [matrixAction_apply,CStarMatrix.mul_apply,map_sum,map_mul,sum_apply,
      mul_apply_eq_comp,map_sum]
    rw [Finset.sum_comm]
  commutes' c := by
    classical
    ext x i
    rw [matrixAction_apply]
    change ∑ j, σ ((algebraMap ℂ (CStarMatrix ι ι A) c) i j) (x j)=c • x i
    have he (j : ι) : σ ((algebraMap ℂ (CStarMatrix ι ι A) c) i j) (x j)=
        if i=j then c • x j else 0 := by
      by_cases h : i=j <;> simp [CStarMatrix.algebraMap_apply,h,Algebra.algebraMap_eq_smul_one]
    simp_rw [he]
    simp
  map_star' X := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [PiLp.inner_apply,matrixAction_apply,CStarMatrix.star_apply,map_star,
      ContinuousLinearMap.star_eq_adjoint,sum_inner,
      ContinuousLinearMap.adjoint_inner_left,inner_sum]
    rw [Finset.sum_comm]

end Kadison.CyclicColumns

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicSpatialImplementation
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

namespace Kadison.CyclicSpatial

open OperatorAmplification CyclicColumns ReducingRepresentation

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι]

attribute [local instance] OAI.Kadison.CyclicSpatial.instDecidableEq_solutions
@[simp] lemma represented_matrix_apply (lam : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : CStarMatrix ι ι A) (x : SumSpace (H:=H) ι) (i : ι) :
    matrixRepresentation lam X x i=∑ j,lam (X i j) (x j) :=
  matrixAction_apply _ _ _

lemma matrixRepresentation_injective (lam : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hlam : Function.Injective lam) :
    Function.Injective (matrixRepresentation (ι:=ι) lam) := by
  intro X Y h
  apply CStarMatrix.ext
  intro i j
  apply hlam
  ext x
  have hh := congrArg (fun T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι =>
    T (single ι j x) i) h
  simpa [matrixRepresentation,matrixAction_apply,single_apply,apply_ite] using hh

end Kadison.CyclicSpatial

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableOperator
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

open scoped Topology ComplexOrder InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def act (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (f : Lp H 2 μ) : Lp H 2 μ :=
  (memLp_apply μ T hm hb f).toLp _

lemma act_ae (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (f : Lp H 2 μ) :
    act μ T hm hb f =ᵐ[μ] fun a => T a (f a) := MemLp.coeFn_toLp _

lemma act_add (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (f g : Lp H 2 μ) :
    act μ T hm hb (f+g)=act μ T hm hb f+act μ T hm hb g := by
  apply Lp.ext
  filter_upwards [act_ae μ T hm hb (f+g),act_ae μ T hm hb f,act_ae μ T hm hb g,
    Lp.coeFn_add f g,Lp.coeFn_add (act μ T hm hb f) (act μ T hm hb g)] with a h1 h2 h3 h4 h5
  rw [h1,h4,h5]
  change T a (f a+g a)=act μ T hm hb f a+act μ T hm hb g a
  rw [map_add,h2,h3]

lemma act_smul (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (c : ℂ) (f : Lp H 2 μ) :
    act μ T hm hb (c • f)=c • act μ T hm hb f := by
  apply Lp.ext
  filter_upwards [act_ae μ T hm hb (c • f),act_ae μ T hm hb f,
    Lp.coeFn_smul c f,Lp.coeFn_smul c (act μ T hm hb f)] with a h1 h2 h3 h4
  simp [h1,h2,h3,h4]

lemma act_norm_le (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b d : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hd : ∀ᵐ a ∂μ,‖T a‖≤d) (f : Lp H 2 μ) :
    ‖act μ T hm hb f‖≤d*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [act_ae μ T hm hb f,hd] with a ha hda
  rw [ha]
  exact ((T a).le_opNorm (f a)).trans (mul_le_mul_of_nonneg_right hda (norm_nonneg _))

def operator (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  ({toFun := act μ T hm hb
    map_add' := act_add μ T hm hb
    map_smul' := act_smul μ T hm hb} : Lp H 2 μ →ₗ[ℂ] Lp H 2 μ).mkContinuous b
      (act_norm_le μ T hm hb hb)

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HankelAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.DihedralCorner

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

variable (u d : unitary A)

@[simp] lemma wave_zero : wave u 0=(1 : A) := by simp [wave]

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialCommutation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped ComplexOrder InnerProductSpace

open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

noncomputable def starPre : τ.PreGNS →L⋆[ℂ] τ.PreGNS :=
  (τ.toPreGNS.toLinearMap.comp
    ((starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap.comp τ.ofPreGNS.toLinearMap)).mkContinuous
    1 (fun x => by
      change ‖τ.toPreGNS (star (τ.ofPreGNS x))‖ ≤ 1 * ‖x‖
      rw [norm_star_preGNS τ hτ, PositiveLinearMap.toPreGNS_ofPreGNS, one_mul])

@[simp] lemma starPre_apply (x : τ.PreGNS) :
    starPre τ hτ x = τ.toPreGNS (star (τ.ofPreGNS x)) := rfl

noncomputable def starMap : τ.GNS →L⋆[ℂ] τ.GNS := (starPre τ hτ).completion

@[simp] lemma starMap_algebra (a : A) :
    starMap τ hτ (algebraVector τ a) = algebraVector τ (star a) := by
  simp only [algebraVector_apply, starMap, ContinuousLinearMap.completion_apply_coe,
    starPre_apply, PositiveLinearMap.ofPreGNS_toPreGNS]

end Kadison.TracialGNS

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_VonNeumannCStar
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.VonNeumannCStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance cstarAlgebra (M : VonNeumannAlgebra H) : CStarAlgebra M :=
  StarSubalgebra.cstarAlgebra M

end Kadison.VonNeumannCStar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalGNS

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma tendsto_trace (hnormal : BoundedWOTContinuous M τ)
    {ι : Type*} {l : Filter ι} (a : ι → M) (b : M) (C : ℝ)
    (ha : ∀ i, ‖a i‖≤C) (hb : ‖b‖≤C)
    (hlim : ∀ x y, Tendsto (fun i => inner ℂ ((a i : H →L[ℂ] H) x) y) l
      (𝓝 (inner ℂ ((b : H →L[ℂ] H) x) y))) :
    Tendsto (fun i => τ (a i)) l (𝓝 (τ b)) := by
  let f : ι → {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} :=
    fun i => ⟨ofCLM (a i), (a i).property, ha i⟩
  let z : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} :=
    ⟨ofCLM b,b.property,hb⟩
  have hf : Tendsto f l (𝓝 z) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_iff_forall_inner_apply_tendsto.mpr
    intro x y
    simpa only [f,z,RCLike.star_def,inner_conj_symm,ofCLM_apply] using (hlim x y).star
  exact ((hnormal C).tendsto z).comp hf

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalSubalgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology InnerProductSpace

namespace Kadison.NormalSubalgebra

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M N : VonNeumannAlgebra H) (hNM : N≤M)

def inclusion : N →⋆ₐ[ℂ] M := StarSubalgebra.inclusion hNM

@[simp] lemma inclusion_apply (a : N) : (inclusion M N hNM a:H →L[ℂ] H)=(a:H →L[ℂ] H) := rfl

variable (τ : M →ₚ[ℂ] ℂ)

def trace : N →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap.comp (inclusion M N hNM).toLinearMap
  monotone' := fun _ _ h => τ.monotone h

@[simp] lemma trace_apply (a : N) : trace M N hNM τ a=τ (inclusion M N hNM a) := rfl

end Kadison.NormalSubalgebra

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PointwiseLinearLift
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.PointwiseLift

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable (A : H →L[ℂ] Lp H 2 μ) (b : ℝ)

attribute [local instance] OAI.Kadison.PointwiseLift.instNormedSpaceRat_solutions
def Good (a : Ω) : Prop :=
  (∀ x y : RationalDense.subspace H,A ((x+y:H)) a=A (x:H) a+A (y:H) a) ∧
  (∀ (r : ℚ) (x : RationalDense.subspace H),A (r • (x:H)) a=r • A (x:H) a) ∧
  (∀ x : RationalDense.subspace H,‖A (x:H) a‖≤b*‖(x:H)‖)

end Kadison.PointwiseLift

end

end
end

end OAI
end


