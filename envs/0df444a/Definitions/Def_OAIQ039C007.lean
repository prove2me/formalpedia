-- Prove2me | Definitions.Def_OAIQ039C007
-- name    : OAIQ039C007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:12:07.778124+00:00
-- url     : https://prove2.me/theorems/84179c77-559c-4889-a4de-bc5685729a5c
-- title:
--   Definitions bundle OAIQ039C007 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 7 definitions, 1 instance and 19 theorems. The definitions and types are `OAI.Kadison.Decomposable.assemble`, `OAI.Kadison.Decomposable.assembleIsometry`, `OAI.Kadison.Decomposable.instNormedAlgebraRat_solutions`, `OAI.Kadison.Kaplansky.instDecidableEqFinOfNatNat_solutions`, `OAI.Kadison.OperatorAmplification.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions`, `OAI.Kadison.RationalDense.instNormedSpaceRat_solutions`, `OAI.Kadison.RationalDense.subspace`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CountableFieldHom`, `Commutator_DecomposableAlgebra`, `Commutator_DecomposableNorm`, `Commutator_DiagonalField`, `Commutator_FiberCommutator`, `Commutator_FieldAdjoint`, `Commutator_FiniteVectorLpConvergence`, `Commutator_KaplanskyFull`, `Commutator_L2FiniteSum`, `Commutator_MainCommutantDistance`, `Commutator_MainMatrix`, `Commutator_MatrixAlgebraDensity`, `Commutator_RationalDense`, `Commutator_StarField`.
--
--   **Imports.** It imports the published bundle `Def_UniformCommutator`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C022`, `OAIQ039C023` and `OAIQ039C030`; the statements `OAI_Kadison_MatrixTower_finite_standard_matrixOperator_bound`, `OAI_Kadison_OrbitStateHull_hull_normal` and `OAI_Kadison_TracialGNS_actual_block_classification`; the proofs of `OAI_Kadison_Decomposable_uniform_commutator_in_central_spectral_model`, `OAI_Kadison_Decomposable_uniform_commutator_in_representation_model`, `OAI.Kadison.IntertwinerCompression.pullback_matrix_commutator_norm_le`, `OAI_Kadison_MatrixCornerImplementation_exists_represented_local_module`, `OAI_Kadison_MatrixTower_finite_standard_matrixOperator_bound`, `OAI.Kadison.UnitaryTransport.bound_of_conjugate_bound`, `OAI.Kadison.isometry_row_error_bound`, `OAI.Kadison.uniform_commutator_nonfinite_factor`, `OAI.Kadison.uniform_commutator_of_isometries` and `OAI_Kadison_uniform_commutator_of_two_isometries`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_UniformCommutator

section
-- module Solutions.OAIQ039_CM.Commutator_CountableFieldHom
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

local instance instNormedAlgebraRat_solutions : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableAlgebra
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

lemma mul_bound (T S : Ω → H →L[ℂ] H) {b c : ℝ} (hb0 : 0≤b)
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖ ≤ c) :
    ∀ᵐ a ∂μ,‖T a*S a‖≤b*c := by
  filter_upwards [hb,hc] with a ha hc
  exact (norm_mul_le _ _).trans (mul_le_mul ha hc (norm_nonneg _) hb0)

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableNorm
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

lemma l2_norm_sq (f : Lp H 2 μ) : ‖f‖^2=∫ a,‖f a‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ←integral_re (L2.integrable_inner f f)]
  congr 1
  ext a
  exact (norm_sq_eq_re_inner (𝕜:=ℂ) (f a)).symm

lemma indicator_norm_sq (s : Set Ω) (hs : MeasurableSet s) (hμs : μ s≠⊤) (ξ : H) :
    ‖indicatorConstLp 2 hs hμs ξ‖^2=∫ _ in s,‖ξ‖^2 ∂μ := by
  classical
  rw [l2_norm_sq,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p:=2) (hs:=hs) (hμs:=hμs) (c:=ξ)] with a ha
  rw [ha]
  by_cases hx : a∈s <;> simp [hx]

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_L2FiniteSum
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

omit [CompleteSpace H] in
lemma memLp_vector (f : PiLp 2 (fun _ : ι => Lp H 2 μ)) :
    MemLp (fun a => WithLp.toLp 2 (fun i => f i a)) 2 μ := by
  have hm : MemLp (fun a i => f i a) 2 μ := memLp_pi_iff.mpr (fun i => Lp.memLp (f i))
  exact hm.continuousLinearMap_comp (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap

def assemble (f : PiLp 2 (fun _ : ι => Lp H 2 μ)) : Lp (PiLp 2 (fun _ : ι => H)) 2 μ :=
  (memLp_vector μ f).toLp _

omit [CompleteSpace H] in
lemma assemble_ae (f : PiLp 2 (fun _ : ι => Lp H 2 μ)) :
    assemble μ f =ᵐ[μ] fun a => WithLp.toLp 2 (fun i => f i a) := MemLp.coeFn_toLp _

omit [CompleteSpace H] in
lemma assemble_add (f g : PiLp 2 (fun _ : ι => Lp H 2 μ)) :
    assemble μ (f+g)=assemble μ f+assemble μ g := by
  apply Lp.ext
  have hv : ∀ᵐ a ∂μ,∀ i,(f i+g i) a=f i a+g i a := ae_all_iff.mpr (fun i => Lp.coeFn_add (f i) (g i))
  filter_upwards [assemble_ae μ (f+g),assemble_ae μ f,assemble_ae μ g,
    Lp.coeFn_add (assemble μ f) (assemble μ g),hv] with a h1 h2 h3 h4 ha
  rw [h1,h4]
  change _=assemble μ f a+assemble μ g a
  rw [h2,h3]
  ext i
  exact ha i

omit [CompleteSpace H] in
lemma assemble_smul (c : ℂ) (f : PiLp 2 (fun _ : ι => Lp H 2 μ)) :
    assemble μ (c • f)=c • assemble μ f := by
  apply Lp.ext
  have hv : ∀ᵐ a ∂μ,∀ i,(c • f i) a=c • (f i a) := ae_all_iff.mpr (fun i => Lp.coeFn_smul c (f i))
  filter_upwards [assemble_ae μ (c • f),assemble_ae μ f,Lp.coeFn_smul c (assemble μ f),hv]
    with a h1 h2 h3 ha
  rw [h1,h3]
  change _=c • (assemble μ f a)
  rw [h2]
  ext i
  exact ha i

omit [CompleteSpace H] in
lemma assemble_norm (f : PiLp 2 (fun _ : ι => Lp H 2 μ)) : ‖assemble μ f‖=‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq,PiLp.norm_sq_eq_of_L2]
  calc
    _=(∫ a,∑ i,‖f i a‖^2 ∂μ) := by
      apply integral_congr_ae
      filter_upwards [assemble_ae μ f] with a ha
      rw [ha,PiLp.norm_sq_eq_of_L2]
    _=∑ i,∫ a,‖f i a‖^2 ∂μ := integral_finsetSum _ (fun i _ =>
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (f i))).mp (Lp.memLp (f i)))
    _=_ := by congr 1; ext i; exact (l2_norm_sq μ (f i)).symm

def assembleIsometry : PiLp 2 (fun _ : ι => Lp H 2 μ) →ₗᵢ[ℂ] Lp (PiLp 2 (fun _ : ι => H)) 2 μ where
  toFun := assemble μ
  map_add' := assemble_add μ
  map_smul' := assemble_smul μ
  norm_map' := assemble_norm μ

omit [CompleteSpace H] in
lemma assemble_surjective : Function.Surjective (assembleIsometry (H:=H) (ι:=ι) μ) := by
  intro f
  let g : PiLp 2 (fun _ : ι => Lp H 2 μ) :=
    WithLp.toLp 2 (fun i => (PiLp.proj 2 (fun _ : ι => H) i : PiLp 2 (fun _ : ι => H) →L[ℂ] H).compLp f)
  refine ⟨g,?_⟩
  apply Lp.ext
  have hg : ∀ᵐ a ∂μ,∀ i,g i a=f a i := ae_all_iff.mpr (fun i => ContinuousLinearMap.coeFn_compLp _ _)
  filter_upwards [assemble_ae μ g,hg] with a ha hb
  change assemble μ g a=f a
  rw [ha]
  ext i
  exact hb i

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MainMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

universe u

open scoped InnerProductSpace BigOperators ComplexOrder

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
@[simp] lemma diagonalAmplification_apply (h : ℕ) (Y : K →L[ℂ] K)
    (x : PiLp 2 (fun _ : Fin h => K)) (i : Fin h) : diagonalAmplification h Y x i=Y (x i) := by
  simp [diagonalAmplification]

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MainCommutantDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

open ContinuousLinearMap

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
lemma diagonalAmplification_norm_le (h : ℕ) (Y : K →L[ℂ] K) :
    ‖diagonalAmplification h Y‖≤‖Y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Y)
  intro x
  have hs : ‖diagonalAmplification h Y x‖^2≤(‖Y‖*‖x‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2,mul_pow,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by
      rw [diagonalAmplification_apply,←mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (le_opNorm Y (x i)) 2)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg Y) (norm_nonneg x))).mp hs

omit [CompleteSpace K] in
@[simp] lemma diagonalAmplification_sub (h : ℕ) (Y Z : K →L[ℂ] K) :
    diagonalAmplification h (Y-Z)=diagonalAmplification h Y-diagonalAmplification h Z := by
  ext x i
  simp

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DiagonalField
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
lemma diagonal_field_bound (h : ℕ) (T : Ω → H →L[ℂ] H)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) :
    ∀ᵐ a ∂μ,‖diagonalAmplification h (T a)‖≤b := by
  filter_upwards [hb] with a ha
  exact (diagonalAmplification_norm_le h (T a)).trans ha

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiberCommutator
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
lemma commutator_field_bound (T S : Ω → H →L[ℂ] H) {b c : ℝ} (hb0 : 0≤b) (hc0 : 0 ≤ c)
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖ ≤ c) :
    ∀ᵐ a ∂μ,‖T a*S a-S a*T a‖≤2*b*c := by
  filter_upwards [mul_bound μ T S hb0 hb hc,mul_bound μ S T hc0 hc hb] with a h1 h2
  exact (norm_sub_le _ _).trans (by nlinarith)

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FieldAdjoint
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
  [IsFiniteMeasure μ]

omit [CompleteSpace H] in
lemma field_inner_right_integrable (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (ξ η : H) :
    Integrable (fun a => inner ℂ ξ (T a η)) μ := by
  apply (integrable_const (‖ξ‖*(b*‖η‖))).mono' (aestronglyMeasurable_const.inner (hm η))
  filter_upwards [hb] with a ha
  exact (norm_inner_le_norm ξ (T a η)).trans
    (mul_le_mul_of_nonneg_left (((T a).le_opNorm η).trans
      (mul_le_mul_of_nonneg_right ha (norm_nonneg η))) (norm_nonneg ξ))

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteVectorLpConvergence
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

omit [CompleteSpace H] in
theorem exists_finite_test_subsequence (f : ℕ → ι → Lp H 2 μ) (g : ι → Lp H 2 μ)
    (h : ∀ i,Tendsto (fun n => f n i) atTop (𝓝 (g i))) :
    ∃ k : ℕ → ℕ,StrictMono k ∧
      ∀ᵐ a ∂μ,∀ i,Tendsto (fun n => f (k n) i a) atTop (𝓝 (g i a)) := by
  let F : ℕ → PiLp 2 (fun _ : ι => Lp H 2 μ) := fun n => WithLp.toLp 2 (f n)
  let G : PiLp 2 (fun _ : ι => Lp H 2 μ) := WithLp.toLp 2 g
  have hFG : Tendsto F atTop (𝓝 G) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp H 2 μ)).symm.continuous.tendsto g |>.comp
      (tendsto_pi_nhds.mpr h)
  have hL : Tendsto (fun n => assemble μ (F n)) atTop (𝓝 (assemble μ G)) :=
    (assembleIsometry μ).continuous.tendsto G |>.comp hFG
  obtain ⟨k,hk,hka⟩ := (tendstoInMeasure_of_tendsto_Lp hL).exists_seq_tendsto_ae
  refine ⟨k,hk,?_⟩
  filter_upwards [hka,assemble_ae μ G,ae_all_iff.mpr (fun n => assemble_ae μ (F n))]
    with a hka hG hF
  intro i
  have he (n : ℕ) : assemble μ (F (k n)) a=WithLp.toLp 2 (fun i => f (k n) i a) := hF (k n)
  simp only [he] at hka
  rw [hG] at hka
  exact (PiLp.proj 2 (fun _ : ι => H) i : PiLp 2 (fun _ : ι => H) →L[ℂ] H).continuous.tendsto _ |>.comp hka

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixAlgebraDensity
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

variable (ι : Type*) [Fintype ι]

local instance matrixAlgebraDensityDecidableEq_rc33202_1 : DecidableEq ι := Classical.decEq ι
variable (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]

local instance instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : PartialOrder S := CStarAlgebra.spectralOrder S

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.Kaplansky

open OperatorAmplification

local instance instDecidableEqFinOfNatNat_solutions : DecidableEq (Fin 2) := Classical.decEq (Fin 2)

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RationalDense
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology

namespace Kadison.RationalDense

variable (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

local instance instNormedSpaceRat_solutions : NormedSpace ℚ H := NormedSpace.restrictScalars ℚ ℂ H

def subspace : Submodule ℚ H := Submodule.span ℚ (Set.range (TopologicalSpace.denseSeq H))

instance instCountableSubtypeMemSubmoduleRatSubspace : Countable (subspace H) := by unfold subspace; infer_instance

lemma dense : DenseRange ((subspace H).subtypeL : subspace H →L[ℚ] H) := by
  apply denseRange_subtype_val.mpr
  exact Dense.mono (Submodule.subset_span) (TopologicalSpace.denseRange_denseSeq H)

lemma exists_seq (x : H) : ∃ f : ℕ → subspace H,Tendsto (fun n => (f n:H)) atTop (𝓝 x) := by
  obtain ⟨f,hf,hl⟩ := mem_closure_iff_seq_limit.mp ((dense H) x)
  choose g hg using hf
  have he : (fun n => (g n:H))=f := funext hg
  exact ⟨g,by rw [he]; exact hl⟩

end Kadison.RationalDense

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StarField
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

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
lemma adjoint_field_bound (T : Ω → H →L[ℂ] H)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) : ∀ᵐ a ∂μ,‖(T a).adjoint‖≤b := by
  simpa only [←ContinuousLinearMap.star_eq_adjoint,norm_star] using hb

end Kadison.Decomposable

end

end
end

end OAI
end


