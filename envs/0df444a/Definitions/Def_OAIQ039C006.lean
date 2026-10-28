-- Prove2me | Definitions.Def_OAIQ039C006
-- name    : OAIQ039C006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:12:16.807419+00:00
-- url     : https://prove2.me/theorems/4437a633-74bc-4b26-9741-3303551aca51
-- title:
--   Definitions bundle OAIQ039C006 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 14 definitions and 20 theorems. The definitions and types are `OAI.Kadison.CyclicSpectral.stableUnitary`, `OAI.Kadison.Decomposable.evalL`, `OAI.Kadison.Decomposable.infiniteSumEquiv`, `OAI.Kadison.Decomposable.singleL`, `OAI.Kadison.Decomposable.singleLI`, `OAI.Kadison.FiniteTest.familyTrace`, `OAI.Kadison.InfiniteAmplification.Space`, `OAI.Kadison.InfiniteAmplification.diagonal`, `OAI.Kadison.InfiniteAmplification.map`, `OAI.Kadison.InfiniteAmplification.mapEquiv`, `OAI.Kadison.InfiniteAmplification.mapIsometry`, `OAI.Kadison.InfiniteAmplification.mapLinear`, `OAI.Kadison.PointwiseLift.instNormedSpaceRat_solutions`, `OAI.l2InfiniteSumDecidableEq`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_AddField`, `Commutator_DecomposableAlgebra`, `Commutator_FieldAdjoint`, `Commutator_FiniteTestPatching`, `Commutator_InfiniteAmplification`, `Commutator_InfiniteUnitary`, `Commutator_L2InfiniteSum`, `Commutator_PointwiseLinearLift`, `Commutator_ScalarIndicator`, `Commutator_StableSpectralUnitary`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C022`, `OAIQ039C024`, `OAIQ039C025`, `OAIQ039C027`, `OAIQ039C028` and `OAIQ039C029`; the statements `OAI_Kadison_FaithfulNormalFunctional_restricted_normal`, `OAI.Kadison.InfiniteAmplification.separable_space` and `OAI_Kadison_TracialGNS_actual_block_classification`; the proofs of `OAI_Kadison_FaithfulNormalFunctional_restricted_normal`, `OAI.Kadison.InfiniteAmplification.separable_space`, `OAI.Kadison.MatrixCorners.normalizedStageAlphabet_centered`, `OAI.Kadison.MatrixCorners.normalizedStageAlphabet_orthonormal`, `OAI.Kadison.MatrixCorners.projection_rank`, `OAI.Kadison.WOTDistance.exists_commutant_approximation`, `OAI.Kadison.finite_pairing_source_bound`, `OAI.Kadison.finite_pairing_test_bound` and `OAI.Kadison.isometry_row_adjoint_comp`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

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

lemma add_measurable (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ) (ξ : H) :
    AEStronglyMeasurable (fun a => (T a+S a) ξ) μ := (hT ξ).add (hS ξ)

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AddField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma add_field_bound (T S : Ω → H →L[ℂ] H) {b c : ℝ}
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖ ≤ c) :
    ∀ᵐ a ∂μ,‖T a+S a‖≤b+c := by
  filter_upwards [hb,hc] with a ha hc
  exact (norm_add_le _ _).trans (add_le_add ha hc)

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ScalarIndicator
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

lemma indicator_measurable (s : Set Ω) (hs : MeasurableSet s) (ξ : H) :
    AEStronglyMeasurable (fun a => (s.indicator (fun _ => (1:H →L[ℂ] H)) a) ξ) μ := by
  classical
  convert (aestronglyMeasurable_const (b:=ξ)).indicator hs using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  by_cases ha : a∈s <;> simp [ha]

lemma indicator_bound (s : Set Ω) :
    ∀ᵐ a ∂μ,‖s.indicator (fun _ => (1:H →L[ℂ] H)) a‖≤1 := by
  classical
  apply Eventually.of_forall
  intro a
  by_cases ha : a∈s
  · simp only [Set.indicator_of_mem ha]
    exact ContinuousLinearMap.norm_id_le
  · simp [ha]

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
lemma field_inner_integrable (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (ξ η : H) :
    Integrable (fun a => inner ℂ (T a ξ) η) μ := by
  apply (integrable_const (b*‖ξ‖*‖η‖)).mono' ((hm ξ).inner aestronglyMeasurable_const)
  filter_upwards [hb] with a ha
  exact (norm_inner_le_norm (T a ξ) η).trans
    (mul_le_mul_of_nonneg_right (((T a).le_opNorm ξ).trans
      (mul_le_mul_of_nonneg_right ha (norm_nonneg ξ))) (norm_nonneg η))

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestPatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.FiniteTest

section FiniteFamily

open Matrix

variable {A I J H : Type*} [CStarAlgebra A] [Fintype I] [LinearOrder I]
  [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
  (τ : A →ₗ[ℝ] ℝ)
  (hτ : ∀ a b : A, τ (a*b) = τ (b*a))
  (v : A →ₗ[ℝ] H)

def familyTrace : (J → A) →ₗ[ℝ] ℝ := ∑ j, τ.comp (LinearMap.proj j)

end FiniteFamily

end Kadison.FiniteTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace ENNReal

namespace Kadison.InfiniteAmplification

variable {ι : Type*}

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

abbrev Space (ι H : Type*) [NormedAddCommGroup H] := lp (fun _ : ι => H) 2

omit [CompleteSpace H] [CompleteSpace G] in
lemma map_mem (T : H →L[ℂ] G) (x : Space ι H) : Memℓp (fun i => T (x i)) 2 := by
  apply ((lp.memℓp x).norm.const_smul ‖T‖).mono
  intro i
  exact T.le_opNorm (x i)

def mapLinear (T : H →L[ℂ] G) : Space ι H →ₗ[ℂ] Space ι G where
  toFun x := ⟨fun i => T (x i),map_mem T x⟩
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' c x := by ext i; exact map_smul _ _ _

omit [CompleteSpace H] [CompleteSpace G] in
lemma norm_mapLinear_le (T : H →L[ℂ] G) (x : Space ι H) :
    ‖mapLinear T x‖≤‖T‖*‖x‖ := by
  calc
    _≤‖(‖T‖:ℂ) • x‖ := lp.norm_mono (by norm_num) (by
      intro i
      change ‖T (x i)‖≤‖(‖T‖:ℂ) • x i‖
      simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg T)] using T.le_opNorm (x i))
    _=_ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg T)]

def map (T : H →L[ℂ] G) : Space ι H →L[ℂ] Space ι G :=
  (mapLinear T).mkContinuous ‖T‖ (norm_mapLinear_le T)

omit [CompleteSpace H] [CompleteSpace G] in
@[simp] lemma map_apply (T : H →L[ℂ] G) (x : Space ι H) (i : ι) : map T x i=T (x i) := rfl

lemma map_adjoint (T : H →L[ℂ] G) : (map (ι:=ι) T).adjoint=map T.adjoint := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [lp.inner_eq_tsum,map_apply,ContinuousLinearMap.adjoint_inner_left]

def diagonal : (H →L[ℂ] H) →⋆ₐ[ℂ] (Space ι H →L[ℂ] Space ι H) where
  toFun := map
  map_one' := by ext x i; rfl
  map_zero' := by ext x i; rfl
  map_add' a b := by ext x i; rfl
  map_mul' a b := by ext x i; rfl
  commutes' c := by ext x i; rfl
  map_star' a := (map_adjoint a).symm

@[simp] lemma diagonal_apply (T : H →L[ℂ] H) (x : Space ι H) (i : ι) : (diagonal (ι:=ι) (H:=H)) T x i=T (x i) := rfl

def mapIsometry (V : H →ₗᵢ[ℂ] G) : Space ι H →ₗᵢ[ℂ] Space ι G where
  toLinearMap := (map V.toContinuousLinearMap).toLinearMap
  norm_map' x := by
    apply le_antisymm
    · exact lp.norm_mono (by norm_num) (fun i => (V.norm_map (x i)).le)
    · exact lp.norm_mono (by norm_num) (fun i => (V.norm_map (x i)).ge)

omit [CompleteSpace H] [CompleteSpace G] in
@[simp] lemma mapIsometry_apply (V : H →ₗᵢ[ℂ] G) (x : Space ι H) (i : ι) :
    mapIsometry V x i=V (x i) := rfl

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteUnitary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.InfiniteAmplification

variable {ι H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def mapEquiv (U : H ≃ₗᵢ[ℂ] G) : Space ι H ≃ₗᵢ[ℂ] Space ι G :=
  LinearIsometryEquiv.ofSurjective (mapIsometry U.toLinearIsometry) (fun x =>
    ⟨mapIsometry U.symm.toLinearIsometry x,by ext i; exact U.apply_symm_apply (x i)⟩)

omit [CompleteSpace H] [CompleteSpace G] in
@[simp] lemma mapEquiv_apply (U : H ≃ₗᵢ[ℂ] G) (x : Space ι H) (i : ι) :
    mapEquiv U x i=U (x i) := rfl

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_L2InfiniteSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

local instance l2InfiniteSumDecidableEq {α : Sort*} : DecidableEq α := Classical.decEq α

open MeasureTheory Filter

open scoped Topology InnerProductSpace ENNReal

namespace Kadison.Decomposable

variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open InfiniteAmplification

def singleL (i : ι) : Lp H 2 μ →L[ℂ] Lp (Space ι H) 2 μ :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 i).compLpL 2 μ

def evalL (i : ι) : Lp (Space ι H) 2 μ →L[ℂ] Lp H 2 μ :=
  (lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLpL 2 μ

omit [Countable ι] [CompleteSpace H] in
lemma inner_singleL (i : ι) (f : Lp H 2 μ) (g : Lp (Space ι H) 2 μ) :
    inner ℂ (singleL μ i f) g=inner ℂ f (evalL μ i g) := by
  classical
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLp
    (lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 i) f,
    ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i) g] with a ha hb
  change inner ℂ ((lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 i).compLp f a) (g a)=
    inner ℂ (f a) ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp g a)
  rw [ha,hb]
  exact lp.inner_single_left (𝕜:=ℂ) i (f a) (g a)

omit [Countable ι] [CompleteSpace H] in
lemma evalL_singleL (i j : ι) (f : Lp H 2 μ) :
    evalL μ i (singleL μ j f)=if i=j then f else 0 := by
  classical
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLp
    (lp.evalCLM ℂ (fun _ : ι => H) 2 i) (singleL μ j f),
    ContinuousLinearMap.coeFn_compLp (lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 j) f,
    Lp.coeFn_zero H 2 μ] with a ha hb hz
  change ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp (singleL μ j f)) a=_
  rw [ha]
  change singleL μ j f a i=_
  change ((lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 j).compLp f) a i=_
  rw [hb]
  change lp.single (E:=fun _ : ι => H) 2 j (f a) i=_
  by_cases hij : i=j
  · subst j
    simp [lp.single_apply]
  · rw [ite_eq_right hij,hz]
    simp [lp.single_apply,hij]

def singleLI (i : ι) : Lp H 2 μ →ₗᵢ[ℂ] Lp (Space ι H) 2 μ :=
  (singleL μ i).toLinearMap.isometryOfInner (fun f g => by
    change inner ℂ (singleL μ i f) (singleL μ i g)=inner ℂ f g
    rw [inner_singleL,evalL_singleL,ite_eq_left rfl])

omit [Countable ι] [CompleteSpace H] in
lemma singleLI_orthogonal : OrthogonalFamily ℂ (fun _ : ι => Lp H 2 μ) (singleLI μ) := by
  intro i j hij f g
  change inner ℂ (singleL μ i f) (singleL μ j g)=0
  rw [inner_singleL,evalL_singleL,ite_eq_right hij,inner_zero_right]

omit [CompleteSpace H] in
lemma evalL_separates (f : Lp (Space ι H) 2 μ) (hf : ∀ i,evalL μ i f=0) : f=0 := by
  classical
  apply Lp.ext
  have hcoord : ∀ᵐ a ∂μ,∀ i : ι,f a i=0 := ae_all_iff.mpr (fun i => by
    filter_upwards [ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i) f,
      Lp.coeFn_zero H 2 μ] with a ha hz
    have he : (evalL μ i f) a=0 := by rw [hf]; exact hz
    change ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp f) a=0 at he
    rw [ha] at he
    exact he)
  filter_upwards [hcoord,Lp.coeFn_zero (Space ι H) 2 μ] with a ha hz
  rw [hz]
  ext i
  exact ha i

lemma singleLI_total :
    ⊤≤(⨆ i,LinearMap.range (singleLI (H:=H) (ι:=ι) μ i).toLinearMap).topologicalClosure := by
  let K : Submodule ℂ (Lp (Space ι H) 2 μ) :=
    (⨆ i,LinearMap.range (singleLI μ i).toLinearMap).topologicalClosure
  have hclosed : IsClosed (K : Set (Lp (Space ι H) 2 μ)) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace K := hclosed.completeSpace_coe
  have hbot : Kᗮ=⊥ := by
    apply le_antisymm ?_ bot_le
    intro f hf
    rw [Submodule.mem_bot]
    apply evalL_separates μ f
    intro i
    apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    rw [←inner_singleL]
    exact Submodule.inner_right_of_mem_orthogonal
      ((Submodule.le_topologicalClosure _)
        ((le_iSup (fun i => LinearMap.range (singleLI μ i).toLinearMap) i)
          ⟨evalL μ i f,rfl⟩)) hf
  exact le_of_eq ((Submodule.orthogonal_eq_bot_iff).mp hbot).symm

def infiniteSumEquiv : Space ι (Lp H 2 μ) ≃ₗᵢ[ℂ] Lp (Space ι H) 2 μ :=
  (IsHilbertSum.mk (singleLI_orthogonal (ι:=ι) μ) (singleLI_total μ)).linearIsometryEquiv.symm

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PointwiseLinearLift
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

local instance instNormedSpaceRat_solutions : NormedSpace ℚ H := NormedSpace.restrictScalars ℚ ℂ H

end Kadison.PointwiseLift

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StableSpectralUnitary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped Topology InnerProductSpace

namespace Kadison.CyclicSpectral

open InfiniteAmplification Decomposable

variable {Ω H G : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [CompactSpace Ω]
  [BorelSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

def stableUnitary (W : Space ℕ H ≃ₗᵢ[ℂ] Space ℕ G) (V : Lp ℂ 2 μ ≃ₗᵢ[ℂ] G) :
    Space ℕ H ≃ₗᵢ[ℂ] Lp (Space ℕ ℂ) 2 μ :=
  W.trans ((mapEquiv (ι:=ℕ) V.symm).trans (infiniteSumEquiv (ι:=ℕ) μ))

end Kadison.CyclicSpectral

end

end
end

end OAI
end


