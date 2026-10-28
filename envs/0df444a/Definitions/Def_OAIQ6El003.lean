-- Prove2me | Definitions.Def_OAIQ6El003
-- name    : OAIQ6El003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T10:18:01.510796+00:00
-- url     : https://prove2.me/theorems/63ee41f6-705c-4c70-bd9a-c74538059f0c
-- title:
--   Definitions bundle OAIQ6El003 of the split of OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 38 declarations of OpenAI's Lean: 29 definitions, 4 instances and 5 theorems. The definitions and types are `OAI.ElasticityParameter.Smooth`, `OAI.ElasticityParameter.characteristicPlane`, `OAI.ElasticityParameter.delta`, `OAI.ElasticityParameter.pbar`, `OAI.ElasticityParameter.smoothAlgebra`, `OAI.ElasticityPlanar.PL2`, `OAI.ElasticityPlanar.classicalDbar`, `OAI.ElasticityPlanar.coord`, `OAI.ElasticityPlanar.coords`, `OAI.ElasticityPlanar.planeMap`, `OAI.ElasticityPlanar.schwartzDbar`, `OAI.ElasticityPlanarDistribution.Dist`, `OAI.ElasticityPlanarDistribution.Equation`, `OAI.ElasticityPlanarDistribution.Test`, `OAI.ElasticityPlanarDistribution.dbar`, `OAI.ElasticityPlanarDistribution.dhol`, `OAI.ElasticityRecovery.RMat`, `OAI.ElasticityRegularity.LocalEqual`, `OAI.ElasticityRegularity.LocalSobolev`, `OAI.ElasticityRegularity.bcfToDist`, `OAI.ElasticityRegularity.bcfToLinfty`, `OAI.ElasticityRigidity.D`, `OAI.ElasticityRigidity.HolomorphicComparison`, `OAI.ElasticityRigidity.M`, `OAI.ElasticityRigidity.Mat`, `OAI.ElasticityRigidity.Transport`, `OAI.ElasticityRigidity.X`, `OAI.ElasticityRigidity.e`, `OAI.ElasticityRigidity.θ`.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics, in whole or in part: [`Elasticity_Homotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Homotopy.lean), [`Elasticity_LocalRegularity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/LocalRegularity.lean), [`Elasticity_Parameters`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Parameters.lean), [`Elasticity_Planar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Planar.lean), [`Elasticity_Recovery`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Recovery.lean), [`Elasticity_Regularity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Regularity.lean), [`Elasticity_Rigidity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Rigidity.lean), [`Elasticity_Transport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transport.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ6El005`; the statements `OAI.ElasticityFrame.exists_constraint_columns`, `OAI.ElasticityFrame.exists_constraint_transport`, `OAI.ElasticityGeneralSlicing.smooth_cylinder_representative`, `OAI.ElasticityGeneralSlicing.smooth_supported_of_cylinder`, `OAI_ElasticityODE_fundamental_contDiff`, `OAI.ElasticityParameter.holomorphic_of_supported_transport`, `OAI_ElasticityPlanar_classical_parameter_smooth`, `OAI.ElasticityPlanar.exists_algebra_variable_homotopy` and `OAI_ElasticityPlanar_exists_classical_variable`; the proofs of `OAI.ElasticityAugmented.supported_matrix_holomorphic`, `OAI.ElasticityConic.chart_comparison_trivial`, `OAI.ElasticityCoordinates.planar_smooth_representative`, `OAI.ElasticityDistribution.affine_cutoff_bound`, `OAI.ElasticityDistribution.augmentation_cutoff_bound`, `OAI.ElasticityDistribution.normSource_cutoff_bound`, `OAI.ElasticityDistribution.physical_quantitative_H1`, `OAI.ElasticityFrame.exists_constraint_columns`, `OAI.ElasticityFrame.exists_constraint_transport`, `OAI_ElasticityODE_fundamental_contDiff`, `OAI_ElasticityPlanar_exists_spatial_linear_frame`, `OAI_ElasticityPlanar_exists_spatial_linear_transport`, `OAI_ElasticityRegularity_exists_bounded_integer_multiplier`, `OAI.ElasticityRegularity.exists_localized_derivative`, `OAI.ElasticityRegularity.quantitative_cutoff_gain` and `OAI.Elasticity.dn_common_normal_frame`.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ6_Elast.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Regularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual distributional elliptic regularity dependencies of the physical and
planar weak-limit constructions. No regularity assumption on an L2 unknown is
used in the gain of Sobolev order below. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
namespace ElasticityRegularity


variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Local Bessel-potential regularity, using actual compact smooth multipliers. -/
def LocalSobolev (Ω : Set E) (s : ℝ) (u : 𝓢'(E,F)) : Prop :=
  ∀ g : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ Ω →
    MemSobolev s 2 (smulLeftCLM F g u)

end ElasticityRegularity

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_LocalRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
namespace ElasticityRegularity


section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def LocalEqual (Ω : Set E) (u v : 𝓢'(E,ℂ)) : Prop :=
  ∀ φ : 𝓢(E,ℂ), HasCompactSupport (φ : E → ℂ) → tsupport (φ : E → ℂ) ⊆ Ω → u φ=v φ
end

end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Planar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanarDistribution
open MeasureTheory TemperedDistribution Complex
open scoped SchwartzMap LineDeriv Laplacian ENNReal BigOperators
open ElasticityRegularity
abbrev Test := 𝓢(ℂ,ℂ)
abbrev Dist := 𝓢'(ℂ,ℂ)
def dbar (u : Dist) : Dist := ∂_{(1 : ℂ)} u+I • ∂_{I} u
def dhol (u : Dist) : Dist := ∂_{(1 : ℂ)} u-I • ∂_{I} u

/-- Actual planar first-order equation on distributions, not an abstract
regularity or frame existence interface. -/
def Equation {n : Type*} [Fintype n] (Ω : Set ℂ) (a : n → n → ℂ → ℂ) (u f : n → Dist) : Prop :=
  ∀ i, ElasticityRegularity.LocalEqual Ω (dbar (u i)) (f i+∑ j, smulLeftCLM ℂ (a i j) (u j))

end ElasticityPlanarDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
abbrev PL2 := Lp ℂ 2 (volume : Measure ℂ)

end ElasticityPlanar
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
omit [InnerProductSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma compact_slice {S : Set E} (hS : IsCompact S) (a : P × E → ℂ)
    (hs : ∀ p x, x∉S → a (p,x)=0) (p : P) : HasCompactSupport (fun x => a (p,x)) := by
  apply hS.of_isClosed_subset (isClosed_tsupport _)
  exact closure_minimal (fun x hx => by contrapose! hx; simpa only [Function.mem_support,not_not] using hs p x hx) hS.isClosed

end ElasticityRegularity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
def bcfToLinfty : BoundedContinuousFunction E ℂ →L[ℂ] Lp ℂ ∞ (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := fun g => g.memLp_top.toLp _
      map_add' := fun f g => by exact f.memLp_top.toLp_add g.memLp_top
      map_smul' := fun c f => by exact f.memLp_top.toLp_const_smul c } 1 (fun g => by
        change ‖(g.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E))‖ ≤ 1*‖g‖
        rw [one_mul,Lp.norm_toLp,eLpNorm_exponent_top]
        exact (ENNReal.toReal_mono (by simp)
          (eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall g.norm_coe_le_norm))).trans_eq
            (ENNReal.toReal_ofReal (norm_nonneg g)))
def bcfToDist : BoundedContinuousFunction E ℂ →L[ℂ] 𝓢'(E,ℂ) :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) ∞).comp bcfToLinfty
end ElasticityRegularity
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Complex
open scoped SchwartzMap ENNReal LineDeriv BigOperators
variable {n : Type*} [Fintype n]
open ElasticityRegularity

def schwartzDbar (v : 𝓢(ℂ,ℂ)) : 𝓢(ℂ,ℂ) := ∂_{(1 : ℂ)} v+I • ∂_{I} v
end ElasticityPlanar

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Homotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Complex Module
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityPlanar
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
  [FiniteDimensional ℂ R]
variable {n : Type*} [Fintype n] [DecidableEq n]
def coords (q : Basis n ℂ R) : R ≃L[ℂ] (n → ℂ) := q.equivFun.toContinuousLinearEquiv
def coord (q : Basis n ℂ R) (i : n) : R →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp (coords q).toContinuousLinearMap

def classicalDbar (f : ℂ → R) (z : ℂ) : R := fderiv ℝ f z 1+I • fderiv ℝ f z I
end ElasticityPlanar

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Recovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix

/-! Finite-type uniqueness used in the last step of the elasticity proof.
All spaces and coefficient fields below are actual functions, not axioms. -/
noncomputable section
open Set Filter Module
open scoped BigOperators Topology

namespace ElasticityRecovery
open Module

abbrev RMat := Matrix (Fin 3) (Fin 3) ℝ

end ElasticityRecovery

end
end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory Set Topology
open scoped BigOperators ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : Type*} [Fintype n]

def planeMap (J : ℂ →L[ℝ] E) (x : E) (z : ℂ) : E := x+J z
end ElasticityPlanar
namespace ElasticityParameter
open scoped BigOperators
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
def smoothAlgebra : Subalgebra ℂ (E → ℂ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f}
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ (⊤ : ℕ∞) f at hf
    change ContDiff ℝ (⊤ : ℕ∞) g at hg
    exact hf.add hg
  mul_mem' := by
    intro f g hf hg
    change ContDiff ℝ (⊤ : ℕ∞) f at hf
    change ContDiff ℝ (⊤ : ℕ∞) g at hg
    exact hf.mul hg
  zero_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : E => (0 : ℂ))
    exact contDiff_const
  one_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : E => (1 : ℂ))
    exact contDiff_const
  algebraMap_mem' c := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : E => c)
    exact contDiff_const
abbrev Smooth := smoothAlgebra E
variable {E}
lemma smooth (f : Smooth E) : ContDiff ℝ (⊤ : ℕ∞) (f : E → ℂ) := f.property

def delta (v : E) : Derivation ℂ (Smooth E) (Smooth E) := Derivation.mk'
  { toFun := fun f => ⟨fun x => fderiv ℝ (f : E → ℂ) x v,
      ((smooth f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const⟩
    map_add' f g := by
      apply Subtype.ext
      funext x
      exact congrArg (fun T : E →L[ℝ] ℂ => T v)
        (fderiv_add ((smooth f).differentiable (by simp) x) ((smooth g).differentiable (by simp) x))
    map_smul' c f := by
      apply Subtype.ext
      funext x
      exact congrArg (fun T : E →L[ℝ] ℂ => T v)
        (fderiv_const_smul ((smooth f).differentiable (by simp) x) c) }
  (by
    intro f g
    apply Subtype.ext
    funext x
    exact congrArg (fun T : E →L[ℝ] ℂ => T v)
      (fderiv_mul ((smooth f).differentiable (by simp) x) ((smooth g).differentiable (by simp) x)))

/-- Parameter antiholomorphic derivative in fixed physical coordinates, without
changing the physical point or differentiating any moving plane coordinates. -/
def pbar : Derivation ℂ (Smooth (E × ℂ)) (Smooth (E × ℂ)) :=
  delta ((0 : E),(1 : ℂ))+Complex.I • delta ((0 : E),Complex.I)
end ElasticityParameter
namespace ElasticityParameter
open Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {k n : Type*} [Fintype k] [Fintype n]

def characteristicPlane (e : k → E) (θ : k → ℂ) : ℂ →L[ℝ] E :=
  Complex.reCLM.smulRight (∑ r, (θ r).re • e r)+
    Complex.imCLM.smulRight (∑ r, (θ r).im • e r)
end ElasticityParameter

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Rigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Two-chart proof of precisely the holomorphic-conic rigidity step. The
analytic construction of the comparison from DN equality is NOT assumed in
the main target and is still missing. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology Matrix
namespace ElasticityRigidity

abbrev X := EuclideanSpace ℝ (Fin 3)
abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

def θ (z : ℂ) : Fin 3 → ℂ := ![1 - z ^ 2, Complex.I * (1 + z ^ 2), 2 * z]

def e (i : Fin 3) : X := EuclideanSpace.single i 1

def D (z : ℂ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ i, θ z i * fderiv ℝ f x (e i)

/-- The exact chart transition for End(O(-1)² ⊕ O). The two spatial
coefficients are expressed in h₁(1,z),h₂(1,z) and h₁(w,1),h₂(w,1). -/
def HolomorphicComparison (G₀ Ginf : X → ℂ → Mat) : Prop :=
  (∀ x i j, Differentiable ℂ (fun z => G₀ x z i j)) ∧
  (∀ x i j, Differentiable ℂ (fun w => Ginf x w i j)) ∧
  (∀ x z, z ≠ 0 → ∀ i j,
    G₀ x z i j =
      (if i = 2 then (1 : ℂ) else z⁻¹) * Ginf x z⁻¹ i j *
      (if j = 2 then (1 : ℂ) else z))

/-- Normal-form connection matrix on the finite chart; q is the bottom-left
row in this frame and T the original scalar coefficient. -/
def M (q : X → ℂ → Fin 2 → ℂ) (T : X → ℂ → ℂ) (x : X) (z : ℂ) : Mat :=
  !![0, 0, 1; 0, 0, z; q x z 0, q x z 1, T x z]

def Transport (G : X → ℂ → Mat)
    (q₁ q₂ : X → ℂ → Fin 2 → ℂ) (T₁ T₂ : X → ℂ → ℂ) : Prop :=
  ∀ x z i j, D z (fun y => G y z i j) x =
    (M q₂ T₂ x z * G x z - G x z * M q₁ T₁ x z) i j

end ElasticityRigidity

end
end

end OAI
end


