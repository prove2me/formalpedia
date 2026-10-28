-- Prove2me | Definitions.Def_OAIQ3Vx002
-- name    : OAIQ3Vx002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:22:59.027719+00:00
-- url     : https://prove2.me/theorems/6e5ea625-f0bd-4b93-8b49-9d33695f0b0b
-- title:
--   Definitions bundle OAIQ3Vx002 of the split of OpenAI, Strongly rational unitary vertex operator algebras and conformal nets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinimalVertex.main`, carved from OpenAI's openai/math development (OpenAI, *Strongly rational unitary vertex operator algebras and conformal nets*, OpenAI Math Release, September 25, 2026, result family 280, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 68 declarations of OpenAI's Lean: 17 definitions, 4 instances and 47 theorems. The definitions and types are `OAI.StronglyRationalVOA.CircleMobiusGeometry.Rel`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.constant`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.cosine`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.cross`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.density`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.dot`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.polarAngle`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.polarPhase`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.positiveLiftFun`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.positiveMatrices`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.rotationMatrix`, `OAI.StronglyRationalVOA.CircleMobiusGeometry.sine`, `OAI.StronglyRationalVOA.ProperCircleArc.translate`, `OAI.StronglyRationalVOA.globalCyclicSpace`, `OAI.StronglyRationalVOA.globalObservableAlgebra`, `OAI.StronglyRationalVOA.phaseUnitary`, `OAI.StronglyRationalVOA.projectiveConjugation`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/VertexAlgebra, in whole or in part: `VertexAlgebra_AlgebraCovariance`, `VertexAlgebra_MobiusAnomaly`, `VertexAlgebra_MobiusExistence`, `VertexAlgebra_MobiusFullGeometry`, `VertexAlgebra_MobiusGeometry`, `VertexAlgebra_MobiusGroup`, `VertexAlgebra_MobiusRepresentation`, `VertexAlgebra_MobiusStandardAction`, `VertexAlgebra_MobiusStandardTopology`, `VertexAlgebra_MobiusVacuum`, `VertexAlgebra_NetAxioms`, `VertexAlgebra_NetVacuum`, `VertexAlgebra_ObservableScalars`, `VertexAlgebra_ProjectiveTopology`, `VertexAlgebra_SmoothTopology`.
--
--   **Imports.** It imports the published bundle `Def_VertexAlgebraNet`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ3Vx004` and `OAIQ3Vx005`.
-- source:
--   OpenAI, Strongly rational unitary vertex operator algebras and conformal nets, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 280; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/VertexAlgebra at commit adc7f12

import Mathlib
import Definitions.Def_VertexAlgebraNet

section
-- module Solutions.OAIQ3_Vtx.Compat
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
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

open UniformSpace Set Filter
open scoped Topology
namespace StronglyRationalVOA.ProperCircleArc
def translate (I : ProperCircleArc) (t : ℝ) : ProperCircleArc :=
  ⟨I.left+t,I.right+t,by linarith [I.nonempty'],by linarith [I.nondense']⟩
end StronglyRationalVOA.ProperCircleArc

open UniformSpace Set

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothTopology
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

lemma periodic_bound_from_unitInterval {f : ℝ → ℝ}
    (hf : Function.Periodic f 1) {C : ℝ} (hC : ∀ x ∈ Icc (0:ℝ) 1, |f x| ≤ C) (x : ℝ) :
    |f x| ≤ C := by
  have hx : x-(⌊x⌋ : ℤ) ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Int.floor_le x)
    · linarith [Int.lt_floor_add_one x]
  have he : f (x-(⌊x⌋ : ℤ))=f x := by simpa using hf.sub_int_mul_eq (x := x) ⌊x⌋
  rw [← he]
  exact hC _ hx

end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ProjectiveTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology
namespace StronglyRationalVOA



lemma unitaryStrong_isInducing (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Topology.IsInducing (fun E : H ≃ₗᵢ[ℂ] H => (E : H → H)) := ⟨rfl⟩

lemma unitaryStrong_continuous_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : H) : Continuous (fun E : H ≃ₗᵢ[ℂ] H => E x) :=
  (continuous_apply x).comp (unitaryStrong_isInducing H).continuous

lemma unitaryStrong_continuous_mul_right {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : H ≃ₗᵢ[ℂ] H) : Continuous (fun F : H ≃ₗᵢ[ℂ] H => F*E) := by
  apply (unitaryStrong_isInducing H).continuous_iff.mpr
  apply continuous_pi
  intro x
  exact unitaryStrong_continuous_apply (E x)

 
lemma projectiveStrong_continuous_mul_right {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : ProjectiveUnitaryGroup H) : Continuous (fun F : ProjectiveUnitaryGroup H => F*E) := by
  induction E using QuotientGroup.induction_on with
  | H E =>
    apply (QuotientGroup.isQuotientMap_mk (scalarPhaseSubgroup H)).continuous_iff.mpr
    change Continuous (fun F : H ≃ₗᵢ[ℂ] H => QuotientGroup.mk F*QuotientGroup.mk E)
    simp only [← QuotientGroup.mk_mul]
    exact (QuotientGroup.isQuotientMap_mk (scalarPhaseSubgroup H)).continuous.comp
      (unitaryStrong_continuous_mul_right E)



end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_AlgebraCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
namespace StronglyRationalVOA
lemma projective_equality_conjugation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (E F : H ≃ₗᵢ[ℂ] H)
    (h : (QuotientGroup.mk E : ProjectiveUnitaryGroup H)=QuotientGroup.mk F) :
    E.conjStarAlgEquiv=F.conjStarAlgEquiv := by
  obtain ⟨c,_,hc⟩ := QuotientGroup.eq.mp h
  have he (x : H) : F x=c • E x := by
    have H := congrArg E (hc x)
    change E (E.symm (F x))=E (c • x) at H
    simpa only [E.apply_symm_apply,map_smul] using H
  ext B x
  change E (B (E.symm x))=F (B (F.symm x))
  have hi : E.symm x=c • F.symm x := by
    apply E.injective
    rw [E.apply_symm_apply,map_smul,← he,F.apply_symm_apply]
  rw [hi,map_smul,map_smul,← he]
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry
 

def Rel (M : SL(2,ℝ)) (x y : ℝ) : Prop :=
  (M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2))*Real.sin (y/2)=
    (M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2))*Real.cos (y/2)

def density (M : SL(2,ℝ)) (x : ℝ) : ℝ :=
  (M 1 1*Real.cos (x/2)-M 0 1*Real.sin (x/2))^2+
    (M 0 0*Real.sin (x/2)-M 1 0*Real.cos (x/2))^2
lemma det (M : SL(2,ℝ)) : M 0 0*M 1 1-M 0 1*M 1 0=1 := by
  simpa only [Matrix.det_fin_two] using M.det_coe
lemma cos_sq_add_sin_sq (x : ℝ) : Real.cos x^2+Real.sin x^2=1 := by
  nlinarith [Real.sin_sq_add_cos_sq x]
lemma collinear_unit {p q c s : ℝ} (hu : c^2+s^2=1) (h : p*s=q*c) :
    (p*c+q*s)*c=p ∧ (p*c+q*s)*s=q := by
  constructor
  · linear_combination p*hu-s*h
  · linear_combination q*hu+c*h

def constant (M : SL(2,ℝ)) : ℝ := (M 0 0^2+M 0 1^2+M 1 0^2+M 1 1^2)/2
def cosine (M : SL(2,ℝ)) : ℝ := (M 1 0^2+M 1 1^2-M 0 0^2-M 0 1^2)/2
def sine (M : SL(2,ℝ)) : ℝ := -(M 0 0*M 1 0+M 0 1*M 1 1)
lemma density_trigonometric (M : SL(2,ℝ)) (x : ℝ) :
    density M x=constant M+cosine M*Real.cos x+sine M*Real.sin x := by
  have hc : Real.cos x=Real.cos (x/2)^2-Real.sin (x/2)^2 := by
    have H := Real.cos_two_mul (x/2)
    rw [show 2*(x/2)=x by ring] at H
    nlinarith [cos_sq_add_sin_sq (x/2)]
  have hs : Real.sin x=2*Real.sin (x/2)*Real.cos (x/2) := by
    have H := Real.sin_two_mul (x/2)
    rwa [show 2*(x/2)=x by ring] at H
  rw [hc,hs]
  dsimp only [density,constant,cosine,sine]
  linear_combination (M 0 0^2+M 0 1^2+M 1 0^2+M 1 1^2)/2*cos_sq_add_sin_sq (x/2)
lemma determinant_constants (M : SL(2,ℝ)) : constant M^2-cosine M^2-sine M^2=1 := by
  calc
    _ = (M 0 0*M 1 1-M 0 1*M 1 0)^2 := by dsimp [constant,cosine,sine]; ring
    _ = 1 := by rw [det]; norm_num
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusAnomaly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma density_smooth (M : SL(2,ℝ)) : ContDiff ℝ ∞ (density M) := by
  have he : density M=fun x => constant M+cosine M*Real.cos x+sine M*Real.sin x :=
    funext (density_trigonometric M)
  rw [he]
  exact (contDiff_const.add (contDiff_const.mul Real.contDiff_cos)).add
    (contDiff_const.mul Real.contDiff_sin)
lemma density_derivative (M : SL(2,ℝ)) (x : ℝ) :
    deriv (density M) x= -cosine M*Real.sin x+sine M*Real.cos x := by
  have he : density M=fun x => constant M+cosine M*Real.cos x+sine M*Real.sin x :=
    funext (density_trigonometric M)
  rw [he]
  convert (((Real.hasDerivAt_cos x).const_mul (cosine M)).const_add (constant M)).add
    ((Real.hasDerivAt_sin x).const_mul (sine M)) |>.deriv using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring
lemma density_derivative_square (M : SL(2,ℝ)) (x : ℝ) :
    (deriv (density M) x)^2= -(density M x)^2+2*constant M*density M x-1 := by
  rw [density_derivative,density_trigonometric]
  linear_combination (cosine M^2+sine M^2)*cos_sq_add_sin_sq x-determinant_constants M
lemma integral_density (M : SL(2,ℝ)) :
    (∫ x in 0..2*Real.pi, density M x)=2*Real.pi*constant M := by
  have he : density M=fun x => constant M+cosine M*Real.cos x+sine M*Real.sin x :=
    funext (density_trigonometric M)
  have hc : IntervalIntegrable (fun x => cosine M*Real.cos x) volume 0 (2*Real.pi) :=
    (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun x => sine M*Real.sin x) volume 0 (2*Real.pi) :=
    (continuous_const.mul Real.continuous_sin).intervalIntegrable _ _
  have ha : IntervalIntegrable (fun _ : ℝ => constant M) volume 0 (2*Real.pi) :=
    continuous_const.intervalIntegrable _ _
  rw [he,intervalIntegral.integral_add (ha.add hc) hs,
    intervalIntegral.integral_add ha hc,
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,integral_cos,integral_sin]
  simp [Real.sin_two_pi,Real.cos_two_pi,smul_eq_mul]
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry
def rotationMatrix (s : ℝ) : SL(2,ℝ) :=
  ⟨!![Real.cos (s/2),-Real.sin (s/2);Real.sin (s/2),Real.cos (s/2)],by
    simp only [Matrix.det_fin_two_of]
    nlinarith [cos_sq_add_sin_sq (s/2)]⟩
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups ContDiff
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma derivative_pos_of_rel (M : SL(2,ℝ)) (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hrel : ∀ x, Rel M x (f x)) (x : ℝ) : 0 < deriv f x := by
  let a := M 0 0
  let b := M 0 1
  let c := M 1 0
  let d := M 1 1
  have hdet : a*d-b*c=1 := det M
  let r := (a*Real.cos (x/2)+b*Real.sin (x/2))*Real.cos (f x/2)+
    (c*Real.cos (x/2)+d*Real.sin (x/2))*Real.sin (f x/2)
  obtain ⟨hr1,hr2⟩ := collinear_unit (cos_sq_add_sin_sq (f x/2)) (hrel x)
  change r*Real.cos (f x/2)=a*Real.cos (x/2)+b*Real.sin (x/2) at hr1
  change r*Real.sin (f x/2)=c*Real.cos (x/2)+d*Real.sin (x/2) at hr2
  have hid := (hasDerivAt_id x).div_const (2:ℝ)
  have hfd := (hf x).hasDerivAt.div_const 2
  have hl := ((hid.cos.const_mul a).add (hid.sin.const_mul b)).mul hfd.sin
  have hr := ((hid.cos.const_mul c).add (hid.sin.const_mul d)).mul hfd.cos
  have he : (fun y => (a*Real.cos (y/2)+b*Real.sin (y/2))*Real.sin (f y/2))=
      (fun y => (c*Real.cos (y/2)+d*Real.sin (y/2))*Real.cos (f y/2)) := funext hrel
  change HasDerivAt (fun y => (a*Real.cos (y/2)+b*Real.sin (y/2))*Real.sin (f y/2)) _ x at hl
  rw [he] at hl
  have hd := hl.unique hr
  dsimp only [id, Pi.add_apply] at hd
  have hd' : r*deriv f x=
      (-c*Real.sin (x/2)+d*Real.cos (x/2))*Real.cos (f x/2)-
      (-a*Real.sin (x/2)+b*Real.cos (x/2))*Real.sin (f x/2) := by
    dsimp only [r]
    linear_combination 2*hd
  have hrd : r^2*deriv f x=1 := by
    calc
      _ = r*(r*deriv f x) := by ring
      _ = (-c*Real.sin (x/2)+d*Real.cos (x/2))*(r*Real.cos (f x/2))-
          (-a*Real.sin (x/2)+b*Real.cos (x/2))*(r*Real.sin (f x/2)) := by rw [hd']; ring
      _ = (a*d-b*c)*(Real.cos (x/2)^2+Real.sin (x/2)^2) := by rw [hr1,hr2]; ring
      _ = 1 := by rw [hdet,cos_sq_add_sin_sq]; ring
  nlinarith [sq_nonneg r]

 

def dot (M : SL(2,ℝ)) (x : ℝ) : ℝ :=
  (M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2))*Real.cos (x/2)+
  (M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2))*Real.sin (x/2)
def cross (M : SL(2,ℝ)) (x : ℝ) : ℝ :=
  (M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2))*Real.cos (x/2)-
  (M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2))*Real.sin (x/2)
def positiveLiftFun (M : SL(2,ℝ)) (x : ℝ) : ℝ :=
  x+2*Real.arctan (cross M x/dot M x)
lemma positiveLiftFun_rel (M : SL(2,ℝ)) (hp : ∀ x, 0 < dot M x) (x : ℝ) :
    Rel M x (positiveLiftFun M x) := by
  have ht : Real.sin (Real.arctan (cross M x/dot M x))=
      (cross M x/dot M x)*Real.cos (Real.arctan (cross M x/dot M x)) := by
    rw [Real.sin_arctan,Real.cos_arctan]; ring
  unfold Rel positiveLiftFun
  rw [show (x+2*Real.arctan (cross M x/dot M x))/2=
      x/2+Real.arctan (cross M x/dot M x) by ring,Real.sin_add,Real.cos_add,ht]
  have hd : dot M x ≠ 0 := (hp x).ne'
  field_simp
  dsimp only [dot,cross]
  ring
lemma dot_smooth (M : SL(2,ℝ)) : ContDiff ℝ ∞ (dot M) := by
  have hc : ContDiff ℝ ∞ (fun x:ℝ => Real.cos (x/2)) := (contDiff_id.div_const 2).cos
  have hs : ContDiff ℝ ∞ (fun x:ℝ => Real.sin (x/2)) := (contDiff_id.div_const 2).sin
  exact (((contDiff_const.mul hc).add (contDiff_const.mul hs)).mul hc).add
    (((contDiff_const.mul hc).add (contDiff_const.mul hs)).mul hs)
lemma cross_smooth (M : SL(2,ℝ)) : ContDiff ℝ ∞ (cross M) := by
  have hc : ContDiff ℝ ∞ (fun x:ℝ => Real.cos (x/2)) := (contDiff_id.div_const 2).cos
  have hs : ContDiff ℝ ∞ (fun x:ℝ => Real.sin (x/2)) := (contDiff_id.div_const 2).sin
  exact (((contDiff_const.mul hc).add (contDiff_const.mul hs)).mul hc).sub
    (((contDiff_const.mul hc).add (contDiff_const.mul hs)).mul hs)
lemma positiveLiftFun_smooth (M : SL(2,ℝ)) (hp : ∀ x, 0 < dot M x) :
    ContDiff ℝ ∞ (positiveLiftFun M) :=
  contDiff_id.add (contDiff_const.mul (((cross_smooth M).div (dot_smooth M) (fun x => (hp x).ne')).arctan))
lemma positiveLiftFun_period (M : SL(2,ℝ)) (x : ℝ) :
    positiveLiftFun M (x+2*Real.pi)=positiveLiftFun M x+2*Real.pi := by
  have hd : dot M (x+2*Real.pi)=dot M x := by
    dsimp only [dot]
    rw [show (x+2*Real.pi)/2=x/2+Real.pi by ring,Real.cos_add_pi,Real.sin_add_pi]
    ring
  have hc : cross M (x+2*Real.pi)=cross M x := by
    dsimp only [cross]
    rw [show (x+2*Real.pi)/2=x/2+Real.pi by ring,Real.cos_add_pi,Real.sin_add_pi]
    ring
  simp only [positiveLiftFun,hd,hc]; ring
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusFullGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups ContDiff
namespace StronglyRationalVOA.CircleMobiusGeometry
 
def polarPhase (M : SL(2,ℝ)) : ℂ :=
  ((M 0 0+M 1 1:ℝ):ℂ)+((M 1 0-M 0 1:ℝ):ℂ)*Complex.I
lemma polarPhase_ne_zero (M : SL(2,ℝ)) : polarPhase M ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [polarPhase] at hr hi
  have hd := det M
  have he : M 1 1 = -M 0 0 := by linarith
  have hf : M 1 0 = M 0 1 := by linarith
  rw [he,hf] at hd
  nlinarith [sq_nonneg (M 0 0),sq_nonneg (M 0 1)]
def polarAngle (M : SL(2,ℝ)) : ℝ := 2*(polarPhase M).arg
lemma polar_cos (M : SL(2,ℝ)) :
    Real.cos (polarAngle M/2)=(M 0 0+M 1 1)/‖polarPhase M‖ := by
  rw [polarAngle,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),Complex.cos_arg (polarPhase_ne_zero M)]
  simp [polarPhase]
lemma polar_sin (M : SL(2,ℝ)) :
    Real.sin (polarAngle M/2)=(M 1 0-M 0 1)/‖polarPhase M‖ := by
  rw [polarAngle,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),Complex.sin_arg]
  simp [polarPhase]
lemma polar_dot_identity (M : SL(2,ℝ)) (x : ℝ) :
    ‖polarPhase M‖*dot ((rotationMatrix (polarAngle M))⁻¹*M) x=
      (M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2))^2+
      (M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2))^2+1 := by
  have hn : ‖polarPhase M‖ ≠ 0 := norm_ne_zero_iff.mpr (polarPhase_ne_zero M)
  have he : ‖polarPhase M‖*dot ((rotationMatrix (polarAngle M))⁻¹*M) x=
      (M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2))^2+
      (M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2))^2+
      (M 0 0*M 1 1-M 0 1*M 1 0)*(Real.cos (x/2)^2+Real.sin (x/2)^2) := by
    have h00 : ((rotationMatrix (polarAngle M))⁻¹*M) 0 0 =
        Real.cos (polarAngle M/2)*M 0 0+Real.sin (polarAngle M/2)*M 1 0 := by
      change (Matrix.adjugate !![Real.cos (polarAngle M/2),-Real.sin (polarAngle M/2);
        Real.sin (polarAngle M/2),Real.cos (polarAngle M/2)] * (M : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 = _
      simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
    have h01 : ((rotationMatrix (polarAngle M))⁻¹*M) 0 1 =
        Real.cos (polarAngle M/2)*M 0 1+Real.sin (polarAngle M/2)*M 1 1 := by
      change (Matrix.adjugate !![Real.cos (polarAngle M/2),-Real.sin (polarAngle M/2);
        Real.sin (polarAngle M/2),Real.cos (polarAngle M/2)] * (M : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 = _
      simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
    have h10 : ((rotationMatrix (polarAngle M))⁻¹*M) 1 0 =
        -Real.sin (polarAngle M/2)*M 0 0+Real.cos (polarAngle M/2)*M 1 0 := by
      change (Matrix.adjugate !![Real.cos (polarAngle M/2),-Real.sin (polarAngle M/2);
        Real.sin (polarAngle M/2),Real.cos (polarAngle M/2)] * (M : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 = _
      simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
    have h11 : ((rotationMatrix (polarAngle M))⁻¹*M) 1 1 =
        -Real.sin (polarAngle M/2)*M 0 1+Real.cos (polarAngle M/2)*M 1 1 := by
      change (Matrix.adjugate !![Real.cos (polarAngle M/2),-Real.sin (polarAngle M/2);
        Real.sin (polarAngle M/2),Real.cos (polarAngle M/2)] * (M : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 = _
      simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
    simp only [dot,h00,h01,h10,h11,polar_cos,polar_sin]
    field_simp [hn]
    ring
  rw [he,det,cos_sq_add_sin_sq]
  ring
lemma polar_dot_positive (M : SL(2,ℝ)) :
    ∀ x, 0 < dot ((rotationMatrix (polarAngle M))⁻¹*M) x := by
  intro x
  have h : 0 < ‖polarPhase M‖*dot ((rotationMatrix (polarAngle M))⁻¹*M) x := by
    rw [polar_dot_identity]
    positivity
  exact pos_of_mul_pos_right h (norm_nonneg _)


end StronglyRationalVOA.CircleMobiusGeometry

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
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma density_second (M : SL(2,ℝ)) (x : ℝ) :
    deriv (deriv (density M)) x= -cosine M*Real.cos x-sine M*Real.sin x := by
  rw [show deriv (density M)=(fun x => -cosine M*Real.sin x+sine M*Real.cos x) from
    funext (density_derivative M)]
  convert (((Real.hasDerivAt_sin x).const_mul (-cosine M)).add
    ((Real.hasDerivAt_cos x).const_mul (sine M))).deriv using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring
lemma density_third (M : SL(2,ℝ)) (x : ℝ) :
    iteratedDeriv 3 (density M) x= -deriv (density M) x := by
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [show deriv (deriv (density M))=(fun x => -cosine M*Real.cos x-sine M*Real.sin x) from
    funext (density_second M)]
  rw [density_derivative]
  convert (((Real.hasDerivAt_cos x).const_mul (-cosine M)).sub
    ((Real.hasDerivAt_sin x).const_mul (sine M))).deriv using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology MatrixGroups
namespace StronglyRationalVOA
 
def phaseUnitary {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) (hc : ‖c‖=1) : H ≃ₗᵢ[ℂ] H where
  toLinearEquiv := LinearEquiv.smulOfNeZero ℂ H c (by intro h; simp [h] at hc)
  norm_map' x := by simp only [LinearEquiv.smulOfNeZero_apply,norm_smul,hc,one_mul]
lemma projective_eq_of_phase {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E F : H ≃ₗᵢ[ℂ] H) {c : ℂ} (hc : ‖c‖=1) (h : ∀ x,F x=c • E x) :
    (QuotientGroup.mk E : ProjectiveUnitaryGroup H)=QuotientGroup.mk F := by
  apply QuotientGroup.eq.mpr
  refine ⟨c,hc,?_⟩
  intro x
  change E.symm (F x)=c • x
  rw [h,map_smul,E.symm_apply_apply]
lemma projective_eq_vacuum_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Ω : H) (hΩ : Ω ≠ 0) (E F : H ≃ₗᵢ[ℂ] H)
    (h : (QuotientGroup.mk E : ProjectiveUnitaryGroup H)=QuotientGroup.mk F)
    (he : E Ω=Ω) (hf : F Ω=Ω) : E=F := by
  obtain ⟨c,_,hc⟩ := QuotientGroup.eq.mp h
  have hEF (x : H) : F x=c • E x := by
    have H := congrArg E (hc x)
    change E (E.symm (F x))=E (c • x) at H
    simpa only [E.apply_symm_apply,map_smul] using H
  have hc1 : c=1 := by
    have hh := hEF Ω
    rw [he,hf] at hh
    exact (smul_left_injective ℂ hΩ) (hh.symm.trans (one_smul ℂ Ω).symm)
  ext x
  rw [hEF,hc1,one_smul]
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusStandardAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry
 
lemma rel_circle_unique (M : SL(2,ℝ)) {x y z : ℝ} (hy : Rel M x y) (hz : Rel M x z) :
    (y : AddCircle (2*Real.pi))=(z : AddCircle (2*Real.pi)) := by
  let p := M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2)
  let q := M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2)
  let r := p*Real.cos (y/2)+q*Real.sin (y/2)
  obtain ⟨h1,h2⟩ := collinear_unit (cos_sq_add_sin_sq (y/2)) hy
  change r*Real.cos (y/2)=p at h1
  change r*Real.sin (y/2)=q at h2
  have hnon : p ≠ 0 ∨ q ≠ 0 := by
    by_contra h
    push Not at h
    have hc : Real.cos (x/2)=0 := by
      have hh := det M
      dsimp [p,q] at h
      linear_combination M 1 1*h.1-M 0 1*h.2-Real.cos (x/2)*hh
    have hs : Real.sin (x/2)=0 := by
      have hh := det M
      dsimp [p,q] at h
      linear_combination -M 1 0*h.1+M 0 0*h.2-Real.sin (x/2)*hh
    have hh := cos_sq_add_sin_sq (x/2)
    rw [hc,hs] at hh
    norm_num at hh
  have hr : r ≠ 0 := by
    intro h
    rw [h,zero_mul] at h1 h2
    exact hnon.elim (fun hp => hp h1.symm) (fun hq => hq h2.symm)
  have hsin : Real.sin ((z-y)/2)=0 := by
    apply (mul_eq_zero.mp (show r*Real.sin ((z-y)/2)=0 from ?_)).resolve_left hr
    rw [show (z-y)/2=z/2-y/2 by ring,Real.sin_sub]
    change p*Real.sin (z/2)=q*Real.cos (z/2) at hz
    linear_combination hz+Real.sin (z/2)*h1-Real.cos (z/2)*h2
  obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp hsin
  apply sub_eq_zero.mp
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨-n,?_⟩
  simp only [zsmul_eq_mul,Int.cast_neg]
  linarith
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MobiusStandardTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped MatrixGroups Topology ContDiff
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma constant_continuous : Continuous constant := by
  change Continuous (fun M : SL(2,ℝ) => (M 0 0^2+M 0 1^2+M 1 0^2+M 1 1^2)/2)
  fun_prop
lemma cosine_continuous : Continuous cosine := by
  change Continuous (fun M : SL(2,ℝ) => (M 1 0^2+M 1 1^2-M 0 0^2-M 0 1^2)/2)
  fun_prop
lemma sine_continuous : Continuous sine := by
  change Continuous (fun M : SL(2,ℝ) => -(M 0 0*M 1 0+M 0 1*M 1 1))
  fun_prop
lemma density_smooth_standard (M : SL(2,ℝ)) : ContDiff ℝ ∞ (density M) := by
  simp only [funext (density_trigonometric M)]
  exact (contDiff_const.add (contDiff_const.mul Real.contDiff_cos)).add
    (contDiff_const.mul Real.contDiff_sin)
lemma density_derivative_continuous (k : ℕ) :
    Continuous (fun p : SL(2,ℝ) × ℝ => iteratedDeriv k (density p.1) p.2) := by
  have he (M : SL(2,ℝ)) (x : ℝ) : iteratedDeriv k (density M) x=
      (if k=0 then constant M else 0)+cosine M*iteratedDeriv k Real.cos x+
        sine M*iteratedDeriv k Real.sin x := by
    rw [funext (density_trigonometric M)]
    change iteratedDeriv k ((fun x => constant M+cosine M*Real.cos x) +
      (fun x => sine M*Real.sin x)) x = _
    rw [iteratedDeriv_add (n := k) (x := x) (f := fun x => constant M+cosine M*Real.cos x) (g := fun x => sine M*Real.sin x) ((contDiff_const.add (contDiff_const.mul Real.contDiff_cos)).contDiffAt)
      (contDiff_const.mul Real.contDiff_sin).contDiffAt]
    change iteratedDeriv k ((fun _ => constant M)+(fun x => cosine M*Real.cos x)) x+
      iteratedDeriv k (fun x => sine M*Real.sin x) x = _
    rw [iteratedDeriv_add (n := k) (x := x) (f := fun _ => constant M) (g := fun x => cosine M*Real.cos x) contDiff_const.contDiffAt (contDiff_const.mul Real.contDiff_cos).contDiffAt]
    rw [iteratedDeriv_const_mul _ Real.contDiff_cos.contDiffAt,
      iteratedDeriv_const_mul _ Real.contDiff_sin.contDiffAt,iteratedDeriv_const]
  simp only [he]
  exact (((constant_continuous.comp continuous_fst).if_const _ continuous_const).add
    ((cosine_continuous.comp continuous_fst).mul
      (((Real.contDiff_cos (n := ∞)).continuous_iteratedDeriv k (by exact_mod_cast (le_top : (k:ℕ∞)≤⊤))).comp continuous_snd))).add
    ((sine_continuous.comp continuous_fst).mul
      (((Real.contDiff_sin (n := ∞)).continuous_iteratedDeriv k (by exact_mod_cast (le_top : (k:ℕ∞)≤⊤))).comp continuous_snd))



def positiveMatrices : Set (SL(2,ℝ)) := {M | ∀ x, 0 < dot M x}
lemma dot_continuous : Continuous (fun p : SL(2,ℝ) × ℝ => dot p.1 p.2) := by
  dsimp only [dot]
  fun_prop
lemma dot_periodic (M : SL(2,ℝ)) : Function.Periodic (dot M) (2*Real.pi) := by
  intro x
  dsimp only [dot]
  rw [show (x+2*Real.pi)/2=x/2+Real.pi by ring,Real.cos_add_pi,Real.sin_add_pi]
  ring
lemma dot_one (x : ℝ) : dot (1:SL(2,ℝ)) x=1 := by
  simp only [dot,Matrix.SpecialLinearGroup.coe_one,Matrix.one_apply]
  norm_num only [Fin.zero_eta,Fin.isValue,show (0:Fin 2) ≠ 1 by decide,
    show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false,one_mul,zero_mul,add_zero,zero_add]
  nlinarith [cos_sq_add_sin_sq (x/2)]
lemma one_mem_positiveMatrices : (1:SL(2,ℝ)) ∈ positiveMatrices := by
  intro x; rw [dot_one]; norm_num
lemma positiveMatrices_mem_nhds_one : positiveMatrices ∈ 𝓝 (1:SL(2,ℝ)) := by
  have hh : ∀ᶠ M : SL(2,ℝ) in 𝓝 1, ∀ x ∈ Icc (0:ℝ) (2*Real.pi), 0 < dot M x := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro x _
    apply (isOpen_lt continuous_const dot_continuous).mem_nhds
    simp [dot_one]
  filter_upwards [hh] with M hM
  intro x
  let n : ℤ := ⌊x/(2*Real.pi)⌋
  have hp : 0 < 2*Real.pi := by positivity
  have hlow := mul_le_mul_of_nonneg_right (Int.floor_le (x/(2*Real.pi))) hp.le
  have hupp := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x/(2*Real.pi))) hp
  rw [div_mul_cancel₀ _ hp.ne'] at hlow hupp
  have hin : x-(n:ℝ)*(2*Real.pi) ∈ Icc (0:ℝ) (2*Real.pi) := by
    change (n:ℝ)*(2*Real.pi) ≤ x at hlow
    change x < ((n:ℝ)+1)*(2*Real.pi) at hupp
    constructor <;> linarith
  have he := (dot_periodic M).sub_int_mul_eq (x := x) n
  rw [← he]
  exact hM _ hin
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_NetAxioms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Topology MatrixGroups
namespace StronglyRationalVOA


def projectiveConjugation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : ProjectiveUnitaryGroup H → ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)) :=
  Quotient.lift (fun E : H ≃ₗᵢ[ℂ] H => E.conjStarAlgEquiv) (by
    intro E F h
    exact projective_equality_conjugation E F (Quotient.sound h))
@[simp] lemma projectiveConjugation_mk {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (E : H ≃ₗᵢ[ℂ] H) :
    projectiveConjugation (QuotientGroup.mk E)=E.conjStarAlgEquiv := rfl

 

def globalObservableAlgebra {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : ProperCircleArc → VonNeumannAlgebra H) :
    Subalgebra ℂ (H →L[ℂ] H) :=
  Algebra.adjoin ℂ (⋃ I, (N I : Set (H →L[ℂ] H)))
 
def globalCyclicSpace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : ProperCircleArc → VonNeumannAlgebra H) (Ω : H) : Submodule ℂ H :=
  (Submodule.span ℂ {x | ∃ B ∈ globalObservableAlgebra N, x=B Ω}).topologicalClosure



end StronglyRationalVOA

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
namespace StronglyRationalVOA
lemma globalCyclicSpace_contains {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : ProperCircleArc → VonNeumannAlgebra H) (Ω : H) : Ω ∈ globalCyclicSpace N Ω := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨1,one_mem _,rfl⟩
lemma globalCyclicSpace_invariant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : ProperCircleArc → VonNeumannAlgebra H) (Ω : H)
    (I : ProperCircleArc) (B : H →L[ℂ] H) (hB : B ∈ N I) :
    ∀ x ∈ globalCyclicSpace N Ω, B x ∈ globalCyclicSpace N Ω := by
  let S := Submodule.span ℂ {x | ∃ C ∈ globalObservableAlgebra N, x=C Ω}
  have hBs : B ∈ globalObservableAlgebra N := Algebra.subset_adjoin (mem_iUnion.mpr ⟨I,hB⟩)
  have hinv : Set.MapsTo B (S : Set H) (S : Set H) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨C,hC,rfl⟩ := hx
      apply Submodule.subset_span
      exact ⟨B*C,mul_mem hBs hC,rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      change B (x+y) ∈ S
      rw [map_add]
      exact S.add_mem ihx ihy
    | smul c x hx ih =>
      change B (c • x) ∈ S
      rw [map_smul]
      exact S.smul_mem c ih
  exact hinv.closure B.continuous
end StronglyRationalVOA

end

end OAI
end


