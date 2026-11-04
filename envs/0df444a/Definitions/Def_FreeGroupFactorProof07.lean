-- Prove2me | Definitions.Def_FreeGroupFactorProof07
-- name    : FreeGroupFactorProof07
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T01:10:17.81763+00:00
-- url     : https://prove2.me/theorems/9df6c0ce-dfd5-498e-b0dc-2215e0ad7dca
-- title:
--   Free group factors: supporting development, part 7
-- statement:
--   Part 7 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof06

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification WeightedCornerIndex

theorem kindCreator_annihilator (u v : ℝ) (k : Kind) (hk : k.valid) :
    kindCreator u v k∈oldAnnihilators u v := by
  intro a
  cases k with
  | fresh n r s =>
    exact normalizedCreation_annihilate u v (0:ℕ) 1 (n+2)
      (by omega) (by omega) (by omega) r s (filledOfCorner a)
  | residual r s => exact normalizedResidual_annihilate u v (0:ℕ) 1 (by omega) r s hk (filledOfCorner a)
  | diagonal r => exact normalizedDiagonal_annihilate u v (0:ℕ) 1 0 (by omega) (by omega) r (filledOfCorner a)

theorem rawReservoir_annihilator (u v : ℝ) (i : WeightedCornerIndex.Index) (n : ℕ) :
    rawReservoir u v i n∈oldAnnihilators u v := by
  intro a
  exact normalizedCreation_annihilate u v (0:ℕ) 1 (reservoirCode (i,n)+2)
    (by omega) (by omega) (by omega) false false (filledOfCorner a)

theorem cornerAbsorption_annihilator (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (i : WeightedCornerIndex.Index) (n : ℕ) :
    (cornerAbsorption u v hv hvu).output i n∈oldAnnihilators u v :=
  (cornerAbsorption u v hv hvu).output_mem (oldAnnihilators u v) (oldAnnihilators_sandwich u v)
    (fun i => kindCreator_annihilator u v _ (description_valid i)) (rawReservoir_annihilator u v) i n
end FreeGroupFactorMain.WeightedFock

namespace FreeGroupFactorMain.Amplification
variable {A : Type u_1} [CStarAlgebra A]

def cornerEqualityEquiv (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p=q) :
    Corner p hp ≃⋆ₐ[ℂ] Corner q hq := by
  subst q
  exact StarAlgEquiv.refl ℂ (Corner p hp)

theorem cornerEqualityEquiv_val (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p=q)
    (x : Corner p hp) : (cornerEqualityEquiv p q hp hq h x : A)=(x:A) := by
  subst q
  rfl

variable {E : Type u_2} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (p : E →L[ℂ] E) (hp : IsStarProjection p) [CompleteSpace p.range]

include hp in
theorem projectionRange_starProjection : p.range.starProjection=p :=
  (isStarProjection_iff_eq_starProjection_range.mp hp).choose_spec.symm

def projectionRepresentation : Corner p hp ≃⋆ₐ[ℂ] (p.range →L[ℂ] p.range) :=
  (cornerEqualityEquiv p p.range.starProjection hp isStarProjection_starProjection
    (projectionRange_starProjection p hp).symm).trans (cornerRepresentation p.range)

theorem projectionRepresentation_apply (x : Corner p hp) (ξ : p.range) :
    (projectionRepresentation p hp x ξ : E)=(x:E →L[ℂ] E) ξ := by
  change (cornerRestrict p.range
    (cornerEqualityEquiv p p.range.starProjection hp isStarProjection_starProjection
      (projectionRange_starProjection p hp).symm x) ξ : E) = _
  rw [cornerRestrict_apply,cornerEqualityEquiv_val]
end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification Filter Topology
open scoped ENNReal
variable {ι : Type u_3} [DecidableEq ι]

abbrev PRange (ι : Type u_4) [DecidableEq ι] := (P : Operator ι).range
instance pRange_complete : CompleteSpace (PRange ι) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (projection_P (ι := ι)).isIdempotentElem).completeSpace_coe

def pRoot : PRange ι := ⟨lp.single 2 ([],true) 1,⟨lp.single 2 ([],true) 1,P_nil_true 1⟩⟩

theorem pRoot_norm : ‖(pRoot : PRange ι)‖=1 := by
  change ‖lp.single (E := fun _ : Path ι => ℂ) 2 ([],true) 1‖=1
  rw [lp.norm_single] <;> norm_num

instance pRange_nontrivial : Nontrivial (PRange ι) := by
  apply nontrivial_of_ne (pRoot : PRange ι) 0
  intro h
  have hh := pRoot_norm (ι := ι)
  rw [h,norm_zero] at hh
  exact zero_ne_one hh

abbrev pRepresentation : PCorner ι ≃⋆ₐ[ℂ] (PRange ι →L[ℂ] PRange ι) :=
  projectionRepresentation P projection_P

theorem pRepresentation_apply (x : PCorner ι) (ξ : PRange ι) :
    (pRepresentation x ξ : H ι)=(x:Operator ι) ξ :=
  projectionRepresentation_apply P projection_P x ξ

def pProject : H ι →L[ℂ] PRange ι := (P : Operator ι).range.orthogonalProjectionOnto

theorem pProject_val (ξ : H ι) : (pProject ξ : H ι)=P ξ := by
  change (P : Operator ι).range.starProjection ξ=P ξ
  rw [projectionRange_starProjection P projection_P]

def oldBaseCorner (u v : ℝ) (i j : ι) : PCorner ι :=
  ⟨oldBaseGenerator u v i j,oldBaseGenerator_left u v i j,oldBaseGenerator_right u v i j⟩

def oldBaseOp (u v : ℝ) (i j : ι) : PRange ι →L[ℂ] PRange ι := pRepresentation (oldBaseCorner u v i j)

theorem oldBaseCorner_selfAdjoint (u v : ℝ) (i j : ι) : IsSelfAdjoint (oldBaseCorner u v i j) :=
  Subtype.ext (oldBaseGenerator_selfAdjoint u v i j).star_eq

theorem oldBaseOp_selfAdjoint (u v : ℝ) (i j : ι) : IsSelfAdjoint (oldBaseOp u v i j) :=
by
  change star (pRepresentation (oldBaseCorner u v i j))=pRepresentation (oldBaseCorner u v i j)
  exact ((pRepresentation (ι := ι)).map_star' (oldBaseCorner u v i j)).symm.trans
    (congrArg (fun x : PCorner ι => pRepresentation x) (oldBaseCorner_selfAdjoint u v i j).star_eq)

theorem oldBaseOp_eigen_root_zero (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι)
    (z : ℂ) (η : PRange ι) (he : oldBaseOp u v i j η=z • η) : inner ℂ (pRoot : PRange ι) η=0 := by
  have hh := congrArg (fun x : PRange ι => (x:H ι)) he
  rw [oldBaseOp,pRepresentation_apply] at hh
  have hz := oldBaseGenerator_eigen_root_zero u v hv hvu i j z (η:H ι) hh
  change inner ℂ (lp.single 2 ([],true) 1) (η:H ι)=0
  simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] using hz
end

open FreeFock Amplification
variable {ι : Type u_5} [DecidableEq ι]

def pSandwich (B : Operator ι) : PCorner ι :=
  ⟨P*B*P,by
    constructor
    · rw [← mul_assoc,← mul_assoc,projection_P.isIdempotentElem.eq]
    · rw [mul_assoc,mul_assoc,projection_P.isIdempotentElem.eq,mul_assoc]⟩

theorem pRoot_vacuum (u v : ℝ) : (P : Operator ι) (vacuum u v)=(u:ℂ) • ((pRoot : PRange ι):H ι) := by
  simp only [vacuum,map_add,map_smul,P_nil_true,P_nil_false,smul_zero,add_zero,pRoot]

theorem centralizer_bicommutant {E : Type u_6} [Ring E] [StarRing E] [Algebra ℂ E] [StarModule ℂ E]
    (S : Set E) (B : StarSubalgebra.centralizer ℂ S) :
    (B:E)∈StarSubalgebra.centralizer ℂ (Bicommutant.algebra S : Set E) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  exact ⟨((StarSubalgebra.mem_centralizer_iff ℂ).mp hT B B.property).1.symm,
    ((StarSubalgebra.mem_centralizer_iff ℂ).mp (star_mem hT) B B.property).1.symm⟩

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15

open MeasureTheory Set CompactlySupported
open scoped ENNReal
namespace FreeGroupFactorMain.CyclicSpectral

section
variable {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance fgfLocalInst_46_0 : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
abbrev Space := spectrum ℝ A

instance compactSpace : CompactSpace (Space A) := isCompact_iff_compactSpace.mp (spectrum.isCompact A)

def functional : C_c(Space A,ℝ) →ₚ[ℝ] ℝ where
  toFun f := (inner ℂ ξ (cfcHom hA f.toContinuousMap ξ)).re
  map_add' f g := by
    change (inner ℂ ξ (cfcHom hA (f.toContinuousMap+g.toContinuousMap) ξ)).re=_
    rw [map_add,add_apply,inner_add_right,Complex.add_re]
  map_smul' c f := by
    change (inner ℂ ξ (cfcHom hA (c • f.toContinuousMap) ξ)).re=_
    rw [map_smul,_root_.smul_apply]
    change inner ℝ ξ (c • cfcHom hA f.toContinuousMap ξ)=c * inner ℝ ξ (cfcHom hA f.toContinuousMap ξ)
    exact real_inner_smul_right _ _ _
  monotone' f g hfg := by
    have hn : 0 ≤ cfcHom hA (g.toContinuousMap-f.toContinuousMap) :=
      (cfcHom_nonneg_iff hA).mpr (sub_nonneg.mpr hfg)
    have hi := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hn).re_inner_nonneg_right ξ
    rw [map_sub,sub_apply,inner_sub_right] at hi
    change 0 ≤ (inner ℂ ξ (cfcHom hA g.toContinuousMap ξ)).re-
      (inner ℂ ξ (cfcHom hA f.toContinuousMap ξ)).re at hi
    exact sub_nonneg.mp hi

def measure : Measure (Space A) := RealRMK.rieszMeasure (functional A hA ξ)

instance measure_regular : (measure A hA ξ).Regular := inferInstanceAs
  (RealRMK.rieszMeasure (functional A hA ξ)).Regular

instance measure_finite : IsFiniteMeasure (measure A hA ξ) := inferInstance

 theorem integral_continuous (f : C(Space A,ℝ)) :
    ∫ x, f x ∂measure A hA ξ=(inner ℂ ξ (cfcHom hA f ξ)).re := by
  exact RealRMK.integral_rieszMeasure (functional A hA ξ)
    (CompactlySupportedContinuousMap.continuousMapEquiv f)

 theorem measure_univ : measure A hA ξ univ=ENNReal.ofReal (‖ξ‖^2) := by
  have hi := integral_continuous A hA ξ (1 : C(Space A,ℝ))
  simp only [ContinuousMap.one_apply,integral_const,map_one,one_apply_eq_self] at hi
  have hh : (measure A hA ξ).real univ=‖ξ‖^2 := by
    simpa only [smul_eq_mul,mul_one] using hi.trans (norm_sq_eq_re_inner (𝕜 := ℂ) ξ).symm
  rw [← hh,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]

 theorem integral_sq (f : C(Space A,ℝ)) :
    ∫ x, (f x)^2 ∂measure A hA ξ=‖cfcHom hA f ξ‖^2 := by
  have hi := integral_continuous A hA ξ (f*f)
  have hs : IsSelfAdjoint (cfcHom hA f) := cfcHom_predicate hA f
  calc
    _ = (inner ℂ ξ (cfcHom hA (f*f) ξ)).re := by
      simpa only [ContinuousMap.mul_apply,pow_two] using hi
    _ = (inner ℂ (cfcHom hA f ξ) (cfcHom hA f ξ)).re := by
      rw [map_mul,mul_apply_eq_comp]
      have he : inner ℂ ξ (cfcHom hA f (cfcHom hA f ξ))=
          inner ℂ (cfcHom hA f ξ) (cfcHom hA f ξ) := by
        calc
          _ = inner ℂ ξ (star (cfcHom hA f) (cfcHom hA f ξ)) := by rw [hs.star_eq]
          _ = _ := by rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      exact congrArg Complex.re he
    _ = _ := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

 theorem probability (hξ : ‖ξ‖=1) : IsProbabilityMeasure (measure A hA ξ) := by
  constructor
  rw [measure_univ,hξ,one_pow,ENNReal.ofReal_one]

end
section
open MeasureTheory
variable {H : Type u_2} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

def complexHom : C(Space A,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  let e := SpectrumRestricts.homeomorph (f := ⟨Complex.re,Complex.continuous_re⟩) hA.spectrumRestricts
  (cfcHom hA.isStarNormal).comp (ContinuousMap.compStarAlgHom' ℂ ℂ ⟨e,e.continuous⟩)

def complexLift (f : C(Space A,ℝ)) : C(Space A,ℂ) :=
  ⟨fun x => (f x:ℂ), Complex.continuous_ofReal.comp f.continuous⟩

 theorem complexHom_real (f : C(Space A,ℝ)) :
    complexHom A hA (complexLift A f)=cfcHom hA f := by
  rw [SpectrumRestricts.cfcHom_eq_restrict ⟨Complex.re,Complex.continuous_re⟩ hA hA.isStarNormal hA.spectrumRestricts]
  rfl

 theorem real_inner_im (f : C(Space A,ℝ)) :
    (inner ℂ ξ (cfcHom hA f ξ)).im=0 := by
  have hs := cfcHom_predicate hA f
  have he : star (inner ℂ ξ (cfcHom hA f ξ))=inner ℂ ξ (cfcHom hA f ξ) := by
    change (starRingEnd ℂ) (inner ℂ ξ (cfcHom hA f ξ))=_
    rw [inner_conj_symm]
    calc
      _ = inner ℂ ξ (star (cfcHom hA f) ξ) := by
        rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      _ = _ := by rw [hs.star_eq]
  have hh := congrArg Complex.im he
  simp only [Complex.star_def,Complex.conj_im] at hh
  linarith

 theorem integral_complexLift (f : C(Space A,ℝ)) :
    ∫ x, complexLift A f x ∂measure A hA ξ=inner ℂ ξ (complexHom A hA (complexLift A f) ξ) := by
  rw [complexHom_real]
  change (∫ x, (f x:ℂ) ∂measure A hA ξ)=_
  rw [integral_complex_ofReal,integral_continuous]
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im,real_inner_im]

 theorem integral_complex (f : C(Space A,ℂ)) :
    ∫ x, f x ∂measure A hA ξ=inner ℂ ξ (complexHom A hA f ξ) := by
  let fr : C(Space A,ℝ) := ⟨fun x => (f x).re,Complex.continuous_re.comp f.continuous⟩
  let fi : C(Space A,ℝ) := ⟨fun x => (f x).im,Complex.continuous_im.comp f.continuous⟩
  have hf : f=complexLift A fr+Complex.I • complexLift A fi := by
    ext x
    change f x=(f x).re+(Complex.I:ℂ)*(f x).im
    simpa only [mul_comm Complex.I] using (Complex.re_add_im (f x)).symm
  rw [hf,map_add,map_smul,add_apply,_root_.smul_apply,inner_add_right,inner_smul_right]
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply]
  have hir : Integrable (fun x => complexLift A fr x) (measure A hA ξ) :=
    (complexLift A fr).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hii : Integrable (fun x => Complex.I • complexLift A fi x) (measure A hA ξ) :=
    (((complexLift A fi).continuous.const_smul Complex.I).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [integral_add hir hii,integral_smul,integral_complexLift,integral_complexLift]
  rfl

end
section
variable {H : Type u_3} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
 theorem complexHom_mem (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : IsClosed (S : Set (H →L[ℂ] H))) (hAS : A ∈ S) (f : C(Space A,ℂ)) :
    complexHom A hA f ∈ S := by
  apply StarSubalgebra.topologicalClosure_minimal (t := S) (by simpa) hS
    (cfcHom_mem_elemental hA.isStarNormal _)
end
open MeasureTheory
variable {H : Type u_4} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

def complexEvaluate : C(Space A,ℂ) →ₗ[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H ξ).toLinearMap.comp (complexHom A hA).toAlgHom.toLinearMap

 theorem complexEvaluate_inner (f g : C(Space A,ℂ)) :
    inner ℂ (complexEvaluate A hA ξ f) (complexEvaluate A hA ξ g)=
      inner ℂ (ContinuousMap.toLp 2 (measure A hA ξ) ℂ f)
        (ContinuousMap.toLp 2 (measure A hA ξ) ℂ g) := by
  rw [ContinuousMap.inner_toLp]
  have hi := integral_complex A hA ξ (star f*g)
  rw [map_mul,map_star] at hi
  change (∫ x, star (f x)*g x ∂measure A hA ξ)=
    inner ℂ ξ (star (complexHom A hA f) (complexHom A hA g ξ)) at hi
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at hi
  refine hi.symm.trans ?_
  apply integral_congr_ae
  filter_upwards [] with x
  exact mul_comm _ _

 theorem complexEvaluate_norm (f : C(Space A,ℂ)) :
    ‖complexEvaluate A hA ξ f‖=‖ContinuousMap.toLp 2 (measure A hA ξ) ℂ f‖ := by
  have he := complexEvaluate_inner A hA ξ f f
  have hr : ‖complexEvaluate A hA ξ f‖^2=‖ContinuousMap.toLp 2 (measure A hA ξ) ℂ f‖^2 := by
    calc
      _ = (inner ℂ (complexEvaluate A hA ξ f) (complexEvaluate A hA ξ f)).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = _ := congrArg Complex.re he
      _ = _ := inner_self_eq_norm_sq (𝕜 := ℂ) _
  nlinarith [norm_nonneg (complexEvaluate A hA ξ f),norm_nonneg (ContinuousMap.toLp 2 (measure A hA ξ) ℂ f)]

def complexRealize : Lp ℂ 2 (measure A hA ξ) →L[ℂ] H :=
  (complexEvaluate A hA ξ).extendOfNorm (ContinuousMap.toLp 2 (measure A hA ξ) ℂ).toLinearMap

 theorem complexRealize_continuous (f : C(Space A,ℂ)) :
    complexRealize A hA ξ (ContinuousMap.toLp 2 (measure A hA ξ) ℂ f)=complexHom A hA f ξ := by
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange ℂ (measure A hA ξ) ℂ (p := 2) (by norm_num)
  · refine ⟨1,fun g => ?_⟩
    change ‖complexEvaluate A hA ξ g‖ ≤ 1 * ‖ContinuousMap.toLp 2 (measure A hA ξ) ℂ g‖
    rw [one_mul,complexEvaluate_norm]

end FreeGroupFactorMain.CyclicSpectral
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal
namespace FreeGroupFactorMain.ProbabilityTransform

section
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

 theorem continuous_cdf : Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (cdf μ).mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [(cdf μ).rightLim_eq]
  apply le_antisymm ((cdf μ).mono.leftLim_le le_rfl)
  have h : ENNReal.ofReal (cdf μ x-leftLim (cdf μ) x)=0 := by
    rw [← (cdf μ).measure_singleton,measure_cdf,measure_singleton]
  exact sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp h)

 theorem level_greatest (r : ℝ) (hr : 0<r) (hr1 : r<1) :
    ∃ x : ℝ, cdf μ x=r ∧ ∀ y, cdf μ y≤r ↔ y≤x := by
  obtain ⟨a,ha⟩ := ((tendsto_cdf_atBot μ).eventually (eventually_lt_nhds hr)).exists
  obtain ⟨b,hb⟩ := ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds hr1)).exists
  have hab : a≤b := le_of_not_gt (fun h => (not_le_of_gt (ha.trans hb)) ((cdf μ).mono h.le))
  have hne : ({x:ℝ | cdf μ x=r}:Set ℝ).Nonempty := by
    obtain ⟨x,_,hxr⟩ := intermediate_value_Icc hab (continuous_cdf μ).continuousOn ⟨ha.le,hb.le⟩
    exact ⟨x,hxr⟩
  have hsub : {x:ℝ | cdf μ x=r} ⊆ Icc a b := by
    intro x hx
    constructor
    · apply le_of_not_gt
      intro h
      have hh := (cdf μ).mono h.le
      rw [hx] at hh
      exact (not_le_of_gt ha) hh
    · exact le_of_not_gt (fun h => (not_le_of_gt hb) ((cdf μ).mono h.le |>.trans_eq hx))
  have hc : IsCompact {x:ℝ | cdf μ x=r} :=
    isCompact_Icc.of_isClosed_subset (isClosed_eq (continuous_cdf μ) continuous_const) hsub
  obtain ⟨x,hx,hmax⟩ := hc.exists_isGreatest hne
  refine ⟨x,hx,fun y => ⟨fun hy => ?_,fun hy => ((cdf μ).mono hy).trans_eq hx⟩⟩
  by_contra h
  have hxy : x≤y := (lt_of_not_ge h).le
  exact h (hmax (le_antisymm hy (hx ▸ (cdf μ).mono hxy)))

 theorem measure_cdf_sublevel (r : ℝ) (hr : 0<r) (hr1 : r<1) :
    μ {x:ℝ | cdf μ x≤r}=ENNReal.ofReal r := by
  obtain ⟨x,hx,he⟩ := level_greatest μ r hr hr1
  have hs : {y:ℝ | cdf μ y≤r}=Iic x := by ext y;exact he y
  rw [hs,← ofReal_cdf,hx]

 theorem measure_cdf_zero : μ {x:ℝ | cdf μ x≤0}=0 := by
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let r : ℝ := min (ε:ℝ) (1/2)
  have hr : 0<r := lt_min (by exact_mod_cast hε) (by norm_num)
  have hr1 : r<1 := (min_le_right _ _).trans_lt (by norm_num)
  rw [zero_add]
  calc
    _ ≤ μ {x:ℝ | cdf μ x≤r} := measure_mono (fun x hx => hx.trans hr.le)
    _ = ENNReal.ofReal r := measure_cdf_sublevel μ r hr hr1
    _ ≤ ENNReal.ofReal (ε:ℝ) := ENNReal.ofReal_le_ofReal (min_le_left _ _)
    _ = (ε:ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

 theorem map_cdf : Measure.map (cdf μ) μ=volume.restrict (Icc (0:ℝ) 1) := by
  apply Measure.ext_of_Iic
  intro r
  rw [Measure.map_apply (continuous_cdf μ).measurable measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  have hs : Iic r ∩ Icc (0:ℝ) 1=Icc 0 (min r 1) := by
    ext x
    simp only [mem_inter_iff,mem_Iic,mem_Icc,le_min_iff]
    tauto
  rw [hs,Real.volume_Icc,sub_zero]
  change μ {x:ℝ | cdf μ x≤r}=ENNReal.ofReal (min r 1)
  by_cases hr : 0<r
  · by_cases hr1 : r<1
    · rw [min_eq_left hr1.le]
      exact measure_cdf_sublevel μ r hr hr1
    · have hr1' : 1≤r := le_of_not_gt hr1
      have huniv : {x:ℝ | cdf μ x≤r}=univ := by
        ext x
        simp only [mem_ofPred_eq,mem_univ,iff_true]
        exact (cdf_le_one μ x).trans hr1'
      rw [huniv,measure_univ,min_eq_right hr1',ENNReal.ofReal_one]
  · have hr' : r≤0 := le_of_not_gt hr
    have hz : μ {x:ℝ | cdf μ x≤r}=0 := by
      apply le_antisymm _ zero_le
      calc
        _ ≤ μ {x:ℝ | cdf μ x≤0} := measure_mono (fun x hx => hx.trans hr')
        _ = 0 := measure_cdf_zero μ
    rw [hz,ENNReal.ofReal_eq_zero.mpr ((min_le_left _ _).trans hr')]

end
section
open MeasureTheory ProbabilityTheory Set
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

def phase (x : ℝ) : ℂ := Complex.exp ((2*Real.pi*Complex.I)*x)

 theorem phase_continuous : Continuous phase := by
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

 theorem phase_star_mul (x : ℝ) : star (phase x)*phase x=1 := by
  change (starRingEnd ℂ) (Complex.exp ((2*Real.pi*Complex.I)*x))*Complex.exp ((2*Real.pi*Complex.I)*x)=1
  rw [← Complex.exp_conj,← Complex.exp_add]
  have he : (starRingEnd ℂ) ((2*Real.pi*Complex.I)*x)+(2*Real.pi*Complex.I)*x=0 := by
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,map_ofNat]
    ring
  rw [he,Complex.exp_zero]

 theorem phase_uniform_moment (n : ℕ) :
    ∫ x:ℝ, phase x^n ∂volume.restrict (Icc (0:ℝ) 1) = if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · simp [hn,Measure.real,Real.volume_Icc]
  · rw [ite_eq_right hn]
    have hrew (x : ℝ) : phase x^n=Complex.exp ((n:ℂ)*(2*Real.pi*Complex.I)*x) := by
      rw [phase,← Complex.exp_nat_mul]
      congr 1
      ring
    simp_rw [hrew]
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    have hc : (n:ℂ)*(2*Real.pi*Complex.I)≠0 := by
      apply mul_ne_zero (by exact_mod_cast hn)
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one,mul_one,Complex.ofReal_zero,mul_zero,Complex.exp_zero]
    have he : Complex.exp ((n:ℂ)*(2*Real.pi*Complex.I))=1 := by
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (n:ℤ)
    rw [he,sub_self,zero_div]

 theorem phase_cdf_moment (n : ℕ) :
    ∫ x:ℝ, phase (cdf μ x)^n ∂μ=if n=0 then 1 else 0 := by
  have hi := integral_map (μ := μ) (continuous_cdf μ).measurable.aemeasurable
    (phase_continuous.pow n).aestronglyMeasurable
  rw [map_cdf μ] at hi
  exact hi.symm.trans (phase_uniform_moment n)

end
section
open MeasureTheory ProbabilityTheory Set Filter
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

 theorem measure_cdf_le (r : ℝ) (hr : 0≤r) (hr1 : r≤1) :
    μ {x:ℝ | cdf μ x≤r}=ENNReal.ofReal r := by
  by_cases h0 : r=0
  · subst r
    simpa using measure_cdf_zero μ
  by_cases h1 : r=1
  · subst r
    have hs : {x:ℝ | cdf μ x≤1}=univ := by
      ext x
      simp [cdf_le_one]
    rw [hs,measure_univ,ENNReal.ofReal_one]
  exact measure_cdf_sublevel μ r (lt_of_le_of_ne hr (Ne.symm h0)) (lt_of_le_of_ne hr1 h1)

 theorem cdf_cut_ae (r : ℝ) : ∀ᵐ x ∂μ, x≤r ↔ cdf μ x≤cdf μ r := by
  have he : (Iic r : Set ℝ)=ᵐ[μ] {x:ℝ | cdf μ x≤cdf μ r} := by
    apply ae_eq_of_subset_of_measure_ge
    · exact fun x hx => (cdf μ).mono hx
    · rw [measure_cdf_le μ _ (cdf_nonneg μ r) (cdf_le_one μ r),ofReal_cdf]
    · exact measurableSet_Iic.nullMeasurableSet
    · exact measure_ne_top _ _
  filter_upwards [he] with x hx
  exact iff_of_eq hx

 theorem cdf_injective_conull :
    ∃ s : Set ℝ, μ sᶜ=0 ∧ Set.InjOn (cdf μ) s := by
  let s : Set ℝ := {x | ∀ q:ℚ, x≤(q:ℝ) ↔ cdf μ x≤cdf μ (q:ℝ)}
  refine ⟨s,?_,?_⟩
  · have he : ∀ᵐ x ∂μ, ∀ q:ℚ, x≤(q:ℝ) ↔ cdf μ x≤cdf μ (q:ℝ) :=
      ae_all_iff.mpr (fun q => cdf_cut_ae μ (q:ℝ))
    exact ae_iff.mp he
  · intro x hx y hy hxy
    apply le_antisymm
    · by_contra h
      obtain ⟨q,hyq,hqx⟩ := exists_rat_btwn (lt_of_not_ge h)
      have hyc := (hy q).mp hyq.le
      rw [← hxy] at hyc
      exact (not_le_of_gt hqx) ((hx q).mpr hyc)
    · by_contra h
      obtain ⟨q,hxq,hqy⟩ := exists_rat_btwn (lt_of_not_ge h)
      have hxc := (hx q).mp hxq.le
      rw [hxy] at hxc
      exact (not_le_of_gt hqy) ((hy q).mpr hxc)

 theorem cdf_between_ae : ∀ᵐ x ∂μ, 0<cdf μ x ∧ cdf μ x<1 := by
  have hpoint (r:ℝ) : μ {x:ℝ | cdf μ x=r}=0 := by
    change μ ((cdf μ) ⁻¹' {r})=0
    rw [← Measure.map_apply (continuous_cdf μ).measurable (measurableSet_singleton r),map_cdf,measure_singleton]
  have hz : ∀ᵐ x ∂μ, cdf μ x≠0 := by
    rw [ae_iff]
    simpa only [not_not] using hpoint 0
  have ho : ∀ᵐ x ∂μ, cdf μ x≠1 := by
    rw [ae_iff]
    simpa only [not_not] using hpoint 1
  filter_upwards [hz,ho] with x hx hy
  exact ⟨lt_of_le_of_ne (cdf_nonneg μ x) (Ne.symm hx),lt_of_le_of_ne (cdf_le_one μ x) hy⟩

 theorem phase_injectiveOn : Set.InjOn phase (Ioo (0:ℝ) 1) := by
  intro x hx y hy hxy
  obtain ⟨n,hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hxy
  have hi := congrArg Complex.im hn
  simp only [Complex.add_im,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.intCast_re,Complex.intCast_im,
    zero_mul,mul_zero,mul_one,sub_zero,add_zero,zero_add] at hi
  norm_num at hi
  have he : x=y+(n:ℝ) := by nlinarith [Real.pi_pos]
  have hl : (-1:ℝ)<(n:ℝ) := by linarith [hx.1,hy.2]
  have hu : (n:ℝ)<1 := by linarith [hx.2,hy.1]
  have hli : (-1:ℤ)<n := by exact_mod_cast hl
  have hui : n<(1:ℤ) := by exact_mod_cast hu
  have hn0 : n=0 := by omega
  simpa only [hn0,Int.cast_zero,add_zero] using he

 theorem phase_cdf_injective_conull :
    ∃ s : Set ℝ, μ sᶜ=0 ∧ Set.InjOn (fun x => phase (cdf μ x)) s := by
  obtain ⟨s,hs,hinj⟩ := cdf_injective_conull μ
  refine ⟨s ∩ {x | 0<cdf μ x ∧ cdf μ x<1},?_,?_⟩
  · have hs' : ∀ᵐ x ∂μ, x∈s := ae_iff.mpr hs
    exact ae_iff.mp (hs'.and (cdf_between_ae μ))
  · intro x hx y hy he
    exact hinj hx.1 hy.1 (phase_injectiveOn hx.2 hy.2 he)

end
section
open MeasureTheory ProbabilityTheory Set Filter Function
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

 theorem exists_measurable_phase_inverse :
    ∃ g : ℂ → ℝ, Measurable g ∧ ∀ᵐ x ∂μ, g (phase (cdf μ x))=x := by
  classical
  obtain ⟨s,hs,hinj⟩ := phase_cdf_injective_conull μ
  let t : Set ℝ := (toMeasurable μ sᶜ)ᶜ
  have ht : MeasurableSet t := (measurableSet_toMeasurable μ sᶜ).compl
  have hts : t ⊆ s := by
    intro x hx
    by_contra hn
    exact hx (subset_toMeasurable μ sᶜ hn)
  have htm : μ tᶜ=0 := by
    change μ ((toMeasurable μ sᶜ)ᶜ)ᶜ=0
    rw [compl_compl,measure_toMeasurable,hs]
  have hae : ∀ᵐ x ∂μ, x∈t := ae_iff.mpr htm
  obtain ⟨x,hx⟩ := hae.exists
  let : Nonempty t := ⟨⟨x,hx⟩⟩
  let : StandardBorelSpace t := ht.standardBorel
  let f : t → ℂ := fun y => phase (cdf μ y)
  have hf : Measurable f :=
    (phase_continuous.comp (continuous_cdf μ)).measurable.comp measurable_subtype_coe
  have hfi : Injective f := by
    intro y z he
    apply Subtype.ext
    exact hinj (hts y.property) (hts z.property) he
  let e : MeasurableEmbedding f := hf.measurableEmbedding hfi
  refine ⟨fun z => (e.invFun z:ℝ),measurable_subtype_coe.comp e.measurable_invFun,?_⟩
  filter_upwards [hae] with y hy
  exact congrArg Subtype.val (e.leftInverse_invFun (⟨y,hy⟩:t))

end
open MeasureTheory ProbabilityTheory Set Function Filter
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

def haarMeasure : Measure ℂ := μ.map (fun x => phase (cdf μ x))

 theorem haarTransform_measurable : Measurable (fun x => phase (cdf μ x)) :=
  (phase_continuous.comp (continuous_cdf μ)).measurable

 theorem haarTransform_preserving :
    MeasurePreserving (fun x => phase (cdf μ x)) μ (haarMeasure μ) :=
  ⟨haarTransform_measurable μ,rfl⟩

 theorem haarPullback_surjective : Function.Surjective
    (Lp.compMeasurePreservingₗᵢ ℂ (fun x => phase (cdf μ x))
      (haarTransform_preserving μ) : Lp ℂ 2 (haarMeasure μ) →ₗᵢ[ℂ] Lp ℂ 2 μ) := by
  obtain ⟨g,hg,hleft⟩ := exists_measurable_phase_inverse μ
  have hpres : MeasurePreserving g (haarMeasure μ) μ := by
    refine ⟨hg,?_⟩
    change (μ.map (fun x => phase (cdf μ x))).map g=μ
    rw [Measure.map_map hg (haarTransform_measurable μ)]
    exact (Measure.map_congr hleft).trans (Measure.map_id)
  intro u
  let v := Lp.compMeasurePreserving g hpres u
  refine ⟨v,?_⟩
  apply Lp.ext
  have hv := (haarTransform_preserving μ).quasiMeasurePreserving.ae
    (Lp.coeFn_compMeasurePreserving u hpres)
  have hc := Lp.coeFn_compMeasurePreserving v (haarTransform_preserving μ)
  filter_upwards [hc,hv,hleft] with x hxc hxv hxl
  exact hxc.trans (hxv.trans (congrArg (fun y => u y) hxl))

noncomputable def haarL2Equiv : Lp ℂ 2 (haarMeasure μ) ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ (fun x => phase (cdf μ x)) (haarTransform_preserving μ))
    (haarPullback_surjective μ)

 theorem haarL2Equiv_apply (u : Lp ℂ 2 (haarMeasure μ)) :
    haarL2Equiv μ u =ᵐ[μ] fun x => u (phase (cdf μ x)) :=
  Lp.coeFn_compMeasurePreserving u (haarTransform_preserving μ)

instance haarMeasure_probability : IsProbabilityMeasure (haarMeasure μ) :=
  (Measure.isProbabilityMeasure_map_iff (haarTransform_measurable μ).aemeasurable).mpr
    inferInstance

end FreeGroupFactorMain.ProbabilityTransform
namespace FreeGroupFactorMain.SpectralPullback
open MeasureTheory Function Filter
variable {X : Type u_5} {Y : Type u_6} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) {f : X → Y} (e : MeasurableEmbedding f) [Nonempty X]

theorem pullback_surjective : Function.Surjective
    (Lp.compMeasurePreservingₗᵢ ℂ f ⟨e.measurable,rfl⟩ :
      Lp ℂ 2 (μ.map f) →ₗᵢ[ℂ] Lp ℂ 2 μ) := by
  have hleft : e.invFun ∘ f=id := funext e.leftInverse_invFun
  have hpres : MeasurePreserving e.invFun (μ.map f) μ := by
    refine ⟨e.measurable_invFun,?_⟩
    rw [Measure.map_map e.measurable_invFun e.measurable,hleft,Measure.map_id]
  intro u
  let v := Lp.compMeasurePreserving e.invFun hpres u
  let hp : MeasurePreserving f μ (μ.map f) := ⟨e.measurable,rfl⟩
  refine ⟨v,?_⟩
  apply Lp.ext
  have hv := hp.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving u hpres)
  have hc := Lp.coeFn_compMeasurePreserving v hp
  filter_upwards [hc,hv] with x hxc hxv
  exact hxc.trans (hxv.trans (congrArg (fun y => u y) (e.leftInverse_invFun x)))

noncomputable def equivalence : Lp ℂ 2 (μ.map f) ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ f ⟨e.measurable,rfl⟩)
    (pullback_surjective μ e)

end FreeGroupFactorMain.SpectralPullback
namespace FreeGroupFactorMain.CyclicSpectral

section
open MeasureTheory ProbabilityTheory Set
variable {H : Type u_7} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

def realMeasure : Measure ℝ := Measure.map (fun x : Space A => (x:ℝ)) (measure A hA ξ)

instance realMeasure_probability [IsProbabilityMeasure (measure A hA ξ)] :
    IsProbabilityMeasure (realMeasure A hA ξ) :=
  (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mpr inferInstance

instance realMeasure_noAtoms [NullSingletonClass (measure A hA ξ)] :
    NullSingletonClass (realMeasure A hA ξ) where
  measure_singleton x := by
    rw [realMeasure,Measure.map_apply measurable_subtype_coe (measurableSet_singleton x)]
    by_cases hx : x ∈ Space A
    · have he : (fun y : Space A => (y:ℝ)) ⁻¹' {x}={⟨x,hx⟩} := by
        ext y
        simp only [mem_preimage,mem_singleton_iff,Subtype.ext_iff]
      rw [he,measure_singleton]
    · have he : (fun y : Space A => (y:ℝ)) ⁻¹' {x}=∅ := by
        ext y
        simp only [mem_preimage,mem_singleton_iff,mem_empty_iff_false,iff_false]
        intro hy
        exact hx (hy ▸ y.property)
      rw [he,measure_empty]

variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

def haarFunction : C(Space A,ℂ) :=
  ⟨fun x => ProbabilityTransform.phase (cdf (realMeasure A hA ξ) x),
    ProbabilityTransform.phase_continuous.comp
      ((ProbabilityTransform.continuous_cdf (realMeasure A hA ξ)).comp continuous_subtype_val)⟩

 theorem haarFunction_unitary : haarFunction A hA ξ ∈ unitary C(Space A,ℂ) := by
  apply Unitary.mem_iff.mpr
  constructor
  · ext x
    change star (ProbabilityTransform.phase _)*ProbabilityTransform.phase _=1
    exact ProbabilityTransform.phase_star_mul _
  · ext x
    change ProbabilityTransform.phase _*star (ProbabilityTransform.phase _)=1
    rw [mul_comm]
    exact ProbabilityTransform.phase_star_mul _

def haarUnitary : unitary (H →L[ℂ] H) :=
  ⟨complexHom A hA (haarFunction A hA ξ),Unitary.map_mem (complexHom A hA) (haarFunction_unitary A hA ξ)⟩

 theorem haarUnitary_moment (n : ℕ) :
    inner ℂ ξ (((haarUnitary A hA ξ : H →L[ℂ] H)^n) ξ)=if n=0 then 1 else 0 := by
  change inner ℂ ξ (((complexHom A hA (haarFunction A hA ξ))^n) ξ)=_
  rw [← map_pow,← integral_complex]
  change (∫ x:Space A, ProbabilityTransform.phase (cdf (realMeasure A hA ξ) x)^n ∂measure A hA ξ)=_
  have hi := integral_map (μ := measure A hA ξ) measurable_subtype_coe.aemeasurable
    (((ProbabilityTransform.phase_continuous.comp
      (ProbabilityTransform.continuous_cdf (realMeasure A hA ξ))).pow n).aestronglyMeasurable)
  exact hi.symm.trans (ProbabilityTransform.phase_cdf_moment (realMeasure A hA ξ) n)

end
section
open MeasureTheory Set Function Filter
variable {H : Type u_8} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

noncomputable def realL2Equiv : Lp ℂ 2 (realMeasure A hA ξ) ≃ₗᵢ[ℂ] Lp ℂ 2 (measure A hA ξ) := by
  let : Nonempty (Space A) := nonempty_of_isProbabilityMeasure (measure A hA ξ)
  exact SpectralPullback.equivalence (measure A hA ξ)
    (MeasurableEmbedding.subtype_coe (spectrum.isClosed A).measurableSet)

omit [NullSingletonClass (measure A hA ξ)] in
 theorem realL2Equiv_apply (u : Lp ℂ 2 (realMeasure A hA ξ)) :
    realL2Equiv A hA ξ u =ᵐ[measure A hA ξ] fun x => u (x:ℝ) := by
  exact Lp.coeFn_compMeasurePreserving u ⟨measurable_subtype_coe,rfl⟩

noncomputable def haarSpectralTransfer :
    Lp ℂ 2 (ProbabilityTransform.haarMeasure (realMeasure A hA ξ)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (measure A hA ξ) :=
  (ProbabilityTransform.haarL2Equiv (realMeasure A hA ξ)).trans (realL2Equiv A hA ξ)

 theorem haarSpectralTransfer_continuous (q : BoundedContinuousFunction ℂ ℂ) :
    haarSpectralTransfer A hA ξ
        (BoundedContinuousFunction.toLp 2 (ProbabilityTransform.haarMeasure (realMeasure A hA ξ)) ℂ q)
      = ContinuousMap.toLp 2 (measure A hA ξ) ℂ (q.toContinuousMap.comp (haarFunction A hA ξ)) := by
  let μ := realMeasure A hA ξ
  let u := BoundedContinuousFunction.toLp 2 (ProbabilityTransform.haarMeasure μ) ℂ q
  let hp : MeasurePreserving (fun x : Space A => (x:ℝ)) (measure A hA ξ) μ :=
    ⟨measurable_subtype_coe,rfl⟩
  have h1 := realL2Equiv_apply A hA ξ (ProbabilityTransform.haarL2Equiv μ u)
  have h2 := hp.quasiMeasurePreserving.ae (ProbabilityTransform.haarL2Equiv_apply μ u)
  have h3 := hp.quasiMeasurePreserving.ae
    ((ProbabilityTransform.haarTransform_preserving μ).quasiMeasurePreserving.ae
      (BoundedContinuousFunction.coeFn_toLp 2 (ProbabilityTransform.haarMeasure μ) ℂ q))
  have h4 := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (measure A hA ξ) (q.toContinuousMap.comp (haarFunction A hA ξ))
  apply Lp.ext
  filter_upwards [h1,h2,h3,h4] with x hx1 hx2 hx3 hx4
  exact hx1.trans (hx2.trans (hx3.trans hx4.symm))

 theorem haar_spectral_functions_dense : DenseRange
    (fun q : BoundedContinuousFunction ℂ ℂ => ContinuousMap.toLp 2 (measure A hA ξ) ℂ
      (q.toContinuousMap.comp (haarFunction A hA ξ))) := by
  have hd := (haarSpectralTransfer A hA ξ).surjective.denseRange.comp
    (BoundedContinuousFunction.toLp_denseRange ℂ
      (ProbabilityTransform.haarMeasure (realMeasure A hA ξ)) ℂ (p := 2) (by norm_num))
    (haarSpectralTransfer A hA ξ).continuous
  convert hd using 1
  funext q
  exact (haarSpectralTransfer_continuous A hA ξ q).symm

end
section
open MeasureTheory Set Function Filter
variable {H : Type u_9} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

 theorem haar_cyclic_contains_continuous (f : C(Space A,ℂ)) :
    complexHom A hA f ξ ∈ closure (Set.range (fun q : BoundedContinuousFunction ℂ ℂ =>
      complexHom A hA (q.toContinuousMap.comp (haarFunction A hA ξ)) ξ)) := by
  let s := closure (Set.range (fun q : BoundedContinuousFunction ℂ ℂ =>
    complexHom A hA (q.toContinuousMap.comp (haarFunction A hA ξ)) ξ))
  have hd := haar_spectral_functions_dense A hA ξ
  have hall : ∀ v : Lp ℂ 2 (measure A hA ξ), complexRealize A hA ξ v ∈ s := by
    intro v
    refine hd.induction_on (p := fun v => complexRealize A hA ξ v ∈ s) v
      (isClosed_closure.preimage (complexRealize A hA ξ).continuous) ?_
    intro q
    rw [complexRealize_continuous]
    exact subset_closure (Set.mem_range_self q)
  simpa only [complexRealize_continuous] using hall (ContinuousMap.toLp 2 (measure A hA ξ) ℂ f)

 theorem haar_cyclic_contains_operator :
    A ξ ∈ closure (Set.range (fun q : BoundedContinuousFunction ℂ ℂ =>
      complexHom A hA (q.toContinuousMap.comp (haarFunction A hA ξ)) ξ)) := by
  have h := haar_cyclic_contains_continuous A hA ξ
    (complexLift A ((ContinuousMap.id ℝ).restrict (spectrum ℝ A)))
  rwa [complexHom_real,cfcHom_id] at h

end
section
variable {H : Type u_10} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)

 theorem complexHom_continuous : Continuous (complexHom A hA) := by
  exact AddMonoidHomClass.continuous_of_bound (complexHom A hA) 1
    (by simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le (complexHom A hA))

end
section
open MeasureTheory Set Function Filter

variable {H : Type u_11} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
open MeasureTheory Set Function Filter
variable {H : Type u_12} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

end FreeGroupFactorMain.CyclicSpectral
namespace FreeGroupFactorMain
open Filter Topology
variable {E : Type u_13} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FreeGroupFactorMain

namespace FreeGroupFactorMain.CyclicSpectral
open Filter Topology Set MeasureTheory
variable {E : Type u_15} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
variable (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (ξ : E)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

end FreeGroupFactorMain.CyclicSpectral

end

end OAI
end


