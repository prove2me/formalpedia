-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0131_parallel1
-- name    : PNT_ZeroFree_433_0131_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:57:10.966427+00:00
-- url     : https://prove2.me/theorems/4c121f41-6213-4f81-8855-631498bfbbe7
-- title:
--   Zero-free region foundations: Eisenstein.HyperbolicVolume [0131_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicVolume
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/HyperbolicVolume.lean#L79-L440

import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel1
import Definitions.Def_PNT_ZeroFree_433_0188_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0228_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel1
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1
import Definitions.Def_PNT_ZeroFree_433_0303_parallel1
import Definitions.Def_PNT_ZeroFree_433_0329_parallel1
import Definitions.Def_PNT_ZeroFree_433_0330_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/HyperbolicVolume.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
attribute [simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

namespace CubicEisenstein
open Filter MeasureTheory EuclideanGeometry
open scoped BigOperators Classical Topology InnerProductSpace ENNReal Matrix

lemma linear_preserves_hyperbolicVolume (A : EuclideanSpatial →L[ℝ] EuclideanSpatial)
    (k : ℝ) (hk : 0<k) (hh : ∀p,(A p) 2=k*p 2) (hd : |A.det|=k^3) :
    Measure.map A hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  have hdet : A.det≠0 := by intro he; rw [he,abs_zero] at hd; exact (pow_ne_zero 3 hk.ne') hd.symm
  have hker : LinearMap.ker A.toLinearMap=⊥ := by
    by_contra hn
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn)
  have hinj : Function.Injective A := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective A := (LinearMap.injective_iff_surjective).mp hinj
  apply hyperbolic_volume_map_of_jacobian A (fun _ => A) A.continuous.measurable
    (fun p hp => A.hasFDerivAt) hinj.injOn
  · apply Set.Subset.antisymm
    · rintro q ⟨p,hp,rfl⟩
      exact show 0<(A p) 2 by rw [hh]; exact mul_pos hk hp
    · intro q hq
      obtain ⟨p,hp⟩ := hsurj q
      refine ⟨p,?_,hp⟩
      change 0<p 2
      have h := hh p
      rw [hp] at h
      exact (mul_pos_iff_of_pos_left hk).mp (h.symm ▸ hq)
  · intro p hp
    rw [hd,hyperbolicDensity,hyperbolicDensity,hh]
    rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp

lemma translation_preserves_hyperbolicVolume (u : EuclideanSpatial) (hu : u 2=0) :
    Measure.map (fun p => p+u) hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply hyperbolic_volume_map_of_jacobian (fun p => p+u) (fun _ => ContinuousLinearMap.id ℝ _)
    (continuous_id.add continuous_const).measurable
    (fun p hp => (hasFDerivAt_id p).add_const u) (add_left_injective u).injOn
  · apply Set.Subset.antisymm
    · rintro q ⟨p,hp,rfl⟩
      simpa [euclideanUpperHalf,hu] using hp
    · intro p hp
      refine ⟨p-u,?_,sub_add_cancel p u⟩
      simpa [euclideanUpperHalf,hu] using hp
  · intro p hp
    have hid : (ContinuousLinearMap.id ℝ EuclideanSpatial).det=1 := by
      change LinearMap.det (LinearMap.id : EuclideanSpatial →ₗ[ℝ] EuclideanSpatial)=1
      simp
    simp [hyperbolicDensity,hu,hid]

def euclideanMatrixOperator (M : Matrix (Fin 3) (Fin 3) ℝ) :
    EuclideanSpatial →L[ℝ] EuclideanSpatial := M.toEuclideanLin.toContinuousLinearMap

lemma euclideanMatrixOperator_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (p : EuclideanSpatial)
    (j : Fin 3) : euclideanMatrixOperator M p j=∑i,M j i*p i := rfl

lemma euclideanMatrixOperator_det (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (euclideanMatrixOperator M).det=M.det := by
  change LinearMap.det (Matrix.toEuclideanLin M)=M.det
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]

def euclideanWeylReflection : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  euclideanMatrixOperator !![-1,0,0;0,1,0;0,0,1]

lemma euclideanWeylReflection_apply (p : EuclideanSpatial) :
    euclideanWeylReflection p 0= -p 0 ∧ euclideanWeylReflection p 1=p 1 ∧
      euclideanWeylReflection p 2=p 2 := by
  simp [euclideanWeylReflection,euclideanMatrixOperator_apply,Fin.sum_univ_three]

lemma euclideanWeylReflection_preserves_hyperbolicVolume :
    Measure.map euclideanWeylReflection hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply linear_preserves_hyperbolicVolume euclideanWeylReflection 1 (by norm_num)
  · intro p
    simpa using (euclideanWeylReflection_apply p).2.2
  · norm_num [euclideanWeylReflection,euclideanMatrixOperator_det,Matrix.det_fin_three]

def euclideanComplexDilation (β : ℂ) : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  euclideanMatrixOperator !![(β^2).re,-(β^2).im,0;(β^2).im,(β^2).re,0;0,0,Complex.normSq β]

lemma euclideanComplexDilation_apply (β : ℂ) (p : EuclideanSpatial) :
    euclideanComplexDilation β p 0=(β^2).re*p 0-(β^2).im*p 1 ∧
      euclideanComplexDilation β p 1=(β^2).im*p 0+(β^2).re*p 1 ∧
      euclideanComplexDilation β p 2=Complex.normSq β*p 2 := by
  simp [euclideanComplexDilation,euclideanMatrixOperator_apply,Fin.sum_univ_three,sub_eq_add_neg]

lemma euclideanComplexDilation_det (β : ℂ) :
    (euclideanComplexDilation β).det=Complex.normSq β^3 := by
  rw [euclideanComplexDilation,euclideanMatrixOperator_det,Matrix.det_fin_three]
  have h : (β^2).re^2+(β^2).im^2=(Complex.normSq β)^2 := by
    simpa [Complex.normSq_apply,sq] using map_pow Complex.normSq β 2
  change (β^2).re*(β^2).re*Complex.normSq β-(β^2).re*0*0-
    (-(β^2).im)*(β^2).im*Complex.normSq β+(-(β^2).im)*0*0+
    0*(β^2).im*0-0*(β^2).re*0=Complex.normSq β^3
  calc
    _ = ((β^2).re^2+(β^2).im^2)*Complex.normSq β := by ring
    _ = _ := by rw [h]; ring

lemma euclideanComplexDilation_preserves_hyperbolicVolume (β : ℂ) (hβ : β≠0) :
    Measure.map (euclideanComplexDilation β) hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply linear_preserves_hyperbolicVolume (euclideanComplexDilation β) (Complex.normSq β)
    (Complex.normSq_pos.mpr hβ) (fun p => (euclideanComplexDilation_apply β p).2.2)
  rw [euclideanComplexDilation_det,abs_of_nonneg (pow_nonneg (Complex.normSq_nonneg β) 3)]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein


def positiveCoordinateHeight (p : EuclideanSpatial) : ℝ := if 0<p 2 then p 2 else 1
lemma positiveCoordinateHeight_pos (p : EuclideanSpatial) : 0<positiveCoordinateHeight p := by
  unfold positiveCoordinateHeight
  split_ifs with hp
  · exact hp
  · norm_num


lemma hyperbolicEuclideanVolume_ae_positive :
    ∀ᵐp∂hyperbolicEuclideanVolume,0<p 2 := by
  exact (ae_restrict_mem euclideanUpperHalf_measurable).filter_mono
    ((withDensity_absolutelyContinuous (volume.restrict euclideanUpperHalf) hyperbolicDensity).ae_le)


open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

def matrixCross (g : SL(2,ℂ)) : ℂ := g 0 0*star (g 1 0)+g 0 1*star (g 1 1)


lemma matrixCross_upperSection (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0<v) :
    matrixCross (g*upperSection z v hv)=
      ((g 0 0*z+g 0 1)*star (g 1 0*z+g 1 1)+
        g 0 0*star (g 1 0)*(v:ℂ)^2)/(v:ℂ) := by
  have hr : (Real.sqrt v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hv).ne'
  have hrs : (Real.sqrt v:ℂ)^2=(v:ℂ) := by exact_mod_cast Real.sq_sqrt hv.le
  simp only [matrixCross,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  change (g 0 0*(Real.sqrt v:ℂ)+g 0 1*0)*star (g 1 0*(Real.sqrt v:ℂ)+g 1 1*0)+
    (g 0 0*(z/(Real.sqrt v:ℂ))+g 0 1*(Real.sqrt v:ℂ)⁻¹)*
      star (g 1 0*(z/(Real.sqrt v:ℂ))+g 1 1*(Real.sqrt v:ℂ)⁻¹)=_
  simp only [mul_zero,add_zero,star_add,star_mul,Complex.star_def,
    map_inv₀,map_div₀,Complex.conj_ofReal]
  rw [←hrs]
  field_simp
  ; ring

lemma mobius_denominator_pos (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0<v) :
    0<‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2 := by
  exact heightDenominator_pos z v hv (complexBottomRow g) (complexBottomRow_ne_zero g)

lemma upperPoint_congr {z z' : ℂ} {v v' : ℝ} (hv : 0<v) (hv' : 0<v')
    (hz : z=z') (hvv : v=v') : upperPoint z v hv=upperPoint z' v' hv' := by
  subst z'
  subst v'
  rfl


def complexTranslation (b : ℂ) : SL(2,ℂ) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two]⟩
def complexDiagonal (b : ℂ) (hb : b≠0) : SL(2,ℂ) :=
  ⟨!![b,0;0,b⁻¹],by simp [Matrix.det_fin_two,hb]⟩
def complexWeyl : SL(2,ℂ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma complexTranslation_action (b z : ℂ) (v : ℝ) (hv : 0<v) :
    complexTranslation b • upperPoint z v hv=upperPoint (z+b) v hv := by
  change (QuotientGroup.mk (complexTranslation b*upperSection z v hv) : HyperbolicSpace)=
    QuotientGroup.mk (upperSection (z+b) v hv)
  apply congrArg (fun g : SL(2,ℂ) => (QuotientGroup.mk g : HyperbolicSpace))
  apply Subtype.ext
  change (complexTranslation b : Matrix (Fin 2) (Fin 2) ℂ) *
    (upperSection z v hv : Matrix (Fin 2) (Fin 2) ℂ) =
    (upperSection (z + b) v hv : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,upperSection,Matrix.mul_apply,
      Fin.sum_univ_two,div_eq_mul_inv] ; ring


lemma complex_bruhat_nonzero (g : SL(2,ℂ)) (hc : g 1 0≠0) :
    g=complexTranslation (g 0 0/g 1 0)*complexDiagonal (g 1 0)⁻¹ (inv_ne_zero hc)*
      complexWeyl*complexTranslation (g 1 1/g 1 0) := by
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) ℂ) =
    (complexTranslation (g 0 0 / g 1 0) : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexDiagonal (g 1 0)⁻¹ (inv_ne_zero hc) : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexWeyl : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexTranslation (g 1 1 / g 1 0) : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,complexDiagonal,complexWeyl,Matrix.mul_apply,Fin.sum_univ_two,hc] <;>
      field_simp ; linear_combination -hd

lemma complex_bruhat_zero (g : SL(2,ℂ)) (hc : g 1 0=0) :
    ∃ha : g 0 0≠0,g=complexDiagonal (g 0 0) ha*complexTranslation (g 0 1/g 0 0) := by
  have hd : g 0 0*g 1 1=1 := by simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using g.property
  have ha : g 0 0≠0 := by intro h; simp [h] at hd
  refine ⟨ha,?_⟩
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) ℂ) =
    (complexDiagonal (g 0 0) ha : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexTranslation (g 0 1 / g 0 0) : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,complexDiagonal,Matrix.mul_apply,Fin.sum_univ_two,hc] <;>
      field_simp ; linear_combination hd

def euclideanHorizontalTranslation (b : ℂ) : EuclideanSpatial := WithLp.toLp 2 ![b.re,b.im,0]


lemma euclidean_complex_norm_sq (p : EuclideanSpatial) :
    ‖(p 0:ℂ)+Complex.I*(p 1:ℂ)‖^2+(p 2)^2=‖p‖^2 := by
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_three,sq]

def euclideanWeylAction (p : EuclideanSpatial) : EuclideanSpatial :=
  euclideanWeylReflection (euclideanInversion p)

lemma euclideanWeylAction_measurable : Measurable euclideanWeylAction :=
  euclideanWeylReflection.continuous.measurable.comp euclideanInversion_measurable

lemma euclideanWeylAction_preserves_hyperbolicVolume :
    Measure.map euclideanWeylAction hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  rw [show euclideanWeylAction=euclideanWeylReflection ∘ euclideanInversion from rfl,
    ←Measure.map_map euclideanWeylReflection.continuous.measurable euclideanInversion_measurable,
    euclideanInversion_preserves_hyperbolicVolume,euclideanWeylReflection_preserves_hyperbolicVolume]

lemma euclideanWeylAction_apply (p : EuclideanSpatial) :
    euclideanWeylAction p 0= -((1/‖p‖)^2*p 0) ∧
      euclideanWeylAction p 1=(1/‖p‖)^2*p 1 ∧
      euclideanWeylAction p 2=(1/‖p‖)^2*p 2 := by
  simpa [euclideanWeylAction,euclideanInversion_apply] using
    euclideanWeylReflection_apply (euclideanInversion p)


end CubicEisenstein


end

end OAI

end


