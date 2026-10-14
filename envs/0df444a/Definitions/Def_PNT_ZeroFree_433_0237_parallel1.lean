-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0237_parallel1
-- name    : PNT_ZeroFree_433_0237_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:06:07.023992+00:00
-- url     : https://prove2.me/theorems/5ca95cd6-254f-4668-9afb-4d15f8d80943
-- title:
--   Zero-free region foundations: Eisenstein.ArbitraryCuspPullback [0237_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.ArbitraryCuspPullback
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ArbitraryCuspPullback.lean#L84-L325

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0014
import Definitions.Def_PNT_ZeroFree_433_0019
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0068_1_1
import Definitions.Def_PNT_ZeroFree_433_0068_1_1_1
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0076
import Definitions.Def_PNT_ZeroFree_433_0108
import Definitions.Def_PNT_ZeroFree_433_0153_parallel1
import Definitions.Def_PNT_ZeroFree_433_0182_parallel1
import Definitions.Def_PNT_ZeroFree_433_0198_parallel1
import Definitions.Def_PNT_ZeroFree_433_0206_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221
import Definitions.Def_PNT_ZeroFree_433_0224_parallel1
import Definitions.Def_PNT_ZeroFree_433_0224_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0276_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ArbitraryCuspPullback.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CubicEisenstein

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_omega_relation : omega^2+omega+1=(0:Eis) := by
  apply eisEmbedding_injective
  simp only [map_add,map_pow,map_one,map_zero,eisEmbedding_omega_actual]
  exact EisensteinEmbedding.omega3_sq

def lowerCuspMatrix (t : Eis) : SL(2,Eis) :=
  ⟨!![1,0;t,1],by simp [Matrix.det_fin_two]⟩

def ramifiedParabolic (t x : Eis) : levelThree := by
  let M : SL(2,Eis) := ⟨!![1-3*t*x,3*x;-3*t^2*x,1+3*t*x],by
    rw [Matrix.det_fin_two]
    change (1-3*t*x)*(1+3*t*x)-(3*x)*(-3*t^2*x)=1
    ring⟩
  refine ⟨M,levelThree_of_entries M ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨-t*x,by change 1-3*t*x-1=3*(-t*x);ring⟩
  · exact ⟨x,by change 3*x-0=3*x;ring⟩
  · exact ⟨-t^2*x,by change -3*t^2*x-0=3*(-t^2*x);ring⟩
  · exact ⟨t*x,by change 1+3*t*x-1=3*(t*x);ring⟩

lemma ramifiedParabolic_mul_lower (t x : Eis) :
    (ramifiedParabolic t x : SL(2,Eis))*lowerCuspMatrix t=
      lowerCuspMatrix t*(upperTranslation x : SL(2,Eis)) := by
  apply Subtype.ext
  change (ramifiedParabolic t x : Matrix (Fin 2) (Fin 2) Eis) *
    (lowerCuspMatrix t : Matrix (Fin 2) (Fin 2) Eis) =
    (lowerCuspMatrix t : Matrix (Fin 2) (Fin 2) Eis) *
      (upperTranslation x : Matrix (Fin 2) (Fin 2) Eis)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [ramifiedParabolic,lowerCuspMatrix,upperTranslation,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma ramifiedParabolic_character (t x : Eis) :
    complexCharacter (ramifiedParabolic t x)=
      eisEmbedding (symbol (-t) (1-3*t*x)) := by
  simp only [complexCharacter,MonoidHom.comp_apply,character,ramifiedParabolic]
  apply congrArg eisEmbedding
  apply symbol_congr
  refine ⟨t,?_⟩
  change (-3*t^2*x)-(-t)=(1-3*t*x)*t
  ring

lemma ramifiedParabolic_omega_value (A B : ℤ) :
    complexCharacter (ramifiedParabolic omega (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding (cubicExp (A+B)) := by
  rw [ramifiedParabolic_character]
  have hd : 1-3*omega*ActualEisensteinCoordinates.eval A B=primaryCoord B (B-A) := by
    rw [primaryCoord_eq]
    change 1-3*omega*((A:Eis)+(B:Eis)*omega)=_
    push_cast
    linear_combination -3*(B:Eis)*ramified_omega_relation
  rw [hd,symbol_neg_numerator _ _ (primaryCoord_primary _ _),
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),linearRay_primaryCoord]
  congr 2
  ring

lemma ramifiedParabolic_omega_sq_value (A B : ℤ) :
    complexCharacter (ramifiedParabolic (omega^2) (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding (cubicExp (-(A+B))) := by
  rw [ramifiedParabolic_character]
  have hd : 1-3*omega^2*ActualEisensteinCoordinates.eval A B=primaryCoord (A-B) A := by
    rw [primaryCoord_eq]
    change 1-3*omega^2*((A:Eis)+(B:Eis)*omega)=_
    push_cast
    linear_combination -3*((A:Eis)+(B:Eis)*omega-(B:Eis))*ramified_omega_relation
  rw [hd,symbol_neg_numerator _ _ (primaryCoord_primary _ _),
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) 2,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),linearRay_primaryCoord]
  have he : cubicExp (2*((A-B)*2+(-1)*A))=cubicExp (-(A+B)) := by
    apply cubicExp_eq_of_dvd_sub
    exact ⟨A-B,by ring⟩
  have hs : cubicExp ((A-B)*2+(-1)*A)^2=cubicExp (2*((A-B)*2+(-1)*A)) := by
    rw [pow_two,←cubicExp_add]
    congr 1
    ring
  convert! congrArg eisEmbedding (hs.trans he) using 1 ; congr 2 ; ring_nf


end

section
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CubicRamified
open EisensteinEmbedding (omega3)
local notation "Eis" => ActualEisensteinCubic.O

lemma embedding_cubicExp (n : ℤ) :
    eisEmbedding (cubicExp n)=Complex.exp (2*Real.pi*Complex.I*(n:ℂ)/3) := by
  have hw : omega3=Complex.exp (2*Real.pi*Complex.I/3) := by
    rw [←TraceLambdaPhase.exp_minus_four_pi_div_three]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    exact ⟨-1,by push_cast;ring⟩
  rw [cubicExp,map_pow,eisEmbedding_omega_actual,hw,←Complex.exp_nat_mul]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-(n/3),?_⟩
  have hn : (n%3).toNat=(n%3) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hnc : ((n%3).toNat:ℂ)=((n%3:ℤ):ℂ) := by exact_mod_cast hn
  have he : ((n%3:ℤ):ℂ)=(n:ℂ)-3*((n/3:ℤ):ℂ) := by
    have he0 : n%3=n-3*(n/3) := by omega
    exact_mod_cast he0
  rw [hnc,he]
  push_cast
  ring

def ramifiedShift10 : ℂ := eisEmbedding (omega-1)/(9*eisLam)

def ramifiedShift19 : ℂ := eisEmbedding (-2-omega)/(9*eisLam)

lemma ramifiedShift10_explicit : ramifiedShift10=-(omega3^2)/9 := by
  unfold ramifiedShift10
  apply (div_eq_iff (mul_ne_zero (by norm_num : (9:ℂ)≠0) eisLam_ne_zero)).mpr
  rw [map_sub,eisEmbedding_omega_actual,map_one]
  change omega3-1=-(omega3^2)/9*(9*(1+2*omega3))
  linear_combination (2*omega3-1)*EisensteinEmbedding.omega3_sq

lemma ramifiedShift19_explicit : ramifiedShift19=omega3/9 := by
  unfold ramifiedShift19
  apply (div_eq_iff (mul_ne_zero (by norm_num : (9:ℂ)≠0) eisLam_ne_zero)).mpr
  rw [map_sub,map_neg,map_ofNat,eisEmbedding_omega_actual]
  change -2-omega3=omega3/9*(9*(1+2*omega3))
  linear_combination -2*EisensteinEmbedding.omega3_sq

lemma ramifiedShift10_period (A B : ℤ) :
    ShortDraftTrace.breveE (ramifiedShift10*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B)))=
      eisEmbedding (cubicExp (A+B)) := by
  have he : ramifiedShift10*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding ((omega-1)*ActualEisensteinCoordinates.eval A B)/eisLam/3 := by
    rw [ramifiedShift10,map_mul]
    ring
  have ht := breveE_real_trace_of_O (3:ℝ) ((omega-1)*ActualEisensteinCoordinates.eval A B)
  norm_num only [Complex.ofReal_ofNat] at ht
  rw [he,ht]
  have hcoords : (ActualEisensteinCoordinates.coords
      ((omega-1)*ActualEisensteinCoordinates.eval A B)).2=A-2*B := by
    have hw : omega-1=ActualEisensteinCoordinates.eval (-1) 1 := by
      simp only [ActualEisensteinCoordinates.eval,Int.cast_neg,Int.cast_one,one_mul]
      change omega-1=-1+omega
      ring
    rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
    ring
  rw [hcoords,←embedding_cubicExp]
  exact congrArg eisEmbedding (cubicExp_eq_of_dvd_sub ⟨-B,by ring⟩)

lemma ramifiedShift19_period (A B : ℤ) :
    ShortDraftTrace.breveE (ramifiedShift19*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B)))=
      eisEmbedding (cubicExp (-(A+B))) := by
  have he : ramifiedShift19*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding ((-2-omega)*ActualEisensteinCoordinates.eval A B)/eisLam/3 := by
    rw [ramifiedShift19,map_mul]
    ring
  have ht := breveE_real_trace_of_O (3:ℝ) ((-2-omega)*ActualEisensteinCoordinates.eval A B)
  norm_num only [Complex.ofReal_ofNat] at ht
  rw [he,ht]
  have hcoords : (ActualEisensteinCoordinates.coords
      ((-2-omega)*ActualEisensteinCoordinates.eval A B)).2=-(A+B) := by
    have hw : -2-omega=ActualEisensteinCoordinates.eval (-2) (-1) := by
      simp only [ActualEisensteinCoordinates.eval,Int.cast_neg,Int.cast_one,Int.cast_ofNat,neg_mul,one_mul]
      change -2-omega=-2+-omega
      ring
    rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
    ring
  rw [hcoords,embedding_cubicExp]


lemma trace_dephase_periodic (f : ℂ→ℂ) (shift : ℂ)
    (hf : ∀ x : Eis,∀z, f (z+3*eisEmbedding x)=
      ShortDraftTrace.breveE (shift*(3*eisEmbedding x))*f z) :
    ∀x:Eis,∀z,(f (z+3*eisEmbedding x)*ShortDraftTrace.breveE (-shift*(z+3*eisEmbedding x)))=
      f z*ShortDraftTrace.breveE (-shift*z) := by
  intro x z
  rw [hf,mul_add,AddChar.map_add_eq_mul]
  have hn : -shift*(3*eisEmbedding x)=-(shift*(3*eisEmbedding x)) := by ring
  rw [hn,AddChar.map_neg_eq_inv]
  have hne : ShortDraftTrace.breveE (shift*(3*eisEmbedding x))≠0 :=
    Complex.exp_ne_zero _
  calc
    _ = (ShortDraftTrace.breveE (shift*(3*eisEmbedding x))*
      (ShortDraftTrace.breveE (shift*(3*eisEmbedding x)))⁻¹)*
        (f z*ShortDraftTrace.breveE (-shift*z)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hne,one_mul]


end


end CubicEisenstein

end

end OAI

end


