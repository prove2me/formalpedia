-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0242_parallel2
-- name    : PNT_ZeroFree_433_0242_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:22:02.239561+00:00
-- url     : https://prove2.me/theorems/200cf11f-92ba-4ee7-8d32-3f027d98dc2f
-- title:
--   Zero-free region foundations: Reciprocity.PrimaryCongruences [0242_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.PrimaryCongruences
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/PrimaryCongruences.lean#L215-L682

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0014
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0019
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0068_1_1
import Definitions.Def_PNT_ZeroFree_433_0068_1_1_1
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0088
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0109
import Definitions.Def_PNT_ZeroFree_433_0138_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel2
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0242_parallel1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/PrimaryCongruences.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical


open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O


lemma ramified_trace_symbol (a : Eis) (ha : lambda^2∣a-1) :
    symbol ramifiedTraceLambda a=linearRay 0 (-1) a := by
  have h := symbol_traceLambda_eq_linearRay a ha
  change symbol ramifiedTraceLambda a=linearRay 0 (-1) a at h
  exact h

lemma ramifiedSymbol_primaryCoord (j n : ℕ) (A B : ℤ) :
    symbol (omega^j*ramifiedTraceLambda^n) (primaryCoord A B)=
      cubicExp ((j:ℤ)*(2*A-B)-(n:ℤ)*B) := by
  rw [symbol_mul_numerator _ _ _ (primaryCoord_primary _ _),
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) j,
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) n,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),
    ramified_trace_symbol _ (primaryCoord_primary _ _),linearRay_primaryCoord,linearRay_primaryCoord,
    ←ramified_cubicExp_nat_mul,←ramified_cubicExp_nat_mul,←cubicExp_add]
  congr 1
  ring

def ramifiedAffineParameter (j n : ℕ) : Eis := (j:Eis)*ramifiedTraceLambda-(n:Eis)

lemma ramifiedAffineParameter_coords (j n : ℕ) (C D : ℤ) :
    (ActualEisensteinCoordinates.coords
      (ramifiedAffineParameter j n*ActualEisensteinCoordinates.eval C D)).2=
      (j:ℤ)*(2*C-D)-(n:ℤ)*D := by
  have hk : ramifiedAffineParameter j n=ActualEisensteinCoordinates.eval ((j:ℤ)-(n:ℤ)) (2*(j:ℤ)) := by
    change (j:Eis)*(1+2*omega)-(n:Eis)=(((j:ℤ)-(n:ℤ):ℤ):Eis)+((2*(j:ℤ):ℤ):Eis)*omega
    push_cast
    ring
  rw [hk,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
  ring

theorem ramified_symbol_primary_shift (j n : ℕ) (a x : Eis) (ha : lambda^2∣a-1) :
    eisEmbedding (symbol (omega^j*ramifiedTraceLambda^n) (a+3*x))=
      eisEmbedding (symbol (omega^j*ramifiedTraceLambda^n) a)*
        ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3) := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  let C := (ActualEisensteinCoordinates.coords x).1
  let D := (ActualEisensteinCoordinates.coords x).2
  have hx : x=ActualEisensteinCoordinates.eval C D := (ActualEisensteinCoordinates.eval_coords x).symm
  have hsum : primaryCoord A B+3*x=primaryCoord (A+C) (B+D) := by
    rw [hx,primaryCoord_eq,primaryCoord_eq]
    change 1+3*(A:Eis)+3*(B:Eis)*omega+3*((C:Eis)+(D:Eis)*omega)=_
    push_cast
    ring
  rw [hsum,ramifiedSymbol_primaryCoord,ramifiedSymbol_primaryCoord]
  have ht := breveE_real_trace_of_O (3:ℝ) (ramifiedAffineParameter j n*x)
  norm_num only [Complex.ofReal_ofNat] at ht
  rw [ht,hx,ramifiedAffineParameter_coords,←embedding_cubicExp,←map_mul,←cubicExp_add]
  apply congrArg eisEmbedding
  apply congrArg cubicExp
  ring

lemma ramified_symbol_primary_shift_signed (j n : ℕ) (r a x : Eis)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (ha : lambda^2∣a-1) :
    eisEmbedding (symbol r (a+3*x))=eisEmbedding (symbol r a)*
      ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3) := by
  rcases hr with rfl|rfl
  · exact ramified_symbol_primary_shift j n a x ha
  · rw [symbol_neg_numerator _ _ (primary_add_three a x ha),symbol_neg_numerator _ _ ha]
    exact ramified_symbol_primary_shift j n a x ha

end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedTraceLambda_square : ramifiedTraceLambda^2=(-3:Eis) := by
  unfold ramifiedTraceLambda
  linear_combination 4*ramified_omega_relation

lemma ramified_character_coprime (j n : ℕ) (r a : Eis)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (ha : lambda^2∣a-1) : IsCoprime r a := by
  have hc3 := (primary_coprime_three a ha).symm
  have ht : ramifiedTraceLambda∣(3:Eis) := by
    refine ⟨-ramifiedTraceLambda,?_⟩
    linear_combination ramifiedTraceLambda_square
  have hcT := hc3.of_isCoprime_of_dvd_left ht
  have hcW : IsCoprime omega a := by
    refine ⟨omega^2,0,?_⟩
    rw [zero_mul,add_zero,←pow_succ,omega_primitive.pow_eq_one]
  have hc : IsCoprime (omega^j*ramifiedTraceLambda^n) a := hcW.pow_left.mul_left hcT.pow_left
  rcases hr with rfl|rfl
  · exact hc
  · exact hc.neg_left

lemma affineCusp_phase_identity (h h1 q a k c x : Eis)
    (ha : a≠0) (hq : q≠0) (hh : h=q*h1) (hk : 3*k=h1+c*a) :
    ShortDraftTrace.breveE (eisEmbedding (c*x)/eisLam/3)*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a))=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*residueAdditive (3*k) a x := by
  have hk' : eisEmbedding k=(eisEmbedding h1+eisEmbedding c*eisEmbedding a)/3 := by
    apply (eq_div_iff (by norm_num : (3:ℂ)≠0)).mpr
    have he := congrArg eisEmbedding hk
    simp only [map_mul,map_add,map_ofNat] at he
    linear_combination he
  rw [←AddChar.map_add_eq_mul]
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  apply congrArg ShortDraftTrace.breveE
  rw [hh]
  simp only [ninthCuspFrequency,cuspFrequency,map_add,map_mul,map_ofNat]
  rw [hk']
  field_simp [eisEmbedding_ne_zero ha,eisEmbedding_ne_zero hq,eisLam_ne_zero]
  ;ring

def ramifiedAffineGauss (h q r a : Eis) : ℂ :=
  ∑'x:CubicUnitResidue a,
    (eisEmbedding (symbol r (a+3*GaussianShiftedPartition.representative a x.val))*
      eisEmbedding (symbol (a+3*GaussianShiftedPartition.representative a x.val) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*
        eisEmbedding (a+3*GaussianShiftedPartition.representative a x.val)/eisEmbedding (q*a))

lemma ramifiedAffineGauss_factor (h h1 q r a k : Eis) (j n : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hq : q≠0)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh : h=q*h1) (hk : 3*k=h1+ramifiedAffineParameter j n*a) :
    ramifiedAffineGauss h q r a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
        (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a))*cubicUnitGaussSum k a := by
  rw [ramifiedAffineGauss,cubicUnitGaussSum,←tsum_mul_left]
  apply tsum_congr
  intro x
  let t := GaussianShiftedPartition.representative a x.val
  have hs : symbol (a+3*t) a=symbol (3*t) a := symbol_congr ⟨1,by ring⟩
  change (eisEmbedding (symbol r (a+3*t))*eisEmbedding (symbol (a+3*t) a))*
    ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*t)/eisEmbedding (q*a))=_
  rw [ramified_symbol_primary_shift_signed j n r a t hr hprimary,hs,
    symbol_mul_numerator _ _ _ hprimary]
  rw [map_mul eisEmbedding (symbol 3 a) (symbol t a)]
  have hp := affineCusp_phase_identity h h1 q a k (ramifiedAffineParameter j n) t ha hq hh hk
  calc
    _ = (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol t a))*
      (ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*t)/eisLam/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*t)/eisEmbedding (q*a))) := by ring
    _ = _ := by rw [hp];ring

theorem ramifiedAffineGauss_eq_unramified (h h1 q r a k : Eis) (j n : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hq : q≠0)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh : h=q*h1) (hk : 3*k=h1+ramifiedAffineParameter j n*a) :
    ramifiedAffineGauss h q r a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
        cubicUnitGaussSum (3*r^2*h1) a := by
  rw [ramifiedAffineGauss_factor h h1 q r a k j n ha hprimary hq hr hh hk]
  have hcop := ramified_character_coprime j n r a hr hprimary
  have hcop3 : IsCoprime (3*r^2) a := (primary_coprime_three a hprimary).symm.mul_left hcop.pow_left
  have hp := cubicUnitGaussSum_phase_shift k (r^2) a ha hprimary hcop3
  have hc := symbol_cube_of_isCoprime r a hprimary hcop
  have hchars : eisEmbedding (symbol (r^2) a)*eisEmbedding (symbol (3*r^2) a)=
      eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a) := by
    rw [←map_mul,←symbol_mul_numerator _ _ a hprimary,
      show r^2*(3*r^2)=3*r^4 by ring,symbol_mul_numerator _ _ a hprimary,
      symbol_pow_numerator _ _ hprimary 4,pow_succ,hc,one_mul,map_mul]
    ring
  rw [hchars] at hp
  have hcong : a∣k*(9*r^2)-3*r^2*h1 := by
    refine ⟨3*r^2*ramifiedAffineParameter j n,?_⟩
    linear_combination 3*r^2*hk
  have hg := cubicUnitGaussSum_frequency_congr (k*(9*r^2)) (3*r^2*h1) a ha hcong
  calc
    _ = ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
      (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*cubicUnitGaussSum k a) := by ring
    _ = _ := by rw [hp,hg]

end


open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

local notation "O" => ActualEisensteinCubic.O


end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ConcreteTraceCRT CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O

lemma lowerCuspMatrix_zero : lowerCuspMatrix (0:ActualEisensteinCubic.O)=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerCuspMatrix]


def sourcePrincipalCuspConstant : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*((3*(Real.pi:ℂ))*constantArithmeticResidue)


lemma sourcePrincipalCuspConstant_ne_zero : sourcePrincipalCuspConstant≠0 := by
  unfold sourcePrincipalCuspConstant
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      constantArithmeticResidue_ne_zero


end CubicEisenstein

end

end OAI

end


