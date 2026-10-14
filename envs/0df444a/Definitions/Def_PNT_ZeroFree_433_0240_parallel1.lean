-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0240_parallel1
-- name    : PNT_ZeroFree_433_0240_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:14:46.229005+00:00
-- url     : https://prove2.me/theorems/8a733541-c64b-4f1f-946a-d692b78bc2dd
-- title:
--   Zero-free region foundations: Eisenstein.CuspDilation [0240_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CuspDilation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CuspDilation.lean#L84-L568

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0014
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0019
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0046_1_1
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0068_1_1
import Definitions.Def_PNT_ZeroFree_433_0068_1_1_1
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0088
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0154_parallel1
import Definitions.Def_PNT_ZeroFree_433_0183_parallel1
import Definitions.Def_PNT_ZeroFree_433_0197_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0224_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CuspDilation.lean
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

def ramifiedTraceLambda : Eis := 1+2*omega

lemma ramifiedEmbedding_traceLambda : eisEmbedding ramifiedTraceLambda=eisLam := by
  change eisEmbedding (1+2*omega)=1+2*EisensteinEmbedding.omega3
  rw [map_add,map_one,map_mul,map_ofNat,eisEmbedding_omega_actual]

lemma breveE_embedding_third_eval (A B : ℤ) :
    ShortDraftTrace.breveE (eisEmbedding (ActualEisensteinCoordinates.eval A B)/3)=
      eisEmbedding (cubicExp (2*A-B)) := by
  have htrace : ramifiedTraceLambda=ActualEisensteinCoordinates.eval 1 2 := by
    change 1+2*omega=(1:Eis)+(2:Eis)*omega
    rfl
  have h := breveE_real_trace_of_O (3:ℝ)
    (ActualEisensteinCoordinates.eval A B*ramifiedTraceLambda)
  rw [map_mul,ramifiedEmbedding_traceLambda,mul_div_cancel_right₀ _ eisLam_ne_zero] at h
  rw [htrace,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval] at h
  norm_num only [Complex.ofReal_ofNat] at h
  rw [h,embedding_cubicExp]
  congr 3
  ring_nf

lemma primary_add_three (a r : Eis) (ha : lambda^2∣a-1) :
    lambda^2∣a+3*r-1 := by
  have h3 : (3:Eis)∣a-1 := three_dvd_lambda_sq.trans ha
  exact lambda_sq_dvd_three.trans (by
    convert! dvd_add h3 (dvd_mul_right (3:Eis) r) using 1 ;ring)

lemma symbol_omega_pow_primary_shift (j : ℕ) (a r : Eis) (ha : lambda^2∣a-1) :
    eisEmbedding (symbol (omega^j) (a+3*r))=
      eisEmbedding (symbol (omega^j) a)*
        ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3) := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  let C := (ActualEisensteinCoordinates.coords r).1
  let D := (ActualEisensteinCoordinates.coords r).2
  have hr : r=ActualEisensteinCoordinates.eval C D := (ActualEisensteinCoordinates.eval_coords r).symm
  have hsum : primaryCoord A B+3*r=primaryCoord (A+C) (B+D) := by
    rw [hr,primaryCoord_eq,primaryCoord_eq]
    change 1+3*(A:Eis)+3*(B:Eis)*omega+3*((C:Eis)+(D:Eis)*omega)=_
    push_cast
    ring
  rw [hsum,symbol_pow_numerator _ _ (primaryCoord_primary _ _) j,
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) j,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),
    linearRay_primaryCoord,linearRay_primaryCoord,map_pow,map_pow]
  have hp : ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3)=
      (ShortDraftTrace.breveE (eisEmbedding r/3))^j := by
    simpa only [nsmul_eq_mul,mul_div_assoc] using
      AddChar.map_nsmul_eq_pow ShortDraftTrace.breveE j (eisEmbedding r/3)
  rw [hp,hr,breveE_embedding_third_eval]
  rw [show 2*(A+C)+(-1)*(B+D)=(2*A+(-1)*B)+(2*C-D) by ring,
    cubicExp_add,map_mul,mul_pow]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def ninthCuspFrequency (h : Eis) : ℂ := cuspFrequency h/3

def unitLowerGauss (h : Eis) (u : Eisˣ) (a : Eis) : ℂ :=
  ∑'r:CubicUnitResidue a,
    (eisEmbedding (symbol (u:Eis) (a+3*GaussianShiftedPartition.representative a r.val))*
      eisEmbedding (symbol (a+3*GaussianShiftedPartition.representative a r.val) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*
        eisEmbedding (a+3*GaussianShiftedPartition.representative a r.val)/eisEmbedding ((u:Eis)*a))

lemma unitLower_phase_identity (h a r k : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3)*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a))=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*residueAdditive (3*k) a r := by
  have ha0 := eisEmbedding_ne_zero ha
  have hu0 := eisEmbedding_ne_zero u.ne_zero
  have hui : eisEmbedding (↑u⁻¹:Eis)=(eisEmbedding (u:Eis))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [←map_mul]
    simp
  have hk' : 3*eisEmbedding k=eisEmbedding h/(eisEmbedding (u:Eis))+
      (j:ℂ)*eisEmbedding a*eisLam := by
    have he := congrArg eisEmbedding hk
    simpa only [map_mul,map_add,map_ofNat,map_natCast,hui,ramifiedEmbedding_traceLambda,
      div_eq_mul_inv] using he
  have hkk : eisEmbedding k=(eisEmbedding h/eisEmbedding (u:Eis)+
      (j:ℂ)*eisEmbedding a*eisLam)/3 := by
    apply (eq_div_iff (by norm_num : (3:ℂ)≠0)).mpr
    linear_combination hk'
  rw [←AddChar.map_add_eq_mul]
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  apply congrArg ShortDraftTrace.breveE
  simp only [ninthCuspFrequency,cuspFrequency,map_add,map_mul,map_ofNat]
  rw [hkk]
  field_simp [ha0,hu0,eisLam_ne_zero]
  ;ring

lemma unitLowerGauss_factor (h a k : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    unitLowerGauss h u a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
        (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a))*cubicUnitGaussSum k a := by
  rw [unitLowerGauss,cubicUnitGaussSum,←tsum_mul_left]
  apply tsum_congr
  intro r
  let x := GaussianShiftedPartition.representative a r.val
  have hchar : eisEmbedding (symbol (u:Eis) (a+3*x))=
      eisEmbedding (symbol (u:Eis) a)*ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding x/3) := by
    rw [hu]
    exact symbol_omega_pow_primary_shift j a x hprimary
  have hs : symbol (a+3*x) a=symbol (3*x) a := symbol_congr ⟨1,by ring⟩
  change (eisEmbedding (symbol (u:Eis) (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
    ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding ((u:Eis)*a))=_
  rw [hchar,hs,symbol_mul_numerator _ _ _ hprimary,map_mul]
  have hp := unitLower_phase_identity h a x k u j ha hk
  calc
    _ = (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol x a))*
      (ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding x/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding ((u:Eis)*a))) := by ring
    _ = _ := by rw [hp];ring

theorem unitLowerGauss_eq_unramified (h a k : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    unitLowerGauss h u a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
        cubicUnitGaussSum (3*h*(u:Eis)) a := by
  rw [unitLowerGauss_factor h a k u j ha hprimary hu hk]
  have hu3 : (u:Eis)^3=1 := by
    rw [hu,←pow_mul,mul_comm j 3,pow_mul,omega_primitive.pow_eq_one,one_pow]
  have hu4 : (u:Eis)^4=(u:Eis) := by
    rw [show (4:ℕ)=3+1 by rfl,pow_add,hu3,pow_one,one_mul]
  have hcop : IsCoprime (3*(u:Eis)^2) a :=
    (isCoprime_mul_unit_right_left (u.isUnit.pow 2) 3 a).mpr
      (primary_coprime_three a hprimary).symm
  have hphase := cubicUnitGaussSum_phase_shift k ((u:Eis)^2) a ha hprimary hcop
  have hchars : eisEmbedding (symbol ((u:Eis)^2) a)*eisEmbedding (symbol (3*(u:Eis)^2) a)=
      eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a) := by
    rw [←map_mul,←symbol_mul_numerator _ _ a hprimary]
    rw [show (u:Eis)^2*(3*(u:Eis)^2)=3*(u:Eis)^4 by ring,hu4,
      symbol_mul_numerator _ _ a hprimary,map_mul]
    ring
  rw [hchars] at hphase
  have hcong : a∣k*(9*(u:Eis)^2)-3*h*(u:Eis) := by
    refine ⟨3*(j:Eis)*ramifiedTraceLambda*(u:Eis)^2,?_⟩
    have hi : (↑u⁻¹:Eis)*(u:Eis)^2=(u:Eis) := by
      rw [pow_two,←mul_assoc]
      simp
    have he := congrArg (fun z:Eis=>3*(u:Eis)^2*z) hk
    have hi' : (u:Eis)^2*(↑u⁻¹:Eis)=(u:Eis) := by simpa only [mul_comm] using hi
    linear_combination he+3*h*hi'
  have hg := cubicUnitGaussSum_frequency_congr (k*(9*(u:Eis)^2)) (3*h*(u:Eis)) a ha hcong
  calc
    _ = ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
      (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)*cubicUnitGaussSum k a) := by ring
    _ = _ := by rw [hphase,hg]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def UnitCuspFrequency (h : Eis) (u : Eisˣ) (j : ℕ) : Prop :=
  (3:Eis)∣h*(↑u⁻¹:Eis)+(j:Eis)*ramifiedTraceLambda

lemma unitCuspFrequency_lift (h a : Eis) (u : Eisˣ) (j : ℕ)
    (ha : lambda^2∣a-1) (hh : UnitCuspFrequency h u j) :
    ∃k:Eis,3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda := by
  obtain ⟨q,hq⟩ := hh
  obtain ⟨r,hr⟩ := three_dvd_lambda_sq.trans ha
  refine ⟨q+(j:Eis)*r*ramifiedTraceLambda,?_⟩
  linear_combination -hq-(j:Eis)*ramifiedTraceLambda*hr

lemma unitLowerGauss_eq_unramified_of_frequency (h : Eis) (a : PrimaryLower)
    (u : Eisˣ) (j : ℕ) (hu : (u:Eis)=omega^j) (hh : UnitCuspFrequency h u j) :
    unitLowerGauss h u a.val=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
        cubicUnitGaussSum (3*h*(u:Eis)) a.val := by
  obtain ⟨k,hk⟩ := unitCuspFrequency_lift h a.val u j (primaryLower_primary a) hh
  exact unitLowerGauss_eq_unramified h a.val k u j (primaryLower_ne_zero a)
    (primaryLower_primary a) hu hk

def unitCuspArithmeticSeries (s : ℂ) (h : Eis) (u : Eisˣ) : ℂ :=
  ∑'a:PrimaryLower,((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*unitLowerGauss h u a.val

theorem unitCuspArithmeticSeries_eq (s : ℂ) (h : Eis) (u : Eisˣ) (j : ℕ)
    (hu : (u:Eis)=omega^j) (hh : UnitCuspFrequency h u j) :
    unitCuspArithmeticSeries s h u=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
        unramifiedCubicGaussSeries s (3*h*(u:Eis)) := by
  rw [unitCuspArithmeticSeries,←primaryLowerIdealEquiv.symm.tsum_eq,
    unramifiedCubicGaussSeries,←tsum_mul_left]
  apply tsum_congr
  intro I
  rw [unitLowerGauss_eq_unramified_of_frequency h _ u j hu hh]
  change ((‖eisEmbedding (primaryGenerator I.val)‖^2:ℝ):ℂ)^(-s)*
    (ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
      cubicUnitGaussSum (3*h*(u:Eis)) (primaryGenerator I.val))=_
  rw [eisEmbedding_norm_sq_eq_absNorm_span,(primaryGenerator_spec I.val I.2).1,
    Complex.ofReal_natCast]
  ring

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology


open scoped Classical MatrixGroups
namespace CubicKubota

section
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_congruent_cusp_completion (A : SL(2,Eis)) (x y : Eis)
    (hxy : IsCoprime x y) (hx : (3:Eis)∣x-A 0 0) (hy : (3:Eis)∣y-A 1 0) :
    ∃ N : SL(2,Eis), N 0 0=x ∧ N 1 0=y ∧ N*A⁻¹∈levelThree := by
  obtain ⟨u,v,huv⟩ := hxy
  let t := u*A 0 1+v*A 1 1
  let N : SL(2,Eis) := ⟨!![x,-v+x*t;y,u+y*t],by
    rw [Matrix.det_fin_two_of]
    linear_combination huv⟩
  have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hr : (3:Eis)∣1+y*A 0 1-x*A 1 1 := by
    convert! dvd_sub (dvd_mul_of_dvd_left hy (A 0 1))
      (dvd_mul_of_dvd_left hx (A 1 1)) using 1 ; linear_combination -hd
  have hmod : ∀i j,(3:Eis)∣N i j-A i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hx
    · have hv := dvd_mul_of_dvd_left hr (-v)
      convert! hv using 1 ; dsimp [N,t] ; linear_combination (A 0 1)*huv
    · exact hy
    · have hu := dvd_mul_of_dvd_left hr u
      convert! hu using 1 ; dsimp [N,t] ; linear_combination (A 1 1)*huv
  have hq : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) N =
      Matrix.SpecialLinearGroup.map (n:=Fin 2)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) A := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (hmod i j))
  refine ⟨N,rfl,rfl,?_⟩
  change Matrix.SpecialLinearGroup.map (n:=Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (N*A⁻¹)=1
  rw [map_mul,map_inv,hq,mul_inv_cancel]

lemma cusp_completion_upper_factor (A N : SL(2,Eis)) (q g x y : Eis)
    (hx : A 0 0+3*q*A 1 0=g*N 0 0) (hy : x*A 1 0=g*N 1 0)
    (hg : g≠0) (hdet : x=g*y) :
    N.val⁻¹ * (!![1,3*q;0,x] * A.val) =
      !![g,(N.val⁻¹ * (!![1,3*q;0,x] * A.val)) 0 1;0,y] := by
  have hNdet : N 0 0*N 1 1-N 0 1*N 1 0=1 := by
    simpa only [Matrix.det_fin_two] using N.property
  have hAdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hinv : N.val⁻¹ = !![N 1 1,-N 0 1;-N 1 0,N 0 0] := by
    rw [Matrix.inv_def,Matrix.SpecialLinearGroup.det_coe,Ring.inverse_one,one_smul,Matrix.adjugate_fin_two]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    rw [hx,hy]
    linear_combination g*hNdet
  · rfl
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    rw [hx,hy]
    ring
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    apply mul_left_cancel₀ hg
    linear_combination x*hAdet-x*(A 1 1)*hx+(A 0 1+3*q*A 1 1)*hy+hdet

end


end CubicKubota

end

end OAI

end


