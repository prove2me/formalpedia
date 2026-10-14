-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0273_parallel1
-- name    : PNT_ZeroFree_433_0273_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:52:59.108479+00:00
-- url     : https://prove2.me/theorems/190ce842-6185-4e08-bd72-a123f2f3d6bf
-- title:
--   Zero-free region foundations: ChineseRemainder.PrimaryCompletions [0273_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.ChineseRemainder.PrimaryCompletions
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ChineseRemainder/PrimaryCompletions.lean#L83-L577

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0012
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0088
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0121
import Definitions.Def_PNT_ZeroFree_433_0123
import Definitions.Def_PNT_ZeroFree_433_0128_parallel2
import Definitions.Def_PNT_ZeroFree_433_0139_parallel1
import Definitions.Def_PNT_ZeroFree_433_0141_parallel1
import Definitions.Def_PNT_ZeroFree_433_0149_parallel2
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel1
import Definitions.Def_PNT_ZeroFree_433_0182_parallel1
import Definitions.Def_PNT_ZeroFree_433_0183_parallel1
import Definitions.Def_PNT_ZeroFree_433_0190_parallel1
import Definitions.Def_PNT_ZeroFree_433_0209_parallel1
import Definitions.Def_PNT_ZeroFree_433_0214_parallel1
import Definitions.Def_PNT_ZeroFree_433_0226_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ChineseRemainder/PrimaryCompletions.lean
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

namespace ShortDraftCRT
open scoped BigOperators Classical Matrix MatrixGroups

section
open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primary_coprime_nine (a:Eis) (ha:lambda^2∣a-1) : IsCoprime a (9:Eis) := by
  have h3:=primary_coprime_three a ha
  simpa only [show (3:Eis)*3=9 by norm_num] using h3.mul_right h3

lemma nine_coprime_of_not_lambda_dvd (c:Eis) (hc:¬lambda∣c) : IsCoprime (9:Eis) c := by
  have hL:IsCoprime lambda c:=
    PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr hc
  have h3:IsCoprime (3:Eis) c:=(hL.mul_left hL).of_isCoprime_of_dvd_left
    (by simpa only [pow_two] using three_dvd_lambda_sq)
  simpa only [show (3:Eis)*3=9 by norm_num] using h3.mul_left h3


lemma completion_primary_lower_right (a b c d:Eis)
    (hdet:a*d-b*c=1) (ha:(3:Eis)∣a-1) (hb:(3:Eis)∣b) : (3:Eis)∣d-1 := by
  have had:(3:Eis)∣a*d-1:=by
    convert! dvd_mul_of_dvd_left hb c using 1
    linear_combination hdet
  convert! dvd_sub had (dvd_mul_of_dvd_left ha d) using 1 ; ring

lemma completion_negative_upper_right (a b c d:Eis)
    (hdet:a*d-b*c=1) (hc:(3:Eis)∣c-1) (hd:(3:Eis)∣d) : (3:Eis)∣b+1 := by
  have hbc:(3:Eis)∣b*c+1:=by
    convert! dvd_mul_of_dvd_right hd a using 1
    linear_combination -hdet
  convert! dvd_sub hbc (dvd_mul_of_dvd_right hc b) using 1 ; ring


end

section
variable {R:Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
lemma controlled_inverse_sector (B M c a a0 d0:R)
    (hBM:B∣M) (ha:M*c∣a-a0) (hinv:B*c∣a0*d0-1) : B*c∣a*d0-1 := by
  have hdiff:=dvd_mul_of_dvd_left ((mul_dvd_mul_right hBM c).trans ha) d0
  convert! dvd_add hdiff hinv using 1 ; ring

theorem exists_fixed_matrix_completion_controlled
    (B N M c a0 r0 b0 d0 bResidue dResidue:R)
    (hc:c≠0) (hBM:B∣M) (hNM:N∣M)
    (hdet0:a0*d0-b0*(c*r0)=1)
    (hb0:B∣b0-bResidue) (hd0:N∣d0-dResidue) :
    ∀a r:R,M*c∣a-a0→M∣r-r0→IsCoprime r (M*c)→IsCoprime a r→
      ∃b d:R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ B∣b-bResidue ∧ N∣d-dResidue ∧
        (!![a,b;c*r,d]:Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M}))=
        (!![a0,b0;c*r0,d0]:Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M})) := by
  intro a r ha hrr hr har
  obtain ⟨b,d,hdet,hd,hmat⟩:=exists_fixed_matrix_completion M c a0 r0 d0 b0 hc hdet0
    a r ha hrr hr har
  have hbd:B∣b-b0:=hBM.trans (fixed_completion_congr M c r r0 a a0 b b0 d d0 hc
    hr.of_mul_right_left.symm hdet hdet0 ha hd hrr)
  have hdd:N∣d-d0:=(hNM.trans (dvd_mul_right M c)).trans hd
  refine ⟨b,d,hdet,hd,?_,?_,hmat⟩
  · convert! dvd_add hbd hb0 using 1 ; ring
  · convert! dvd_add hdd hd0 using 1 ; ring

end

section
open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal CubicKubota ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O

def controlledCompletionMatrix (a b c d:Eis) (hdet:a*d-b*c=1) : SL(2,Eis) :=
  ⟨!![a,b;c,d],by simpa [Matrix.det_fin_two] using hdet⟩


end

open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O


end ShortDraftCRT


open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def coprimalityMask (m:Eis) : Eis→*ℂ where
  toFun n:=if IsCoprime m n then 1 else 0
  map_one' := by simp only [isCoprime_one_right,ite_true]
  map_mul' x y := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hx:IsCoprime m x <;> by_cases hy:IsCoprime m y <;> simp [hx,hy]

lemma coprimalityMask_norm (m n:Eis) : ‖coprimalityMask m n‖≤1 := by
  change ‖if IsCoprime m n then (1:ℂ) else 0‖≤1
  split_ifs <;> norm_num

lemma isCoprime_congr_mod (m x y:Eis) (hxy:m∣x-y) : IsCoprime m x↔IsCoprime m y := by
  obtain ⟨z,hz⟩:=hxy
  constructor
  · rintro ⟨r,s,hrs⟩
    refine ⟨r+s*z,s,?_⟩
    linear_combination hrs-s*hz
  · rintro ⟨r,s,hrs⟩
    refine ⟨r-s*z,s,?_⟩
    linear_combination hrs+s*hz

lemma coprimalityMask_periodic (m:Eis) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {m}) (coprimalityMask m) := by
  intro x y hxy
  change (if IsCoprime m x then (1:ℂ) else 0)=(if IsCoprime m y then 1 else 0)
  rw [isCoprime_congr_mod m x y (Ideal.mem_span_singleton.mp hxy)]

lemma idealRowHom_prime_sixth_mask (m:Eis) (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P) :
    idealRowHom (m^6) P=if IsCoprime P (Ideal.span {m}) then 1 else 0 := by
  rw [idealRowHom_prime _ P hg]
  have hm:=canonicalSextic_sixth_power_mask P hg m
  rw [hm]
  rw [SixthPowerAverage.prime_coprime_span_iff]
  by_cases hm:m∈P <;> simp [hm]

theorem idealRowHom_sixth_mask (m:Eis) (I:Ideal Eis) (hI:Supported I) :
    idealRowHom (m^6) I=if IsCoprime I (Ideal.span {m}) then 1 else 0 := by
  have hprod (s:Multiset (Ideal Eis))
      (hs:∀P∈s,P.IsMaximal ∧ lambda∉P) :
      idealRowHom (m^6) s.prod=if IsCoprime s.prod (Ideal.span {m}) then 1 else 0 := by
    induction s using Multiset.induction_on with
    | empty =>
      change idealRowHom (m^6) 1=if IsCoprime (1:Ideal Eis) (Ideal.span {m}) then 1 else 0
      simp only [map_one,isCoprime_one_left,ite_true]
    | @cons P s ih =>
      have hp:=hs P (Multiset.mem_cons_self _ _)
      let:P.IsMaximal:=hp.1
      have ht:∀R∈s,R.IsMaximal ∧ lambda∉R:=fun R hR=>hs R (Multiset.mem_cons_of_mem hR)
      rw [Multiset.prod_cons,map_mul,idealRowHom_prime_sixth_mask m P hp.2,ih ht,
        IsCoprime.mul_left_iff]
      by_cases hP:IsCoprime P (Ideal.span {m}) <;>
        by_cases hS:IsCoprime s.prod (Ideal.span {m}) <;> simp [hP,hS]
  have h:=hprod (normalizedFactors I) (fun P hP=>
    ⟨(supported_factors_good I hI P hP).1,(supported_factors_good I hI P hP).2.1⟩)
  rwa [Ideal.prod_normalizedFactors_eq_self hI.1] at h

lemma idealRowHom_sixth_eq_mask (m n:Eis) (hn:Supported (Ideal.span {n})) :
    idealRowHom (m^6) (Ideal.span {n})=coprimalityMask m n := by
  rw [idealRowHom_sixth_mask m _ hn,Ideal.isCoprime_span_singleton_iff]
  change (if IsCoprime n m then (1:ℂ) else 0)=(if IsCoprime m n then 1 else 0)
  rw [isCoprime_comm]

lemma rowTwist_extract_sixth_mask (Ψ:Eis→*ℂ) (m f z n:Eis)
    (hn:Supported (Ideal.span {n})) :
    rowTwist Ψ m f z n=Ψ n*coprimalityMask m n*
      idealRowHom (f^4*z) (Ideal.span {n}) := by
  change Ψ n*idealRowHom (m^6*f^4*z) (Ideal.span {n})=_
  rw [show m^6*f^4*z=m^6*(f^4*z) by ring,idealRowHom_argument_mul,
    idealRowHom_sixth_eq_mask m n hn]
  ring

end CanonicalRowCompletion

open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp


open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_field_inverse {F : Type*} [Field F] (a d B : F) (σ ε : Fˣ) (h x : F)
    (had : a*d=1) (ha : a=(σ:F)*h) (hε : B*(σ:F)*(ε:F)=-1) :
    h≠0 ∧ -d*B⁻¹*x=((ε:F)*x)*h⁻¹ := by
  have hh : h≠0 := by
    intro hz
    rw [ha,hz,mul_zero,zero_mul] at had
    exact zero_ne_one had
  have hB : B≠0 := by
    intro hz
    rw [hz,zero_mul,zero_mul] at hε
    exact neg_ne_zero.mpr (one_ne_zero : (1:F)≠0) hε.symm
  have hd : d=((σ:F)*h)⁻¹ := eq_inv_of_mul_eq_one_right (ha ▸ had)
  have he : (ε:F)=-(B*(σ:F))⁻¹ := by
    have heq : (B*(σ:F))*(-(ε:F))=1 := by linear_combination -hε
    exact neg_eq_iff_eq_neg.mp (eq_inv_of_mul_eq_one_right heq)
  refine ⟨hh,?_⟩
  rw [hd,he]
  field_simp

noncomputable local instance A4quotientField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance A4quotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

lemma A4_active_local {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (a b c0 d : Eis) (hdet : a*d-b*(c0*∏i,p i)=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (x : Eis) (i : ι) :
    h i≠0 ∧
      -(Ideal.Quotient.mk (Ideal.span {p i}) d)*
        (Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i))⁻¹*
        Ideal.Quotient.mk (Ideal.span {p i}) x =
      ((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk (Ideal.span {p i}) x)*(h i)⁻¹ := by
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (∏k,p k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
      (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
  have had : Ideal.Quotient.mk (Ideal.span {p i}) a*
      Ideal.Quotient.mk (Ideal.span {p i}) d=1 := by
    have he := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hdet
    simpa only [map_sub,map_mul,map_one,hz,mul_zero,sub_zero] using he
  exact A4_field_inverse _ _ _ (σ i) (ε i) (h i) _ had (ha i) (hε i)

lemma A4_complement_inverse {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (c0 U w : Eis) (hbez : U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (i : ι) (v t : Eis) (hlocal : t*p i+v*cofactor p i=1) :
    (Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i))⁻¹=
      Ideal.Quotient.mk (Ideal.span {p i}) (w*v) := by
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (∏k,p k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
      (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
  have hp0 : Ideal.Quotient.mk (Ideal.span {p i}) (p i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hw := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hbez
  have hv := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hlocal
  simp only [map_add,map_mul,map_pow,map_one,hz,mul_zero,zero_add] at hw
  simp only [map_add,map_mul,map_one,hp0,mul_zero,zero_add] at hv
  symm
  apply eq_inv_of_mul_eq_one_right
  simp only [map_mul,map_pow]
  calc
    _ = ((Ideal.Quotient.mk _ ramifiedTraceLambda)^3*Ideal.Quotient.mk _ w*
        Ideal.Quotient.mk _ c0)*(Ideal.Quotient.mk _ v*Ideal.Quotient.mk _ (cofactor p i)) := by ring
    _ = 1 := by rw [hw,hv,mul_one]

end ShortDraftCusp

end

end OAI

end


