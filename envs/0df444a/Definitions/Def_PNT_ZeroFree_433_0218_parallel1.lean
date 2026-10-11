-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0218_parallel1
-- name    : PNT_ZeroFree_433_0218_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:43:02.555772+00:00
-- url     : https://prove2.me/theorems/36187e74-5d34-4a1d-89b3-47dba9d54820
-- title:
--   Zero-free region foundations: Reciprocity.KubotaCharacter [0218_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.KubotaCharacter
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/KubotaCharacter.lean#L83-L498

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0046_1_1
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0068_1_1
import Definitions.Def_PNT_ZeroFree_433_0068_1_1_1
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0079_1
import Definitions.Def_PNT_ZeroFree_433_0167
import Definitions.Def_PNT_ZeroFree_433_0327
import Definitions.Def_PNT_ZeroFree_433_0505

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/KubotaCharacter.lean
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

section

open scoped BigOperators Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic
open CubicJacobiGlobal hiding O

def rationalEmbedding : SL(2,ℤ)→*SL(2,ActualEisensteinCubic.O) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ActualEisensteinCubic.O)

def levelThreeConjugate (g : SL(2,ActualEisensteinCubic.O)) (M : levelThree) : levelThree :=
  ⟨g*(M:SL(2,ActualEisensteinCubic.O))*g⁻¹,by
    change Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:ActualEisensteinCubic.O)})) _=1
    rw [map_mul,map_mul,map_inv,M.property,mul_one,mul_inv_cancel]⟩

lemma levelThree_bottom_primary (M : levelThree) : lambda^2∣(M:SL(2,ActualEisensteinCubic.O)) 1 1-1 :=
  lambda_sq_dvd_three.trans (by simpa using levelThree_entry M 1 1)

lemma value_inverse_formula (M : levelThree) :
    value M⁻¹=symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1) := by
  have hd := levelThree_bottom_primary M
  change symbol (((M:SL(2,ActualEisensteinCubic.O))⁻¹) 1 0) (((M:SL(2,ActualEisensteinCubic.O))⁻¹) 0 0)=_
  simp only [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  exact symbol_neg_numerator _ _ hd

lemma value_upper_formula (M : levelThree) :
    value M=symbol ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1) := by
  have hd := levelThree_bottom_primary M
  have hdet : (M:SL(2,ActualEisensteinCubic.O)) 0 0*(M:SL(2,ActualEisensteinCubic.O)) 1 1-
      (M:SL(2,ActualEisensteinCubic.O)) 0 1*(M:SL(2,ActualEisensteinCubic.O)) 1 0=1 := by
    simpa only [Matrix.det_fin_two] using (M:SL(2,ActualEisensteinCubic.O)).property
  have hprod : symbol ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)*
      symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)=1 := by
    rw [←symbol_mul_numerator _ _ _ hd]
    calc
      _ = symbol (-1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1) := by
        apply symbol_congr
        refine ⟨(M:SL(2,ActualEisensteinCubic.O)) 0 0,?_⟩
        linear_combination -hdet
      _ = 1 := symbol_neg_one _ hd
  have hinv : value M*symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)=1 := by
    rw [←value_inverse_formula,←value_mul,mul_inv_cancel,value_one]
  calc
    value M = value M*1 := by rw [mul_one]
    _ = value M*(symbol ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)*
      symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)) := by rw [hprod]
    _ = symbol ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)*
      (value M*symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)) := by ring
    _ = _ := by rw [hinv,mul_one]

theorem value_conjugate_S (M : levelThree) :
    value (levelThreeConjugate (rationalEmbedding ModularGroup.S) M)=value M := by
  rw [value_upper_formula M]
  change symbol (((rationalEmbedding ModularGroup.S)*(M:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding ModularGroup.S)⁻¹) 1 0)
    (((rationalEmbedding ModularGroup.S)*(M:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding ModularGroup.S)⁻¹) 0 0)=_
  simp only [rationalEmbedding,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.coe_inv,ModularGroup.coe_S,Matrix.adjugate_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two]
  simpa using symbol_neg_numerator ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1) (levelThree_bottom_primary M)

theorem complexCharacter_conjugate_S (M : levelThree) :
    complexCharacter (levelThreeConjugate (rationalEmbedding ModularGroup.S) M)=complexCharacter M :=
  congrArg ConcreteTraceCRT.eisEmbedding (value_conjugate_S M)

end CubicKubota

namespace CubicJacobiGlobal
open ActualEisensteinCubic

theorem symbol_shift_by_self (c a : ActualEisensteinCubic.O) (ha : lambda^2∣a-1) (hc : (3:ActualEisensteinCubic.O)∣c) :
    symbol c (a+c)=symbol c a := by
  have hA : lambda^2∣a+c-1 := by
    convert! dvd_add ha (lambda_sq_dvd_three.trans hc) using 1 ; ring
  calc
    symbol c (a+c)=symbol (-a) (a+c) := by
      apply symbol_congr
      refine ⟨1,?_⟩
      ring
    _ = symbol a (a+c) := symbol_neg_numerator a (a+c) hA
    _ = symbol (a+c) a := symbol_reciprocity a (a+c) (primary_ne_zero a ha)
      (primary_ne_zero (a+c) hA) ha hA
    _ = symbol c a := by
      apply symbol_congr
      refine ⟨1,?_⟩
      ring
end CubicJacobiGlobal

namespace CubicKubota
open ActualEisensteinCubic
open CubicJacobiGlobal hiding O

theorem value_conjugate_T (M : levelThree) :
    value (levelThreeConjugate (rationalEmbedding ModularGroup.T) M)=value M := by
  change symbol (((rationalEmbedding ModularGroup.T)*(M:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding ModularGroup.T)⁻¹) 1 0)
    (((rationalEmbedding ModularGroup.T)*(M:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding ModularGroup.T)⁻¹) 0 0)=_
  simp only [rationalEmbedding,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.coe_inv,ModularGroup.coe_T,Matrix.adjugate_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two]
  simpa [value] using symbol_shift_by_self ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 0 0)
    (levelThree_primary M) (levelThree_lower M)

lemma levelThreeConjugate_one (M : levelThree) : levelThreeConjugate 1 M=M := by
  apply Subtype.ext
  simp [levelThreeConjugate]

lemma levelThreeConjugate_mul (g h : SL(2,ActualEisensteinCubic.O)) (M : levelThree) :
    levelThreeConjugate (g*h) M=levelThreeConjugate g (levelThreeConjugate h M) := by
  apply Subtype.ext
  simp [levelThreeConjugate,mul_assoc]

def characterConjugationStabilizer : Subgroup (SL(2,ActualEisensteinCubic.O)) where
  carrier g := ∀M : levelThree,value (levelThreeConjugate g M)=value M
  one_mem' M := by rw [levelThreeConjugate_one]
  mul_mem' hg hh M := by rw [levelThreeConjugate_mul,hg,hh]
  inv_mem' {g} hg M := by
    have h := hg (levelThreeConjugate g⁻¹ M)
    rw [←levelThreeConjugate_mul,mul_inv_cancel,levelThreeConjugate_one] at h
    exact h.symm

theorem value_conjugate_rational (g : SL(2,ℤ)) (M : levelThree) :
    value (levelThreeConjugate (rationalEmbedding g) M)=value M := by
  have htop : characterConjugationStabilizer.comap rationalEmbedding=⊤ := by
    apply top_unique
    rw [←SpecialLinearGroup.SL2Z_generators]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with (rfl|rfl)
    · exact value_conjugate_S
    · exact value_conjugate_T
  have hg : g∈characterConjugationStabilizer.comap rationalEmbedding := by rw [htop];trivial
  exact hg M

theorem complexCharacter_conjugate_rational (g : SL(2,ℤ)) (M : levelThree) :
    complexCharacter (levelThreeConjugate (rationalEmbedding g) M)=complexCharacter M :=
  congrArg ConcreteTraceCRT.eisEmbedding (value_conjugate_rational g M)

end CubicKubota
end

open scoped BigOperators Classical
namespace CubicJacobiGlobal
open ActualEisensteinCubic
open CubicRamified
open CompletedGauss hiding O

def rationalPrimary (n : ℕ) : ActualEisensteinCubic.O := if n%3=1 then (n:ActualEisensteinCubic.O) else -(n:ActualEisensteinCubic.O)

lemma rationalPrimary_coord (n : ℕ) (hn : ¬3∣n) : ∃A : ℤ,rationalPrimary n=primaryCoord A 0 := by
  have hm : n%3=1 ∨ n%3=2 := by
    have hl := Nat.mod_lt n (by decide : 0<3)
    have h0 : n%3≠0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
    omega
  rcases hm with hm|hm
  · refine ⟨(n/3:ℕ),?_⟩
    have he : n=1+3*(n/3) := by omega
    rw [rationalPrimary,if_pos hm,primaryCoord_eq]
    conv_lhs => rw [he]
    simp only [Int.cast_natCast,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,]
    ring
  · refine ⟨-((n/3:ℕ):ℤ)-1,?_⟩
    have he : n=2+3*(n/3) := by omega
    rw [rationalPrimary,if_neg (by omega),primaryCoord_eq]
    conv_lhs => rw [he]
    simp only [Int.cast_sub,Int.cast_neg,Int.cast_natCast,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,]
    ring

lemma rationalPrimary_primary (n : ℕ) (hn : ¬3∣n) : lambda^2∣rationalPrimary n-1 := by
  obtain ⟨A,hA⟩ := rationalPrimary_coord n hn
  rw [hA]
  exact primaryCoord_primary A 0

lemma rationalPrimary_denominator (x : ActualEisensteinCubic.O) (n : ℕ) : symbol x (rationalPrimary n)=symbol x (n:ActualEisensteinCubic.O) := by
  unfold rationalPrimary
  split_ifs
  · rfl
  · simp only [symbol,Ideal.span_singleton_neg]

lemma rationalPrimary_numerator (m n : ℕ) (hn : ¬3∣n) :
    symbol (rationalPrimary m) (rationalPrimary n)=symbol (m:ActualEisensteinCubic.O) (rationalPrimary n) := by
  change symbol (if m%3=1 then (m:ActualEisensteinCubic.O) else -(m:ActualEisensteinCubic.O)) (rationalPrimary n)=_
  split_ifs
  · rfl
  · exact symbol_neg_numerator _ _ (rationalPrimary_primary n hn)

lemma rational_symbol_mul (a b n : ℕ) (hn : ¬3∣n) :
    symbol ((a*b:ℕ):ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=symbol (a:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)*symbol (b:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O) := by
  rw [←rationalPrimary_denominator _ n,←rationalPrimary_denominator (a:ActualEisensteinCubic.O) n,
    ←rationalPrimary_denominator (b:ActualEisensteinCubic.O) n,Nat.cast_mul]
  exact symbol_mul_numerator _ _ _ (rationalPrimary_primary n hn)

lemma rational_symbol_three (n : ℕ) (hn : ¬3∣n) : symbol (3:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=1 := by
  rw [←rationalPrimary_denominator _ n]
  obtain ⟨A,hA⟩ := rationalPrimary_coord n hn
  rw [hA]
  have hprimary := primaryCoord_primary A 0
  have hthree : (3:ActualEisensteinCubic.O)=-((1+2*omega)^2) := by
    have hw : omega^2=-omega-1 := by
      change (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger^2=
        -(IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger-1
      exact IsCyclotomicExtension.Rat.Three.eta_sq (IsCyclotomicExtension.zeta_spec 3 ℚ K)
    linear_combination 4*hw
  have htrace := symbol_traceLambda_eq_linearRay (primaryCoord A 0) hprimary
  change symbol (1+2*omega) (primaryCoord A 0)=_ at htrace
  rw [hthree,symbol_neg_numerator _ _ hprimary,symbol_pow_numerator _ _ hprimary,
    htrace,linearRay_primaryCoord]
  simp

lemma rational_symbol_reciprocity (m n : ℕ) (hm : ¬3∣m) (hn : ¬3∣n) :
    symbol (m:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=symbol (n:ActualEisensteinCubic.O) (m:ActualEisensteinCubic.O) := by
  calc
    _ = symbol (rationalPrimary m) (rationalPrimary n) := by
      rw [rationalPrimary_numerator m n hn,rationalPrimary_denominator]
    _ = symbol (rationalPrimary n) (rationalPrimary m) :=
      symbol_reciprocity _ _ (primary_ne_zero _ (rationalPrimary_primary m hm))
        (primary_ne_zero _ (rationalPrimary_primary n hn))
        (rationalPrimary_primary m hm) (rationalPrimary_primary n hn)
    _ = _ := by rw [rationalPrimary_numerator n m hm,rationalPrimary_denominator]

lemma rational_symbol_mod (m n : ℕ) : symbol (m:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=symbol ((m%n:ℕ):ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O) := by
  apply symbol_congr
  refine ⟨(m/n:ℕ),?_⟩
  have he : m=m%n+n*(m/n) := (Nat.mod_add_div m n).symm
  have hh : (m:ActualEisensteinCubic.O)=(m%n:ℕ)+ (n:ActualEisensteinCubic.O)*(m/n:ℕ) := by exact_mod_cast he
  linear_combination hh

theorem rational_symbol_eq_one (n : ℕ) (hn : ¬3∣n) (m : ℕ) (hmn : Nat.Coprime m n) :
    symbol (m:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=1 := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    by_cases hn1 : n=1
    · subst n
      simpa only [Nat.cast_one] using symbol_one (m:ActualEisensteinCubic.O)
    have hn0 : 0<n := Nat.pos_of_ne_zero (fun h => hn (by rw [h];exact dvd_zero 3))
    have hsmall : ∀r : ℕ,r<n → Nat.Coprime r n → symbol (r:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=1 := by
      intro r
      induction r using Nat.strong_induction_on with
      | h r ihr =>
        intro hrn hcop
        by_cases hr0 : r=0
        · subst r
          have : n=1 := by simpa using hcop
          exact False.elim (hn1 this)
        by_cases hr3 : 3∣r
        · have hquot : r/3<r := Nat.div_lt_self (Nat.pos_of_ne_zero hr0) (by decide)
          have hfactor : r=3*(r/3) := (Nat.mul_div_cancel' hr3).symm
          have hqc : Nat.Coprime (r/3) n := hcop.of_dvd_left (Nat.div_dvd_of_dvd hr3)
          rw [hfactor,rational_symbol_mul _ _ n hn]
          norm_num only [Nat.cast_ofNat]
          rw [rational_symbol_three n hn,one_mul]
          exact ihr (r/3) hquot (lt_trans hquot hrn) hqc
        · rw [rational_symbol_reciprocity r n hr3 hn]
          exact ih r hrn hr3 n hcop.symm
    rw [rational_symbol_mod]
    apply hsmall (m%n) (Nat.mod_lt m hn0)
    change Nat.gcd (m%n) n=1
    rw [←Nat.gcd_rec n m]
    exact hmn.symm

end CubicJacobiGlobal

section

open scoped BigOperators Classical MatrixGroups
namespace CubicJacobiGlobal
open ActualEisensteinCubic

lemma primary_int_natAbs_not_three (a : ℤ) (ha : lambda^2∣(a:ActualEisensteinCubic.O)-1) : ¬3∣a.natAbs := by
  intro h
  have hInt : (3:ℤ)∣a := Int.natCast_dvd.mpr h
  have hO : (3:ActualEisensteinCubic.O)∣(a:ActualEisensteinCubic.O) := by
    rcases hInt with ⟨b,hb⟩
    refine ⟨(b:ActualEisensteinCubic.O),?_⟩
    simpa only [Int.cast_mul,Int.cast_ofNat] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) hb
  have hL2 : lambda∣lambda^2 := dvd_pow_self _ (by decide : (2:ℕ)≠0)
  have hLa := (hL2.trans lambda_sq_dvd_three).trans hO
  have hLa1 := hL2.trans ha
  have h1 : lambda∣(1:ActualEisensteinCubic.O) := by
    convert! dvd_sub hLa hLa1 using 1 ; ring
  exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (isUnit_of_dvd_one h1)

theorem integer_symbol_eq_one (c a : ℤ) (ha : lambda^2∣(a:ActualEisensteinCubic.O)-1)
    (hcop : Nat.Coprime c.natAbs a.natAbs) : symbol (c:ActualEisensteinCubic.O) (a:ActualEisensteinCubic.O)=1 := by
  have hnum : symbol (c:ActualEisensteinCubic.O) (a:ActualEisensteinCubic.O)=symbol (c.natAbs:ActualEisensteinCubic.O) (a:ActualEisensteinCubic.O) := by
    rcases Int.natAbs_eq c with h|h
    · have he : (c:ActualEisensteinCubic.O)=(c.natAbs:ActualEisensteinCubic.O) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) h
      exact congrArg (fun z : ActualEisensteinCubic.O => symbol z (a:ActualEisensteinCubic.O)) he
    · have he : (c:ActualEisensteinCubic.O)=-(c.natAbs:ActualEisensteinCubic.O) := by
        simpa only [Int.cast_neg,Int.cast_natCast] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) h
      exact (congrArg (fun z : ActualEisensteinCubic.O => symbol z (a:ActualEisensteinCubic.O)) he).trans
        (symbol_neg_numerator _ _ ha)
  rw [hnum]
  have hden : symbol (c.natAbs:ActualEisensteinCubic.O) (a:ActualEisensteinCubic.O)=symbol (c.natAbs:ActualEisensteinCubic.O) (a.natAbs:ActualEisensteinCubic.O) := by
    rcases Int.natAbs_eq a with h|h
    · have he : (a:ActualEisensteinCubic.O)=(a.natAbs:ActualEisensteinCubic.O) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) h
      exact congrArg (symbol (c.natAbs:ActualEisensteinCubic.O)) he
    · have he : (a:ActualEisensteinCubic.O)=-(a.natAbs:ActualEisensteinCubic.O) := by
        simpa only [Int.cast_neg,Int.cast_natCast] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) h
      rw [he]
      simp only [symbol,Ideal.span_singleton_neg]
  rw [hden]
  exact rational_symbol_eq_one a.natAbs (primary_int_natAbs_not_three a ha) c.natAbs hcop
end CubicJacobiGlobal

namespace CubicKubota

section
open ActualEisensteinCubic
open CubicJacobiGlobal hiding O

theorem value_rational_intersection (g : SL(2,ℤ)) (hg : rationalEmbedding g∈levelThree) :
    value ⟨rationalEmbedding g,hg⟩=1 := by
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hcop : IsCoprime (g 1 0) (g 0 0) := by
    refine ⟨-(g 0 1),g 1 1,?_⟩
    linear_combination hdet
  have hp := levelThree_primary ⟨rationalEmbedding g,hg⟩
  change lambda^2∣((g 0 0:ℤ):ActualEisensteinCubic.O)-1 at hp
  change symbol ((g 1 0:ℤ):ActualEisensteinCubic.O) ((g 0 0:ℤ):ActualEisensteinCubic.O)=1
  exact integer_symbol_eq_one (g 1 0) (g 0 0) hp (Int.isCoprime_iff_nat_coprime.mp hcop)

theorem complexCharacter_rational_intersection (g : SL(2,ℤ)) (hg : rationalEmbedding g∈levelThree) :
    complexCharacter ⟨rationalEmbedding g,hg⟩=1 := by
  change ConcreteTraceCRT.eisEmbedding (value ⟨rationalEmbedding g,hg⟩)=1
  rw [value_rational_intersection g hg,map_one]

end

open ActualEisensteinCubic

def levelTwo : Subgroup (SL(2,ActualEisensteinCubic.O)) where
  carrier g := ∃n : levelThree,∃r : SL(2,ℤ),(n:SL(2,ActualEisensteinCubic.O))*rationalEmbedding r=g
  one_mem' := ⟨1,1,by simp⟩
  mul_mem' := by
    rintro g h ⟨n,r,rfl⟩ ⟨m,s,rfl⟩
    refine ⟨n*levelThreeConjugate (rationalEmbedding r) m,r*s,?_⟩
    simp [levelThreeConjugate,map_mul,mul_assoc]
  inv_mem' := by
    rintro g ⟨n,r,rfl⟩
    refine ⟨levelThreeConjugate (rationalEmbedding r⁻¹) n⁻¹,r⁻¹,?_⟩
    simp [levelThreeConjugate,map_inv,mul_assoc]

lemma levelThree_le_levelTwo : levelThree≤levelTwo := by
  intro g hg
  exact ⟨⟨g,hg⟩,1,by simp⟩

lemma rational_mem_levelTwo (r : SL(2,ℤ)) : rationalEmbedding r∈levelTwo :=
  ⟨1,r,by simp⟩

lemma levelTwo_eq_sup : levelTwo=levelThree⊔rationalEmbedding.range := by
  apply le_antisymm
  · rintro g ⟨n,r,rfl⟩
    exact Subgroup.mul_mem _
      ((show levelThree≤levelThree⊔rationalEmbedding.range from le_sup_left) n.property)
      ((show rationalEmbedding.range≤levelThree⊔rationalEmbedding.range from le_sup_right) ⟨r,rfl⟩)
  · apply sup_le levelThree_le_levelTwo
    rintro g ⟨r,rfl⟩
    exact rational_mem_levelTwo r

lemma complexCharacter_product_well_defined (n m : levelThree) (r s : SL(2,ℤ))
    (h : (n:SL(2,ActualEisensteinCubic.O))*rationalEmbedding r=(m:SL(2,ActualEisensteinCubic.O))*rationalEmbedding s) :
    complexCharacter n=complexCharacter m := by
  have he : ((m⁻¹*n:levelThree):SL(2,ActualEisensteinCubic.O))=rationalEmbedding (s*r⁻¹) := by
    have hh := congrArg (fun g : SL(2,ActualEisensteinCubic.O)=>(m:SL(2,ActualEisensteinCubic.O))⁻¹*g*(rationalEmbedding r)⁻¹) h
    simpa [map_mul,map_inv,mul_assoc] using hh
  have hm : rationalEmbedding (s*r⁻¹)∈levelThree := he ▸ (m⁻¹*n).property
  have hv : complexCharacter (m⁻¹*n)=1 := by
    have he' : (m⁻¹*n:levelThree)=⟨rationalEmbedding (s*r⁻¹),hm⟩ := Subtype.ext he
    rw [he']
    exact complexCharacter_rational_intersection (s*r⁻¹) hm
  calc
    complexCharacter n=complexCharacter (m*(m⁻¹*n)) := by rw [mul_inv_cancel_left]
    _ = complexCharacter m*complexCharacter (m⁻¹*n) := map_mul _ _ _
    _ = complexCharacter m := by rw [hv,mul_one]

def levelTwoLeft (g : levelTwo) : levelThree := g.property.choose

def levelTwoRight (g : levelTwo) : SL(2,ℤ) := g.property.choose_spec.choose

lemma levelTwo_product (g : levelTwo) :
    (levelTwoLeft g:SL(2,ActualEisensteinCubic.O))*rationalEmbedding (levelTwoRight g)=(g:SL(2,ActualEisensteinCubic.O)) :=
  g.property.choose_spec.choose_spec

def levelTwoValue (g : levelTwo) : ℂ := complexCharacter (levelTwoLeft g)

lemma levelTwoValue_of_product (g : levelTwo) (n : levelThree) (r : SL(2,ℤ))
    (h : (n:SL(2,ActualEisensteinCubic.O))*rationalEmbedding r=(g:SL(2,ActualEisensteinCubic.O))) : levelTwoValue g=complexCharacter n :=
  complexCharacter_product_well_defined (levelTwoLeft g) n (levelTwoRight g) r
    ((levelTwo_product g).trans h.symm)

def levelTwoComplexCharacter : levelTwo→*ℂ where
  toFun := levelTwoValue
  map_one' := by
    rw [levelTwoValue_of_product 1 1 1 (by simp),map_one]
  map_mul' g h := by
    have hp :
        ((levelTwoLeft g*levelThreeConjugate (rationalEmbedding (levelTwoRight g)) (levelTwoLeft h):levelThree):SL(2,ActualEisensteinCubic.O))*
          rationalEmbedding (levelTwoRight g*levelTwoRight h)=((g*h:levelTwo):SL(2,ActualEisensteinCubic.O)) := by
      simp only [Subgroup.coe_mul,levelThreeConjugate,map_mul]
      simp only [mul_assoc,inv_mul_cancel_left]
      rw [←levelTwo_product g,←levelTwo_product h]
      group
    rw [levelTwoValue_of_product (g*h) _ _ hp,map_mul,complexCharacter_conjugate_rational]
    rfl

lemma levelTwoComplexCharacter_restrict (n : levelThree) :
    levelTwoComplexCharacter ⟨(n:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo n.property⟩=complexCharacter n := by
  exact levelTwoValue_of_product _ n 1 (by simp)

lemma levelTwoComplexCharacter_rational (r : SL(2,ℤ)) :
    levelTwoComplexCharacter ⟨rationalEmbedding r,rational_mem_levelTwo r⟩=1 := by
  exact (levelTwoValue_of_product _ 1 r (by simp)).trans (map_one _)

lemma levelTwoComplexCharacter_cube (g : levelTwo) : levelTwoComplexCharacter g^3=1 :=
  complexCharacter_cube (levelTwoLeft g)

lemma norm_levelTwoComplexCharacter (g : levelTwo) : ‖levelTwoComplexCharacter g‖=1 :=
  norm_complexCharacter (levelTwoLeft g)

end CubicKubota
end


end

end OAI

end


