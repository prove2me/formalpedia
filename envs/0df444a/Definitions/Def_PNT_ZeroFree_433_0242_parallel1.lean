-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0242_parallel1
-- name    : PNT_ZeroFree_433_0242_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:30:53.742646+00:00
-- url     : https://prove2.me/theorems/5584f0cb-a2a2-4702-8e41-c76888dea219
-- title:
--   Zero-free region foundations: Reciprocity.PrimaryCongruences [0242_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.PrimaryCongruences
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/PrimaryCongruences.lean#L83-L459

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0044
import Definitions.Def_PNT_ZeroFree_433_0046_1_1
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0068_1_1_1
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0094
import Definitions.Def_PNT_ZeroFree_433_0216_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0219_parallel1
import Definitions.Def_PNT_ZeroFree_433_0222_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel1
import Definitions.Def_PNT_ZeroFree_433_0241_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel1
import Definitions.Def_PNT_ZeroFree_433_0506_parallel1

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

section

open scoped Classical MatrixGroups
namespace CubicJacobiGlobal
open ActualEisensteinCubic CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma integer_congruence_primary_cases (c : Eis) (r : ℤ) (h : (3:Eis)∣c-(r:Eis)) :
    (3:Eis)∣c ∨ lambda^2∣c-1 ∨ lambda^2∣(-c)-1 := by
  have hr : (3:ℤ)∣r ∨ (3:ℤ)∣r-1 ∨ (3:ℤ)∣r+1 := by omega
  rcases hr with hr|hr|hr
  · left
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis):=⟨(t:Eis),by exact_mod_cast ht⟩
    simpa using dvd_add h hn
  · right;left
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis)-1:=⟨(t:Eis),by exact_mod_cast ht⟩
    exact lambda_sq_dvd_three.trans (by simpa using dvd_add h hn)
  · right;right
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis)+1:=⟨(t:Eis),by exact_mod_cast ht⟩
    apply lambda_sq_dvd_three.trans
    convert! dvd_neg.mpr (dvd_add h hn) using 1 ; ring

lemma symbol_three_shift_primary (c a t:Eis) (hc:lambda^2∣c-1) (ha:lambda^2∣a-1) :
    symbol c (a+3*t*c)=symbol c a := by
  have hs:=primary_add_multiple_three a c t ha
  calc
    _=symbol (a+3*t*c) c:=symbol_reciprocity _ _ (primary_ne_zero _ hc) (primary_ne_zero _ hs) hc hs
    _=symbol a c:=symbol_congr ⟨3*t,by ring⟩
    _=symbol c a:=(symbol_reciprocity _ _ (primary_ne_zero _ hc) (primary_ne_zero _ ha) hc ha).symm

lemma symbol_three_shift_integer (c a t:Eis) (r:ℤ)
    (ha:lambda^2∣a-1) (hc:(3:Eis)∣c-(r:Eis)) :
    symbol c (a+3*t*c)=symbol c a := by
  rcases integer_congruence_primary_cases c r hc with h|h|h
  · exact symbol_three_shift c a t ha h
  · exact symbol_three_shift_primary c a t h ha
  · have hh:=symbol_three_shift_primary (-c) a (-t) h ha
    have he:a+3*(-t)*(-c)=a+3*t*c:=by ring
    rw [he,symbol_neg_numerator _ _ (primary_add_multiple_three a c t ha),
      symbol_neg_numerator _ _ ha] at hh
    exact hh

end CubicJacobiGlobal
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma levelTwo_cube_phase_balance (A N:levelTwo) (p q:Eis) (j:ℕ)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=p^j*(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^(3-j)*(A:SL(2,Eis)) 1 0) :
    levelTwoComplexCharacter N *
        eisEmbedding (symbol ((A:SL(2,Eis)) 1 0) p)^j =
      levelTwoComplexCharacter A *
        eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)^(3-j) := by
  have hs : symbol ((A:SL(2,Eis)) 1 0) ((A:SL(2,Eis)) 0 0) =
      symbol ((A:SL(2,Eis)) 1 0) p ^ j *
        symbol ((A:SL(2,Eis)) 1 0) ((N:SL(2,Eis)) 0 0) := by
    rw [←symbol_three_shift_integer _ _ q (levelTwoRight A 1 0) hA (levelTwo_entry_integer A 1 0),
      hx,symbol_mul_denominator,cubicSymbol_pow_denominator]
  rw [levelTwoComplexCharacter_primary N hN,levelTwoComplexCharacter_primary A hA,hc,
    symbol_mul_numerator _ _ _ hN,symbol_pow_numerator _ _ hN,
    symbol_reciprocity p ((N:SL(2,Eis)) 0 0) (primary_ne_zero _ hp) (primary_ne_zero _ hN) hp hN,
    hs,map_mul,map_pow,map_mul,map_pow]
  ring

lemma levelTwo_comparison_character (A N:levelTwo)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩ *
        levelTwoComplexCharacter A = levelTwoComplexCharacter N := by
  rw [←levelTwoComplexCharacter_restrict ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩]
  change levelTwoComplexCharacter (N*A⁻¹)*levelTwoComplexCharacter A=levelTwoComplexCharacter N
  rw [map_mul,map_inv,mul_assoc]
  have hA:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  rw [inv_mul_cancel₀ hA,mul_one]

lemma levelTwo_cube_comparison_phase (A N:levelTwo) (p q:Eis) (j:ℕ) (hj:j≤3)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=p^j*(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^(3-j)*(A:SL(2,Eis)) 1 0)
    (hC:IsCoprime ((A:SL(2,Eis)) 1 0) p)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩ =
      eisEmbedding (symbol (((N:SL(2,Eis)) 0 0)*((A:SL(2,Eis)) 1 0)) p)^(3-j) := by
  let a:=eisEmbedding (symbol ((A:SL(2,Eis)) 1 0) p)
  let b:=eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)
  have ha3:a^3=1:=by
    dsimp [a]
    rw [←map_pow,symbol_cube_of_isCoprime _ _ hp hC,map_one]
  have hpow:a^j*a^(3-j)=1:=by rw [←pow_add,Nat.add_sub_of_le hj,ha3]
  have hbal:=levelTwo_cube_phase_balance A N p q j hp hA hN hx hc
  change levelTwoComplexCharacter N*a^j=levelTwoComplexCharacter A*b^(3-j) at hbal
  have he:levelTwoComplexCharacter N=levelTwoComplexCharacter A*(b*a)^(3-j):=by
    calc
      _=levelTwoComplexCharacter N*(a^j*a^(3-j)):=by rw [hpow,mul_one]
      _=(levelTwoComplexCharacter N*a^j)*a^(3-j):=(mul_assoc _ _ _).symm
      _=(levelTwoComplexCharacter A*b^(3-j))*a^(3-j):=by rw [hbal]
      _=_:=by rw [mul_pow];ring
  have hcomp:=levelTwo_comparison_character A N hNA
  have hbase:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  rw [symbol_mul_numerator _ _ _ hp,map_mul]
  change complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩=(b*a)^(3-j)
  apply mul_right_cancel₀ hbase
  rw [hcomp,he]
  ring

end CubicKubota
end

open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_cubicExp_nat_mul (n : ℕ) (t : ℤ) :
    cubicExp ((n:ℤ)*t)=cubicExp t^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,cubicExp_add,ih,pow_succ]


end


section
open Filter MeasureTheory
open scoped BigOperators Classical Topology Pointwise

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def eisensteinUnitRotation (u : ActualEisensteinCubic.Oˣ) : ℂ≃ₗᵢ[ℝ]ℂ where
  toFun z := eisEmbedding (u:ActualEisensteinCubic.O)*z
  invFun z := eisEmbedding (↑u⁻¹:ActualEisensteinCubic.O)*z
  left_inv z := by
    dsimp only
    rw [←mul_assoc,←map_mul]
    simp
  right_inv z := by
    dsimp only
    rw [←mul_assoc,←map_mul]
    simp
  map_add' z w := mul_add _ _ _
  map_smul' t z := by
    simp only [RingHom.id_apply,Complex.real_smul]
    ring
  norm_map' z := by
    change ‖eisEmbedding (u:ActualEisensteinCubic.O)*z‖=‖z‖
    rw [norm_mul,GaussGeneratorTransport.norm_eisEmbedding_unit,one_mul]

def eisensteinUnitEquiv (u : ActualEisensteinCubic.Oˣ) : ActualEisensteinCubic.O≃ActualEisensteinCubic.O where
  toFun x := (u:ActualEisensteinCubic.O)*x
  invFun x := (↑u⁻¹:ActualEisensteinCubic.O)*x
  left_inv x := by dsimp only; rw [←mul_assoc];simp
  right_inv x := by dsimp only; rw [←mul_assoc];simp

def periodUnitEquiv (u : ActualEisensteinCubic.Oˣ) : periodLattice≃periodLattice :=
  (periodEquiv.symm.trans (eisensteinUnitEquiv u)).trans periodEquiv

lemma periodUnitEquiv_val (u : ActualEisensteinCubic.Oˣ) (x : periodLattice) :
    (periodUnitEquiv u x:ℂ)=eisEmbedding (u:ActualEisensteinCubic.O)*(x:ℂ) := by
  obtain ⟨n,rfl⟩ := periodEquiv.surjective x
  dsimp only [periodUnitEquiv,Equiv.trans_apply]
  rw [Equiv.symm_apply_apply]
  change (periodEquiv ((u:ActualEisensteinCubic.O)*n):ℂ)=eisEmbedding (u:ActualEisensteinCubic.O)*(periodEquiv n:ℂ)
  change 3*eisEmbedding ((u:ActualEisensteinCubic.O)*n)=eisEmbedding (u:ActualEisensteinCubic.O)*(3*eisEmbedding n)
  rw [map_mul]
  ring

lemma periodDomain_unit_rotation (u : ActualEisensteinCubic.Oˣ) :
    IsAddFundamentalDomain periodLattice (eisensteinUnitRotation u '' periodDomain) volume := by
  apply periodDomain_fundamental.image_of_equiv (eisensteinUnitRotation u).toEquiv
    (eisensteinUnitRotation u).symm.measurePreserving.quasiMeasurePreserving (periodUnitEquiv u⁻¹)
  intro n z
  change eisEmbedding (u:ActualEisensteinCubic.O)*((periodUnitEquiv u⁻¹ n:ℂ)+z)=
    (n:ℂ)+eisEmbedding (u:ActualEisensteinCubic.O)*z
  rw [periodUnitEquiv_val,mul_add,←mul_assoc,←map_mul]
  simp

theorem period_integral_unit_rotation (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (u : ActualEisensteinCubic.Oˣ) :
    (∫z in periodDomain,f (eisEmbedding (u:ActualEisensteinCubic.O)*z))=∫z in periodDomain,f z := by
  have hperiod (n : periodLattice) (z : ℂ) : f (n+ᵥz)=f z := by
    obtain ⟨m,rfl⟩ := periodEquiv.surjective n
    change f (3*eisEmbedding m+z)=f z
    simpa only [add_comm] using hp m z
  have heq := periodDomain_fundamental.setIntegral_eq (periodDomain_unit_rotation u) hperiod
  have hchange := (eisensteinUnitRotation u).measurePreserving.setIntegral_image_emb
    (eisensteinUnitRotation u).toHomeomorph.measurableEmbedding f periodDomain
  exact hchange.symm.trans heq.symm

theorem period_integral_unit_affine (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (u : ActualEisensteinCubic.Oˣ) (b : ℂ) :
    (∫z in periodDomain,f (eisEmbedding (u:ActualEisensteinCubic.O)*z+b))=∫z in periodDomain,f z := by
  have hg : ∀n : ActualEisensteinCubic.O,∀z : ℂ,(fun w=>f (w+b)) (z+3*eisEmbedding n)=(fun w=>f (w+b)) z := by
    intro n z
    dsimp
    rw [show z+3*eisEmbedding n+b=(z+b)+3*eisEmbedding n by ring,hp]
  rw [period_integral_unit_rotation (fun w=>f (w+b)) hg u]
  simpa only [add_comm] using period_integral_translation f hp b

end


end CubicEisenstein


end

end OAI

end


