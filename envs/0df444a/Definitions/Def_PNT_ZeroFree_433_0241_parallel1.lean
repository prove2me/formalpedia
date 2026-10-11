-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0241_parallel1
-- name    : PNT_ZeroFree_433_0241_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:11:43.965779+00:00
-- url     : https://prove2.me/theorems/1dce5edc-51b3-4994-aa9b-2b5430ecacbb
-- title:
--   Zero-free region foundations: Cusp.ResiduesModThree [0241_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Cusp.ResiduesModThree
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Cusp/ResiduesModThree.lean#L85-L633

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0083
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0136_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel1
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0144_parallel1
import Definitions.Def_PNT_ZeroFree_433_0161_parallel1
import Definitions.Def_PNT_ZeroFree_433_0184_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel1
import Definitions.Def_PNT_ZeroFree_433_0190_parallel1
import Definitions.Def_PNT_ZeroFree_433_0203_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221_parallel1
import Definitions.Def_PNT_ZeroFree_433_0228_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel1
import Definitions.Def_PNT_ZeroFree_433_0332_parallel1
import Definitions.Def_PNT_ZeroFree_433_0506_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Cusp/ResiduesModThree.lean
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

open scoped Classical MatrixGroups

namespace EisensteinCuspModThree

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCoordinates (eval coords eval_coords unique_coordinates eval_mul)

abbrev Pair := ZMod 3 × ZMod 3
def add (x y : Pair) : Pair := (x.1+y.1,x.2+y.2)
def neg (x : Pair) : Pair := (-x.1,-x.2)
def sub (x y : Pair) : Pair := add x (neg y)
def mul (x y : Pair) : Pair := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1-x.2*y.2)
def scalar (a : ZMod 3) (x : Pair) : Pair := (a*x.1,a*x.2)
def residue (x : ActualEisensteinCubic.O) : Pair := ((coords x).1,(coords x).2)

lemma residue_eval (a b : ℤ) : residue (eval a b)=((a:ZMod 3),(b:ZMod 3)) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext (congrArg (fun n : ℤ => (n:ZMod 3)) h.1)
    (congrArg (fun n : ℤ => (n:ZMod 3)) h.2)

lemma residue_intCast (a : ℤ) : residue (a:ActualEisensteinCubic.O)=((a:ZMod 3),0) := by
  simpa [eval] using residue_eval a 0

lemma residue_zero : residue (0:ActualEisensteinCubic.O)=(0,0) := by simpa using residue_intCast 0
lemma residue_one : residue (1:ActualEisensteinCubic.O)=(1,0) := by simpa using residue_intCast 1

lemma residue_add (x y : ActualEisensteinCubic.O) : residue (x+y)=add (residue x) (residue y) := by
  have he : x+y=eval ((coords x).1+(coords y).1) ((coords x).2+(coords y).2) := by
    nth_rw 1 [←eval_coords x,←eval_coords y]
    simp only [eval,Int.cast_add]
    ring
  rw [he,residue_eval]
  simp [residue,add]

lemma residue_neg (x : ActualEisensteinCubic.O) : residue (-x)=neg (residue x) := by
  have he : -x=eval (-(coords x).1) (-(coords x).2) := by
    nth_rw 1 [←eval_coords x]
    simp only [eval,Int.cast_neg]
    ring
  rw [he,residue_eval]
  simp [residue,neg]

lemma residue_sub (x y : ActualEisensteinCubic.O) : residue (x-y)=sub (residue x) (residue y) := by
  rw [sub_eq_add_neg,residue_add,residue_neg]
  rfl

lemma residue_mul (x y : ActualEisensteinCubic.O) : residue (x*y)=mul (residue x) (residue y) := by
  calc
    residue (x*y)=residue (eval (coords x).1 (coords x).2*eval (coords y).1 (coords y).2) := by
      rw [eval_coords,eval_coords]
    _ = _ := by rw [eval_mul,residue_eval]; simp [residue,mul]

lemma residue_eq_implies_three_dvd {x y : ActualEisensteinCubic.O} (h : residue x=residue y) : (3:ActualEisensteinCubic.O)∣x-y := by
  have h1 : (3:ℤ)∣(coords x).1-(coords y).1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (coords y).1 (coords x).1 3).mp
      (congrArg Prod.fst h).symm
  have h2 : (3:ℤ)∣(coords x).2-(coords y).2 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (coords y).2 (coords x).2 3).mp
      (congrArg Prod.snd h).symm
  obtain ⟨a,ha⟩ := h1
  obtain ⟨b,hb⟩ := h2
  refine ⟨eval a b,?_⟩
  nth_rw 1 [←eval_coords x,←eval_coords y]
  have he1 : (coords x).1=(coords y).1+3*a := by omega
  have he2 : (coords x).2=(coords y).2+3*b := by omega
  simp only [eval,he1,he2]
  push_cast
  ring

lemma residue_mul_intCast (a : ℤ) (x : ActualEisensteinCubic.O) : residue ((a:ActualEisensteinCubic.O)*x)=scalar (a:ZMod 3) (residue x) := by
  rw [residue_mul,residue_intCast]
  simp [mul,scalar]

def primitive (a c : Pair) : Prop := ¬(a.1+a.2=0 ∧ c.1+c.2=0)
instance primitive_decidable (a c : Pair) : Decidable (primitive a c) := inferInstanceAs
  (Decidable (¬(a.1+a.2=0 ∧ c.1+c.2=0)))

lemma primitive_of_determinant : ∀a b c d : Pair,sub (mul a d) (mul b c)=(1,0) → primitive a c := by
  decide +kernel

lemma first_column_primitive (M : SL(2,ActualEisensteinCubic.O)) : primitive (residue (M 0 0)) (residue (M 1 0)) := by
  have hd : M 0 0*M 1 1-M 0 1*M 1 0=1 := by simpa only [Matrix.det_fin_two] using M.property
  have hh := congrArg residue hd
  rw [residue_sub,residue_mul,residue_mul,residue_one] at hh
  exact primitive_of_determinant _ _ _ _ hh

def omegaPower (k : Fin 3) : Pair := if k=0 then (1,0) else if k=1 then (0,1) else (-1,-1)
def unitPair (u : Fin 2 × Fin 3) : Pair := scalar ((-1:ZMod 3)^u.1.val) (omegaPower u.2)
def cuspPair (j : Fin 3) : Pair := if j=0 then (0,0) else if j=1 then (0,1) else (-1,-1)

def columnTop (g : SL(2,ZMod 3)) (j : Fin 3) (u : Fin 2 × Fin 3) : Pair :=
  mul (add (g 0 0,0) (scalar (g 0 1) (cuspPair j))) (unitPair u)
def columnBottom (g : SL(2,ZMod 3)) (j : Fin 3) (u : Fin 2 × Fin 3) : Pair :=
  mul (add (g 1 0,0) (scalar (g 1 1) (cuspPair j))) (unitPair u)

theorem primitive_column_three_cusps : ∀a c : Pair, primitive a c →
    ∃g : SL(2,ZMod 3), ∃j : Fin 3, ∃u : Fin 2 × Fin 3,
      columnTop g j u=a ∧ columnBottom g j u=c := by
  decide +kernel

end

open scoped Classical MatrixGroups Matrix

local notation "O" => ActualEisensteinCubic.O
local notation "ζ" => ActualEisensteinCubic.omega
open CubicKubota CubicEisenstein

def unitRepresentative (u : Fin 2 × Fin 3) : ActualEisensteinCubic.Oˣ :=
  (-1:ActualEisensteinCubic.Oˣ)^u.1.val*CubicRamified.omega_isUnit.unit^u.2.val

lemma unitRepresentative_value (u : Fin 2 × Fin 3) :
    (unitRepresentative u:ActualEisensteinCubic.O)=(-1:ActualEisensteinCubic.O)^u.1.val*ζ^u.2.val := by
  simp [unitRepresentative]

lemma residue_omega : residue ζ=(0,1) := by
  have he : ActualEisensteinCoordinates.eval 0 1=ζ := by
    simp only [ActualEisensteinCoordinates.eval,Int.cast_zero,Int.cast_one,zero_add,one_mul]
    rfl
  rw [←he]
  exact residue_eval 0 1

lemma residue_omega_sq : residue (ζ^2)=(-1,-1) := by
  rw [pow_two,residue_mul,residue_omega]
  norm_num [mul]

lemma unitRepresentative_residue (u : Fin 2 × Fin 3) :
    residue (unitRepresentative u:ActualEisensteinCubic.O)=unitPair u := by
  rw [unitRepresentative_value]
  rcases u with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [unitPair,omegaPower,scalar,residue_one,residue_neg,residue_omega,residue_omega_sq,neg]

def cuspParameter (j : Fin 3) : ActualEisensteinCubic.O := if j=0 then 0 else if j=1 then ζ else ζ^2


lemma cuspParameter_residue (j : Fin 3) : residue (cuspParameter j)=cuspPair j := by
  fin_cases j <;> simp [cuspParameter,cuspPair,residue_zero,residue_omega,residue_omega_sq]

def unitDiagonal (u : ActualEisensteinCubic.Oˣ) : SL(2,ActualEisensteinCubic.O) :=
  ⟨!![(u:ActualEisensteinCubic.O),0;0,(↑u⁻¹:ActualEisensteinCubic.O)],by simp [Matrix.det_fin_two]⟩


lemma same_column_quotient_lower_zero (M N : SL(2,ActualEisensteinCubic.O))
    (h0 : N 0 0=M 0 0) (h1 : N 1 0=M 1 0) : (N⁻¹*M) 1 0=0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,]
  rw [h0,h1]
  ring


end EisensteinCuspModThree


open Filter MeasureTheory
open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O


def unitCuspIndexEquiv (u : Eisˣ) : Eis≃Eis where
  toFun n := (u:Eis)*n
  invFun n := (↑u⁻¹:Eis)*n
  left_inv n := by simp [←mul_assoc]
  right_inv n := by simp [←mul_assoc]

end

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O


end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma levelTwo_entry_integer (g : levelTwo) (i j : Fin 2) :
    (3:Eis)∣((g:SL(2,Eis)) i j-((levelTwoRight g) i j:ℤ)) := by
  have he : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (g:SL(2,Eis)) =
      Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (rationalEmbedding (levelTwoRight g)) := by
    rw [←levelTwo_product g,map_mul]
    have hn : Matrix.SpecialLinearGroup.map (n:=Fin 2)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (levelTwoLeft g:SL(2,Eis))=1 := (levelTwoLeft g).property
    rw [hn,one_mul]
  have h := congrArg (fun A : SL(2,Eis⧸Ideal.span {(3:Eis)})=>A i j) he
  exact Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h)

def integerUpper (b : ℤ) : SL(2,ℤ) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two_of]⟩
def integerLower (c : ℤ) : SL(2,ℤ) := ⟨!![1,0;c,1],by simp [Matrix.det_fin_two_of]⟩

lemma levelTwoComplexCharacter_primary (g : levelTwo)
    (ha : lambda^2∣((g:SL(2,Eis)) 0 0)-1) :
    levelTwoComplexCharacter g =
      eisEmbedding (symbol ((g:SL(2,Eis)) 1 0) ((g:SL(2,Eis)) 0 0)) := by
  let A : SL(2,Eis) := g
  let b : ℤ := levelTwoRight g 0 1
  let c : ℤ := levelTwoRight g 1 0
  have hA : (3:Eis)∣A 0 0-1 := three_dvd_primary_sub_one _ ha
  have hB : (3:Eis)∣A 0 1-(b:Eis) := levelTwo_entry_integer g 0 1
  have hC : (3:Eis)∣A 1 0-(c:Eis) := levelTwo_entry_integer g 1 0
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hD : (3:Eis)∣A 1 1-(1+(b:Eis)*(c:Eis)) := by
    have hh := dvd_add (dvd_add (dvd_neg.mpr (dvd_mul_of_dvd_left hA (A 1 1)))
      (dvd_mul_of_dvd_left hB (A 1 0))) (dvd_mul_of_dvd_right hC (b:Eis))
    convert! hh using 1 ; linear_combination hdet
  let N : SL(2,Eis) := ⟨!![A 0 0,A 0 1-(b:Eis)*A 0 0;
    A 1 0-(c:Eis)*A 0 0,A 1 1-(c:Eis)*A 0 1-(b:Eis)*(A 1 0-(c:Eis)*A 0 0)],by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet⟩
  have hN : N∈levelThree := by
    apply (mem_levelThree_iff_entries N).mpr
    intro i j
    fin_cases i <;> fin_cases j
    · exact hA
    · have hh:=dvd_sub hB (dvd_mul_of_dvd_right hA (b:Eis))
      convert! hh using 1 ; dsimp [N] ; ring
    · have hh:=dvd_sub hC (dvd_mul_of_dvd_right hA (c:Eis))
      convert! hh using 1 ; dsimp [N] ; ring
    · have hh:=dvd_add (dvd_sub (dvd_sub hD (dvd_mul_of_dvd_right hB (c:Eis)))
        (dvd_mul_of_dvd_right hC (b:Eis))) (dvd_mul_of_dvd_right hA ((b:Eis)*(c:Eis)))
      convert! hh using 1 ; dsimp [N] ; ring
  let lengthScale : levelTwo := ⟨rationalEmbedding (integerLower c),rational_mem_levelTwo _⟩
  let U : levelTwo := ⟨rationalEmbedding (integerUpper b),rational_mem_levelTwo _⟩
  let n : levelThree := ⟨N,hN⟩
  let n2 : levelTwo := ⟨N,levelThree_le_levelTwo hN⟩
  have he : g=lengthScale*n2*U := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change A i j = (((!![(1 : ℤ), 0; c, 1]).map (Int.castRingHom Eis) *
      (N : Matrix (Fin 2) (Fin 2) Eis)) *
      (!![(1 : ℤ), b; 0, 1]).map (Int.castRingHom Eis)) i j
    fin_cases i <;> fin_cases j <;>
      norm_num [N, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  conv_lhs => rw [he,map_mul,map_mul]
  have hL : levelTwoComplexCharacter lengthScale=1 := levelTwoComplexCharacter_rational _
  have hU : levelTwoComplexCharacter U=1 := levelTwoComplexCharacter_rational _
  rw [hL,hU,one_mul,mul_one]
  change levelTwoComplexCharacter ⟨(n:SL(2,Eis)),levelThree_le_levelTwo n.property⟩=_
  rw [levelTwoComplexCharacter_restrict]
  change eisEmbedding (symbol (A 1 0-(c:Eis)*A 0 0) (A 0 0))=_
  congr 1
  exact symbol_congr (x:=A 1 0-(c:Eis)*A 0 0) (y:=A 1 0) (d:=A 0 0) ⟨-(c:Eis),by ring⟩

end CubicKubota

end

end OAI

end


