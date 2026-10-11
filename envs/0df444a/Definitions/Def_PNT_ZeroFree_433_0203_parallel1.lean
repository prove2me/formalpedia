-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0203_parallel1
-- name    : PNT_ZeroFree_433_0203_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:55:24.608648+00:00
-- url     : https://prove2.me/theorems/9504a9e7-3c45-4a40-a83a-9e52c56799cf
-- title:
--   Zero-free region foundations: RowCompletion.CompletedEnergy [0203_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.RowCompletion.CompletedEnergy
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/CompletedEnergy.lean#L159-L613

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0011
import Definitions.Def_PNT_ZeroFree_433_0016
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0046_2
import Definitions.Def_PNT_ZeroFree_433_0062
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
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/CompletedEnergy.lean
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

open scoped BigOperators Classical SchwartzMap ContDiff


open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

def fractionalThetaPoint (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) : ℂ :=
  eisEmbedding u.val * eisEmbedding lambda^((m:ℤ)-4) * eisEmbedding n * eisEmbedding b^3

lemma embedding_lambda_ne_zero : eisEmbedding lambda≠0 :=
  by
    intro hz
    apply PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
    apply ConcreteTraceCRT.eisEmbedding_injective
    simpa only [map_zero] using hz

theorem fractionalThetaPoint_clear (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    eisEmbedding lambda^4*fractionalThetaPoint u m n b=
      eisEmbedding (u.val*lambda^m*(n*b^3)) := by
  unfold fractionalThetaPoint
  rw [zpow_sub₀ embedding_lambda_ne_zero]
  simp only [zpow_natCast,map_mul,map_pow]
  field_simp [embedding_lambda_ne_zero]


theorem fractionalThetaPoint_ne_zero (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O)
    (hn : n≠0) (hb : b≠0) : fractionalThetaPoint u m n b≠0 := by
  unfold fractionalThetaPoint
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero ((u.isUnit.map eisEmbedding).ne_zero) (zpow_ne_zero _ embedding_lambda_ne_zero)
    · intro hz
      apply hn
      apply ConcreteTraceCRT.eisEmbedding_injective
      simpa only [map_zero] using hz
  · apply pow_ne_zero
    intro hz
    apply hb
    apply ConcreteTraceCRT.eisEmbedding_injective
    simpa only [map_zero] using hz

end


open ActualEisensteinCubic LocalReflectionBrackets
open ConcreteTraceCRT (eisEmbedding)

def paperLambda : ActualEisensteinCubic.O := 1+2*omega

def paperLambdaUnit : ActualEisensteinCubic.Oˣ where
  val := -omega
  inv := -omega^2
  val_inv := by
    calc
      (-omega)*(-omega^2)=omega^3:=by ring
      _=1:=omega_primitive.pow_eq_one
  inv_val := by
    calc
      (-omega^2)*(-omega)=omega^3:=by ring
      _=1:=omega_primitive.pow_eq_one

lemma paperLambdaUnit_six : (paperLambdaUnit.val:ActualEisensteinCubic.O)^6=1 := by
  change (-omega)^6=1
  calc
    (-omega)^6=(omega^3)^2:=by ring
    _=1:=by rw [omega_primitive.pow_eq_one,one_pow]

lemma paperLambda_eq : paperLambda=paperLambdaUnit.val*lambda := by
  change 1+2*omega=(-omega)*lambda
  change (1+2*omega:ActualEisensteinCubic.O)=(-omega)*(omega-1)
  have hw:=omega_primitive.geom_sum_eq_zero (by decide : 1<(3:ℕ))
  norm_num [Finset.sum_range_succ] at hw
  linear_combination hw

lemma paperLambda_embedding_ne_zero : eisEmbedding paperLambda≠0 := by
  rw [paperLambda_eq,map_mul]
  exact mul_ne_zero ((paperLambdaUnit.isUnit.map eisEmbedding).ne_zero) embedding_lambda_ne_zero

def paperFractionalThetaPoint (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) : ℂ :=
  eisEmbedding u.val*eisEmbedding paperLambda^((m:ℤ)-4)*eisEmbedding n*eisEmbedding b^3

def paperUnitReindex (m : ℕ) : ActualEisensteinCubic.Oˣ ≃ ActualEisensteinCubic.Oˣ := Equiv.mulRight (paperLambdaUnit^(m+2))

lemma paperUnitReindex_apply (m : ℕ) (u : ActualEisensteinCubic.Oˣ) :
    paperUnitReindex m u=u*paperLambdaUnit^(m+2):=rfl

theorem paperFractionalThetaPoint_eq (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    paperFractionalThetaPoint u m n b=
      fractionalThetaPoint (paperUnitReindex m u) m n b := by
  have ht : eisEmbedding paperLambdaUnit.val≠0:=(paperLambdaUnit.isUnit.map eisEmbedding).ne_zero
  have ht6 : eisEmbedding paperLambdaUnit.val^6=1:=by
    rw [←map_pow,paperLambdaUnit_six,map_one]
  have hp : eisEmbedding paperLambdaUnit.val^((m:ℤ)-4)=eisEmbedding paperLambdaUnit.val^(m+2) := by
    rw [show (m:ℤ)-4=((m+2:ℕ):ℤ)-6 by omega,zpow_sub₀ ht]
    norm_num only [zpow_natCast,zpow_ofNat,ht6,div_one]
  simp only [paperFractionalThetaPoint,fractionalThetaPoint,paperUnitReindex_apply,
    Units.val_mul,Units.val_pow_eq_pow_val,map_mul,map_pow,paperLambda_eq,mul_zpow,hp]
  ring

theorem paperFractionalThetaPoint_clear (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    eisEmbedding paperLambda^4*paperFractionalThetaPoint u m n b=
      eisEmbedding (u.val*paperLambda^m*(n*b^3)) := by
  unfold paperFractionalThetaPoint
  rw [zpow_sub₀ paperLambda_embedding_ne_zero]
  simp only [zpow_natCast,map_mul,map_pow]
  field_simp [paperLambda_embedding_ne_zero]


theorem paperIntegralArgument_eq (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    u.val*paperLambda^m*(n*b^3)=paperLambdaUnit.val^4*
      ((paperUnitReindex m u).val*lambda^m*(n*b^3)) := by
  apply ConcreteTraceCRT.eisEmbedding_injective
  rw [←paperFractionalThetaPoint_clear,paperFractionalThetaPoint_eq,
    paperLambda_eq,map_mul,mul_pow]
  rw [map_mul,map_pow,←fractionalThetaPoint_clear]
  ring


lemma paperLambdaUnit_four : paperLambdaUnit.val^4=omega := by
  change (-omega)^4=omega
  calc
    _=omega^3*omega:=by ring
    _=omega:=by rw [omega_primitive.pow_eq_one,one_mul]


end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalCubeSeparation


lemma fixed_reopening_child_radius (A : ℝ) : (2*A+4)+7=2*A+11 := by ring

end CanonicalCubeSeparation


namespace CanonicalCubeSeparation

def radiusIter (A : ℝ) : ℕ→ℝ
  | 0=>A
  | n+1=>radiusIter (2*A+11) n

@[simp] theorem radiusIter_zero (A : ℝ) : radiusIter A 0=A:=rfl
@[simp] theorem radiusIter_succ (A : ℝ) (n : ℕ) :
    radiusIter A (n+1)=radiusIter (2*A+11) n:=rfl

theorem radiusIter_mono_base (n : ℕ) : Monotone (fun A:ℝ=>radiusIter A n) := by
  induction n with
  | zero=>intro A B h;exact h
  | succ n ih=>intro A B h;exact ih (by linarith : 2*A+11≤2*B+11)

theorem radiusIter_nonneg (A : ℝ) (hA : 0≤A) (n : ℕ) : 0≤radiusIter A n := by
  induction n generalizing A with
  | zero=>exact hA
  | succ n ih=>exact ih (2*A+11) (by linarith)

theorem radiusIter_mono_depth (A : ℝ) (hA : 0≤A) : Monotone (radiusIter A) := by
  apply monotone_nat_of_le_succ
  intro n
  exact radiusIter_mono_base n (by linarith : A≤2*A+11)

theorem le_radiusIter (A : ℝ) (hA : 0≤A) (n : ℕ) : A≤radiusIter A n :=
  radiusIter_mono_depth A hA (Nat.zero_le n)

theorem radiusIter_child_le (A : ℝ) (hA : 0≤A) (s r : ℕ) (hs : s<r) :
    radiusIter (2*A+11) s≤radiusIter A r :=
  radiusIter_mono_depth A hA (Nat.succ_le_of_lt hs)

theorem common_pool_parent (A Z X D : ℝ) (r : ℕ) (hA : 0≤A)
    (_hZ : 0≤Z) (hX : 0≤X) (hXZ : X≤Z^3)
    (hD : Real.exp (radiusIter A r)*Z^3≤D) : Real.exp A*X≤D := by
  exact (mul_le_mul (Real.exp_le_exp.mpr (le_radiusIter A hA r)) hXZ hX
    (Real.exp_pos _).le).trans hD

theorem common_pool_child (A Z D : ℝ) (s r : ℕ) (hA : 0≤A)
    (hZ : 0≤Z) (hs : s<r) (hD : Real.exp (radiusIter A r)*Z^3≤D) :
    Real.exp (radiusIter (2*A+11) s)*Z^3≤D :=
  (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (radiusIter_child_le A hA s r hs))
    (pow_nonneg hZ _)).trans hD

end CanonicalCubeSeparation

open scoped BigOperators Classical
namespace QuadraticAllOddCRT
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisTraceModChar finite_quotient_span)
open FiniteGaussPhase hiding O

def character (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] : MulChar (ActualEisensteinCubic.O⧸P) ℂ := by
  letI : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  letI : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  exact (quadraticChar (ActualEisensteinCubic.O⧸P)).ringHomComp (Int.castRingHom ℂ)

theorem normalized_prime_eq_square_sum (p : ActualEisensteinCubic.O) (hp : p≠0)
    [(Ideal.span {p}).IsMaximal] (hc : ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2) :
    ConcreteBreveE.normalizedTraceGauss p hp (character (Ideal.span {p}))=
      quadraticGammaO p hp := by
  let : Field (ActualEisensteinCubic.O⧸Ideal.span {p}):=Ideal.Quotient.field _
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {p}):=Fintype.ofFinite _
  let ψ:=eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates p hp
  have hψ:ψ≠1:=by
    have hprim:=GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp
    simpa only [AddChar.mulShift_one] using hprim (a:=1) one_ne_zero
  change gaussSum (character (Ideal.span {p})) ψ/(‖eisEmbedding p‖:ℂ)=
    (∑x:ActualEisensteinCubic.O⧸Ideal.span {p},ψ (x^2))/(‖eisEmbedding p‖:ℂ)
  congr 1
  exact ShortDraftQuadraticGauss.quadratic_gauss_as_square_phase ψ hc hψ

theorem normalized_product_eq_square_sum {ι : Type*} [Fintype ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2) :
    normalizedProductTraceGauss p hp hcop (fun i=>character (Ideal.span {p i}))=
      quadraticGammaO (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)) := by
  let c:=∏i,p i
  have hc0:c≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  let : Finite (ActualEisensteinCubic.O⧸Ideal.span {c}):=finite_quotient_span hc0
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {c}):=Fintype.ofFinite _
  let (i:ι) : Fintype (ActualEisensteinCubic.O⧸Ideal.span {p i}):=Fintype.ofFinite _
  let (i:ι) : Field (ActualEisensteinCubic.O⧸Ideal.span {p i}):=Ideal.Quotient.field _
  let e:=productElementCRT p hcop
  let ψ:=eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0
  change (∑x:ActualEisensteinCubic.O⧸Ideal.span {c},(∏i,character (Ideal.span {p i}) (e x i))*ψ x)/(‖eisEmbedding c‖:ℂ)=
    (∑x:ActualEisensteinCubic.O⧸Ideal.span {c},ψ (x^2))/(‖eisEmbedding c‖:ℂ)
  congr 1
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i=>ActualEisensteinCubic.O⧸Ideal.span {p i}) e ψ (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0) hc

theorem quadraticGamma_product {ι : Type*} [Fintype ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2) :
    quadraticGammaO (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))=
      ∏i,character (Ideal.span {p i}) (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i))*
        quadraticGammaO (p i) (hp i) := by
  rw [←normalized_product_eq_square_sum p hp hcop hc,normalizedProductTraceGauss_crt]
  apply Finset.prod_congr rfl
  intro i hi
  rw [normalized_prime_eq_square_sum _ _ (hc i)]

end QuadraticAllOddCRT

end

end OAI

end


