-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0185_parallel1
-- name    : PNT_ZeroFree_433_0185_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:55:49.986455+00:00
-- url     : https://prove2.me/theorems/8686c64f-29f3-4f63-a952-99a3e4ffa0df
-- title:
--   Zero-free region foundations: CubicSieve.LogSeparation [0185_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.LogSeparation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/LogSeparation.lean#L83-L624

import Definitions.Def_PNT_ZeroFree_433_0003
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0044
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0049
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0073
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0081
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
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/LogSeparation.lean
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

namespace CanonicalCubeSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open FourierBridge JointLogSeparation

lemma cube_log_bin (B n : ℝ) (hB : 0 < B) (hn : B ≤ n)
    (hn' : n ≤ Real.exp 1 * B) : Real.log (n/B) ∈ Set.Icc (0:ℝ) 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hn
  constructor
  · exact Real.log_nonneg ((le_div_iff₀ hB).mpr (by simpa using hn))
  · have hh : n/B ≤ Real.exp 1 := (div_le_iff₀ hB).mpr hn'
    have := Real.log_le_log (div_pos hn0 hB) hh
    simpa only [Real.log_exp] using this

lemma cube_log_argument (B ell n q : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) (hq : 0 < q) :
    Real.exp (Real.log (q/ell) + 3*Real.log (n/B)) = q*n^3/(B^3*ell) := by
  rw [Real.exp_add, Real.exp_log (div_pos hq hell)]
  have he : Real.exp (3*Real.log (n/B)) = (n/B)^3 := by
    rw [show (3:ℝ)*Real.log (n/B) =
      Real.log (n/B)+Real.log (n/B)+Real.log (n/B) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hn hB)]
    ring
  rw [he]
  field_simp

lemma cube_half_normalization (B ell n : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) :
    (Real.sqrt (B^3*ell))⁻¹ * Real.sqrt n =
      (B*Real.sqrt ell)⁻¹ * Real.exp (Real.log (n/B)/2) := by
  have hb0 := (Real.sqrt_pos.mpr hB).ne'
  have he0 := (Real.sqrt_pos.mpr hell).ne'
  have hs : Real.sqrt (B^3*ell) = B*Real.sqrt B*Real.sqrt ell := by
    rw [show B^3*ell=B^2*(B*ell) by ring,
      Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB.le, Real.sqrt_mul hB.le]
    ring
  have hnexp : Real.exp (Real.log (n/B)/2) = Real.sqrt n/Real.sqrt B := by
    rw [← sqrt_exp_half, Real.exp_log (div_pos hn hB), Real.sqrt_div hn.le]
  rw [hs, hnexp]
  field_simp

lemma cube_half_normalization_complex (B ell n : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) :
    (Real.sqrt (B^3*ell) : ℂ)⁻¹ * (Real.sqrt n : ℂ) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * (Real.exp (Real.log (n/B)/2) : ℂ) := by
  exact_mod_cast cube_half_normalization B ell n hB hell hn


lemma completed_cube_half_weight (X n : ℝ) (hX : 0 < X) (hn : 0 < n) :
    n⁻¹ * (Real.sqrt (X/n^3))⁻¹ = (Real.sqrt X)⁻¹ * Real.sqrt n := by
  have hs : Real.sqrt (n^3) = n*Real.sqrt n := by
    rw [show n^3=n^2*n by ring, Real.sqrt_mul (sq_nonneg n), Real.sqrt_sq hn.le]
  rw [Real.sqrt_div hX.le, hs, inv_div]
  field_simp

lemma completed_cube_half_weight_complex (X n : ℝ) (hX : 0 < X) (hn : 0 < n) :
    (n : ℂ)⁻¹ * (Real.sqrt (X/n^3) : ℂ)⁻¹ =
      (Real.sqrt X : ℂ)⁻¹ * (Real.sqrt n : ℂ) := by
  exact_mod_cast completed_cube_half_weight X n hX hn


end CanonicalCubeSeparation

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight


open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O

theorem inner_completed_sum (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (hX : 0<X)
    (B : Ideal ActualEisensteinCubic.O) (hB : B≠0) :
    (∑'I:Ideal ActualEisensteinCubic.O,summand Ψ W X I B) =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        ∑'I:Ideal ActualEisensteinCubic.O,columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3)) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := div_pos hX (pow_pos hN _)
  have ht (I:Ideal ActualEisensteinCubic.O) : summand Ψ W X I B =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        (columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
    have harg : (Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X =
        (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3) := by
      rw [div_div_eq_mul_div]
    have hn := vstar_source_normalization Ψ W (X/(Ideal.absNorm B:ℝ)^3) hY I
    calc
      _ = cubeWeight Ψ B * (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ) *
          Vstar W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
        rw [summand,harg]
        ring
      _ = _ := by rw [hn]; ring
  simp_rw [ht]
  exact tsum_mul_left


end

open ActualEisensteinCubic
open CompletedGauss hiding O

theorem cubeWeight_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal ActualEisensteinCubic.O) :
    ‖cubeWeight Ψ B‖ ≤ 1/(Ideal.absNorm B:ℝ) := by
  have hang : ‖FiniteGaussPhase.angularFactor (primaryGenerator B)‖ ≤ 1 := by
    by_cases hz : primaryGenerator B=0
    · simp [hz,FiniteGaussPhase.angularFactor]
    · exact (FiniteGaussPhase.norm_angularFactor _ hz).le
  change ‖star (FiniteGaussPhase.angularFactor (primaryGenerator B))^3*
    Ψ (primaryGenerator B)^3/(Ideal.absNorm B:ℂ)‖ ≤ _
  rw [norm_div,norm_mul,norm_pow,norm_pow,norm_star,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) hang)).trans (pow_le_one₀ (norm_nonneg _) (hΨ _))

def cubePhase (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) : ℂ :=
  (Ideal.absNorm B:ℂ)*cubeWeight Ψ B

theorem cubePhase_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal ActualEisensteinCubic.O) :
    ‖cubePhase Ψ B‖ ≤ 1 := by
  by_cases hB : B=0
  · simp [hB,cubePhase]
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  rw [cubePhase,norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (Ideal.absNorm B:ℝ)*(1/(Ideal.absNorm B:ℝ)) :=
      mul_le_mul_of_nonneg_left (cubeWeight_norm_le Ψ hΨ B) hN.le
    _ = 1 := by field_simp

theorem cube_weight_scale (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) (hB : B≠0)
    (X : ℝ) (hX : 0<X) :
    cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹ =
      cubePhase Ψ B * (Real.sqrt (Ideal.absNorm B:ℝ):ℂ)/(Real.sqrt X:ℂ) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hs3 : Real.sqrt ((Ideal.absNorm B:ℝ)^3) =
      (Ideal.absNorm B:ℝ)*Real.sqrt (Ideal.absNorm B:ℝ) := by
    rw [show (Ideal.absNorm B:ℝ)^3=(Ideal.absNorm B:ℝ)^2*(Ideal.absNorm B:ℝ) by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hN]
  have hs : Real.sqrt (X/(Ideal.absNorm B:ℝ)^3) =
      Real.sqrt X/((Ideal.absNorm B:ℝ)*Real.sqrt (Ideal.absNorm B:ℝ)) := by
    rw [Real.sqrt_div hX.le,hs3]
  rw [hs,Complex.ofReal_div,Complex.ofReal_mul,cubePhase]
  push_cast
  have hNc : (Ideal.absNorm B:ℂ)≠0 := by exact_mod_cast hN.ne'
  have hsN : (Real.sqrt (Ideal.absNorm B:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  have hsX : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  field_simp


end CanonicalRowCompletion

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels

def childLabelRotation (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O :=
  (z.1,(u : ActualEisensteinCubic.O)^4*(if negative then -z.2 else z.2))

theorem childLabelRotation_injective (u : ActualEisensteinCubic.Oˣ) (negative : Bool) :
    Function.Injective (childLabelRotation u negative) := by
  intro z w he
  have hf := congrArg Prod.fst he
  change z.1=w.1 at hf
  have hs := congrArg Prod.snd he
  change (u : ActualEisensteinCubic.O)^4*(if negative then -z.2 else z.2)=
    (u : ActualEisensteinCubic.O)^4*(if negative then -w.2 else w.2) at hs
  have hz := mul_left_cancel₀ (pow_ne_zero 4 u.ne_zero) hs
  apply Prod.ext hf
  cases negative <;> simpa only [Bool.false_eq_true,ite_false,ite_true,neg_inj] using hz

theorem childLabelRotation_norm (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) :
    ‖eisEmbedding (childLabelRotation u negative z).2‖^2=‖eisEmbedding z.2‖^2 := by
  cases negative <;> simp only [childLabelRotation,Bool.false_eq_true,ite_false,ite_true,
    map_mul,norm_mul,map_pow,norm_pow,GaussGeneratorTransport.norm_eisEmbedding_unit,
    one_pow,one_mul,map_neg,norm_neg]

theorem childLabelRotation_ne_zero (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)
    (hz : z.2≠0) : (childLabelRotation u negative z).2≠0 := by
  apply mul_ne_zero (pow_ne_zero 4 u.ne_zero)
  cases negative <;> simpa using hz

section
variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem fixedChildRow_label_mul (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (u f z : ActualEisensteinCubic.O) :
    fixedChildRow p hp hcop hg pool Ψ m H (u*f) z=
      fixedChildRow p hp hcop hg pool Ψ m H f (u^4*z) := by
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,finiteSquarefreeRow_mul,row_pow,mul_pow]
  ring

theorem idealChildRow_eq_rotated (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (negative : Bool) (u : ActualEisensteinCubic.Oˣ) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) :
    idealChildRow p hp hcop hg pool Ψ m H negative u z=
      fixedChildRow p hp hcop hg pool Ψ m H
        (ConcretePrimeRowBridge.idealGenerator (childLabelRotation u negative z).1)
        (childLabelRotation u negative z).2 := by
  exact fixedChildRow_label_mul p hp hcop hg pool Ψ m H (u : ActualEisensteinCubic.O) _ _


end

def orientedLogProfile (negative : Bool) (V : ℝ → ℂ) : ℝ → ℂ :=
  if negative then fun s=>star (V s) else V

theorem fixedSecondTest_zero_profile {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)
    (V : ℝ → ℂ) (X : ℝ) (negative : Bool) :
    fixedSecondTest p V X 0 0 negative=(fun S=>orientedLogProfile negative V (columnLog p X S)) := by
  funext S
  cases negative <;> simp [fixedSecondTest,orientedLogProfile,JointLogSeparation.fixedColumnTest,FourierBridge.logPhase]

end SecondPassArithmetic

end

end OAI

end


