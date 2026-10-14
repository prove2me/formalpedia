-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0230_parallel1
-- name    : PNT_ZeroFree_433_0230_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:27:14.649988+00:00
-- url     : https://prove2.me/theorems/2f96cfc1-9c0f-489c-a1af-8b4b559f09d2
-- title:
--   Zero-free region foundations: Eisenstein.TranslatedFourierResidues [0230_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.TranslatedFourierResidues
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/TranslatedFourierResidues.lean#L86-L574

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel2
import Definitions.Def_PNT_ZeroFree_433_0155_parallel1
import Definitions.Def_PNT_ZeroFree_433_0219_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/TranslatedFourierResidues.lean
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma period_integral_fourier_translation (f:ℂ→ℂ)
    (hp:∀(n:Eis)(z:ℂ),f (z+3*eisEmbedding n)=f z) (h:Eis) (b:ℂ) :
    (∫z in periodDomain,f (z+b)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ShortDraftTrace.breveE (cuspFrequency h*b)*
        ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  let g : ℂ→ℂ := fun z=>f z*ShortDraftTrace.breveE (-cuspFrequency h*z)
  have hg : ∀(n:Eis)(z:ℂ),g (z+3*eisEmbedding n)=g z := by
    intro n z
    dsimp only [g]
    rw [hp,cuspFrequency_negative_period]
  have he (z:ℂ) : f (z+b)*ShortDraftTrace.breveE (-cuspFrequency h*z)=
      ShortDraftTrace.breveE (cuspFrequency h*b)*g (b+z) := by
    dsimp only [g]
    rw [mul_left_comm,←AddChar.map_add_eq_mul]
    congr 1
    · rw [add_comm]
    · congr 1
      ring
  simp_rw [he]
  rw [integral_const_mul,period_integral_translation g hg b]


def sourceRayPhaseSum (h:Eis) : ℂ :=
  ∑ b:Fin 3,ShortDraftTrace.breveE (cuspFrequency h*(b.val:ℂ))


end

section
open CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceRayPhase_cube (h:Eis) :
    ShortDraftTrace.breveE (cuspFrequency h)^3=1 := by
  rw [←AddChar.map_nsmul_eq_pow,nsmul_eq_mul]
  have hp:=cuspFrequency_period h (1:Eis)
  simpa only [map_one,mul_one,one_mul,Nat.cast_ofNat,mul_comm] using hp

lemma sourceRayPhaseSum_formula (h:Eis) :
    sourceRayPhaseSum h=1+ShortDraftTrace.breveE (cuspFrequency h)+
      ShortDraftTrace.breveE (cuspFrequency h)^2 := by
  unfold sourceRayPhaseSum
  simp only [Fin.sum_univ_succ,Fin.val_zero,Nat.cast_zero,mul_zero,AddChar.map_zero_eq_one,
    Fin.val_succ,Nat.cast_add,Nat.cast_one,zero_add,mul_one,Fin.sum_univ_zero,add_zero]
  have he : ShortDraftTrace.breveE (cuspFrequency h*(1+1))=
      ShortDraftTrace.breveE (cuspFrequency h)^2 := by
    rw [mul_add,mul_one,AddChar.map_add_eq_mul,pow_two]
  rw [he]
  ring

lemma sourceRayPhaseSum_eq (h:Eis) :
    sourceRayPhaseSum h=if ShortDraftTrace.breveE (cuspFrequency h)=1 then 3 else 0 := by
  rw [sourceRayPhaseSum_formula]
  split_ifs with he
  · rw [he]
    norm_num
  · have hc:=sourceRayPhase_cube h
    have hz : (ShortDraftTrace.breveE (cuspFrequency h)-1)*
        (1+ShortDraftTrace.breveE (cuspFrequency h)+ShortDraftTrace.breveE (cuspFrequency h)^2)=0 := by
      linear_combination hc
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr he)


end

open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O


end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

def horizontalPhaseMultiplier (freq direction : ℂ) : ℂ :=
  (2*Real.pi*Complex.I)*(freq*direction+star (freq*direction))

lemma brevePhase_hasDerivAt (freq z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => ShortDraftTrace.breveE (freq*(z+(x:ℂ)*direction)))
      (horizontalPhaseMultiplier freq direction*
        ShortDraftTrace.breveE (freq*(z+(t:ℂ)*direction))) t := by
  have hz : HasDerivAt (fun x : ℝ => freq*(z+(x:ℂ)*direction)) (freq*direction) t := by
    convert! (((Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const direction).const_add z).const_mul freq using 1 <;>
      simp
  have he := ((hz.add hz.star).const_mul (2*Real.pi*Complex.I)).cexp
  change HasDerivAt (fun x : ℝ => Complex.exp ((2*Real.pi*Complex.I)*
    (freq*(z+(x:ℂ)*direction)+star (freq*(z+(x:ℂ)*direction)))))
    ((2*Real.pi*Complex.I)*(freq*direction+star (freq*direction))*
      Complex.exp ((2*Real.pi*Complex.I)*
        (freq*(z+(t:ℂ)*direction)+star (freq*(z+(t:ℂ)*direction))))) t
  simpa only [Pi.add_apply,mul_comm] using he

lemma horizontalPhaseMultiplier_norm (freq direction : ℂ) :
    ‖horizontalPhaseMultiplier freq direction‖≤4*Real.pi*‖freq‖*‖direction‖ := by
  have hc : ‖(2*Real.pi*Complex.I:ℂ)‖=2*Real.pi := by
    norm_num [norm_mul,abs_of_pos Real.pi_pos]
  unfold horizontalPhaseMultiplier
  rw [norm_mul,hc]
  calc
    _ ≤ (2*Real.pi)*(‖freq*direction‖+‖star (freq*direction)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = _ := by rw [norm_star,norm_mul];ring

lemma horizontalPhaseMultiplier_wirtinger (freq : ℂ) :
    (1/2:ℂ)*(horizontalPhaseMultiplier freq 1+
      Complex.I*horizontalPhaseMultiplier freq Complex.I)=2*Real.pi*Complex.I*star freq := by
  simp only [horizontalPhaseMultiplier,mul_one,star_mul,Complex.star_def,
    Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq,Complex.I_pow_three]
  ring

lemma norm_mul_exp_neg_bound (a r : ℝ) (ha : 0<a) :
    r*Real.exp (-a*r)≤(2/a)*Real.exp (-(a/2)*r) := by
  have hbase := Real.add_one_le_exp ((a/2)*r)
  have hr : r≤(2/a)*Real.exp ((a/2)*r) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    nlinarith
  calc
    _ ≤ ((2/a)*Real.exp ((a/2)*r))*Real.exp (-a*r) :=
      mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring

lemma summable_norm_mul_exp_neg_cuspFrequency (a : ℝ) (ha : 0<a) :
    Summable (fun h : ActualEisensteinCubic.O => ‖cuspFrequency h‖*Real.exp (-a*‖cuspFrequency h‖)) := by
  apply Summable.of_nonneg_of_le (fun h => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (fun h => norm_mul_exp_neg_bound a _ ha)
  exact (summable_exp_neg_cuspFrequency_norm (a/2) (half_pos ha)).mul_left (2/a)

local notation "O" => ActualEisensteinCubic.O


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def horizontalWirtingerBar (f : ℂ→ℂ) (z : ℂ) : ℂ :=
  (1/2:ℂ)*(deriv (fun t : ℝ => f (z+(t:ℂ))) 0+
    Complex.I*deriv (fun t : ℝ => f (z+(t:ℂ)*Complex.I)) 0)

lemma horizontalWirtingerBar_brevePhase (freq z : ℂ) :
    horizontalWirtingerBar (fun w => ShortDraftTrace.breveE (freq*w)) z=
      (2*Real.pi*Complex.I*star freq)*ShortDraftTrace.breveE (freq*z) := by
  have h1 := (brevePhase_hasDerivAt freq z 1 0).deriv
  have hI := (brevePhase_hasDerivAt freq z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI]
  linear_combination ShortDraftTrace.breveE (freq*z)*horizontalPhaseMultiplier_wirtinger freq


end CubicEisenstein

end

end OAI

end


