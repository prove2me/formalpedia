-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0153_parallel1
-- name    : PNT_ZeroFree_433_0153_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:58:44.181988+00:00
-- url     : https://prove2.me/theorems/0c8ecddb-2124-4f72-bdac-495a51a66772
-- title:
--   Zero-free region foundations: CubicSieve.NormalizedMass [0153_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.NormalizedMass
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/NormalizedMass.lean#L86-L670

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0012
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0061
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0105
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0146_parallel1
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0224_parallel1_1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/NormalizedMass.lean
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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem columnLog_norm_lower (X M : ℝ) (hX : 0<X) (S : Finset ι)
    (h : -M≤columnLog p X S) : X*Real.exp (-M)≤primeProductNorm p S := by
  have he := Real.exp_le_exp.mpr h
  rw [columnLog,Real.exp_log (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp S) hX)] at he
  simpa only [mul_comm] using (le_div_iff₀ hX).mp he


include hp in

omit [DecidableEq ι] in
theorem normalized_second_mass_zero
    (F : Finset ι) (Ψ : O→*ℂ) (m c d : O) (g : ℝ→ℂ)
    (M X : ℝ) (hX : 0<X) (hM : ∀t,g t≠0 → |t|≤M) (hsmall : X*Real.exp M<1) :
    (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)=0 := by
  apply Finset.sum_eq_zero
  intro S hS
  have hz : g (columnLog p X S)=0 := by
    by_contra hn
    have hh := columnLog_norm_upper p hp X M hX S ((le_abs_self _).trans (hM _ hn))
    have ho := primeProductNorm_ge_one p hp S
    linarith
  simp [secondInputCoefficient,normalizedColumn,hz]


end


end


open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)


end SecondPassArithmetic

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic LocalReflectionBrackets

theorem bracket_one_eq_quadratic (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (z : O) :
    bracket (actualSextic P hg) 1 (Ideal.Quotient.mk P z)=
      (actualSextic P hg (Ideal.Quotient.mk P z))^3 := by
  simp only [bracket,show (1:ℕ)≠4 by decide,show (1:ℕ)≠0 by decide,↓reduceIte]
  rw [show (1:ℕ)+2=3 by rfl,MulChar.inv_apply_eq_inv',MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]
  by_cases hz : z∈P
  · have he : Ideal.Quotient.mk P z=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
    simp [he]
  · have h6 := canonicalSextic_sixth_power_mask P hg z
    change actualSextic P hg (Ideal.Quotient.mk P (z^6))=_ at h6
    simp only [map_pow,if_neg hz] at h6
    apply inv_eq_of_mul_eq_one_right
    calc
      _ = (actualSextic P hg (Ideal.Quotient.mk P z))^6 := by ring
      _ = 1 := h6

theorem quadratic_value_cube (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (b : O) :
    (actualSextic P hg (Ideal.Quotient.mk P (b^3)))^3=
      (actualSextic P hg (Ideal.Quotient.mk P b))^3 := by
  simp only [map_pow]
  by_cases hb : b∈P
  · have he : Ideal.Quotient.mk P b=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    simp [he]
  · have h6 := canonicalSextic_sixth_power_mask P hg b
    change actualSextic P hg (Ideal.Quotient.mk P (b^6))=_ at h6
    simp only [map_pow,if_neg hb] at h6
    calc
      _ = (actualSextic P hg (Ideal.Quotient.mk P b))^3 *
          (actualSextic P hg (Ideal.Quotient.mk P b))^6 := by ring
      _ = _ := by rw [h6,mul_one]

theorem residual_bracket_cube (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (z n b : O) :
    bracket (actualSextic P hg) 1 (Ideal.Quotient.mk P (z*n*b^3))=
      (actualSextic P hg (Ideal.Quotient.mk P z))^3 *
      (actualSextic P hg (Ideal.Quotient.mk P (n*b)))^3 := by
  rw [bracket_one_eq_quadratic]
  simp only [map_mul,mul_pow]
  rw [quadratic_value_cube]
  ring

theorem residual_bracket_product {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (z n b : O) :
    (∏i,bracket (actualSextic (P i) (hg i)) 1 (Ideal.Quotient.mk (P i) (z*n*b^3)))=
      finiteSexticRow P hg (fun _ => 3) z * finiteSexticRow P hg (fun _ => 3) (n*b) := by
  simp_rw [residual_bracket_cube,Finset.prod_mul_distrib]
  simp only [finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]

end


open ActualEisensteinCubic UniqueFactorizationMonoid

theorem prime_square_dvd_powerful (I P : Ideal O) (hI : PowerfulIdeal I)
    (hP : Prime P) (hd : P∣I) : P^2∣I := by
  have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI.1).mpr ⟨hP,hd⟩
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero 2 hP.ne_zero) hI.1).mpr
  rw [normalizedFactors_pow,normalizedFactors_irreducible hP.irreducible,normalize_eq]
  apply Multiset.le_iff_count.mpr
  intro Q
  by_cases hQP : Q=P
  · subst Q
    simpa using hI.2 P hm
  · simp [hQP]


def nonresidualGain (I P : Ideal O) : Ideal O := if P∣I then P^2 else P


open ActualEisensteinCubic UniqueFactorizationMonoid

def completedLocalExponent (I F P : Ideal O) : ℕ :=
  ((normalizedFactors I).count P+4*(if P∣F then 1 else 0))%6

def reflectionExtractedPrime (P : Ideal O) (j : ℕ) (e v : Fin 3) : Ideal O :=
  if (j=4 ∧ e=v) ∨ (j=0 ∧ v=0) then P else 1

def reflectionExtractedDivisor {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) : Ideal O :=
  ∏i,reflectionExtractedPrime (P i) (j i) (e i) v

def reflectionConductorCost {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (j : ι→ℕ) (e : ι→Fin 3) : ℝ :=
  (Ideal.absNorm (∏i,P i):ℝ)^2/
    ((Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
     (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
     (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)^4)

def reflectionLocalCost (q : ℝ) (j : ℕ) (e : Fin 3) : ℝ :=
  if j=4 then (if e=2 then 1/q^2 else q)
  else if j=0 then q else q^2

theorem reflectionConductorCost_eq_prod {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hP : ∀i,P i≠0) (j : ι→ℕ) (e : ι→Fin 3) :
    reflectionConductorCost P j e=∏i,reflectionLocalCost (Ideal.absNorm (P i):ℝ) (j i) (e i) := by
  have hn i : (Ideal.absNorm (P i):ℝ)≠0 := by
    exact_mod_cast (fun hz => hP i (Ideal.absNorm_eq_zero_iff.mp hz))
  simp only [reflectionConductorCost,reflectionExtractedDivisor,map_prod,Nat.cast_prod,
    ←Finset.prod_pow,←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hj4 : j i=4
  · rw [hj4]
    generalize he : e i=v
    fin_cases v <;> simp [reflectionExtractedPrime,reflectionLocalCost] <;> field_simp
  · by_cases hj0 : j i=0
    · simp [reflectionExtractedPrime,reflectionLocalCost,hj0]
      field_simp
    · simp [reflectionExtractedPrime,reflectionLocalCost,hj4,hj0]

theorem reflectionLocalCost_nonneg (q : ℝ) (hq : 0≤q) (j : ℕ) (e : Fin 3) :
    0≤reflectionLocalCost q j e := by
  unfold reflectionLocalCost
  split_ifs <;> positivity

theorem reflectionLocalCost_le_square (q : ℝ) (hq : 1≤q) (j : ℕ) (e : Fin 3) :
    reflectionLocalCost q j e≤q^2 := by
  have hq0 : 0<q := by linarith
  have hq2 : 1≤q^2 := one_le_pow₀ hq
  unfold reflectionLocalCost
  split_ifs
  · exact (div_le_one (by positivity)).mpr hq2 |>.trans hq2
  · nlinarith
  · nlinarith
  · rfl

theorem reflectionLocalCost_le_single (q : ℝ) (hq : 1≤q) (j : ℕ) (e : Fin 3)
    (hj : j=0 ∨ j=4) : reflectionLocalCost q j e≤q := by
  have hq0 : 0<q := by linarith
  rcases hj with rfl|rfl
  · simp [reflectionLocalCost]
  · simp only [reflectionLocalCost,ite_true]
    split_ifs
    · exact ((div_le_one (by positivity)).mpr (one_le_pow₀ hq)).trans hq
    · rfl

theorem completedLocalExponent_of_not_dvd (I F P : Ideal O) (hI : I≠0) (_hP : Prime P)
    (hn : ¬P∣I) : completedLocalExponent I F P=0 ∨ completedLocalExponent I F P=4 := by
  have hm : P∉normalizedFactors I := by
    intro h
    exact hn ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mp h).2
  simp only [completedLocalExponent,Multiset.count_eq_zero.mpr hm,zero_add]
  split_ifs <;> norm_num

theorem reflectionLocalCost_le_gain (I F P : Ideal O) (hI : I≠0) (hP : Prime P) (e : Fin 3) :
    reflectionLocalCost (Ideal.absNorm P:ℝ) (completedLocalExponent I F P) e≤
      (Ideal.absNorm (nonresidualGain I P):ℝ) := by
  have hq : 1≤(Ideal.absNorm P:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hP.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  by_cases hd : P∣I
  · rw [nonresidualGain,if_pos hd,map_pow,Nat.cast_pow]
    exact reflectionLocalCost_le_square _ hq _ _
  · rw [nonresidualGain,if_neg hd]
    exact reflectionLocalCost_le_single _ hq _ _ (completedLocalExponent_of_not_dvd I F P hI hP hd)


end CompletedGauss

end

end OAI

end


