-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0210
-- name    : PNT_ZeroFree_433_0210
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:51:34.921565+00:00
-- url     : https://prove2.me/theorems/aa48575c-f436-481d-ba44-4aaa65dc524e
-- title:
--   Zero-free region foundations: Hecke.MobiusEulerCorrection [0210]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Hecke.MobiusEulerCorrection
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/MobiusEulerCorrection.lean#L86-L688

import Definitions.Def_PNT_ZeroFree_433_0005
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0025
import Definitions.Def_PNT_ZeroFree_433_0026
import Definitions.Def_PNT_ZeroFree_433_0029
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0032
import Definitions.Def_PNT_ZeroFree_433_0033
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0121
import Definitions.Def_PNT_ZeroFree_433_0123
import Definitions.Def_PNT_ZeroFree_433_0128_parallel2
import Definitions.Def_PNT_ZeroFree_433_0139_parallel1
import Definitions.Def_PNT_ZeroFree_433_0141_parallel1
import Definitions.Def_PNT_ZeroFree_433_0149_parallel2
import Definitions.Def_PNT_ZeroFree_433_0151_parallel1
import Definitions.Def_PNT_ZeroFree_433_0182_parallel1
import Definitions.Def_PNT_ZeroFree_433_0208_parallel1
import Definitions.Def_PNT_ZeroFree_433_0209_parallel1
import Definitions.Def_PNT_ZeroFree_433_0214_parallel1
import Definitions.Def_PNT_ZeroFree_433_0226_parallel1

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/MobiusEulerCorrection.lean#L86-L688
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Hecke.MobiusEulerCorrection
section
namespace OAI

noncomputable section

namespace SmoothMobiusCorrection

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

section
open ActualEisensteinCubic
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

abbrev PrimeIdeal := {P : Ideal ActualEisensteinCubic.O // Prime P}

def primeProduct (s : Finset PrimeIdeal) : Ideal ActualEisensteinCubic.O := ∏ P ∈ s, P.val

def primeSet (I : Ideal ActualEisensteinCubic.O) : Finset PrimeIdeal :=
  (primeSupport I).attach.image (fun P => ⟨P.val, support_prime P.property⟩)

@[simp] theorem mem_primeSet (I : Ideal ActualEisensteinCubic.O) (P : PrimeIdeal) :
    P ∈ primeSet I ↔ P.val ∈ primeSupport I := by
  simp only [primeSet, Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨Q,hQ⟩
    have hv := congrArg Subtype.val hQ
    simpa only [←hv] using Q.property
  · intro h
    exact ⟨⟨P.val,h⟩,rfl⟩

theorem primeProduct_ne_zero (s : Finset PrimeIdeal) : primeProduct s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => P.property.ne_zero)

theorem factors_primeProduct (s : Finset PrimeIdeal) :
    normalizedFactors (primeProduct s) = s.val.map Subtype.val := by
  have h := normalizedFactors_prod_of_prime
    (m := s.val.map (fun P : PrimeIdeal => P.val)) (by
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Multiset.mem_map.mp hP
      exact Q.property)
  simpa only [primeProduct, Finset.prod_eq_multiset_prod] using h

theorem primeSet_primeProduct (s : Finset PrimeIdeal) : primeSet (primeProduct s) = s := by
  ext P
  rw [mem_primeSet]
  simp only [primeSupport, factors_primeProduct, Multiset.mem_toFinset,
    Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro ⟨Q,hQ,he⟩
    have : Q=P := Subtype.ext he
    simpa [this] using hQ
  · intro h
    exact ⟨P,h,rfl⟩

theorem primeProduct_injective : Function.Injective primeProduct := by
  intro s t h
  simpa only [primeSet_primeProduct] using congrArg primeSet h

theorem primeProduct_squarefree (s : Finset PrimeIdeal) : Squarefree (primeProduct s) := by
  rw [squarefree_iff_nodup_normalizedFactors (primeProduct_ne_zero s),factors_primeProduct]
  exact s.nodup.map Subtype.val_injective

theorem primeProduct_primeSet (I : Ideal ActualEisensteinCubic.O) (hI : Squarefree I) :
    primeProduct (primeSet I) = I := by
  unfold primeProduct primeSet
  rw [Finset.prod_image]
  · change (∏ P ∈ (primeSupport I).attach, (fun Q : Ideal ActualEisensteinCubic.O => Q) P.val) = I
    exact (Finset.prod_attach (primeSupport I) (fun Q : Ideal ActualEisensteinCubic.O => Q)).trans
      (squarefree_support_product_self hI)
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

def mobiusPrimeCoeff (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  (moebius I : ℂ) * primeValueHom w I

theorem mobiusPrimeCoeff_nonsquarefree (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O)
    (hI : ¬Squarefree I) : mobiusPrimeCoeff w I=0 := by
  simp [mobiusPrimeCoeff,moebius_of_not_squarefree hI]

theorem mobiusPrimeCoeff_primeProduct (w : Ideal ActualEisensteinCubic.O → ℂ) (s : Finset PrimeIdeal) :
    mobiusPrimeCoeff w (primeProduct s) = ∏ P ∈ s, -w P.val := by
  have hm : (moebius (primeProduct s) : ℂ)=(-1:ℂ)^s.card := by
    rw [(primeProduct_squarefree s).moebius_eq,factors_eq_normalizedFactors,
      factors_primeProduct]
    simp
  rw [mobiusPrimeCoeff,hm]
  simp only [primeProduct,map_prod,primeValueHom_prime _ _ (Subtype.property _)]
  rw [Finset.prod_neg]

theorem mobiusPrimeCoeff_tsum (w : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∑' s : Finset PrimeIdeal, ∏ P ∈ s, -w P.val := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun s => primeProduct s.val)
  · exact primeProduct_injective.comp Subtype.val_injective
  · intro I hI
    have hs : Squarefree I := by
      by_contra hs
      exact hI (mobiusPrimeCoeff_nonsquarefree w I hs)
    have hp : (∏ P ∈ primeSet I, -w P.val) ≠ 0 := by
      rw [←mobiusPrimeCoeff_primeProduct,primeProduct_primeSet I hs]
      exact hI
    exact ⟨⟨primeSet I,hp⟩,primeProduct_primeSet I hs⟩
  · intro s
    exact mobiusPrimeCoeff_primeProduct w s.val

theorem mobiusPrimeCoeff_euler (w : Ideal ActualEisensteinCubic.O → ℂ)
    (hw : Summable (fun P : PrimeIdeal => ‖w P.val‖)) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∏' P : PrimeIdeal, (1-w P.val) := by
  rw [mobiusPrimeCoeff_tsum]
  have hs : Summable (fun P : PrimeIdeal => ‖-w P.val‖) := by simpa using hw
  simpa only [sub_eq_add_neg] using
    (tprod_one_add (summable_finsetProd_of_summable_norm hs)).symm

end

section
open ActualEisensteinCubic
open Filter

lemma prime_norm_two_le (P : PrimeIdeal) : 2 ≤ Ideal.absNorm P.val := by
  have h0 : Ideal.absNorm P.val ≠ 0 := fun h => P.property.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P.val ≠ 1 := by
    intro h
    apply P.property.not_isUnit
    rw [Ideal.absNorm_eq_one_iff.mp h]
    simpa only [Ideal.one_eq_top] using (show IsUnit (1 : Ideal ActualEisensteinCubic.O) from isUnit_one)
  omega

lemma prime_norm_pos (P : PrimeIdeal) : (0 : ℝ) < Ideal.absNorm P.val := by
  have h := prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

def primeNormPower (P : PrimeIdeal) (s : ℂ) : ℂ := (Ideal.absNorm P.val : ℂ)^(-s)

def primeCharacterTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal) (s : ℂ) : ℂ :=
  χ (Ideal.absNorm P.val) * primeNormPower P s

def primeDensity (P : PrimeIdeal) : ℂ := 1-(1:ℂ)/(Ideal.absNorm P.val:ℂ)

lemma norm_primeNormPower (P : PrimeIdeal) (s : ℂ) :
    ‖primeNormPower P s‖=(Ideal.absNorm P.val : ℝ)^(-s.re) := by
  exact Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-s)

lemma primeDensity_norm_le_one (P : PrimeIdeal) : ‖primeDensity P‖≤1 := by
  have hn := prime_norm_pos P
  have hn1 : (1:ℝ)≤Ideal.absNorm P.val := by exact_mod_cast (by have:=prime_norm_two_le P;omega)
  have he : primeDensity P = ((1-(1:ℝ)/(Ideal.absNorm P.val:ℝ):ℝ):ℂ) := by
    simp [primeDensity]
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
  · have : (0:ℝ)≤1/(Ideal.absNorm P.val:ℝ) := by positivity
    linarith
  · exact sub_nonneg.mpr ((div_le_one hn).mpr hn1)

lemma primeCharacterTerm_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal)
    (s : ℂ) (σ : ℝ) (hs : σ≤s.re) :
    ‖primeCharacterTerm χ P s‖≤(Ideal.absNorm P.val:ℝ)^(-σ) := by
  rw [primeCharacterTerm,norm_mul,norm_primeNormPower]
  have hn1 : (1:ℝ)≤Ideal.absNorm P.val := by exact_mod_cast (by have:=prime_norm_two_le P;omega)
  calc
    _ ≤ 1*(Ideal.absNorm P.val:ℝ)^(-s.re) :=
      mul_le_mul_of_nonneg_right (χ.norm_le_one _) (by positivity)
    _ ≤ _ := by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hs)

lemma primeCharacterTerm_norm_lt_one {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal)
    (s : ℂ) (hs : 0<s.re) : ‖primeCharacterTerm χ P s‖<1 := by
  apply (primeCharacterTerm_norm_le χ P s s.re le_rfl).trans_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg (by have:=prime_norm_two_le P;exact_mod_cast (by omega:1<Ideal.absNorm P.val)) (by linarith)

lemma one_sub_ne_zero {x : ℂ} (hx : ‖x‖<1) : 1-x≠0 := by
  intro h
  have he : x=1 := (sub_eq_zero.mp h).symm
  simp [he] at hx

lemma correctionDenominator_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal)
    (s : ℂ) (hs : 0<s.re) : 1-primeDensity P*primeCharacterTerm χ P s≠0 := by
  apply one_sub_ne_zero
  rw [norm_mul]
  calc
    _ ≤ 1*‖primeCharacterTerm χ P s‖ :=
      mul_le_mul_of_nonneg_right (primeDensity_norm_le_one P) (norm_nonneg _)
    _ < 1 := by rw [one_mul];exact primeCharacterTerm_norm_lt_one χ P s hs

def correctionTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) : ℂ :=
  if P.val∈S then 0 else
    -((1:ℂ)/(Ideal.absNorm P.val:ℂ))*primeCharacterTerm χ P s /
      (1-primeDensity P*primeCharacterTerm χ P s)

def eulerCorrection {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O)) (s : ℂ) : ℂ :=
  ∏' P : PrimeIdeal, (1+correctionTerm χ S P s)

lemma correctionTerm_factor {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) (hs : 0<s.re) :
    1+correctionTerm χ S P s =
      if P.val∈S then 1 else (1-primeCharacterTerm χ P s)/(1-primeDensity P*primeCharacterTerm χ P s) := by
  by_cases hP : P.val∈S
  · simp [correctionTerm,hP]
  · simp only [correctionTerm,if_neg hP]
    have hd := correctionDenominator_ne_zero χ P s hs
    apply (eq_div_iff hd).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hd]
    dsimp [primeDensity]
    ring

lemma correctionFactor_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) (hs : 0<s.re) : 1+correctionTerm χ S P s≠0 := by
  rw [correctionTerm_factor χ S P s hs]
  split_ifs
  · exact one_ne_zero
  · exact div_ne_zero (one_sub_ne_zero (primeCharacterTerm_norm_lt_one χ P s hs))
      (correctionDenominator_ne_zero χ P s hs)

lemma correctionTerm_uniform_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (σ : ℝ) (hσ : 0<σ) (P : PrimeIdeal) (s : ℂ) (hs : σ≤s.re) :
    ‖correctionTerm χ S P s‖ ≤
      (1-(2:ℝ)^(-σ))⁻¹*(Ideal.absNorm P.val:ℝ)^(-(1+σ)) := by
  have hn := prime_norm_pos P
  have hn2 : (2:ℝ)≤Ideal.absNorm P.val := by exact_mod_cast prime_norm_two_le P
  have hr : (2:ℝ)^(-σ)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr0 : 0<1-(2:ℝ)^(-σ) := sub_pos.mpr hr
  have hx := primeCharacterTerm_norm_le χ P s σ hs
  have hx2 : ‖primeCharacterTerm χ P s‖≤(2:ℝ)^(-σ) := hx.trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith))
  have hd : 1-(2:ℝ)^(-σ)≤‖1-primeDensity P*primeCharacterTerm χ P s‖ := by
    have hb : ‖primeDensity P*primeCharacterTerm χ P s‖≤(2:ℝ)^(-σ) := by
      rw [norm_mul]
      calc
        _ ≤ 1*‖primeCharacterTerm χ P s‖ :=
          mul_le_mul_of_nonneg_right (primeDensity_norm_le_one P) (norm_nonneg _)
        _ ≤ _ := by simpa using hx2
    have hh := norm_sub_norm_le (1:ℂ) (primeDensity P*primeCharacterTerm χ P s)
    simpa only [norm_one] using (show 1-(2:ℝ)^(-σ) ≤ ‖(1:ℂ)‖-‖primeDensity P*primeCharacterTerm χ P s‖ from by simpa using sub_le_sub_left hb 1) |>.trans hh
  by_cases hP : P.val∈S
  · simp only [correctionTerm,if_pos hP,norm_zero]
    positivity
  · rw [correctionTerm,if_neg hP,norm_div,norm_mul,norm_neg,norm_div,norm_one,Complex.norm_natCast]
    calc
      _ ≤ ((1:ℝ)/(Ideal.absNorm P.val:ℝ)*(Ideal.absNorm P.val:ℝ)^(-σ))/(1-(2:ℝ)^(-σ)) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hx (by positivity)) hr0 hd
      _ = _ := by
        rw [show -(1+σ)=(-1)+(-σ) by ring,Real.rpow_add hn,Real.rpow_neg_one]
        ring

lemma prime_norm_series_summable (σ : ℝ) (hσ : 0<σ) :
    Summable (fun P : PrimeIdeal => (Ideal.absNorm P.val:ℝ)^(-(1+σ))) := by
  have ht := (CubicEisenstein.fullIdealWeight_summable_norm (1+(σ:ℂ)) (by simp;linarith)).comp_injective
    (i := fun P : PrimeIdeal => P.val) Subtype.val_injective
  apply ht.congr
  intro P
  simp only [Function.comp_def,CubicEisenstein.fullIdealWeight,if_neg P.property.ne_zero]
  simpa only [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.ofReal_re,
    Complex.ofReal_natCast] using
    (Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-(1+(σ:ℂ))))

lemma correctionTerm_summable {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 0<s.re) : Summable (fun P : PrimeIdeal => ‖correctionTerm χ S P s‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => correctionTerm_uniform_bound χ S s.re hs P s le_rfl)
  exact (prime_norm_series_summable s.re hs).mul_left _

theorem eulerCorrection_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 0<s.re) : eulerCorrection χ S s≠0 :=
  tprod_one_add_ne_zero_of_summable (fun P => correctionFactor_ne_zero χ S P s hs)
    (correctionTerm_summable χ S s hs)

lemma primeCharacterTerm_differentiable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : PrimeIdeal) : Differentiable ℂ (primeCharacterTerm χ P) := by
  have hn : (Ideal.absNorm P.val:ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (prime_norm_pos P))
  exact ((differentiable_id.neg).const_cpow (Or.inl hn)).const_mul _

lemma correctionTerm_differentiableOn {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (P : PrimeIdeal) (σ : ℝ) (hσ : 0≤σ) :
    DifferentiableOn ℂ (correctionTerm χ S P) {s:ℂ | σ<s.re} := by
  unfold correctionTerm
  by_cases hP : P.val∈S
  · simpa only [if_pos hP] using (differentiableOn_const (𝕜 := ℂ) (s := {s:ℂ | σ<s.re}) (c := (0:ℂ)))
  · simp only [if_neg hP]
    intro s hs
    have hx := primeCharacterTerm_differentiable χ P s
    convert! ((hx.const_mul (-((1:ℂ)/(Ideal.absNorm P.val:ℂ)))).div
      ((differentiableAt_const (1:ℂ)).sub (hx.const_mul (primeDensity P)))
      (correctionDenominator_ne_zero χ P s (lt_of_le_of_lt hσ hs))).differentiableWithinAt using 1

lemma eulerCorrection_locally_uniform {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (σ : ℝ) (hσ : 0<σ) :
    HasProdLocallyUniformlyOn (fun P s => 1+correctionTerm χ S P s)
      (eulerCorrection χ S) {s:ℂ | σ<s.re} := by
  have hu := (prime_norm_series_summable σ hσ).mul_left ((1-(2:ℝ)^(-σ))⁻¹)
  exact hu.hasProdLocallyUniformlyOn_one_add
    (isOpen_lt continuous_const Complex.continuous_re)
    (Filter.Eventually.of_forall (fun P s hs => correctionTerm_uniform_bound χ S σ hσ P s hs.le))
    (fun P => (correctionTerm_differentiableOn χ S P σ hσ.le).continuousOn)

theorem eulerCorrection_differentiableOn_halfplane {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (σ : ℝ) (hσ : 0<σ) :
    DifferentiableOn ℂ (eulerCorrection χ S) {s:ℂ | σ<s.re} := by
  apply (eulerCorrection_locally_uniform χ S σ hσ).differentiableOn
  · apply Filter.Eventually.of_forall
    intro t
    change DifferentiableOn ℂ (fun z => ∏ P ∈ t, (1+correctionTerm χ S P z)) _
    apply DifferentiableOn.fun_finsetProd
    intro P hP
    exact (differentiableOn_const (𝕜 := ℂ) (c := (1:ℂ))).add
      (correctionTerm_differentiableOn χ S P σ hσ.le)
  · exact isOpen_lt continuous_const Complex.continuous_re

theorem eulerCorrection_differentiableOn {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : DifferentiableOn ℂ (eulerCorrection χ S) {s:ℂ | 0<s.re} := by
  intro s hs
  have hh := eulerCorrection_differentiableOn_halfplane χ S (s.re/2) (by dsimp at hs;linarith)
  exact (hh.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show s∈{z:ℂ | s.re/2<z.re} by dsimp at *;linarith))).differentiableWithinAt

end

section
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

lemma prod_primeSet {M : Type*} [CommMonoid M] (I : Ideal ActualEisensteinCubic.O) (f : Ideal ActualEisensteinCubic.O→M) :
    (∏P∈primeSet I,f P.val)=∏P∈primeSupport I,f P := by
  unfold primeSet
  rw [Finset.prod_image]
  · exact Finset.prod_attach (primeSupport I) f
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

lemma primeValueHom_squarefree (w : Ideal ActualEisensteinCubic.O→ℂ) (I : Ideal ActualEisensteinCubic.O) (hI : Squarefree I) :
    primeValueHom w I=∏P∈primeSet I,w P.val := by
  calc
    _ = primeValueHom w (primeProduct (primeSet I)) :=
      congrArg (primeValueHom w) (primeProduct_primeSet I hI).symm
    _ = _ := by simp only [primeProduct,map_prod,primeValueHom_prime _ _ (Subtype.property _)]

lemma outside_primeProduct_iff (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P)
    (t : Finset PrimeIdeal) :
    (∀P∈S,¬P∣primeProduct t) ↔ ∀Q∈t,Q.val∉S := by
  constructor
  · intro h Q hQ hQS
    apply h Q.val hQS
    exact Finset.dvd_prod_of_mem (fun P : PrimeIdeal => P.val) hQ
  · intro h P hP hd
    obtain ⟨Q,hQ,hPQ⟩ := ((hS P hP).dvd_finsetProd_iff (fun Q : PrimeIdeal => Q.val)).mp hd
    have he : P=Q.val := associated_iff_eq.mp (((hS P hP).dvd_prime_iff_associated Q.property).mp hPQ)
    exact h Q hQ (he ▸ hP)

def outsideMask (S : Finset (Ideal ActualEisensteinCubic.O)) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if ∀P∈S,¬P∣I then 1 else 0

lemma prod_cut_primes (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P)
    (t : Finset PrimeIdeal) (f : Ideal ActualEisensteinCubic.O→ℂ) :
    (∏Q∈t,if Q.val∈S then 0 else f Q.val)=outsideMask S (primeProduct t)*(∏Q∈t,f Q.val) := by
  by_cases ho : ∀P∈S,¬P∣primeProduct t
  · rw [outsideMask,if_pos ho,one_mul]
    apply Finset.prod_congr rfl
    intro Q hQ
    exact if_neg ((outside_primeProduct_iff S hS t).mp ho Q hQ)
  · rw [outsideMask,if_neg ho,zero_mul]
    have hh : ¬∀Q∈t,Q.val∉S := fun h => ho ((outside_primeProduct_iff S hS t).mpr h)
    push Not at hh
    obtain ⟨Q,hQ,hQS⟩ := hh
    exact Finset.prod_eq_zero hQ (if_pos hQS)

lemma nat_cpow_prod {ι : Type*} (t : Finset ι) (N : ι→ℕ) (s : ℂ) :
    ((∏i∈t,N i : ℕ):ℂ)^s=∏i∈t,(N i:ℂ)^s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Nat.cast_mul,Complex.natCast_mul_natCast_cpow,ih]

lemma primeNormTerm_prod {q : ℕ} (χ : DirichletCharacter ℂ q) (t : Finset PrimeIdeal) (s : ℂ) :
    (∏P∈t,χ (Ideal.absNorm P.val)*(Ideal.absNorm P.val:ℂ)^(-s))=
      χ (Ideal.absNorm (primeProduct t))*(Ideal.absNorm (primeProduct t):ℂ)^(-s) := by
  rw [Finset.prod_mul_distrib]
  simp only [primeProduct,map_prod,Nat.cast_prod]
  congr 1
  simpa only [Nat.cast_prod] using (nat_cpow_prod t (fun P=>Ideal.absNorm P.val) (-s)).symm

def ordinaryPrimeValue {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if I∈S then 0 else χ (Ideal.absNorm I)*(Ideal.absNorm I:ℂ)^(-s)

def dampedPrimeValue {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if I∈S then 0 else (1-(1:ℂ)/(Ideal.absNorm I:ℂ))*(χ (Ideal.absNorm I)*(Ideal.absNorm I:ℂ)^(-s))

def ordinarySeriesTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  outsideMask S I * baseChangeWeight χ I * CubicEisenstein.fullIdealWeight s I

def dampedSeriesTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  ordinarySeriesTerm χ S s I * SixthPowerAverage.totientDensity I

lemma ordinarySeriesTerm_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (I : Ideal ActualEisensteinCubic.O) :
    ordinarySeriesTerm χ S s I = mobiusPrimeCoeff (ordinaryPrimeValue χ S s) I := by
  by_cases hI : Squarefree I
  · rw [mobiusPrimeCoeff,primeValueHom_squarefree _ I hI]
    simp only [ordinaryPrimeValue]
    rw [prod_cut_primes S hS (primeSet I) (fun P => χ (Ideal.absNorm P)*(Ideal.absNorm P:ℂ)^(-s)),
      primeNormTerm_prod,primeProduct_primeSet I hI]
    simp only [ordinarySeriesTerm,baseChangeWeight,CubicEisenstein.fullIdealWeight,if_neg hI.ne_zero]
    ring
  · simp [ordinarySeriesTerm,baseChangeWeight,mobiusPrimeCoeff_nonsquarefree _ I hI,
      moebius_of_not_squarefree hI]

lemma dampedSeriesTerm_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (I : Ideal ActualEisensteinCubic.O) :
    dampedSeriesTerm χ S s I = mobiusPrimeCoeff (dampedPrimeValue χ S s) I := by
  by_cases hI : Squarefree I
  · rw [mobiusPrimeCoeff,primeValueHom_squarefree _ I hI]
    simp only [dampedPrimeValue]
    rw [prod_cut_primes S hS (primeSet I) (fun P => (1-(1:ℂ)/(Ideal.absNorm P:ℂ))*(χ (Ideal.absNorm P)*(Ideal.absNorm P:ℂ)^(-s))),
      Finset.prod_mul_distrib,primeNormTerm_prod,
      prod_primeSet I (fun P => (1-(1:ℂ)/(Ideal.absNorm P:ℂ))),
      primeProduct_primeSet I hI]
    simp only [dampedSeriesTerm,ordinarySeriesTerm,baseChangeWeight,SixthPowerAverage.totientDensity,
      CubicEisenstein.fullIdealWeight,if_neg hI.ne_zero]
    ring
  · simp [dampedSeriesTerm,ordinarySeriesTerm,baseChangeWeight,mobiusPrimeCoeff_nonsquarefree _ I hI,
      moebius_of_not_squarefree hI]

end

open ActualEisensteinCubic

lemma ordinaryPrimeValue_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) :
    ‖ordinaryPrimeValue χ S s P.val‖≤(Ideal.absNorm P.val:ℝ)^(-s.re) := by
  by_cases hP : P.val∈S
  · simp only [ordinaryPrimeValue,if_pos hP,norm_zero]
    positivity
  · simpa only [ordinaryPrimeValue,if_neg hP,primeCharacterTerm,primeNormPower] using
      primeCharacterTerm_norm_le χ P s s.re le_rfl

lemma dampedPrimeValue_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) :
    ‖dampedPrimeValue χ S s P.val‖≤(Ideal.absNorm P.val:ℝ)^(-s.re) := by
  by_cases hP : P.val∈S
  · simp only [dampedPrimeValue,if_pos hP,norm_zero]
    positivity
  · change ‖if P.val∈S then 0 else primeDensity P*primeCharacterTerm χ P s‖≤_
    rw [if_neg hP,norm_mul]
    exact (mul_le_mul_of_nonneg_right (primeDensity_norm_le_one P) (norm_nonneg _)).trans
      (by simpa using primeCharacterTerm_norm_le χ P s s.re le_rfl)

lemma prime_reciprocal_series_summable (s : ℂ) (hs : 1<s.re) :
    Summable (fun P : PrimeIdeal => (Ideal.absNorm P.val:ℝ)^(-s.re)) := by
  have hh := prime_norm_series_summable (s.re-1) (by linarith)
  simpa only [show 1+(s.re-1)=s.re by ring] using hh

lemma ordinaryPrimeValue_summable {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : Summable (fun P : PrimeIdeal => ‖ordinaryPrimeValue χ S s P.val‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => ordinaryPrimeValue_norm_le χ S P s) (prime_reciprocal_series_summable s hs)

lemma dampedPrimeValue_summable {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : Summable (fun P : PrimeIdeal => ‖dampedPrimeValue χ S s P.val‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => dampedPrimeValue_norm_le χ S P s) (prime_reciprocal_series_summable s hs)

lemma ordinarySeries_euler {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,ordinarySeriesTerm χ S s I)=
      ∏'P : PrimeIdeal,(1-ordinaryPrimeValue χ S s P.val) := by
  simp_rw [ordinarySeriesTerm_eq χ S hS]
  exact mobiusPrimeCoeff_euler _ (ordinaryPrimeValue_summable χ S s hs)

lemma dampedSeries_euler {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,dampedSeriesTerm χ S s I)=
      ∏'P : PrimeIdeal,(1-dampedPrimeValue χ S s P.val) := by
  simp_rw [dampedSeriesTerm_eq χ S hS]
  exact mobiusPrimeCoeff_euler _ (dampedPrimeValue_summable χ S s hs)

lemma local_correction_identity {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) (hs : 0<s.re) :
    (1-dampedPrimeValue χ S s P.val)*(1+correctionTerm χ S P s)=
      1-ordinaryPrimeValue χ S s P.val := by
  rw [correctionTerm_factor χ S P s hs]
  by_cases hP : P.val∈S
  · simp [dampedPrimeValue,ordinaryPrimeValue,hP]
  · simp only [dampedPrimeValue,ordinaryPrimeValue,if_neg hP]
    change (1-primeDensity P*primeCharacterTerm χ P s)*
      ((1-primeCharacterTerm χ P s)/(1-primeDensity P*primeCharacterTerm χ P s))=
      1-primeCharacterTerm χ P s
    exact mul_div_cancel₀ _ (correctionDenominator_ne_zero χ P s hs)

theorem actual_dirichlet_correction {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,ordinarySeriesTerm χ S s I)=
      eulerCorrection χ S s*(∑'I : Ideal ActualEisensteinCubic.O,dampedSeriesTerm χ S s I) := by
  rw [ordinarySeries_euler χ S hS s hs,dampedSeries_euler χ S hS s hs,mul_comm]
  have hd : Multipliable (fun P : PrimeIdeal => 1-dampedPrimeValue χ S s P.val) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (show Summable (fun P : PrimeIdeal => ‖-dampedPrimeValue χ S s P.val‖) by
        simpa only [norm_neg] using dampedPrimeValue_summable χ S s hs)
  have hc := multipliable_one_add_of_summable (correctionTerm_summable χ S s (by linarith))
  change _ = (∏' P : PrimeIdeal, (1-dampedPrimeValue χ S s P.val))*(∏' P : PrimeIdeal, (1+correctionTerm χ S P s))
  rw [←hd.tprod_mul hc]
  apply tprod_congr
  intro P
  exact (local_correction_identity χ S P s (by linarith)).symm

open scoped BigOperators Classical
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O

lemma normFiber_tsum (a : Ideal ActualEisensteinCubic.O→ℂ) (n : ℕ) :
    (∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},a I.val)=normFiberCoeff a n := by
  let : Fintype {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := ActualEisensteinCubic.O) n).fintype
  rw [tsum_fintype]
  symm
  change (∑I∈FiniteSFactor.fiber n,a I)=_
  apply Finset.sum_bij (fun I hI => (⟨I,FiniteSFactor.mem_fiber.mp hI⟩ : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n}))
  · intro I hI
    exact Finset.mem_univ _
  · intro I hI J hJ he
    exact congrArg Subtype.val he
  · intro I hI
    exact ⟨I.val,FiniteSFactor.mem_fiber.mpr I.property,rfl⟩
  · intro I hI
    rfl

lemma idealDirichlet_fiber (a : Ideal ActualEisensteinCubic.O→ℂ) (s : ℂ) (n : ℕ) :
    (∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},a I.val*CubicEisenstein.fullIdealWeight s I.val)=
      LSeries.term (normFiberCoeff a) s n := by
  by_cases hn : n=0
  · subst n
    have hz (I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=0}) : CubicEisenstein.fullIdealWeight s I.val=0 := by
      have hI : I.val=0 := Ideal.absNorm_eq_zero_iff.mp I.property
      simp [CubicEisenstein.fullIdealWeight,hI]
    simp only [hz,mul_zero,tsum_zero,LSeries.term_zero]
  · have ht (I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n}) :
        CubicEisenstein.fullIdealWeight s I.val=(n:ℂ)^(-s) := by
      have hI : I.val≠0 := fun h => hn (by rw [←I.property,h,map_zero])
      rw [CubicEisenstein.fullIdealWeight,if_neg hI,I.property]
    simp_rw [ht]
    rw [tsum_mul_right,normFiber_tsum,LSeries.term_of_ne_zero hn,Complex.cpow_neg,div_eq_mul_inv]

lemma idealDirichlet_summable (a : Ideal ActualEisensteinCubic.O→ℂ) (ha : ∀I,‖a I‖≤1) (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal ActualEisensteinCubic.O => a I*CubicEisenstein.fullIdealWeight s I) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun I => ?_) (CubicEisenstein.fullIdealWeight_summable_norm s hs)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem idealDirichlet_eq_LSeries (a : Ideal ActualEisensteinCubic.O→ℂ) (ha : ∀I,‖a I‖≤1)
    (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,a I*CubicEisenstein.fullIdealWeight s I)=LSeries (normFiberCoeff a) s := by
  have hh := (idealDirichlet_summable a ha s hs).hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},
    a I.val*CubicEisenstein.fullIdealWeight s I.val) _ at hh
  simp_rw [idealDirichlet_fiber] at hh
  exact hh.tsum_eq.symm

lemma ordinarySeriesTerm_outside {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ordinarySeriesTerm χ S s I=
      FiniteSFactor.outsideWeight S (baseChangeWeight χ) I*CubicEisenstein.fullIdealWeight s I := by
  unfold ordinarySeriesTerm outsideMask FiniteSFactor.outsideWeight
  split_ifs <;> simp

lemma dampedSeriesTerm_outside {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : dampedSeriesTerm χ S s I=
      SixthPowerAverage.outsideWeight χ S I*CubicEisenstein.fullIdealWeight s I := by
  unfold dampedSeriesTerm ordinarySeriesTerm outsideMask SixthPowerAverage.outsideWeight
    FiniteSFactor.outsideWeight SixthPowerAverage.weightedMoebius
  split_ifs <;> ring

lemma ordinarySeries_eq_LSeries {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : (∑'I : Ideal ActualEisensteinCubic.O,ordinarySeriesTerm χ S s I)=
      LSeries (FiniteSFactor.outsideCoeff S (baseChangeWeight χ)) s := by
  simp_rw [ordinarySeriesTerm_outside]
  apply idealDirichlet_eq_LSeries
  intro I
  unfold FiniteSFactor.outsideWeight
  split_ifs
  · exact ConcretePrimeRowBridge.baseChangeWeight_norm_le_one χ I
  · simp
  exact hs

lemma dampedSeries_eq_LSeries {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : (∑'I : Ideal ActualEisensteinCubic.O,dampedSeriesTerm χ S s I)=
      LSeries (SixthPowerAverage.weightedCoeff χ S) s := by
  simp_rw [dampedSeriesTerm_outside]
  exact idealDirichlet_eq_LSeries _ (SixthPowerAverage.outsideWeight_norm_le_one χ S) s hs

theorem actual_LSeries_correction {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    LSeries (FiniteSFactor.outsideCoeff S (baseChangeWeight χ)) s=
      eulerCorrection χ S s*LSeries (SixthPowerAverage.weightedCoeff χ S) s := by
  rw [←ordinarySeries_eq_LSeries χ S s hs,←dampedSeries_eq_LSeries χ S s hs]
  exact actual_dirichlet_correction χ S hS s hs

theorem full_LSeries_correction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 2<s.re) :
    LSeries (normFiberCoeff (baseChangeWeight χ)) s=
      (CompactMellinBridge.finiteEulerFactor χ S s*eulerCorrection χ S s)*
        LSeries (SixthPowerAverage.weightedCoeff χ S) s := by
  rw [FiniteSFactor.normFiberLSeries_finiteEuler_baseChange χ S hS s hs,
    actual_LSeries_correction χ S hS s (by linarith)]
  exact (mul_assoc _ _ _).symm

theorem eulerCorrection_analytic {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    AnalyticOnNhd ℂ (eulerCorrection χ S) {s : ℂ | 0<s.re} :=
  (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).mpr
    (eulerCorrection_differentiableOn χ S)

end SmoothMobiusCorrection

end

end OAI

end


