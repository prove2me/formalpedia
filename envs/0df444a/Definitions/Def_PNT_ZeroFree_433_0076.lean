-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0076
-- name    : PNT_ZeroFree_433_0076
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T21:21:31.054126+00:00
-- url     : https://prove2.me/theorems/6f5c59f9-4344-434b-bed2-c64cab300ed3
-- title:
--   Zero-free region foundations: Eisenstein.PrimitiveRows [0076]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.PrimitiveRows
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/PrimitiveRows.lean#L77-L645

import Definitions.Def_PNT_ZeroFree_433_0074

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/PrimitiveRows.lean#L77-L645
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Eisenstein.PrimitiveRows
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

namespace CubicEisenstein
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

lemma levelThree_of_entries (M : SL(2,O))
    (h : ∀ i j : Fin 2, (3 : O) ∣ M i j - (if i=j then 1 else 0)) :
    M ∈ levelThree := by
  change Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)})) M = 1
  apply Subtype.ext
  funext i j
  change Ideal.Quotient.mk (Ideal.span {(3 : O)}) (M i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ Ideal.span {(3 : O)})) i j
  have hh : Ideal.Quotient.mk (Ideal.span {(3 : O)}) (M i j) =
      Ideal.Quotient.mk (Ideal.span {(3 : O)}) (if i=j then 1 else 0) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (h i j))
  simpa only [Matrix.one_apply, apply_ite, map_one, map_zero] using hh

lemma row_coprime (M : levelThree) : IsCoprime (row M 0) (row M 1) := by
  have h : (M : SL(2,O)) 0 0*(M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1*(M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  refine ⟨-(M : SL(2,O)) 0 1, (M : SL(2,O)) 0 0, ?_⟩
  change -(M : SL(2,O)) 0 1*(M : SL(2,O)) 1 0 +
    (M : SL(2,O)) 0 0*(M : SL(2,O)) 1 1 = 1
  linear_combination h

lemma exists_matrix_of_primitive_row (c d : O) (hcop : IsCoprime c d)
    (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    ∃ M : levelThree, row M = ![c,d] := by
  obtain ⟨r,s,hrs⟩ := hcop
  let M : SL(2,O) := ⟨!![s+r*c,r*(d-1); c,d], by
    rw [Matrix.det_fin_two]
    change (s+r*c)*d-(r*(d-1))*c=1
    linear_combination hrs⟩
  have hA : s+r*c-1 = -s*(d-1) := by linear_combination hrs
  have hM : M ∈ levelThree := by
    apply levelThree_of_entries
    intro i j
    fin_cases i <;> fin_cases j
    · change (3 : O) ∣ s+r*c-1
      rw [hA]
      exact hd.mul_left (-s)
    · change (3 : O) ∣ r*(d-1)-0
      simpa only [sub_zero] using hd.mul_left r
    · change (3 : O) ∣ c-(if (1 : Fin 2)=0 then 1 else 0)
      simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false, sub_zero] using hc
    · change (3 : O) ∣ d-1
      exact hd
  exact ⟨⟨M,hM⟩, rfl⟩

def PrimitiveRow := {v : Fin 2 → O //
  IsCoprime (v 0) (v 1) ∧ (3 : O) ∣ v 0 ∧ (3 : O) ∣ v 1-1}

def cosetPrimitiveRow (x : CuspCosets) : PrimitiveRow :=
  ⟨cosetRow x, by
    induction x using Quotient.inductionOn with | _ M =>
      change IsCoprime (row M 0) (row M 1) ∧ (3 : O) ∣ row M 0 ∧ (3 : O) ∣ row M 1-1
      exact ⟨row_coprime M, levelThree_lower M, by simpa [row] using levelThree_entry M 1 1⟩⟩

lemma cosetPrimitiveRow_bijective : Function.Bijective cosetPrimitiveRow := by
  constructor
  · intro x y hxy
    exact cosetRow_injective (congrArg Subtype.val hxy)
  · intro v
    obtain ⟨M,hM⟩ := exists_matrix_of_primitive_row (v.1 0) (v.1 1)
      v.2.1 v.2.2.1 v.2.2.2
    refine ⟨cosetOf M, ?_⟩
    apply Subtype.ext
    change row M = v.1
    rw [hM]
    funext i
    fin_cases i <;> rfl

def primitiveRowEquiv : CuspCosets ≃ PrimitiveRow := Equiv.ofBijective _ cosetPrimitiveRow_bijective

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal

lemma inverse_character_eq_row_symbol (M : levelThree) :
    (complexCharacter M)⁻¹ = eisEmbedding (symbol (row M 0) (row M 1)) := by
  let a := (M : SL(2,O)) 0 0
  let b := (M : SL(2,O)) 0 1
  let c := (M : SL(2,O)) 1 0
  let d := (M : SL(2,O)) 1 1
  have hdet : a*d-b*c=1 := by
    simpa only [a,b,c,d,Matrix.det_fin_two] using (M : SL(2,O)).property
  have had : a*d-1=b*c := by linear_combination hdet
  have ha : lambda^2 ∣ a-1 := levelThree_primary M
  have hd3 : (3 : O) ∣ d-1 := by simpa [d] using levelThree_entry M 1 1
  have hd : lambda^2 ∣ d-1 := lambda_sq_dvd_three.trans hd3
  obtain ⟨b0,hb⟩ := levelThree_upper M
  obtain ⟨c0,hc⟩ := levelThree_lower M
  change b=3*b0 at hb
  change c=3*c0 at hc
  have h9 : (9 : O) ∣ a*d-1 := by
    refine ⟨b0*c0, ?_⟩
    rw [had,hb,hc]
    ring
  have hcd : c ∣ a*d-1 := by rw [had]; exact dvd_mul_left c b
  have hs := symbol_denominator_congr c (a*d) 1 (primary_mul a d ha hd) (by first | simp | exact_mod_cast le_top) h9 hcd
  rw [symbol_mul_denominator, symbol_one] at hs
  have hm : eisEmbedding (symbol c a)*eisEmbedding (symbol c d)=1 := by
    simpa only [map_mul, map_one] using congrArg eisEmbedding hs
  change (eisEmbedding (symbol c a))⁻¹ = eisEmbedding (symbol c d)
  exact inv_eq_of_mul_eq_one_right hm

lemma inverse_cosetCharacter_eq_row_symbol (x : CuspCosets) :
    (cosetCharacter x)⁻¹ = eisEmbedding (symbol (cosetRow x 0) (cosetRow x 1)) := by
  induction x using Quotient.inductionOn with | _ M => exact inverse_character_eq_row_symbol M

def primitiveRowPhase (v : PrimitiveRow) : ℂ :=
  eisEmbedding (symbol (v.1 0) (v.1 1))

lemma primitiveRowEquiv_val (x : CuspCosets) : (primitiveRowEquiv x).1 = cosetRow x := rfl

lemma primitiveRowEquiv_symm_row (v : PrimitiveRow) :
    cosetRow (primitiveRowEquiv.symm v) = v.1 := by
  exact congrArg Subtype.val (primitiveRowEquiv.apply_symm_apply v)

theorem upperEisenstein_eq_primitive_rows (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) :
    upperEisenstein z v hv s = ∑' row : PrimitiveRow,
      primitiveRowPhase row *
        ((v / (‖eisEmbedding (row.1 0)*z+eisEmbedding (row.1 1)‖^2 +
          ‖eisEmbedding (row.1 0)‖^2*v^2) : ℝ) : ℂ)^s := by
  rw [upperEisenstein_eq_source_series]
  rw [← primitiveRowEquiv.symm.tsum_eq]
  apply tsum_congr
  intro r
  rw [inverse_cosetCharacter_eq_row_symbol, primitiveRowEquiv_symm_row]
  simp only [primitiveRowPhase, transformedHeight, heightDenominator, embeddedRow,
    Function.comp_apply, primitiveRowEquiv_symm_row]

theorem primitive_rows_summable_norm (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun row : PrimitiveRow => ‖primitiveRowPhase row *
      ((v / (‖eisEmbedding (row.1 0)*z+eisEmbedding (row.1 1)‖^2 +
        ‖eisEmbedding (row.1 0)‖^2*v^2) : ℝ) : ℂ)^s‖) := by
  apply primitiveRowEquiv.summable_iff.mp
  apply (summable_norm_summand (upperSection z v hv) s hs).congr
  intro x
  rw [summand_upperSection, inverse_cosetCharacter_eq_row_symbol]
  rfl

lemma primitiveRow_zero_left (row : PrimitiveRow) (hc : row.1 0 = 0) : row.1 1 = 1 := by
  have hu : IsUnit (row.1 1) := by simpa only [hc, isCoprime_zero_left] using row.2.1
  exact A3_primary_unit_eq_one _ hu (lambda_sq_dvd_three.trans row.2.2.2)

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson

def radialSource (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' z : O, if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X)

def radialDual (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' h : O, if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)

theorem radialSource_summable (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun z : O => if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X)) := by
  have hs : Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / X)) := by
    simpa only [scaledRadialTest_apply] using
      (actual_eisenstein_summable_norm (scaledRadialTest W X hX)).of_norm
  convert! hs.indicator {z : O | z ≠ 0} using 1
  ext z
  by_cases hz : z = 0 <;> simp [hz]

theorem radialSource_poisson (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    radialSource W X = (X : ℂ) * paperRadialFourier W 0 - W 0 +
      (X : ℂ) * radialDual W X := by
  let P : Empty → Ideal O := Empty.elim
  let : ∀ i, (P i).IsMaximal := fun i => nomatch i
  have hi : Function.Injective P := by intro i; cases i
  have hp := masked_principal_radial_poisson_zero_split P hi ∅ W X hX
  simp only [maskedPrincipalRemainder, Finset.prod_empty, Finset.powerset_empty,
    Finset.sum_singleton, UniqueFactorizationMonoid.moebius_one, map_one,
    Int.cast_one, Nat.cast_one, div_one, mul_one] at hp
  simp only [rowCoprimeMask, Finset.notMem_empty, false_and, exists_false,
    ite_false, one_mul] at hp
  have hs : Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / X)) := by
    simpa only [scaledRadialTest_apply] using
      (actual_eisenstein_summable_norm (scaledRadialTest W X hX)).of_norm
  have hz := hs.tsum_eq_add_tsum_ite 0
  simp only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div] at hz
  change (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / X)) =
    (X : ℂ) * paperRadialFourier W 0 + (X : ℂ) * radialDual W X at hp
  change (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / X)) = W 0 + radialSource W X at hz
  linear_combination hp - hz

def subsetNorm {ι : Type*} (P : ι → Ideal O) (E : Finset ι) : ℝ :=
  Ideal.absNorm (∏ i ∈ E, P i)

def subsetMobius {ι : Type*} (P : ι → Ideal O) (E : Finset ι) : ℂ :=
  UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i)

def smallDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Z : ℝ) :=
  S.powerset.filter (fun E => subsetNorm P E ≤ Z)

def largeDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Z : ℝ) :=
  S.powerset.filter (fun E => Z < subsetNorm P E)

theorem subsetNorm_pos {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset ι) :
    0 < subsetNorm P E := by
  rw [subsetNorm, ← primeSubsetGenerator_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))

theorem sum_small_add_large {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    (S : Finset ι) (Z : ℝ) (f : Finset ι → ℂ) :
    (∑ E ∈ smallDivisors P S Z, f E) + (∑ E ∈ largeDivisors P S Z, f E) =
      ∑ E ∈ S.powerset, f E := by
  simpa only [smallDivisors, largeDivisors, not_le] using
    Finset.sum_filter_add_sum_filter_not S.powerset (fun E => subsetNorm P E ≤ Z) f

theorem masked_radialSource_dilations {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) =
      ∑ E ∈ S.powerset, subsetMobius P E * radialSource W (X / subsetNorm P E) := by
  rw [tsum_rowCoprimeMask_dilations P hinj S _ (radialSource_summable W X hX)]
  apply Finset.sum_congr rfl
  intro E hE
  change subsetMobius P E * _ = _
  congr 1
  apply tsum_congr
  intro z
  rw [mul_eq_zero, or_iff_right (primeSubsetGenerator_ne_zero P E)]
  by_cases hz : z = 0
  · simp [hz]
  · rw [if_neg hz, if_neg hz, map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_sq]
    congr 1
    simp only [subsetNorm, div_div_eq_mul_div]
    ring

theorem masked_radialSource_truncated {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Z : ℝ) (hX : 0 < X) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) =
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ E ∈ smallDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
      W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E) +
      (X : ℂ) * (∑ E ∈ smallDivisors P S Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  rw [masked_radialSource_dilations P hinj S W X hX,
    ← sum_small_add_large P S Z]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  rw [radialSource_poisson W _ (div_pos hX (subsetNorm_pos P E))]
  push_cast
  ring

theorem masked_radialSource_truncated_euler {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Z : ℝ) (hX : 0 < X) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ E ∈ largeDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
      W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E) +
      (X : ℂ) * (∑ E ∈ smallDivisors P S Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  rw [masked_radialSource_truncated P hinj S W X Z hX]
  have hs := sum_small_add_large P S Z (fun E => subsetMobius P E / (subsetNorm P E : ℂ))
  have hprime : ∀ i, Prime (P i) := fun i => Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  have he := primeSubset_moebius_norm_sum P hprime hinj S
  change (∑ E ∈ S.powerset, subsetMobius P E / (subsetNorm P E : ℂ)) = _ at he
  rw [he] at hs
  linear_combination (X : ℂ) * paperRadialFourier W 0 * hs

end

local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def middleDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Y Z : ℝ) :=
  (smallDivisors P S Z).filter (fun E => Y < subsetNorm P E)

def dualNear (W : ℝ → ℂ) (X lengthScale : ℝ) : ℂ :=
  ∑' h : O, if ‖eisEmbedding h‖ ^ 2 ≤ lengthScale then
    (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0

def dualFar (W : ℝ → ℂ) (X lengthScale : ℝ) : ℂ :=
  ∑' h : O, if lengthScale < ‖eisEmbedding h‖ ^ 2 then
    (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0

theorem radialDual_summable (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun h : O => if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) := by
  have hs := (paperRadialFourier_lattice_summable_norm W X hX).of_norm
  convert! hs.indicator {z : O | z ≠ 0} using 1
  ext z
  by_cases hz : z = 0 <;> simp [hz]

theorem radialDual_near_add_far (W : 𝓢(ℝ, ℂ)) (X lengthScale : ℝ) (hX : 0 < X) :
    radialDual W X = dualNear W X lengthScale + dualFar W X lengthScale := by
  have hs := radialDual_summable W X hX
  have hn : Summable (fun h : O => if ‖eisEmbedding h‖ ^ 2 ≤ lengthScale then
      (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0) := by
    exact hs.indicator {h : O | ‖eisEmbedding h‖ ^ 2 ≤ lengthScale}
  have hf : Summable (fun h : O => if lengthScale < ‖eisEmbedding h‖ ^ 2 then
      (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0) := by
    exact hs.indicator {h : O | lengthScale < ‖eisEmbedding h‖ ^ 2}
  unfold radialDual dualNear dualFar
  rw [← hn.tsum_add hf]
  apply tsum_congr
  intro h
  by_cases hL : ‖eisEmbedding h‖ ^ 2 ≤ lengthScale <;> simp [hL, not_lt_of_ge, lt_of_not_ge]

theorem sum_small_add_middle {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    (S : Finset ι) (Y Z : ℝ) (hYZ : Y ≤ Z) (f : Finset ι → ℂ) :
    (∑ E ∈ smallDivisors P S Y, f E) + (∑ E ∈ middleDivisors P S Y Z, f E) =
      ∑ E ∈ smallDivisors P S Z, f E := by
  have hsmall : (smallDivisors P S Z).filter (fun E => subsetNorm P E ≤ Y) =
      smallDivisors P S Y := by
    ext E
    simp only [Finset.mem_filter, smallDivisors]
    constructor
    · rintro ⟨⟨hE, hEZ⟩, hEY⟩
      exact ⟨hE, hEY⟩
    · rintro ⟨hE, hEY⟩
      exact ⟨⟨hE, hEY.trans hYZ⟩, hEY⟩
  have hs := Finset.sum_filter_add_sum_filter_not (smallDivisors P S Z)
    (fun E => subsetNorm P E ≤ Y) f
  rw [hsmall] at hs
  simpa only [middleDivisors, not_le] using hs

theorem masked_radialSource_five_pieces {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ) (hX : 0 < X) (hYZ : Y ≤ Z) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ E ∈ largeDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
      W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E) +
      (X : ℂ) * (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualNear W (X / subsetNorm P E) lengthScale) +
      (X : ℂ) * (∑ E ∈ smallDivisors P S Y,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (X : ℂ) * (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  rw [masked_radialSource_truncated_euler P hinj S W X Z hX]
  have hs := sum_small_add_middle P S Y Z hYZ (fun E =>
    (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E))
  rw [← hs]
  have hm : (∑ E ∈ middleDivisors P S Y Z,
      (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) =
      (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualNear W (X / subsetNorm P E) lengthScale) +
      (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro E hE
    rw [radialDual_near_add_far W _ lengthScale (div_pos hX (subsetNorm_pos P E)), mul_add]
  rw [hm]
  ring

end TruncatedPrincipalPoisson

namespace EisensteinSchwartzPoisson
open ConcreteTraceCRT

theorem radial_source_nonzero_lattice_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        (∑' h : {h : O // h ≠ 0}, ‖W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  let s : Finset (ℕ × ℕ) := Finset.Iic (A + 2, 0)
  let C : ℝ := 2 ^ (A + 2) * (eisensteinCauchyMass + 1)
  have hC : 0 < C := by
    have hm := eisensteinCauchyMass_nonneg
    dsimp [C]
    positivity
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let B : ℝ := 2 ^ (A + 2) * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (q : ℝ) (hq : 0 ≤ q) : (1 + q) ^ (A + 2) * ‖W q‖ ≤ B := by
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (A + 2, 0)) (k := A + 2) (n := 0) le_rfl le_rfl W q
    simp only [norm_iteratedFDeriv_zero, Real.norm_of_nonneg hq] at hh
    change (1 + q) ^ (A + 2) * ‖W q‖ ≤ B at hh
    exact hh
  have hp (h : {h : O // h ≠ 0}) : ‖W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
      (B / (1 + K) ^ A) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    have hq : K ≤ K * ‖eisEmbedding h.val‖ ^ 2 := by
      nlinarith [one_le_eisenstein_norm_sq h.val h.property]
    have hh := polynomial_tail_majorant A K K (‖eisEmbedding h.val‖ ^ 2) B
      ‖W (K * ‖eisEmbedding h.val‖ ^ 2)‖ hK0 hK0.le (sq_nonneg _) (norm_nonneg _) hq
      (hb _ (by positivity))
    simpa only [min_eq_left hK, one_pow, one_mul] using hh
  have hmajor := (eisenstein_cauchy_summable.subtype (fun h => h ≠ 0)).mul_left
    (B / (1 + K) ^ A)
  have hs : Summable (fun h : {h : O // h ≠ 0} => ‖W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hmajor
  calc
    _ ≤ ∑' h : {h : O // h ≠ 0},
        (B / (1 + K) ^ A) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
      hs.tsum_le_tsum hp hmajor
    _ = (B / (1 + K) ^ A) * ∑' h : {h : O // h ≠ 0},
        ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
    _ ≤ (B / (1 + K) ^ A) * eisensteinCauchyMass :=
      mul_le_mul_of_nonneg_left (eisensteinCauchyMass_subtype {h : O | h ≠ 0}) (by positivity)
    _ ≤ (B / (1 + K) ^ A) * (eisensteinCauchyMass + 1) := by
      gcongr
      linarith
    _ = _ := by dsimp [B, C]; ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

private theorem zero_removed_tsum (f : O → ℂ) :
    (∑' h : O, if h = 0 then 0 else f h) = ∑' h : {h : O // h ≠ 0}, f h.val := by
  rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
    intro h hh hz
    subst h
    exact hh (by first | simp | exact_mod_cast le_top))]
  apply tsum_congr
  intro h
  simp only [if_neg h.property]

theorem radialSource_inverse_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        ‖radialSource W K⁻¹‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := radial_source_nonzero_lattice_decay A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hs : Summable (fun h : O => W (K * ‖eisEmbedding h‖ ^ 2)) := by
    simpa only [scaledRadialTest_apply, div_inv_eq_mul, mul_comm] using
      (actual_eisenstein_summable_norm (scaledRadialTest W K⁻¹ (inv_pos.mpr hK0))).of_norm
  unfold radialSource
  rw [zero_removed_tsum]
  simp only [div_inv_eq_mul, mul_comm (‖eisEmbedding _‖ ^ 2) K]
  exact (norm_tsum_le_tsum_norm (hs.norm.subtype _)).trans (hb W K hK)

theorem radialDual_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        ‖radialDual W K‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hs := paperRadialFourier_lattice_summable_norm W K hK0
  let f : {h : O // h ≠ 0} → {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2} :=
    fun h => ⟨h.val, by nlinarith [one_le_eisenstein_norm_sq h.val h.property]⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2} => z.val) hab)
  have hi : (∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
      ∑' h : {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2}, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
    (hs.subtype _).tsum_le_tsum_of_inj f hf (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype _)
  have ht := hb W K K hK0 hK0.le
  simp only [min_eq_left hK, one_pow, one_mul] at ht
  unfold radialDual
  rw [zero_removed_tsum]
  exact (norm_tsum_le_tsum_norm (hs.subtype _)).trans (hi.trans ht)

theorem subsetMobius_norm_le_one {ι : Type*} (P : ι → Ideal O) (E : Finset ι) :
    ‖subsetMobius P E‖ ≤ 1 := QuadraticInitialBound.norm_ideal_moebius_le_one _

private theorem scale_tail_bound (A : ℕ) (B x Y X : ℝ)
    (hB : 0 ≤ B) (hx : 0 < x) (hxY : x ≤ Y) (hX : 0 < X) :
    (X / x) * (B / (1 + X / x) ^ (A + 1)) ≤ B * (Y / X) ^ A := by
  have hu : 0 < X / x := div_pos hX hx
  calc
    _ ≤ (X / x) * (B / (X / x) ^ (A + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hu.le
      exact div_le_div_of_nonneg_left hB (pow_pos hu _) (pow_le_pow_left₀ hu.le (by linarith) _)
    _ = B * (x / X) ^ A := by
      simp only [div_pow, pow_succ]
      field_simp

    _ ≤ B * (Y / X) ^ A := by gcongr

private theorem norm_sum_subsets_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (T : Finset (Finset ι)) (hT : T ⊆ S.powerset) (f : Finset ι → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ E ∈ T, ‖f E‖ ≤ B) :
    ‖∑ E ∈ T, f E‖ ≤ (2 : ℝ) ^ S.card * B := by
  calc
    _ ≤ ∑ E ∈ T, ‖f E‖ := norm_sum_le _ _
    _ ≤ ∑ E ∈ T, B := Finset.sum_le_sum hf
    _ = (T.card : ℝ) * B := by simp
    _ ≤ (2 : ℝ) ^ S.card * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      have hc := Finset.card_le_card hT
      rw [Finset.card_powerset] at hc
      exact_mod_cast hc

theorem small_divisor_dual_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y : ℝ), 0 < X → 0 ≤ Y → Y ≤ X →
        ‖(X : ℂ) * ∑ E ∈ smallDivisors P S Y,
          (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (Y / X) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := radialDual_decay (A + 1)
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Y hX hY hYX
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  rw [Finset.mul_sum]
  have hf (E : Finset ι) (hE : E ∈ smallDivisors P S Y) :
      ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) *
        radialDual W (X / subsetNorm P E))‖ ≤ B * (Y / X) ^ A := by
    have hn := subsetNorm_pos P E
    have hEY : subsetNorm P E ≤ Y := (Finset.mem_filter.mp hE).2
    have hscale : 1 ≤ X / subsetNorm P E := (le_div_iff₀ hn).mpr (by simpa using hEY.trans hYX)
    calc
      _ = (X / subsetNorm P E) * ‖subsetMobius P E‖ * ‖radialDual W (X / subsetNorm P E)‖ := by
        simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hX, abs_of_pos hn]
        ring
      _ ≤ (X / subsetNorm P E) * 1 * (B / (1 + X / subsetNorm P E) ^ (A + 1)) := by
        gcongr
        · exact subsetMobius_norm_le_one P E
        · exact hb W _ hscale
      _ ≤ B * (Y / X) ^ A := by
        simpa only [mul_one] using scale_tail_bound A B (subsetNorm P E) Y X hB hn hEY hX
  exact (norm_sum_subsets_le S _ (Finset.filter_subset _ _) _ _ (by positivity) hf).trans_eq (by ring)

theorem large_divisor_source_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Z : ℝ), 0 < X → X ≤ Z →
        ‖∑ E ∈ largeDivisors P S Z,
          subsetMobius P E * radialSource W (X / subsetNorm P E)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            (1 + Z / X) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := radialSource_inverse_decay A
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Z hX hXZ
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 < Z := hX.trans_le hXZ
  have hf (E : Finset ι) (hE : E ∈ largeDivisors P S Z) :
      ‖subsetMobius P E * radialSource W (X / subsetNorm P E)‖ ≤ B / (1 + Z / X) ^ A := by
    have hn := subsetNorm_pos P E
    have hEZ : Z < subsetNorm P E := (Finset.mem_filter.mp hE).2
    have hscale : 1 ≤ subsetNorm P E / X := (le_div_iff₀ hX).mpr (by simpa using hXZ.trans hEZ.le)
    have hh := hb W (subsetNorm P E / X) hscale
    rw [inv_div] at hh
    calc
      _ = ‖subsetMobius P E‖ * ‖radialSource W (X / subsetNorm P E)‖ := norm_mul _ _
      _ ≤ 1 * (B / (1 + subsetNorm P E / X) ^ A) :=
        mul_le_mul (subsetMobius_norm_le_one P E) hh (norm_nonneg _) (by norm_num)
      _ ≤ B / (1 + Z / X) ^ A := by
        simp only [one_mul]
        apply div_le_div_of_nonneg_left hB (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by gcongr) A
  exact (norm_sum_subsets_le S _ (Finset.filter_subset _ _) _ _ (by positivity) hf).trans_eq (by ring)

end TruncatedPrincipalPoisson

end

end OAI

end


