-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0098
-- name    : PNT_ZeroFree_433_0098
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:36:39.357474+00:00
-- url     : https://prove2.me/theorems/c5441e99-41f7-48dc-889c-456cd4ea7a97
-- title:
--   Zero-free region foundations: QuadraticSieve.DyadicColumns [0098]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/DyadicColumns.lean#L76-L645

import Definitions.Def_PNT_ZeroFree_433_0097

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/DyadicColumns.lean#L76-L645
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

def columnDyadicLength (N : ℝ) : ℕ := ⌈Real.log N / Real.log 2⌉₊

theorem columnDyadicLength_cover (N : ℝ) : N ≤ (2 : ℝ) ^ columnDyadicLength N := by
  apply Real.pow_le_of_le_log (by norm_num : (0 : ℝ) < 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (div_le_iff₀ hlog).mp (Nat.le_ceil (Real.log N / Real.log 2))

theorem columnDyadicLength_small_power (ε : ℝ) (hε : 0 < ε) (N : ℝ) (hN : 1 ≤ N) :
    (columnDyadicLength N + 1 : ℝ) ≤ (2 + 1 / (ε * Real.log 2)) * N ^ ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ Real.log N / Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  have hL : (columnDyadicLength N + 1 : ℝ) ≤ 2 + Real.log N / Real.log 2 := by
    dsimp only [columnDyadicLength]
    linarith
  have hr : 1 ≤ N ^ ε := Real.one_le_rpow hN hε.le
  have hb : Real.log N / Real.log 2 ≤ (N ^ ε / ε) / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_rpow_div (by linarith) hε) hlog.le
  calc
    _ ≤ 2 + Real.log N / Real.log 2 := hL
    _ ≤ 2 * N ^ ε + (N ^ ε / ε) / Real.log 2 := add_le_add (by linarith) hb
    _ = _ := by field_simp

theorem annularHighEnergy_column_shells_small_power
    (ε : ℝ) (hε : 0 < ε) (M N K : ℝ) (hN : 1 ≤ N) (a : idealRange N → ℂ) :
    annularHighEnergy M N K a ≤ ((2 + 1 / (ε * Real.log 2)) * N ^ ε) *
      ∑ j : Fin (columnDyadicLength N + 1),
        annularHighEnergy M ((2 : ℝ) ^ j.val) K
          (coefficientAtScale N ((2 : ℝ) ^ j.val)
            (dyadicColumnCoefficient N (columnDyadicLength N) (columnDyadicLength_cover N) j a)) := by
  apply (annularHighEnergy_column_shells_at_scale M N K (columnDyadicLength N)
    (columnDyadicLength_cover N) a).trans
  apply mul_le_mul_of_nonneg_right (columnDyadicLength_small_power ε hε N hN)
  apply Finset.sum_nonneg
  intro j _
  unfold annularHighEnergy
  exact Finset.sum_nonneg (fun I _ => mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (sq_nonneg _))

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

theorem squarefreePart_norm_le (lengthScale : Ideal O) (hL : lengthScale ≠ 0) :
    Ideal.absNorm (squarefreePart lengthScale) ≤ Ideal.absNorm lengthScale := by
  have hd : squarefreePart lengthScale ∣ lengthScale :=
    ⟨squarePart lengthScale ^ 2, (squarePart_sq_mul_squarefreePart lengthScale).symm.trans (mul_comm _ _)⟩
  exact Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (fun h => hL (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm hd)

def dualSquarefreeTail (I J : Ideal O) (W : ℝ → ℂ) (t K : ℝ) : ℂ :=
  ∑' lengthScale : {lengthScale : Ideal O // lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)},
    unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))

theorem dualSquarefreeTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (t K : ℝ), 0 < t → 0 ≤ K →
        ‖dualSquarefreeTail I J W t K‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 t) ^ 2 * (1 + t * K) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro I J W t K ht hK
  let Q := {lengthScale : Ideal O // lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)}
  have hgen : Function.Injective (fun lengthScale : Q => idealGenerator lengthScale.val) := by
    intro lengthScale R h
    apply Subtype.ext
    simpa only [span_idealGenerator] using congrArg (fun z : O => Ideal.span {z}) h
  have hlat := paperRadialFourier_lattice_summable_norm W t ht
  have hQ : Summable (fun lengthScale : Q => ‖paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖) := by
    have hs := hlat.comp_injective hgen
    simpa only [Function.comp_def, idealGenerator_norm_sq] using hs
  have hp (lengthScale : Q) :
      ‖unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖ ≤
        ‖paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖ := by
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    unfold unrestrictedPairCharacter
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (quadraticRow_norm_le_one I _) (quadraticRow_norm_le_one J _)
        (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hnorm : Summable (fun lengthScale : Q =>
      ‖unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hQ
  let f : Q → {z : O // t * K ≤ t * ‖eisEmbedding z‖ ^ 2} := fun lengthScale =>
    ⟨idealGenerator lengthScale.val, by
      rw [idealGenerator_norm_sq]
      apply mul_le_mul_of_nonneg_left _ ht.le
      exact lengthScale.property.2.le.trans (Nat.cast_le.mpr (squarefreePart_norm_le lengthScale.val lengthScale.property.1))⟩
  have hf : Function.Injective f := by
    intro lengthScale R h
    apply hgen
    exact congrArg (fun z : {z : O // t * K ≤ t * ‖eisEmbedding z‖ ^ 2} => z.val) h
  have hi : (∑' lengthScale : Q, ‖paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖) ≤
      ∑' z : {z : O // t * K ≤ t * ‖eisEmbedding z‖ ^ 2},
        ‖paperRadialFourier W (t * ‖eisEmbedding z.val‖ ^ 2)‖ := by
    apply hQ.tsum_le_tsum_of_inj f hf (fun _ _ => norm_nonneg _) _ (hlat.subtype _)
    intro lengthScale
    simp only [f, idealGenerator_norm_sq]
    rfl
  exact (norm_tsum_le_tsum_norm hnorm).trans
    ((hnorm.tsum_le_tsum hp hQ).trans (hi.trans (hb W t (t * K) ht (mul_nonneg ht.le hK))))

end CanonicalQuadraticSieve

open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)

def fullIdealWeight (s : ℂ) (I : Ideal O) : ℂ :=
  if I=0 then 0 else (Ideal.absNorm I:ℂ)^(-s)

lemma fullIdealWeight_good (s : ℂ) (I : GoodIdeal) : fullIdealWeight s I.1=unramifiedNormWeight s I.1 := by
  rw [fullIdealWeight,if_neg (primaryGenerator_ne_zero_ideal _ I.2),unramifiedNormWeight_of_good _ _ I.2]

lemma norm_fullIdealWeight (s : ℂ) (I : NonzeroIdeal) :
    ‖fullIdealWeight s I.1‖=‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator I.1)‖^(-2*s.re) := by
  rw [fullIdealWeight,if_neg I.2]
  have hn : 0<‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator I.1)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (ConcretePrimeRowBridge.idealGenerator_ne_zero _ I.2))
  have hnorm : ‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator I.1)‖^2=(Ideal.absNorm I.1:ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ConcretePrimeRowBridge.span_idealGenerator]
  have hcast : (Ideal.absNorm I.1:ℂ)=((‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator I.1)‖^2:ℝ):ℂ) := by
    exact_mod_cast hnorm.symm
  rw [hcast,Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn),← Real.rpow_natCast_mul hn.le 2]
  congr 1
  simp only [Complex.neg_re,Nat.cast_ofNat]
  ring

theorem fullIdealWeight_summable_norm (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal O => ‖fullIdealWeight s I‖) := by
  have hinj : Function.Injective (fun I : NonzeroIdeal => ConcretePrimeRowBridge.idealGenerator I.1) :=
    ConcretePrimeRowBridge.idealGenerator_injective.comp Subtype.val_injective
  have hlat := (summable_embedding_rpow (-2*s.re) (by linarith)).comp_injective hinj
  have hsub : Summable (fun I : NonzeroIdeal => ‖fullIdealWeight s I.1‖) := by
    simpa only [Function.comp_def,norm_fullIdealWeight] using hlat
  have hind := (summable_subtype_iff_indicator (s := {I : Ideal O | I ≠ 0})
    (f := fun I => ‖fullIdealWeight s I‖)).mp hsub
  apply hind.congr
  intro I
  by_cases hI : I=0
  · subst I
    simp [Set.indicator,fullIdealWeight]
  · have hIbot : I ≠ ⊥ := hI
    simp [Set.indicator,hIbot,fullIdealWeight]

def fullIdealZeta (s : ℂ) : ℂ := ∑' I : Ideal O,fullIdealWeight s I

lemma fullIdealWeight_norm_fiber (s : ℂ) (n : ℕ) :
    (∑' I : {I : Ideal O // Ideal.absNorm I=n},fullIdealWeight s I.1)=
      LSeries.term (fun n => (Nat.card {I : Ideal O // Ideal.absNorm I=n}:ℂ)) s n := by
  by_cases hn : n=0
  · subst n
    have hzero (I : {I : Ideal O // Ideal.absNorm I=0}) : fullIdealWeight s I.1=0 := by
      have hz : I.1=(0:Ideal O) := Ideal.absNorm_eq_zero_iff.mp I.2
      rw [fullIdealWeight,if_pos hz]
    simp only [hzero,tsum_zero,LSeries.term_zero]
  · let : Fintype {I : Ideal O // Ideal.absNorm I=n} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := O) n).fintype
    have hterm (I : {I : Ideal O // Ideal.absNorm I=n}) : fullIdealWeight s I.1=(n:ℂ)^(-s) := by
      have hI : I.1 ≠ 0 := fun h => hn (by rw [← I.2,h,map_zero])
      rw [fullIdealWeight,if_neg hI,I.2]
    simp only [hterm,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      LSeries.term_of_ne_zero hn,Nat.card_eq_fintype_card,Complex.cpow_neg,div_eq_mul_inv]

theorem fullIdealZeta_eq_dedekindZeta (s : ℂ) (hs : 1<s.re) :
    fullIdealZeta s=NumberField.dedekindZeta ActualEisensteinCubic.K s := by
  have h := (fullIdealWeight_summable_norm s hs).of_norm.hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ =>
    ∑' I : {I : Ideal O // Ideal.absNorm I=n},fullIdealWeight s I.1) (fullIdealZeta s) at h
  simp_rw [fullIdealWeight_norm_fiber] at h
  exact h.tsum_eq.symm

lemma fullIdealWeight_lambdaFactor (s : ℂ) (n : ℕ) (I : GoodIdeal) :
    fullIdealWeight s (lambdaFactorMap (n,I)).1=((3:ℂ)^(-s))^n*unramifiedNormWeight s I.1 := by
  rw [fullIdealWeight,if_neg (lambdaFactorMap (n,I)).2]
  change (Ideal.absNorm (ramifiedIdeal^n*I.1):ℂ)^(-s)=_
  rw [map_mul,map_pow,ramifiedIdeal_absNorm,Nat.cast_mul,
    unramifiedNormWeight_of_good _ _ I.2]
  rw [Complex.natCast_mul_natCast_cpow]
  congr 1
  have h := (Complex.natCast_cpow_natCast_mul 3 n (-s)).symm.trans (Complex.cpow_nat_mul 3 n (-s))
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h

theorem unramifiedIdealZeta_eq_dedekindZeta (s : ℂ) (hs : 1<s.re) :
    unramifiedIdealZeta s=(1-(3:ℂ)^(-s))*NumberField.dedekindZeta ActualEisensteinCubic.K s := by
  have hnorm : ‖(3:ℂ)^(-s)‖<1 := by
    change ‖((3:ℝ):ℂ)^(-s)‖<1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    simp only [Complex.neg_re]
    linarith
  have hne : 1-(3:ℂ)^(-s) ≠ 0 := by
    intro h
    have hz : (3:ℂ)^(-s)=1 := (sub_eq_zero.mp h).symm
    rw [hz,norm_one] at hnorm
    exact lt_irrefl 1 hnorm
  have hsub : Summable (fun I : NonzeroIdeal => fullIdealWeight s I.1) :=
    (fullIdealWeight_summable_norm s hs).of_norm.subtype _
  have hp := lambdaFactorEquiv.summable_iff.mpr hsub
  change Summable (fun p : ℕ × GoodIdeal => fullIdealWeight s (lambdaFactorMap p).1) at hp
  have hfull : fullIdealZeta s=(1-(3:ℂ)^(-s))⁻¹*unramifiedIdealZeta s := by
    calc
      _ = ∑' I : NonzeroIdeal,fullIdealWeight s I.1 := by
        symm
        apply tsum_subtype_eq_of_support_subset
        intro I hI
        change I ≠ 0
        intro hz
        exact hI (by simp [fullIdealWeight,hz])
      _ = ∑' p : ℕ × GoodIdeal,fullIdealWeight s (lambdaFactorMap p).1 :=
        (lambdaFactorEquiv.tsum_eq _).symm
      _ = ∑' n : ℕ,∑' I : GoodIdeal,((3:ℂ)^(-s))^n*unramifiedNormWeight s I.1 := by
        rw [hp.tsum_prod]
        apply tsum_congr; intro n
        exact tsum_congr (fun I => fullIdealWeight_lambdaFactor s n I)
      _ = ∑' n : ℕ,((3:ℂ)^(-s))^n*unramifiedIdealZeta s := by
        apply tsum_congr; intro n
        rw [tsum_mul_left]
        apply congrArg (fun z : ℂ => ((3:ℂ)^(-s))^n*z)
        apply tsum_subtype_eq_of_support_subset (f := unramifiedNormWeight s)
          (s := {I : Ideal O | primaryGenerator I ≠ 0})
        intro I hI
        change primaryGenerator I ≠ 0
        intro hz
        exact hI (unramifiedNormWeight_of_bad s I hz)
      _ = _ := by rw [tsum_mul_right,tsum_geometric_of_norm_lt_one hnorm]
  rw [← fullIdealZeta_eq_dedekindZeta s hs,hfull,← mul_assoc,mul_inv_cancel₀ hne,one_mul]

end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss

lemma constantDirichletTerm_differentiable (c : LevelLower) :
    Differentiable ℂ (fun s : ℂ => arithmeticDirichletTerm s 0 c) := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,if_pos hc]
    exact differentiable_const _
  · have hq : ((‖eisEmbedding c.1‖^2:ℝ):ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)))
    simp only [arithmeticDirichletTerm,if_neg hc]
    exact (differentiable_id.neg.const_cpow (Or.inl hq)).mul_const _

lemma constantDirichletTerm_norm_mono (a : ℝ) (s : ℂ) (ha : a ≤ s.re) (c : LevelLower) :
    ‖arithmeticDirichletTerm s 0 c‖ ≤ ‖arithmeticDirichletTerm (a:ℂ) 0 c‖ := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,if_pos hc,norm_zero,le_refl]
  · have hpos : 0<‖eisEmbedding c.1‖^2 := sq_pos_of_pos
      (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
    have hq : 1≤‖eisEmbedding c.1‖^2 := by
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
    simp only [arithmeticDirichletTerm,if_neg hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos,Complex.neg_re,Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg ha))
      (norm_nonneg _)

theorem arithmeticDirichletSeries_zero_differentiableAt (s : ℂ) (hs : (4:ℝ)/3<s.re) :
    DifferentiableAt ℂ (fun z => arithmeticDirichletSeries z 0) s := by
  let a : ℝ := ((4:ℝ)/3+s.re)/2
  have ha : (4:ℝ)/3<a := by dsimp [a]; linarith
  have has : a<s.re := by dsimp [a]; linarith
  have hsum := constantDirichlet_summable_norm (a:ℂ) (by simpa using ha)
  have hopen : IsOpen {z : ℂ | a<z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun z => arithmeticDirichletSeries z 0) {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun c => (constantDirichletTerm_differentiable c).differentiableOn) hopen
    intro c z hz
    exact constantDirichletTerm_norm_mono a z hz.le c
  exact (hd s has).differentiableAt (hopen.mem_nhds has)

lemma unramifiedNormWeight_differentiable (I : Ideal O) :
    Differentiable ℂ (fun s : ℂ => unramifiedNormWeight s I) := by
  by_cases hI : primaryGenerator I=0
  · simp only [unramifiedNormWeight_of_bad _ I hI]
    exact differentiable_const _
  · have hn : (Ideal.absNorm I:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (primaryGenerator_ne_zero_ideal I hI))
    simp only [unramifiedNormWeight_of_good _ I hI]
    exact differentiable_id.neg.const_cpow (Or.inl hn)

lemma unramifiedNormWeight_norm_mono (a : ℝ) (s : ℂ) (ha : a ≤ s.re) (I : Ideal O) :
    ‖unramifiedNormWeight s I‖≤‖unramifiedNormWeight (a:ℂ) I‖ := by
  by_cases hI : primaryGenerator I=0
  · simp only [unramifiedNormWeight_of_bad _ I hI,norm_zero,le_refl]
  · have hn : Ideal.absNorm I ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr (primaryGenerator_ne_zero_ideal I hI)
    have hpos : (0:ℝ)<Ideal.absNorm I := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hq : (1:ℝ)≤Ideal.absNorm I := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    simp only [unramifiedNormWeight_of_good _ I hI]
    change ‖((Ideal.absNorm I:ℝ):ℂ)^(-s)‖≤‖((Ideal.absNorm I:ℝ):ℂ)^(-(a:ℂ))‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos,Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    exact Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg ha)

theorem unramifiedIdealZeta_differentiableAt (s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ unramifiedIdealZeta s := by
  let a : ℝ := (1+s.re)/2
  have ha : 1<a := by dsimp [a]; linarith
  have has : a<s.re := by dsimp [a]; linarith
  have hsum := unramifiedNormWeight_summable_norm (a:ℂ) (by simpa using ha)
  have hopen : IsOpen {z : ℂ | a<z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ unramifiedIdealZeta {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun I => (unramifiedNormWeight_differentiable I).differentiableOn) hopen
    intro I z hz
    exact unramifiedNormWeight_norm_mono a z hz.le I
  exact (hd s has).differentiableAt (hopen.mem_nhds has)

end

open Filter
open scoped BigOperators Classical Topology

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss

def unramifiedZetaResidue : ℂ :=
  (2/3:ℂ)*(NumberField.dedekindZeta_residue ActualEisensteinCubic.K:ℂ)

lemma unramifiedZetaResidue_ne_zero : unramifiedZetaResidue ≠ 0 := by
  apply mul_ne_zero (by norm_num)
  exact Complex.ofReal_ne_zero.mpr
    (NumberField.dedekindZeta_residue_pos ActualEisensteinCubic.K).ne'

theorem unramifiedIdealZeta_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-1)*unramifiedIdealZeta (x:ℂ))
      (𝓝[>] (1:ℝ)) (𝓝 unramifiedZetaResidue) := by
  have hcont : Continuous (fun x : ℝ => 1-(3:ℂ)^(-(x:ℂ))) :=
    continuous_const.sub (Complex.continuous_ofReal.neg.const_cpow (Or.inl (by norm_num)))
  have heuler : Tendsto (fun x : ℝ => 1-(3:ℂ)^(-(x:ℂ))) (𝓝[>] (1:ℝ)) (𝓝 (2/3:ℂ)) := by
    apply (hcont.tendsto' 1 (2/3:ℂ) ?_).mono_left nhdsWithin_le_nhds
    norm_num [Complex.cpow_neg]
  have h := heuler.mul (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT ActualEisensteinCubic.K)
  change Tendsto (fun x : ℝ => (1-(3:ℂ)^(-(x:ℂ)))*
    (((x:ℂ)-1)*NumberField.dedekindZeta ActualEisensteinCubic.K (x:ℂ)))
      (𝓝[>] (1:ℝ)) (𝓝 unramifiedZetaResidue) at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 1<(x:ℂ).re := by simpa only [Set.mem_Ioi,Complex.ofReal_re] using hx
  rw [unramifiedIdealZeta_eq_dedekindZeta (x:ℂ) hx']
  ring

lemma cusp_volume_ne_zero : ((9*Real.sqrt 3/2:ℝ):ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  positivity

def constantArithmeticResidue : ℂ := unramifiedZetaResidue /
  (3*((9*Real.sqrt 3/2:ℝ):ℂ)*unramifiedIdealZeta 2)

lemma constantArithmeticResidue_ne_zero : constantArithmeticResidue ≠ 0 := by
  apply div_ne_zero unramifiedZetaResidue_ne_zero
  exact mul_ne_zero (mul_ne_zero (by norm_num) cusp_volume_ne_zero)
    (unramifiedIdealZeta_ne_zero 2 (by norm_num))

lemma tendsto_three_mul_sub_three_four_thirds :
    Tendsto (fun x : ℝ => 3*x-3) (𝓝[>] ((4:ℝ)/3)) (𝓝[>] (1:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · apply ((continuous_const.mul continuous_id).sub continuous_const).tendsto' _ _ (by norm_num)
      |>.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_Ioi] at hx ⊢
    linarith

theorem scatteringCoefficient_zero_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*scatteringCoefficient (x:ℂ) 0)
      (𝓝[>] ((4:ℝ)/3)) (𝓝 constantArithmeticResidue) := by
  have hn0 := unramifiedIdealZeta_oneSidedResidue.comp tendsto_three_mul_sub_three_four_thirds
  have hn : Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*unramifiedIdealZeta (3*(x:ℂ)-3))
      (𝓝[>] ((4:ℝ)/3)) (𝓝 (unramifiedZetaResidue/3)) := by
    convert! hn0.div_const (3:ℂ) using 1
    ext x
    dsimp only [Function.comp_def]
    push_cast
    ring
  have harg : Tendsto (fun x : ℝ => 3*(x:ℂ)-2) (𝓝[>] ((4:ℝ)/3)) (𝓝 (2:ℂ)) := by
    apply (((Complex.continuous_ofReal.const_mul 3).sub continuous_const).tendsto' _ _ ?_).mono_left
      nhdsWithin_le_nhds
    norm_num
  have hz := (unramifiedIdealZeta_differentiableAt 2 (by norm_num)).continuousAt.tendsto.comp harg
  have hdncont : Continuous (fun x : ℝ => (3:ℂ)^(3*(x:ℂ)-3)-1) :=
    (((Complex.continuous_ofReal.const_mul 3).sub continuous_const).const_cpow
      (Or.inl (by norm_num))).sub continuous_const
  have hdn : Tendsto (fun x : ℝ => (3:ℂ)^(3*(x:ℂ)-3)-1)
      (𝓝[>] ((4:ℝ)/3)) (𝓝 (2:ℂ)) := by
    apply (hdncont.tendsto' _ _ ?_).mono_left nhdsWithin_le_nhds
    norm_num
  have hp := ((hdn.inv₀ (by norm_num)).const_mul
    (2/((9*Real.sqrt 3/2:ℝ):ℂ))).mul
      (hn.div hz (unramifiedIdealZeta_ne_zero 2 (by norm_num)))
  have hlimit : (2/((9*Real.sqrt 3/2:ℝ):ℂ))*(2:ℂ)⁻¹*
      ((unramifiedZetaResidue/3)/unramifiedIdealZeta 2)=constantArithmeticResidue := by
    unfold constantArithmeticResidue
    ring
  rw [hlimit] at hp
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : (4:ℝ)/3<(x:ℂ).re := by simpa only [Set.mem_Ioi,Complex.ofReal_re] using hx
  rw [scatteringCoefficient_zero_zeta (x:ℂ) hx']
  dsimp only [Pi.div_apply,Function.comp_def]
  ring

end CubicEisenstein

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss

theorem idealQuotient_in_shell (I D : Ideal O) (hI : Admissible I) (hDI : D ∣ I)
    (N : ℝ) (hlo : N / 2 < (Ideal.absNorm I : ℝ)) (hhi : (Ideal.absNorm I : ℝ) ≤ N) :
    (N / (Ideal.absNorm D : ℝ)) / 2 < (Ideal.absNorm (idealQuotient D I) : ℝ) ∧
      (Ideal.absNorm (idealQuotient D I) : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hI.1 hDI
  have hDN : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  have he : (Ideal.absNorm (idealQuotient D I) : ℝ) * (Ideal.absNorm D : ℝ) = (Ideal.absNorm I : ℝ) := by
    rw [mul_comm, ← Nat.cast_mul, ← map_mul, idealQuotient_mul hDI]
  refine ⟨?_, idealQuotient_norm_le hD hDI N hhi⟩
  have hh : (N / 2) / (Ideal.absNorm D : ℝ) < (Ideal.absNorm (idealQuotient D I) : ℝ) := by
    apply (div_lt_iff₀ hDN).mpr
    simpa only [he] using hlo
  convert! hh using 1 ; ring

theorem residual_modulus_norm_shell (I J D : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (N : ℝ) (hN : 0 < N)
    (hIs : N / 2 < (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ N)
    (hJs : N / 2 < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ N) :
    (N / (Ideal.absNorm D : ℝ)) / 2 <
      ‖eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J))‖ ∧
    ‖eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J))‖ ≤
      N / (Ideal.absNorm D : ℝ) := by
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hI.1 hDI
  have hDN : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  have hQ := admissible_idealQuotient hI hDI
  have hT := admissible_idealQuotient hJ hDJ
  have hqi := idealQuotient_in_shell I D hI hDI N hIs.1 hIs.2
  have hqj := idealQuotient_in_shell J D hJ hDJ N hJs.1 hJs.2
  let X := N / (Ideal.absNorm D : ℝ)
  have hX : 0 < X := div_pos hN hDN
  have hn : ‖eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J))‖ ^ 2 =
      (Ideal.absNorm (idealQuotient D I) : ℝ) * (Ideal.absNorm (idealQuotient D J) : ℝ) := by
    rw [map_mul, norm_mul, mul_pow,
      primaryGenerator_norm_sq _ (primaryGenerator_admissible _ hQ),
      primaryGenerator_norm_sq _ (primaryGenerator_admissible _ hT)]
  have hlo : (X / 2) * (X / 2) <
      (Ideal.absNorm (idealQuotient D I) : ℝ) * (Ideal.absNorm (idealQuotient D J) : ℝ) :=
    mul_lt_mul hqi.1 hqj.1.le (by positivity) (by positivity)
  have hhi : (Ideal.absNorm (idealQuotient D I) : ℝ) * (Ideal.absNorm (idealQuotient D J) : ℝ) ≤ X * X :=
    mul_le_mul hqi.2 hqj.2 (Nat.cast_nonneg _) hX.le
  have hnorm := norm_nonneg (eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J)))
  constructor
  · nlinarith
  · nlinarith

theorem residual_poisson_prefactor_le (I J D : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (M N : ℝ) (hM : 0 ≤ M) (hN : 0 < N)
    (hIs : N / 2 < (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ N)
    (hJs : N / 2 < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ N) :
    M / ‖eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J))‖ ≤
      2 * M * (Ideal.absNorm D : ℝ) / N := by
  have hs := residual_modulus_norm_shell I J D hI hJ hDI hDJ N hN hIs hJs
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hI.1 hDI
  have hDN : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  have hp : 0 < (N / (Ideal.absNorm D : ℝ)) / 2 := by positivity
  calc
    _ ≤ M / ((N / (Ideal.absNorm D : ℝ)) / 2) := div_le_div_of_nonneg_left hM hp hs.1.le
    _ = _ := by field_simp

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

def dualSquarefreeLow (I J : Ideal O) (W : ℝ → ℂ) (t K : ℝ) : ℂ :=
  ∑' lengthScale : NonzeroIdeal, if (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) ≤ K then
    unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ)) else 0

theorem dual_ideal_low_add_tail (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (t K : ℝ) (ht : 0 < t) :
    (∑' lengthScale : NonzeroIdeal, unrestrictedPairCharacter I J lengthScale.val *
      paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))) =
      dualSquarefreeLow I J W t K + dualSquarefreeTail I J W t K := by
  let F : Ideal O → ℂ := fun lengthScale => unrestrictedPairCharacter I J lengthScale *
    paperRadialFourier W (t * (Ideal.absNorm lengthScale : ℝ))
  have hs : Summable (fun lengthScale : NonzeroIdeal => F lengthScale.val) := canonical_pair_ideal_fourier_summable I J W t ht
  have hl : Summable (fun lengthScale : NonzeroIdeal => if (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) ≤ K then F lengthScale.val else 0) :=
    hs.indicator _
  have hh : Summable (fun lengthScale : NonzeroIdeal => if K < (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) then F lengthScale.val else 0) :=
    hs.indicator _
  have htail : (∑' lengthScale : NonzeroIdeal, if K < (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) then F lengthScale.val else 0) =
      dualSquarefreeTail I J W t K := by
    have hleft : (∑' lengthScale : NonzeroIdeal, if K < (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) then F lengthScale.val else 0) =
        ∑' lengthScale : Ideal O, ({lengthScale : Ideal O | lengthScale ≠ 0} : Set (Ideal O)).indicator
          (fun lengthScale => if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then F lengthScale else 0) lengthScale := by
      exact tsum_subtype {lengthScale : Ideal O | lengthScale ≠ 0}
        (fun lengthScale : Ideal O => if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then F lengthScale else 0)
    have hright : (∑' lengthScale : {lengthScale : Ideal O // lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)}, F lengthScale.val) =
        ∑' lengthScale : Ideal O, ({lengthScale : Ideal O | lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)} : Set (Ideal O)).indicator F lengthScale :=
      tsum_subtype _ _
    change _ = ∑' lengthScale : {lengthScale : Ideal O // lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)}, F lengthScale.val
    rw [hleft, hright]
    apply tsum_congr
    intro lengthScale
    by_cases h0 : lengthScale = 0 <;> by_cases hK : K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) <;>
      simp [Set.indicator, h0, hK, F]
  rw [← htail, dualSquarefreeLow, ← hl.tsum_add hh]
  apply tsum_congr
  intro lengthScale
  by_cases hK : (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) ≤ K
  · simp only [hK, not_lt_of_ge hK, ite_true, ite_false, add_zero, F]
  · simp only [hK, lt_of_not_ge hK, ite_true, ite_false, zero_add, F]

theorem dualSquarefreeLow_principal
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (t K : ℝ) (ht : 0 < t) :
    dualSquarefreeLow I J W t K =
      ∑' B : {B : Ideal O // Squarefree B}, if (Ideal.absNorm B.val : ℝ) ≤ K then
        unrestrictedPairCharacter I J B.val *
          dualPrincipalIdeal I J (quadraticTransformedSquareProfile W)
            (Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) else 0 := by
  let G : NonzeroIdeal → ℂ := fun lengthScale => if (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) ≤ K then
    unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ)) else 0
  let F : (NonzeroIdeal × {B : Ideal O // Squarefree B}) → ℂ := fun p =>
    if (Ideal.absNorm p.2.val : ℝ) ≤ K then
      (idealZeroMask I (idealGenerator p.1.val) * idealZeroMask J (idealGenerator p.1.val)) *
      unrestrictedPairCharacter I J p.2.val * paperRadialFourier W
        (t * ((Ideal.absNorm p.1.val : ℝ) ^ 2 * (Ideal.absNorm p.2.val : ℝ))) else 0
  have hg : Summable G := (canonical_pair_ideal_fourier_summable I J W t ht).indicator _
  have hterm (p : NonzeroIdeal × {B : Ideal O // Squarefree B}) : G (decompositionEquiv.symm p) = F p := by
    change (if (Ideal.absNorm (squarefreePart (p.1.val ^ 2 * p.2.val)) : ℝ) ≤ K then
      unrestrictedPairCharacter I J (p.1.val ^ 2 * p.2.val) *
        paperRadialFourier W (t * (Ideal.absNorm (p.1.val ^ 2 * p.2.val) : ℝ)) else 0) = F p
    rw [(squarePart_mul_squarefree p.1.property p.2.property).2]
    by_cases hK : (Ideal.absNorm p.2.val : ℝ) ≤ K
    · simp only [hK, ite_true, F, unrestrictedPairCharacter_mul I J hI hJ hray,
        unrestrictedPairCharacter_square I J hI hJ hray, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
    · simp only [hK, ite_false, F]
  have hf : Summable F := (decompositionEquiv.symm.summable_iff.mpr hg).congr hterm
  calc
    _ = ∑' p : NonzeroIdeal × {B : Ideal O // Squarefree B}, G (decompositionEquiv.symm p) :=
      (decompositionEquiv.symm.tsum_eq G).symm
    _ = ∑' p, F p := tsum_congr hterm
    _ = ∑' p : ({B : Ideal O // Squarefree B} × NonzeroIdeal), F (p.2, p.1) :=
      (Equiv.prodComm _ _).tsum_eq (fun p => F (p.2, p.1))
    _ = ∑' B : {B : Ideal O // Squarefree B}, ∑' A : NonzeroIdeal, F (A, B) := hf.prod_symm.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro B
      by_cases hK : (Ideal.absNorm B.val : ℝ) ≤ K
      · rw [if_pos hK, dualPrincipalIdeal, ← tsum_mul_left]
        apply tsum_congr
        intro A
        have hB : 0 < (Ideal.absNorm B.val : ℝ) := by
          exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => B.property.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))
        have htb : 0 < t * (Ideal.absNorm B.val : ℝ) := mul_pos ht hB
        have harg : ((Ideal.absNorm A.val : ℝ) / Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) ^ 2 =
            t * ((Ideal.absNorm A.val : ℝ) ^ 2 * (Ideal.absNorm B.val : ℝ)) := by
          rw [div_pow, Real.sq_sqrt (one_div_pos.mpr htb).le]
          field_simp
        simp only [F, if_pos hK, quadraticTransformedSquareProfile_apply, harg]
        ring
      · simp only [F, if_neg hK, tsum_zero]

end CanonicalQuadraticSieve

end

end OAI

end


