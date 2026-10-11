-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0142_parallel1
-- name    : PNT_ZeroFree_433_0142_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:55:50.925136+00:00
-- url     : https://prove2.me/theorems/66111f58-ffb7-4f92-9351-91af2ff89b57
-- title:
--   Zero-free region foundations: CubicSieve.PooledRows [0142_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.PooledRows
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/PooledRows.lean#L446-L647

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0053
import Definitions.Def_PNT_ZeroFree_433_0055
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
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/PooledRows.lean
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


open scoped BigOperators Classical
namespace InitialMeanSquare

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O

structure Datum where
  divisor : Ideal O
  shared : Ideal O
  frequency : O
  deriving DecidableEq

def newRow (x : Datum) : O := idealGenerator x.divisor*x.frequency
def newLabel (x : Datum) : Ideal O := x.divisor*x.shared
def oldCommon (b : Ideal O) (x : Datum) : Ideal O := b*x.divisor
def observation (x : Datum) : O × Ideal O := (newRow x,newLabel x)

theorem span_newRow (x : Datum) :
    Ideal.span {newRow x}=x.divisor*Ideal.span {x.frequency} := by
  rw [newRow,←Ideal.span_singleton_mul_span_singleton,span_idealGenerator]

theorem divisor_dvd_row (x : Datum) : x.divisor∣Ideal.span {newRow x} := by
  rw [span_newRow]
  exact dvd_mul_right _ _

theorem divisor_dvd_label (x : Datum) : x.divisor∣newLabel x := dvd_mul_right _ _

theorem divisor_ne_zero_of_row (x : Datum) (hx : newRow x≠0) : x.divisor≠0 := by
  intro hd
  have hs : Ideal.span {newRow x}=(0 : Ideal O) := by rw [span_newRow,hd,zero_mul]
  exact hx (Ideal.span_singleton_eq_bot.mp hs)

theorem divisor_injective_on_fiber (y : O) (f : Ideal O) (hy : y≠0) :
    Set.InjOn Datum.divisor {x : Datum | observation x=(y,f)} := by
  intro x hx z hz hd
  have hxrow : newRow x=y := congrArg Prod.fst hx
  have hzrow : newRow z=y := congrArg Prod.fst hz
  have hxlabel : newLabel x=f := congrArg Prod.snd hx
  have hzlabel : newLabel z=f := congrArg Prod.snd hz
  have hdx := divisor_ne_zero_of_row x (by rwa [hxrow])
  have hshared : x.shared=z.shared := by
    apply mul_left_cancel₀ hdx
    calc
      x.divisor*x.shared = f := hxlabel
      _ = z.divisor*z.shared := hzlabel.symm
      _ = x.divisor*z.shared := by rw [hd]
  have hfreq : x.frequency=z.frequency := by
    apply mul_left_cancel₀ (idealGenerator_ne_zero x.divisor hdx)
    calc
      idealGenerator x.divisor*x.frequency = y := hxrow
      _ = idealGenerator z.divisor*z.frequency := hzrow.symm
      _ = idealGenerator x.divisor*z.frequency := by rw [hd]
  cases x
  cases z
  simp_all

theorem fiber_card_le (s : Finset Datum) (y : O) (f : Ideal O) (hy : y≠0) :
    (s.filter (fun x => observation x=(y,f))).card≤(idealDivisors (Ideal.span {y})).card := by
  have hyI : (Ideal.span {y}:Ideal O)≠0 := by
    intro hz
    exact hy (Ideal.span_singleton_eq_bot.mp hz)
  apply Finset.card_le_card_of_injOn Datum.divisor
  · intro x hx
    change x.divisor∈idealDivisors (Ideal.span {y})
    rw [mem_idealDivisors hyI]
    have he : newRow x=y := congrArg Prod.fst (Finset.mem_filter.mp hx).2
    rw [←he]
    exact divisor_dvd_row x
  · intro x hx z hz he
    exact divisor_injective_on_fiber y f hy (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hz).2 he

theorem fiber_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (s : Finset Datum) (y : O) (f : Ideal O), y≠0 →
      ((s.filter (fun x => observation x=(y,f))).card:ℝ)≤
        C*(Ideal.absNorm (Ideal.span {y}):ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro s y f hy
  have hyI : (Ideal.span {y}:Ideal O)≠0 := by
    intro hz
    exact hy (Ideal.span_singleton_eq_bot.mp hz)
  exact (show ((s.filter (fun x => observation x=(y,f))).card:ℝ)≤
    (idealDivisors (Ideal.span {y})).card by exact_mod_cast fiber_card_le s y f hy).trans (hdiv _ hyI)

theorem weighted_energy_pushforward (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (s : Finset Datum) (t : Finset (O×Ideal O))
      (w : Datum→ℂ) (P : O×Ideal O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,observation x∈t) →
      (∀y∈t,y.1≠0) → (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      (∑x∈s,‖w x‖*‖P (observation x)‖^2)≤A*C*K^ε*∑y∈t,‖P y‖^2 := by
  obtain ⟨C,hC,hfiber⟩ := fiber_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro s t w P A K hA hK hmap ht hnorm hw
  apply (DescentWeightedCauchy.bounded_energy_pushforward s t observation w P A hmap hw).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hc := (hfiber s y.1 y.2 (ht y hy)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm y hy) hε.le) hC.le)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hA) (sq_nonneg ‖P y‖)
  simpa only [Prod.eta,mul_assoc] using hh

theorem norm_newRow (x : Datum) :
    Ideal.absNorm (Ideal.span {newRow x})=Ideal.absNorm x.divisor*Ideal.absNorm (Ideal.span {x.frequency}) := by
  rw [span_newRow,map_mul]

theorem norm_newLabel (x : Datum) :
    Ideal.absNorm (newLabel x)=Ideal.absNorm x.divisor*Ideal.absNorm x.shared := by
  rw [newLabel,map_mul]

theorem norm_oldCommon (b : Ideal O) (x : Datum) :
    Ideal.absNorm (oldCommon b x)=Ideal.absNorm b*Ideal.absNorm x.divisor := by
  rw [oldCommon,map_mul]

end

theorem label_and_mask (b : Ideal O) (x : Datum)
    (hC : Squarefree (oldCommon b x)) (hs : Squarefree x.shared)
    (hcop : IsCoprime (oldCommon b x) x.shared) :
    Squarefree (newLabel x) ∧ IsCoprime b (newLabel x) := by
  have hC' : Squarefree (b*x.divisor) := hC
  have hcop' : IsCoprime (b*x.divisor) x.shared := hcop
  have hds : IsCoprime x.divisor x.shared :=
    hcop'.of_isCoprime_of_dvd_left (dvd_mul_left _ _)
  have hbs : IsCoprime b x.shared :=
    hcop'.of_isCoprime_of_dvd_left (dvd_mul_right _ _)
  have hbd : IsCoprime b x.divisor := by
    apply Ideal.isCoprime_iff_gcd.mpr
    have hh := (IsRelPrime.of_squarefree_mul hC')
      (GCDMonoid.gcd_dvd_left b x.divisor) (GCDMonoid.gcd_dvd_right b x.divisor)
    simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp hh
  exact ⟨squarefree_mul_iff.mpr ⟨hds.isRelPrime,hC'.of_mul_right,hs⟩,hbd.mul_right hbs⟩

def columnScale (Z B F : ℝ) : ℝ := Z/(B*F)
def rowScale (Z H B : ℝ) : ℝ := Z^2/(H*B^2)

theorem initial_prefactor (Z H b d : ℝ) (hd : d≠0) :
    H*(b*d)/(Z^2*d)=H*b/Z^2 := by field_simp

theorem initial_column_scale (Z b d s : ℝ) :
    Z/((b*d)*s)=columnScale Z b (d*s) := by unfold columnScale; ring

theorem initial_row_bound (Z H b d h : ℝ) (hH : 0<H) (hb : 0<b) (hd : 0<d)
    (hh : h≤Z^2*d/(H*(b*d)^2)) : d*h≤rowScale Z H b := by
  have h := mul_le_mul_of_nonneg_left hh hd.le
  have he : d*(Z^2*d/(H*(b*d)^2))=rowScale Z H b := by
    unfold rowScale
    field_simp

  exact h.trans_eq he

theorem initial_mass (Z B F : ℝ) (hF : F≠0) : columnScale Z B F*F=Z/B := by
  unfold columnScale
  field_simp

theorem initial_invariant_identity (Z H B F R : ℝ)
    (hZ : Z≠0) (hB : B≠0) (hF : F≠0) :
    rowScale Z H B*R/(columnScale Z B F*F)=(Z/H)*(R/B) := by
  unfold rowScale columnScale
  field_simp

theorem initial_invariant_bound (Z H B F R c : ℝ)
    (hZ : 0<Z) (hH : 0<H) (hB : 0<B) (hF : 0<F) (hR : R≤c*B) :
    rowScale Z H B*R/(columnScale Z B F*F)≤c*(Z/H) := by
  rw [initial_invariant_identity Z H B F R hZ.ne' hB.ne' hF.ne']
  have hh : R/B≤c := (div_le_iff₀ hB).mpr hR
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (div_nonneg hZ.le hH.le)

theorem initial_invariant_power_general (Z B F R c σ : ℝ)
    (hZ : 0<Z) (hB : 0<B) (hF : 0<F) (hR : R≤c*B) :
    rowScale Z (Z^(1+σ)) B*R/(columnScale Z B F*F)≤c*Z^(-σ) := by
  have he : Z/Z^(1+σ)=Z^(-σ) := by
    calc
      _ = Z^((1:ℝ)-(1+σ)) := by rw [Real.rpow_sub hZ,Real.rpow_one]
      _ = _ := by congr 1; ring
  simpa only [he] using initial_invariant_bound Z (Z^(1+σ)) B F R c
    hZ (Real.rpow_pos_of_pos hZ _) hB hF hR

theorem initial_invariant_power (Z B F R c : ℝ)
    (hZ : 1≤Z) (hB : 0<B) (hF : 0<F) (hR : R≤c*B) :
    rowScale Z (Z^((11:ℝ)/10)) B*R/(columnScale Z B F*F)≤c*Z^(-(1:ℝ)/10) := by
  have hZ0 : 0<Z := by linarith
  have he : Z/(Z^((11:ℝ)/10))=Z^(-(1:ℝ)/10) := by
    calc
      _ = Z^((1:ℝ)-(11:ℝ)/10) := by rw [Real.rpow_sub hZ0,Real.rpow_one]
      _ = _ := by norm_num
  simpa only [he] using initial_invariant_bound Z (Z^((11:ℝ)/10)) B F R c
    hZ0 (Real.rpow_pos_of_pos hZ0 _) hB hF hR

theorem initial_invariant_reserved_margin (Z B F R c : ℝ)
    (hZ : 1≤Z) (hB : 0<B) (hF : 0<F) (hR : R≤c*B) (hc : c≤Z^((1:ℝ)/20)) :
    rowScale Z (Z^((11:ℝ)/10)) B*R≤
      columnScale Z B F*F*Z^(-(1:ℝ)/20) := by
  have hZ0 : 0<Z := by linarith
  have hmass : 0<columnScale Z B F*F := by unfold columnScale; positivity
  rw [mul_comm (columnScale Z B F*F)]
  apply (div_le_iff₀ hmass).mp
  apply (initial_invariant_power Z B F R c hZ hB hF hR).trans
  calc
    c*Z^(-(1:ℝ)/10) ≤ Z^((1:ℝ)/20)*Z^(-(1:ℝ)/10) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hZ0.le _)
    _ = Z^(-(1:ℝ)/20) := by rw [←Real.rpow_add hZ0]; norm_num

theorem initial_budget_identity (Z H B : ℝ) (hZ : Z≠0) (hB : B≠0) :
    (H*B/Z^2)*B*(Z/B)*(Z/B)=H := by field_simp

end InitialMeanSquare

end

end OAI

end


