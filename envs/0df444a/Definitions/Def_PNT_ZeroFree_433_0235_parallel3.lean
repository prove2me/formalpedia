-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0235_parallel3
-- name    : PNT_ZeroFree_433_0235_parallel3
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:47:01.896193+00:00
-- url     : https://prove2.me/theorems/17f8e594-825a-46ac-99a6-62e29f1390be
-- title:
--   Zero-free region foundations: Eisenstein.InverseCuspCoordinates [0235_parallel3]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.InverseCuspCoordinates
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/InverseCuspCoordinates.lean#L307-L520

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0136
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel2
import Definitions.Def_PNT_ZeroFree_433_0234_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0235_parallel1
import Definitions.Def_PNT_ZeroFree_433_0235_parallel2
import Definitions.Def_PNT_ZeroFree_433_0243_parallel3
import Definitions.Def_PNT_ZeroFree_433_0245
import Definitions.Def_PNT_ZeroFree_433_0246_parallel2
import Definitions.Def_PNT_ZeroFree_433_0247_parallel1
import Definitions.Def_PNT_ZeroFree_433_0267_parallel1
import Definitions.Def_PNT_ZeroFree_433_0285_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/InverseCuspCoordinates.lean
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
open scoped BigOperators Classical Topology


open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O


namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)


lemma term_hasFDerivAt (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) (hp : 0<p.1) :
    HasFDerivAt (coeff.term h) (coeff.termFDeriv h p) p := by
  by_cases hh : h=0
  · have hzero : coeff.term h=(fun _ : ℝ × ℂ => (0:ℂ)) := by
      funext q
      simp only [term,if_pos hh]
    rw [hzero,termFDeriv,if_pos hh]
    exact hasFDerivAt_const (𝕜:=ℝ) (0:ℂ) p
  have hvd := (coeff.amplitude_hasDerivAt p.1 hp h).hasFDerivAt.comp p
    (hasFDerivAt_fst (𝕜:=ℝ) (p:=p))
  have hzd := (brevePhase_hasFDerivAt (cuspFrequency h) p.2).comp p
    (hasFDerivAt_snd (𝕜:=ℝ) (p:=p))
  have hprod : HasFDerivAt (fun q : ℝ × ℂ => coeff.amplitude q.1 h*
      ShortDraftTrace.breveE (cuspFrequency h*q.2)) (coeff.termFDeriv h p) p := by
    convert! hvd.mul hzd using 1
    apply ContinuousLinearMap.ext
    intro direction
    simp only [termFDeriv,if_neg hh]
    change (direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
        ShortDraftTrace.breveE (cuspFrequency h*p.2))+
      coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2 =
      coeff.amplitude p.1 h*(ShortDraftTrace.breveE (cuspFrequency h*p.2)*
        horizontalPhaseCLM (cuspFrequency h) direction.2)+
      ShortDraftTrace.breveE (cuspFrequency h*p.2)*
        ((direction.1:ℂ)*coeff.amplitudeDeriv p.1 h)
    rw [coeff.term_eq_amplitude p.1 hp h p.2]
    ring
  apply hprod.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.term_eq_amplitude q.1 hq h q.2

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)


lemma termFDeriv_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖coeff.termFDeriv h p‖≤C*((1+‖cuspFrequency h‖)*
        Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  obtain ⟨A,B,hA,hB,hweighted⟩ := coeff.weighted_bessel_bounds a ha
  obtain ⟨T,hT,hterm⟩ := coeff.slab_bound a b ha hab
  let D := B*b*(4*Real.pi)+T*(4*Real.pi)
  have hb : 0<b := ha.trans_le hab
  have hD : 0≤D := by dsimp [D];positivity
  refine ⟨A+D,add_nonneg hA hD,?_⟩
  intro h p hp
  by_cases hh : h=0
  · simp only [termFDeriv,if_pos hh,norm_zero]
    positivity
  have hv : 0<p.1 := ha.trans_le hp.1
  obtain ⟨hKu,hKd⟩ := hweighted h hh p.1 hp.1
  have hamp : ‖coeff.amplitudeDeriv p.1 h‖≤
      A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)+
      (b*(4*Real.pi*‖cuspFrequency h‖))*
        (B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
    apply (coeff.amplitudeDeriv_norm_le p.1 hv h hh).trans
    gcongr
    exact hp.2
  calc
    _ ≤ ‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*(4*Real.pi*‖cuspFrequency h‖) := coeff.termFDeriv_norm_le h p
    _ ≤ (A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)+
        (b*(4*Real.pi*‖cuspFrequency h‖))*(B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))+
        (T*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖))*(4*Real.pi*‖cuspFrequency h‖) := by
      gcongr
      exact hterm h p hp
    _ = (A+D*‖cuspFrequency h‖)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
      dsimp [D]
      ring
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith [mul_nonneg hA (norm_nonneg (cuspFrequency h))]

end SubexponentialBesselCoefficients
end

local notation "O" => ActualEisensteinCubic.O


namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma termFDeriv_summable (p : ℝ × ℂ) (hp : 0<p.1) :
    Summable (fun h : ActualEisensteinCubic.O => coeff.termFDeriv h p) := by
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound p.1 p.1 hp le_rfl
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun h => norm_nonneg _)
    (fun h => hbound h p ⟨le_rfl,le_rfl⟩)
    ((summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*p.1) (mul_pos Real.pi_pos hp)).mul_left C)

lemma series_hasFDerivAt (p : ℝ × ℂ) (hp : 0<p.1) :
    HasFDerivAt coeff.series (∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h p) p := by
  let a := p.1/2
  let b := 2*p.1
  have ha : 0<a := by dsimp [a];linarith
  have hab : a≤b := by dsimp [a,b];linarith
  have hap : a<p.1 := by dsimp [a];linarith
  have hpb : p.1<b := by dsimp [b];linarith
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound a b ha hab
  have hsum := (summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*a)
    (mul_pos Real.pi_pos ha)).mul_left C
  let slab : Set (ℝ × ℂ) := Set.Ioo a b ×ˢ Set.univ
  have hslab : IsOpen slab := isOpen_Ioo.prod isOpen_univ
  have hconn : IsPreconnected slab := isPreconnected_Ioo.prod isPreconnected_univ
  have hpSlab : p∈slab := ⟨⟨hap,hpb⟩,Set.mem_univ _⟩
  exact hasFDerivAt_tsum_of_isPreconnected hsum hslab hconn
    (fun h q hq => coeff.term_hasFDerivAt h q (ha.trans hq.1.1))
    (fun h q hq => hbound h q ⟨hq.1.1.le,hq.1.2.le⟩)
    hpSlab (coeff.summable p hp) hpSlab

lemma series_differentiableAt (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ coeff.series p := (coeff.series_hasFDerivAt p hp).differentiableAt


end SubexponentialBesselCoefficients
end


end CubicEisenstein

end

end OAI

end


