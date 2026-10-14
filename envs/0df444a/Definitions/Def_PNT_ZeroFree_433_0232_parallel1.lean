-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0232_parallel1
-- name    : PNT_ZeroFree_433_0232_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:29:34.13071+00:00
-- url     : https://prove2.me/theorems/edb118e5-299c-4417-aeff-521f79076f28
-- title:
--   Zero-free region foundations: Eisenstein.PrimePowerGaussSums [0232_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.PrimePowerGaussSums
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/PrimePowerGaussSums.lean#L270-L555

import Definitions.Def_PNT_ZeroFree_433_0232_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/PrimePowerGaussSums.lean
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

open scoped BigOperators Classical
namespace CubicEisenstein


section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O


namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)


lemma term_eq_amplitude (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (z : ℂ) :
    coeff.term h (v,z)=coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  by_cases hh : h=0
  · simp only [term,amplitude,if_pos hh,zero_mul]
  · rw [coeff.term_bessel h hh v hv z,amplitude,if_neg hh]

lemma term_continuousOn (h : ActualEisensteinCubic.O) :
    ContinuousOn (coeff.term h) {p : ℝ × ℂ | 0<p.1} := by
  unfold term
  by_cases hh : h=0
  · simp only [if_pos hh]
    exact continuousOn_const
  simp only [if_neg hh]
  intro p hp
  change 0<p.1 at hp
  have hpow : ContinuousAt (fun q : ℝ × ℂ => (q.1:ℂ)^(2/3:ℂ)) p :=
    (Complex.continuousAt_ofReal_cpow_const p.1 (2/3:ℂ) (Or.inr hp.ne')).comp continuousAt_fst
  have hsource : ContinuousAt (fun q : ℝ × ℂ => sourceFourierKernel (4/3) (cuspFrequency h*q.1)) p :=
    (sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp (by fun_prop)
  have hphase : Continuous (fun q : ℝ × ℂ => ShortDraftTrace.breveE (cuspFrequency h*q.2)) := by
    change Continuous (fun q : ℝ × ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((cuspFrequency h*q.2)+starRingEnd ℂ (cuspFrequency h*q.2))))
    fun_prop
  exact (((continuousAt_const.mul hpow).mul hsource).mul hphase.continuousAt).continuousWithinAt


def series (p : ℝ × ℂ) : ℂ := ∑'h : ActualEisensteinCubic.O,coeff.term h p


lemma series_bessel (v : ℝ) (hv : 0<v) (z : ℂ) :
    coeff.series (v,z)=∑'h : ActualEisensteinCubic.O,coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  exact tsum_congr (fun h => coeff.term_eq_amplitude v hv h z)

lemma series_period (v : ℝ) (z : ℂ) (n : ActualEisensteinCubic.O) :
    coeff.series (v,z+3*ConcreteTraceCRT.eisEmbedding n)=coeff.series (v,z) := by
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · simp only [term,if_pos hh]
  simp only [term,if_neg hh]
  rw [mul_add,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]


end SubexponentialBesselCoefficients
end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

end CubicEisenstein

open scoped BigOperators Classical

namespace ShortDraftCRT
variable {R : Type*} [CommRing R]

theorem inverse_residue_congr (D r r0 u u0 : R) (hcop : IsCoprime D r)
    (hr : D∣r-r0) (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) : D∣u-u0 := by
  apply hcop.dvd_of_dvd_mul_right
  have hh := dvd_sub (dvd_sub hu hu0) (dvd_mul_of_dvd_right hr u0)
  convert! hh using 1 ; ring

theorem inverse_weight_residue_congr (D r r0 u u0 d d0 : R)
    (hcop : IsCoprime D r) (hr : D∣r-r0)
    (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) (hd : D∣d-d0) :
    D∣(-d*u)-(-d0*u0) := by
  have hi := inverse_residue_congr D r r0 u u0 hcop hr hu hu0
  have hh := dvd_add (dvd_mul_of_dvd_left hd u) (dvd_mul_of_dvd_right hi d0)
  convert! dvd_neg.mpr hh using 1 ; ring

theorem fixed_additive_sector {K : Type*} [Field K]
    (ι : R→+*K) (ψ : AddChar K ℂ) (lam D r r0 u u0 d d0 x : R)
    (hlam : ι lam≠0) (hD : ι D≠0)
    (hperiod : ∀y : R,ψ (ι y/ι lam)=1)
    (hcop : IsCoprime D r) (hr : D∣r-r0)
    (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) (hd : D∣d-d0) :
    ψ (ι (-d*u)*ι x/(ι lam*ι D))=
      ψ (ι (-d0*u0)*ι x/(ι lam*ι D)) :=
  addChar_congr_of_dvd ι ψ lam D (-d*u) (-d0*u0) x hlam hD hperiod
    (inverse_weight_residue_congr D r r0 u u0 d d0 hcop hr hu hu0 hd)

theorem strong_sector_additive_congruences (M lam c r r0 d d0 : R)
    (hlam : lam^3∣M) (hc : c∣M) (hr : M^2∣r-r0) (hd : M*c∣d-d0) :
    lam^3*c∣r-r0 ∧ lam^3*c∣d-d0 := by
  constructor
  · apply (show lam^3*c∣M^2 by simpa only [pow_two] using mul_dvd_mul hlam hc).trans hr
  · exact (mul_dvd_mul hlam (dvd_refl c)).trans hd

end ShortDraftCRT


end

end OAI

end


