-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0243_parallel3
-- name    : PNT_ZeroFree_433_0243_parallel3
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:36:17.084397+00:00
-- url     : https://prove2.me/theorems/fe604dbb-1e02-4fcc-9b1e-67ca0bcf7a2f
-- title:
--   Zero-free region foundations: Eisenstein.CubeResidueStrata [0243_parallel3]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CubeResidueStrata
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CubeResidueStrata.lean#L85-L429

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0133
import Definitions.Def_PNT_ZeroFree_433_0179_parallel1
import Definitions.Def_PNT_ZeroFree_433_0180_parallel1
import Definitions.Def_PNT_ZeroFree_433_0186_parallel1
import Definitions.Def_PNT_ZeroFree_433_0190_parallel2
import Definitions.Def_PNT_ZeroFree_433_0200_parallel1
import Definitions.Def_PNT_ZeroFree_433_0202_parallel1
import Definitions.Def_PNT_ZeroFree_433_0212_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0219_parallel1
import Definitions.Def_PNT_ZeroFree_433_0223_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0230_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0235_parallel2
import Definitions.Def_PNT_ZeroFree_433_0236_parallel2
import Definitions.Def_PNT_ZeroFree_433_0243_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel3
import Definitions.Def_PNT_ZeroFree_433_0249_parallel2
import Definitions.Def_PNT_ZeroFree_433_0251_parallel1
import Definitions.Def_PNT_ZeroFree_433_0257_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel2
import Definitions.Def_PNT_ZeroFree_433_0268_parallel1
import Definitions.Def_PNT_ZeroFree_433_0284_parallel1
import Definitions.Def_PNT_ZeroFree_433_0291_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CubeResidueStrata.lean
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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients

theorem series_cusp_decay (coeff : SubexponentialBesselCoefficients) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀v z,a≤v → ‖coeff.series (v,z)‖≤C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨D,hD,hterm⟩ := coeff.term_cusp_bound a ha
  let S : ℝ := ∑'h : ActualEisensteinCubic.O,Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)
  have hS : 0≤S := tsum_nonneg (fun h => (Real.exp_pos _).le)
  have hs := summable_exp_neg_cuspFrequency_norm (Real.pi*a/2) (by positivity)
  refine ⟨D*S*(2/(2*residualCuspDecayRate)),by have := residualCuspDecayRate_pos;positivity,?_⟩
  intro v z hav
  have hv : 0<v := ha.trans_le hav
  have hb (h : ActualEisensteinCubic.O) : ‖coeff.term h (v,z)‖≤
      (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
    by_cases hh : h=0
    · simp only [term,if_pos hh,norm_zero]
      positivity
    have he : Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)≤
        Real.exp (-(2*residualCuspDecayRate)*v)*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left (cuspFrequency_norm_lower h hh)
        (show 0≤Real.pi*v/2 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hav (show 0≤Real.pi*‖cuspFrequency h‖/2 by positivity)
      unfold residualCuspDecayRate
      nlinarith
    exact (hterm h v z hav).trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring))
  have hsum := tsum_of_norm_bounded (hs.hasSum.mul_left (D*v*Real.exp (-(2*residualCuspDecayRate)*v))) hb
  calc
    _ ≤ (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*S := hsum
    _ = (D*S)*(v*Real.exp (-(2*residualCuspDecayRate)*v)) := by ring
    _ ≤ (D*S)*((2/(2*residualCuspDecayRate))*Real.exp (-((2*residualCuspDecayRate)/2)*v)) :=
      mul_le_mul_of_nonneg_left (norm_mul_exp_neg_bound (2*residualCuspDecayRate) v
        (mul_pos (by norm_num) residualCuspDecayRate_pos)) (mul_nonneg hD hS)
    _ = _ := by
      rw [show -((2*residualCuspDecayRate)/2)*v=-residualCuspDecayRate*v by ring]
      ring

theorem series_cubic_decay (coeff : SubexponentialBesselCoefficients) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀v z,a≤v → ‖coeff.series (v,z)‖≤C/v^3 := by
  obtain ⟨C,hC,hbound⟩ := coeff.series_cusp_decay a ha
  let k := residualCuspDecayRate
  have hk : 0<k := residualCuspDecayRate_pos
  refine ⟨C*(6/k^3),by positivity,?_⟩
  intro v z hav
  have hv : 0<v := ha.trans_le hav
  have he : Real.exp (-k*v)*v^3≤6/k^3 := by
    have hb := Real.pow_div_factorial_le_exp (k*v) (mul_nonneg hk.le hv.le) 3
    norm_num only [Nat.factorial] at hb
    have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-k*v)).le
    rw [←Real.exp_add,show k*v+ -k*v=0 by ring,Real.exp_zero] at hm
    apply (le_div_iff₀ (pow_pos hk 3)).mpr
    nlinarith [hm]
  apply (le_div_iff₀ (pow_pos hv 3)).mpr
  calc
    _ ≤ (C*Real.exp (-k*v))*v^3 := mul_le_mul_of_nonneg_right (hbound v z hav) (pow_nonneg hv.le 3)
    _ = C*(Real.exp (-k*v)*v^3) := by ring
    _ ≤ C*(6/k^3) := mul_le_mul_of_nonneg_left he hC


end SubexponentialBesselCoefficients
end

open scoped BigOperators Classical MatrixGroups Matrix


open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O


end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicEisenstein


open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O


lemma cubeStratumSymbol_sum (p C:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hC:IsCoprime C p) (j:Fin 4) :
    (∑' b:CubicUnitResidue (p^(3-j.val)), cubeStratumSymbol p C j b) =
      if j=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else if j=3 then 1 else 0 := by
  have h3:eisEmbedding (symbol C (p^3))=1:=by
    rw [cubicSymbol_pow_denominator,symbol_cube_of_isCoprime C p hprimary hC,map_one]
  unfold cubeStratumSymbol
  rw [unit_stratum_symbol_gauss p C hprimary (3-j.val)]
  fin_cases j
  · have hh:=cubicUnitGaussSum_prime_power_zero p hp hprimary 2
    norm_num at hh ⊢
    rw [hh,h3,mul_one]
  · have hh:=cubicUnitGaussSum_prime_power_zero p hp hprimary 1
    norm_num at hh ⊢
    simp [hh]
  · have hh:=cubicUnitGaussSum_prime_power_zero p hp hprimary 0
    norm_num at hh ⊢
    simp [hh]
  · simp

lemma cubeStrata_weighted_sum (p C:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hC:IsCoprime C p) (w:Fin 4→ℂ) :
    (∑ j:Fin 4, w j * ∑' b:CubicUnitResidue (p^(3-j.val)), cubeStratumSymbol p C j b) =
      w 0*(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)+w 3 := by
  simp_rw [cubeStratumSymbol_sum p C hp hprimary hC]
  simp [Fin.sum_univ_succ]
  ring

end CubicEisenstein


end

end OAI

end


