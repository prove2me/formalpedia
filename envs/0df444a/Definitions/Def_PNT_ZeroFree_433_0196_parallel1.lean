-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0196_parallel1
-- name    : PNT_ZeroFree_433_0196_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:24:23.513221+00:00
-- url     : https://prove2.me/theorems/29c0193e-a57b-440c-ad71-cec18dc3cd86
-- title:
--   Zero-free region foundations: Eisenstein.BarrierPotential [0196_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.BarrierPotential
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/BarrierPotential.lean#L83-L550

import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0104
import Definitions.Def_PNT_ZeroFree_433_0105
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel2
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel2
import Definitions.Def_PNT_ZeroFree_433_0155_parallel1
import Definitions.Def_PNT_ZeroFree_433_0195_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/BarrierPotential.lean
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
open scoped BigOperators Classical Topology ContDiff MatrixGroups

lemma axisLaplacian_const_add (c : ℂ) (f : SpatialCoordinates→ℂ) (p : SpatialCoordinates) :
    axisLaplacian (fun q => c+f q) p=axisLaplacian f p := by
  unfold axisLaplacian axisSlice
  simp only [deriv_const_add,deriv_const_add']


lemma cuspBarrierProfile_laplacian_zero (a b v : ℝ) (ha : 1<a) (hab : a<b) (hv : v≤1) :
    positiveHeightLaplacian (cuspBarrierProfile a b) v=0 := by
  have hh := cuspBarrierDefectProfile_zero a b v hab (hv.trans_lt ha)
  rw [cuspBarrierDefectProfile,cuspBarrierProfile_zero a b hab v (hv.trans ha.le),sub_zero] at hh
  exact hh

def cuspBarrierField (a b : ℝ) (p : SpatialCoordinates) : ℝ :=
  1+fullCuspProfileField (cuspBarrierProfile a b) p

def cuspBarrierDefectField (a b : ℝ) (p : SpatialCoordinates) : ℝ :=
  -1+fullCuspProfileField (cuspBarrierDefectProfile a b) p

lemma cuspBarrierField_eq (a b : ℝ) (p : SpatialCoordinates) (hp : 0<p 2) :
    cuspBarrierField a b p=cuspBarrier a b (upperPoint (spatialHorizontal p) (p 2) hp) := by
  rw [cuspBarrierField,cuspBarrier,fullCuspProfileField_eq _ p hp]

lemma cuspBarrierDefectField_eq (a b : ℝ) (p : SpatialCoordinates) (hp : 0<p 2) :
    cuspBarrierDefectField a b p=cuspBarrierDefect a b (upperPoint (spatialHorizontal p) (p 2) hp) := by
  rw [cuspBarrierDefectField,cuspBarrierDefect,fullCuspProfileField_eq _ p hp]


lemma cuspBarrier_euclidean_eq (a b : ℝ) (p : EuclideanSpatial) (hp : 0<p 2) :
    cuspBarrier a b (euclideanToHyperbolic p)=cuspBarrierField a b p.ofLp := by
  rw [cuspBarrierField_eq a b p.ofLp hp,euclideanToHyperbolic_positive p hp]
  congr 1
  simp only [spatialHorizontal,mul_comm]

lemma cuspBarrierDefect_euclidean_eq (a b : ℝ) (p : EuclideanSpatial) (hp : 0<p 2) :
    cuspBarrierDefect a b (euclideanToHyperbolic p)=cuspBarrierDefectField a b p.ofLp := by
  rw [cuspBarrierDefectField_eq a b p.ofLp hp,euclideanToHyperbolic_positive p hp]
  congr 1
  simp only [spatialHorizontal,mul_comm]


end


open scoped ComplexConjugate

theorem ground_state_square_completion (a b : ℝ) (ha : a ≠ 0) (z d : ℂ) :
    ‖d‖^2 - b*((2*(conj z*d).re*a - ‖z‖^2*b)/a^2) =
      ‖d - (b/a : ℝ)*z‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  field_simp
  ; ring

theorem ground_state_directional_inequality (a b : ℝ) (ha : a ≠ 0) (z d : ℂ) :
    b*((2*(conj z*d).re*a - ‖z‖^2*b)/a^2) ≤ ‖d‖^2 := by
  have hh := ground_state_square_completion a b ha z d
  nlinarith [sq_nonneg ‖d - (b/a : ℝ)*z‖]

end CubicEisenstein

namespace SecondPassArithmetic


section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)


theorem canonicalFirstZero_normalization (C Γ X F K B Z ε : ℝ)
    (hC : 0≤C) (hX : 0<X) (hF : 0≤F) (hK : 0≤K) (hB : 1≤B)
    (hrow : K≤(X*F)*Z^(-((1:ℝ)/40))) :
    B*(C*(Real.exp 1*B)^(1+ε)*(X/B^3)*F*Γ^2*K)≤
      (C*(Real.exp 1)^(1+ε))*B^ε*Γ^2*(X*F)^2*Z^(-((1:ℝ)/40)) := by
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hc : 0≤C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F) := by
    positivity
  calc
    _ = (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*K/B := by
      rw [Real.mul_rpow (Real.exp_pos _).le hB0.le,Real.rpow_add hB0,Real.rpow_one]
      field_simp

    _ ≤ (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*K :=
      div_le_self (mul_nonneg hc hK) hB
    _ ≤ (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*((X*F)*Z^(-((1:ℝ)/40))) :=
      mul_le_mul_of_nonneg_left hrow hc
    _ = _ := by ring

end

theorem canonicalFirstTail_numerator (C Γ B₀ B lengthScale F K U ε : ℝ)
    (hC : 0≤C) (_hB₀ : 0≤B₀) (hB : 0≤B) (hL : 0≤lengthScale) (hF : 0≤F)
    (hK : 1≤K) (hU : 1≤U) (hε : 0≤ε)
    (hB₀U : B₀≤U) (hBU : B≤U) (hLU : lengthScale≤U) (hFU : F≤U) (hKU : K≤U) :
    B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*K*(1+lengthScale^3*B^4/K)^2)≤
      4*C*Γ^2*U^(25+ε) := by
  have hU0 : 0<U := zero_lt_one.trans_le hU
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hratio : lengthScale^3*B^4/K≤U^7 := by
    calc
      _ ≤ lengthScale^3*B^4 := div_le_self (mul_nonneg (pow_nonneg hL _) (pow_nonneg hB _)) hK
      _ ≤ U^3*U^4 := by gcongr
      _ = U^7 := by ring
  have hU7 : 1≤U^7 := one_le_pow₀ hU
  have hs : (1+lengthScale^3*B^4/K)^2≤4*U^14 := by
    have hnonneg : 0≤lengthScale^3*B^4/K := div_nonneg (by positivity) hK0.le
    have ha : 1+lengthScale^3*B^4/K≤2*U^7 := by linarith
    have hp := pow_le_pow_left₀ (by positivity : 0≤1+lengthScale^3*B^4/K) ha 2
    nlinarith [show (U^7)^2=U^14 by ring]
  calc
    _ ≤ U*(C*U^(4+ε)*U^4*U*Γ^2*U*(4*U^14)) := by
      gcongr
    _ = _ := by
      rw [Real.rpow_add hU0,Real.rpow_add hU0]
      norm_num
      ring

theorem canonicalCutoff_ratio (Ksrc Z η : ℝ) (hK : 0<Ksrc) (hZ : 0<Z) :
    Ksrc/(Ksrc/Z^η)=Z^η := by
  have hz := (Real.rpow_pos_of_pos hZ η).ne'
  field_simp

theorem canonicalFirstTail_polynomial (C Γ B₀ B lengthScale F Ksrc U Z η ε M : ℝ) (A : ℕ)
    (hC : 0≤C) (hB₀ : 0≤B₀) (hB : 0≤B) (hL : 0≤lengthScale) (hF : 0≤F)
    (hK : 1≤Ksrc) (hU : 1≤U) (hε : 0≤ε) (hZ : 0<Z)
    (hB₀U : B₀≤U) (hBU : B≤U) (hLU : lengthScale≤U) (hFU : F≤U) (hKU : Ksrc≤U) :
    B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2/
      (1+(Ksrc/(Ksrc/Z^η))/Real.exp (2*M))^A)≤
      (4*C*Γ^2*(Real.exp (2*M))^A)*U^(25+ε)/Z^(η*(A:ℝ)) := by
  have hK0 : 0<Ksrc := zero_lt_one.trans_le hK
  have hη : 0<Z^η := Real.rpow_pos_of_pos hZ _
  have hden : 0<(Z^η/Real.exp (2*M))^A := pow_pos (div_pos hη (Real.exp_pos _)) _
  rw [canonicalCutoff_ratio Ksrc Z η hK0 hZ]
  calc
    _ = (B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2))/(1+Z^η/Real.exp (2*M))^A := by ring
    _ ≤ (4*C*Γ^2*U^(25+ε))/(1+Z^η/Real.exp (2*M))^A :=
      div_le_div_of_nonneg_right (canonicalFirstTail_numerator C Γ B₀ B lengthScale F Ksrc U ε
        hC hB₀ hB hL hF hK hU hε hB₀U hBU hLU hFU hKU) (by positivity)
    _ ≤ (4*C*Γ^2*U^(25+ε))/(Z^η/Real.exp (2*M))^A := by
      exact div_le_div_of_nonneg_left (by positivity) hden
        (pow_le_pow_left₀ (div_pos hη (Real.exp_pos _)).le (by linarith) A)
    _ = _ := by
      rw [div_pow,←Real.rpow_natCast (Z^η) A,←Real.rpow_mul hZ.le]
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring


end SecondPassArithmetic

end

end OAI

end


