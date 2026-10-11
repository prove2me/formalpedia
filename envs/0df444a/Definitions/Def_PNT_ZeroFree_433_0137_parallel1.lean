-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0137_parallel1
-- name    : PNT_ZeroFree_433_0137_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:55:30.731079+00:00
-- url     : https://prove2.me/theorems/9f6790d2-38c7-403d-9135-e34036c5506e
-- title:
--   Zero-free region foundations: QuadraticSieve.PoissonConstants [0137_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonConstants
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonConstants.lean#L80-L560

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
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonConstants.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

theorem list_exists_positive_bound (xs : List ℝ) :
    ∃ H : ℝ, 1≤H ∧ ∀x∈xs, x≤H := by
  induction xs with
  | nil => exact ⟨1,le_rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨H,hH,hxs⟩ := ih
    refine ⟨max H x, hH.trans (le_max_left _ _), ?_⟩
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact le_max_right _ _
    · exact (hxs y hy).trans (le_max_left _ _)


end

section

theorem selectedPoisson_upper (C C1 M X η : ℝ)
    (hC : 4≤C) (hCC : C≤C1) (hM : 1≤M) (hX : 1≤X)
    (hη : 0≤η) (hη1 : η≤1) :
    4≤selectedPoissonT C M X η ∧
    (M*X)^η≤selectedPoissonT C M X η ∧
    selectedPoissonK C M X η≤C1*(M*X)^3 := by
  have hC10 : 0≤C1 := by linarith
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 1≤M*X := by nlinarith
  have hP0 : 0<M*X := by positivity
  have hR : 1≤(M*X)^η := Real.one_le_rpow hP hη
  have hT : 4≤selectedPoissonT C M X η := by dsimp [selectedPoissonT]; nlinarith
  refine ⟨hT,by dsimp [selectedPoissonT]; nlinarith,?_⟩
  have hXP : X≤M*X := by nlinarith
  have hfrac : X^2/M≤(M*X)^2 :=
    (div_le_self (sq_nonneg _) hM).trans (pow_le_pow_left₀ hX0.le hXP 2)
  have hrpow : (M*X)^η≤M*X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hη1
  calc
    selectedPoissonK C M X η = C*(M*X)^η*(X^2/M) := by
      unfold selectedPoissonK selectedPoissonT
      ring
    _ ≤ C1*(M*X)*(M*X)^2 := by gcongr
    _ = C1*(M*X)^3 := by ring

theorem poisson_seven_scale_bounds (g K N P B C1 : ℝ)
    (hP : 1≤P) (hB : 1≤B) (hC1 : 1≤C1)
    (hg0 : 0≤g) (hK0 : 0≤K) (hN0 : 0≤N)
    (hg : g≤B*P) (hK : K≤C1*P^3) (hN : N≤P) :
    ∀x∈([g,K,N,(2*K)*N,N*N,g*(N*N),K*N] : List ℝ),
      0≤x ∧ x≤(2*C1+B)*P^4 := by
  have hP0 : 0≤P := by linarith
  have hD : 1≤2*C1+B := by linarith
  have hp14 : P≤P^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hP (show 1≤4 by omega)
  have hp24 : P^2≤P^4 := pow_le_pow_right₀ hP (by omega)
  have hp34 : P^3≤P^4 := pow_le_pow_right₀ hP (by omega)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨hg0, hg.trans ?_⟩
    calc
      B*P ≤ B*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨hK0,hK.trans ?_⟩
    calc
      C1*P^3 ≤ C1*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨hN0,hN.trans (hp14.trans ?_)⟩
    nlinarith [show 0≤P^4 by positivity]
  · refine ⟨by positivity,?_⟩
    calc
      2*K*N ≤ 2*(C1*P^3)*P := by gcongr
      _ = (2*C1)*P^4 := by ring
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨by positivity,?_⟩
    calc
      N*N ≤ P*P := by gcongr
      _ = P^2 := by ring
      _ ≤ P^4 := hp24
      _ ≤ (2*C1+B)*P^4 := by nlinarith [show 0≤P^4 by positivity]
  · refine ⟨by positivity,?_⟩
    calc
      g*(N*N) ≤ (B*P)*(P*P) := by gcongr
      _ = B*P^3 := by ring
      _ ≤ B*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨by positivity,?_⟩
    calc
      K*N ≤ (C1*P^3)*P := by gcongr
      _ = C1*P^4 := by ring
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith

theorem power_cutoff_dominates (P T η : ℝ) (l : ℕ)
    (hP : 1≤P) (hT : P^η≤T) (hpow : 4≤η*l) :
    P^4≤T^l := by
  have hp0 : 0<P := by linarith
  calc
    P^4 = P^(4:ℝ) := by rw [Real.rpow_ofNat]
    _ ≤ P^(η*l) := Real.rpow_le_rpow_of_exponent_le hP hpow
    _ = (P^η)^l := by rw [Real.rpow_mul hp0.le,Real.rpow_natCast]
    _ ≤ T^l := pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) hT l

theorem poisson_truncation_small (P T η K M N C1 : ℝ) (l : ℕ)
    (hP : 1≤P) (hT : P^η≤T) (hpow : 4≤η*l)
    (_hK : 0≤K) (hM : 0≤M) (hN : 0≤N) (hC1 : 0≤C1)
    (hKP : K≤C1*P^3) (hMP : M≤P) (hNP : N≤P) :
    K*M/T^l≤C1 ∧ K*N/T^l≤C1 := by
  have hp0 : 0<P := by linarith
  have htpos : 0<T := lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 _) hT
  have hcut := power_cutoff_dominates P T η l hP hT hpow
  have hb (Y : ℝ) (hY : 0≤Y) (hYP : Y≤P) : K*Y/T^l≤C1 := by
    apply (div_le_iff₀ (pow_pos htpos _)).mpr
    calc
      K*Y ≤ (C1*P^3)*P := by gcongr
      _ = C1*P^4 := by ring
      _ ≤ C1*T^l := by gcongr
  exact ⟨hb M hM hMP,hb N hN hNP⟩

theorem poisson_tail_abstract (B P t K η M : ℝ) (A : ℕ)
    (hB : 1≤B) (hP : 1≤P) (hM : 0≤M)
    (ht : 1/(B*P^2)≤t) (hu : P^η≤1+t*K) (hA : 4≤η*A) :
    M/((min 1 t)^2*(1+t*K)^A)≤B^2*M := by
  have hB0 : 0<B := by linarith
  have hP0 : 0<P := by linarith
  have hBP : 1≤B*P^2 := by nlinarith [sq_nonneg (P-1)]
  have hinv : 1/(B*P^2)≤1 := (div_le_one (by positivity)).mpr hBP
  have htlo : 1/(B*P^2)≤min 1 t := le_min hinv ht
  have htpos : 0<min 1 t := lt_of_lt_of_le (by positivity) htlo
  have hup : 0<1+t*K := lt_of_lt_of_le (Real.rpow_pos_of_pos hP0 _) hu
  have hpow := power_cutoff_dominates P (1+t*K) η A hP hu hA
  have hprod : 1/B^2≤(min 1 t)^2*(1+t*K)^A := by
    calc
      1/B^2 = (1/(B*P^2))^2*P^4 := by field_simp
      _ ≤ (min 1 t)^2*(1+t*K)^A := by gcongr
  apply (div_le_iff₀ (by positivity : 0<(min 1 t)^2*(1+t*K)^A)).mpr
  have hh := mul_le_mul_of_nonneg_left hprod (show 0≤B^2*M by positivity)
  have he : (B^2*M)*(1/B^2)=M := by field_simp
  rw [he] at hh
  exact hh

theorem selectedPoisson_tail_shape (C B M X q η : ℝ) (A : ℕ)
    (hC : B≤C) (hB : 1≤B) (hM : 1≤M) (hX : 1≤X)
    (hq : 1≤q) (_hη : 0≤η) (hA : 4≤η*A) :
    M/((min 1 (M/((B*q)*(X/q)*(X/q))))^2*
      (1+(M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η)^A)≤B^2*M := by
  have hB0 : 0<B := by linarith
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hq0 : 0<q := by linarith
  have hC0 : 0<C := by linarith
  have hP : 1≤M*X := by nlinarith
  have hXP : X≤M*X := by nlinarith
  have hMQ : 1≤M*q := by nlinarith
  have hEq : M/((B*q)*(X/q)*(X/q))=M*q/(B*X^2) := by field_simp
  have ht : 1/(B*(M*X)^2)≤M/((B*q)*(X/q)*(X/q)) := by
    rw [hEq]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      1*(B*X^2) ≤ B*(M*X)^2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0.le hXP 2) hB0.le
      _ ≤ (M*q)*(B*(M*X)^2) := by nlinarith [show 0≤B*(M*X)^2 by positivity]
  have hu : (M*X)^η≤1+(M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η := by
    rw [selectedPoisson_radial_identity C B M X q η hM0 hX0 hq0 hB0]
    have hp : 0≤(M*X)^η := Real.rpow_nonneg (by positivity) _
    have hb : (M*X)^η≤selectedPoissonT C M X η*q/B := by
      apply (le_div_iff₀ hB0).mpr
      dsimp [selectedPoissonT]
      calc
        (M*X)^η*B = B*(M*X)^η := by ring
        _ ≤ C*(M*X)^η := mul_le_mul_of_nonneg_right hC hp
        _ ≤ C*(M*X)^η*q := le_mul_of_one_le_right (by positivity) hq
    linarith
  exact poisson_tail_abstract B (M*X) _ _ η M A hB hP hM0.le ht hu hA

theorem selectedPoisson_principal_shape (C M X N η α : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hN : 0≤N) (hNX : N≤X)
    (hη : 0≤η) (hα : 1/2≤α) :
    Real.sqrt (M/selectedPoissonK C M X η)*N+
      Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) ≤
    M+selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hP hη
  have hT : 1≤selectedPoissonT C M X η := by dsimp [selectedPoissonT]; nlinarith
  have hT0 : 0<selectedPoissonT C M X η := by linarith
  have hK0 : 0<selectedPoissonK C M X η := by unfold selectedPoissonK; positivity
  have hfrac : M/selectedPoissonK C M X η≤(M/X)^2 := by
    apply (div_le_iff₀ hK0).mpr
    have he : (M/X)^2*selectedPoissonK C M X η=M*selectedPoissonT C M X η := by
      unfold selectedPoissonK
      field_simp
    rw [he]
    nlinarith
  have hsqrt : Real.sqrt (M/selectedPoissonK C M X η)≤M/X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,hfrac⟩
  have hfirst : Real.sqrt (M/selectedPoissonK C M X η)*N≤M := by
    calc
      _ ≤ (M/X)*X := by gcongr
      _ = M := by field_simp
  have hsecond : Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) ≤
      selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
    calc
      _ ≤ Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
        gcongr ; linarith
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hT
          (show 0≤Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) by positivity)
        nlinarith
  exact add_le_add hfirst hsecond

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

def poissonShape (M X α : ℝ) : ℝ := M+X+X^(2*α-1)*M^(1-α)
def poissonShapeConstant (B C1 : ℝ) : ℝ := 2+4*C1^3+B^2+C1

theorem poisson_envelope_identity (H C P η Z : ℝ) (hP : 0<P) :
    262144*((H*P^(4*η))^8)^8*(C*P^(3*η)*Z) =
      (262144*H^64*C)*P^(259*η)*Z := by
  have hp : (P^(4*η))^64*P^(3*η)=P^(259*η) := by
    calc
      _ = P^((4*η)*64)*P^(3*η) := by rw [Real.rpow_mul hP.le (4*η) 64,Real.rpow_ofNat]
      _ = P^((4*η)*64+3*η) := (Real.rpow_add hP _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = (262144*H^64*C)*((P^(4*η))^64*P^(3*η))*Z := by ring
    _ = _ := by rw [hp]


end CanonicalQuadraticSieve

end

end OAI

end


