-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0013
-- name    : PNT_ZeroFree_433_0013
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:13:30.65966+00:00
-- url     : https://prove2.me/theorems/1ccaf338-000b-4fd3-9697-638435509208
-- title:
--   Zero-free region foundations: GaussSum.RamifiedTracePhase [0013]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.RamifiedTracePhase
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/RamifiedTracePhase.lean#L23-L581

import Definitions.Def_PNT_ZeroFree_433_0012

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/RamifiedTracePhase.lean#L23-L581
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.RamifiedTracePhase
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

namespace TraceLambdaPhase

open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped ComplexConjugate

theorem eisLam_sq : eisLam ^ 2 = (-3 : ℂ) := by
  change (1 + 2 * omega3) ^ 2 = -3
  linear_combination 4 * omega3_sq

theorem exp_minus_four_pi_div_three :
    Complex.exp (-(4 : ℂ) * Real.pi * Complex.I / 3) = omega3 := by
  have hshift : Complex.exp (-(4 : ℂ) * Real.pi * Complex.I / 3) =
      Complex.exp ((2 : ℂ) * Real.pi * Complex.I / 3) := by
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-1, ?_⟩
    push_cast
    ring
  rw [hshift]
  have harg : ((2 : ℂ) * Real.pi * Complex.I / 3) =
      (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I]
  have htwo : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [htwo, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  unfold omega3
  push_cast
  ring

theorem breveE_traceLambda_square :
    ShortDraftTrace.breveE (1 / (eisLam * eisLam)) = omega3 := by
  have harg : (1 : ℂ) / (eisLam * eisLam) = -(1 : ℂ) / 3 := by
    rw [← pow_two, eisLam_sq]
    ring
  rw [harg]
  change Complex.exp (2 * Real.pi * Complex.I *
    ((-(1 : ℂ) / 3) + conj (-(1 : ℂ) / 3))) = omega3
  have hconj : conj (-(1 : ℂ) / 3) = -(1 : ℂ) / 3 := by
    simp only [map_div₀, map_neg, map_one, map_ofNat]
  rw [hconj]
  convert! exp_minus_four_pi_div_three using 1 ; ring_nf

end TraceLambdaPhase

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase

theorem traceLambda_ne_zero : traceLambda ≠ 0 := by
  intro h
  have hh := congrArg eisEmbedding h
  rw [eisEmbedding_traceLambda, map_zero] at hh
  exact eisLam_ne_zero hh

private theorem traceLambda_span_eq_lambda :
    Ideal.span {traceLambda} = Ideal.span {lambda} := by
  rw [traceLambda_eq_unit_mul_lambda]
  exact Ideal.span_singleton_mul_left_unit neg_omega_isUnit lambda

theorem traceLambda_quotient_card :
    Nat.card (O ⧸ Ideal.span {traceLambda}) = 3 := by
  rw [traceLambda_span_eq_lambda]
  exact ActualEisensteinSieve.lambda_card

private theorem traceLambda_quotient_maximal :
    (Ideal.span {traceLambda}).IsMaximal := by
  rw [traceLambda_span_eq_lambda]
  exact ActualEisensteinSieve.lambda_maximal

noncomputable def quadraticGammaTraceLambda : ℂ := by
  let c : O := traceLambda
  let hc : c ≠ 0 := traceLambda_ne_zero
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  exact (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)

theorem quadraticGammaTraceLambda_eq_I : quadraticGammaTraceLambda = Complex.I := by
  let c : O := traceLambda
  let hc : c ≠ 0 := traceLambda_ne_zero
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  have hcard : Fintype.card (O ⧸ Ideal.span {c}) = 3 := by
    simpa only [Nat.card_eq_fintype_card] using traceLambda_quotient_card
  let e : ZMod 3 ≃+* (O ⧸ Ideal.span {c}) :=
    ZMod.ringEquivOfPrime _ Nat.prime_three hcard
  have hphase : ψ 1 = omega3 := by
    change ShortDraftTrace.breveE
      (eisEmbedding 1 / (eisEmbedding c * eisLam)) = omega3
    rw [map_one, show eisEmbedding c = eisLam from eisEmbedding_traceLambda]
    exact breveE_traceLambda_square
  have hsum : (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) = 1 + 2 * omega3 := by
    have hreindex := (e.toEquiv.sum_comp (fun x : O ⧸ Ideal.span {c} => ψ (x ^ 2))).symm
    rw [hreindex]
    have hfin : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
    rw [hfin]
    rw [Finset.sum_insert (by decide : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3))),
      Finset.sum_insert (by decide : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3))),
      Finset.sum_singleton]
    have h2sq : (2 : ZMod 3) ^ 2 = 1 := by decide
    have he2 : e (2 : ZMod 3) ^ 2 = 1 := by
      rw [← map_pow, h2sq, map_one]
    change ψ (e (0 : ZMod 3) ^ 2) +
      (ψ (e (1 : ZMod 3) ^ 2) + ψ (e (2 : ZMod 3) ^ 2)) =
        1 + 2 * omega3
    simp only [map_zero, map_one, zero_pow (by decide : 2 ≠ 0),
      one_pow, he2, map_zero_eq_one, hphase]
    ring
  have hLam : eisLam = (Real.sqrt 3 : ℝ) * Complex.I := by
    unfold eisLam omega3
    ring
  have hnorm : ‖eisEmbedding c‖ = Real.sqrt 3 := by
    rw [show eisEmbedding c = eisLam from eisEmbedding_traceLambda, hLam,
      norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 (by norm_num))]
  unfold quadraticGammaTraceLambda
  change (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) /
      (‖eisEmbedding c‖ : ℂ) = Complex.I
  rw [hsum, hnorm]
  change eisLam / ((Real.sqrt 3 : ℝ) : ℂ) = Complex.I
  rw [hLam]
  field_simp

end ActualEisensteinCubic

namespace PoissonFirstLocal
open scoped Classical

def quotientUnitMask {R : Type*} [CommRing R] (z : R) : ℂ :=
  if IsUnit z then 1 else 0

private theorem quotientUnitMask_mul {R : Type*} [CommRing R]
    (a b : R) :
    quotientUnitMask (a * b) =
      quotientUnitMask a * quotientUnitMask b := by
  classical
  by_cases ha : IsUnit a <;> by_cases hb : IsUnit b <;>
    simp [quotientUnitMask, (Commute.all a b).isUnit_mul_iff, ha, hb]

def oldFactorRing {R : Type*} [CommRing R]
    (side parityBit ε₁ ε₂ : Bool) (z : R) (χ : MulChar R ℂ) : ℂ :=
  let q := χ z
  quotientUnitMask z * q ^ (4 * bit (if side then ε₂ else ε₁)) *
    q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
    q ^ EExp parityBit ε₁ ε₂

def newFactorRing {R : Type*} [CommRing R]
    (parityBit ε₁ ε₂ : Bool) (z : R) (χ : MulChar R ℂ) : ℂ :=
  if retained parityBit ε₁ ε₂ then (χ z) ^ 4 else quotientUnitMask z

theorem first_local_identity_ring {R : Type*} [CommRing R]
    (side parityBit ε₁ ε₂ : Bool)
    (z : R) (χ : MulChar R ℂ) (hχ : χ ^ 6 = 1) :
    oldFactorRing side parityBit ε₁ ε₂ z χ =
      newFactorRing parityBit ε₁ ε₂ z χ := by
  let q := χ z
  by_cases hu : IsUnit z
  · have h6 : q ^ 6 = 1 := by
      dsimp [q]
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
      simp [MulChar.one_apply, hu]
    have hmask : quotientUnitMask z = 1 := by
      simp [quotientUnitMask, hu]
    change quotientUnitMask z * q ^ (4 * bit (if side then ε₂ else ε₁)) *
      q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
      q ^ EExp parityBit ε₁ ε₂ =
        (if retained parityBit ε₁ ε₂ then q ^ 4 else quotientUnitMask z)
    rw [hmask, one_mul, ← pow_add, ← pow_add]
    cases side
    · change q ^ (totalExp₁ parityBit ε₁ ε₂) =
        (if retained parityBit ε₁ ε₂ then q ^ 4 else 1)
      rw [pow_eq_pow_mod _ h6, (exponent_table parityBit ε₁ ε₂).1]
      split_ifs <;> simp
    · change q ^ (totalExp₂ parityBit ε₁ ε₂) =
        (if retained parityBit ε₁ ε₂ then q ^ 4 else 1)
      rw [pow_eq_pow_mod _ h6, (exponent_table parityBit ε₁ ε₂).2]
      split_ifs <;> simp
  · have hz : q = 0 := MulChar.map_nonunit χ hu
    simp [oldFactorRing, newFactorRing, quotientUnitMask, hu]

theorem first_prime_product_identity_ring
    {R : Type*} [CommRing R]
    (side : Bool) (P : Finset R)
    (parityBit ε₁ ε₂ : R → Bool)
    (χ : MulChar R ℂ) (hχ : χ ^ 6 = 1) :
    (∏ z ∈ P, oldFactorRing side (parityBit z) (ε₁ z) (ε₂ z) z χ) =
      (χ (∏ z ∈ P with retained (parityBit z) (ε₁ z) (ε₂ z), z)) ^ 4 *
      quotientUnitMask
        (∏ z ∈ P with ¬retained (parityBit z) (ε₁ z) (ε₂ z), z) := by
  classical
  calc
    (∏ z ∈ P, oldFactorRing side (parityBit z) (ε₁ z) (ε₂ z) z χ) =
      ∏ z ∈ P, newFactorRing (parityBit z) (ε₁ z) (ε₂ z) z χ := by
        apply Finset.prod_congr rfl
        intro z hz
        exact first_local_identity_ring side (parityBit z) (ε₁ z) (ε₂ z) z χ hχ
    _ = (∏ z ∈ P with retained (parityBit z) (ε₁ z) (ε₂ z),
          (χ z) ^ 4) *
        (∏ z ∈ P with ¬retained (parityBit z) (ε₁ z) (ε₂ z),
          quotientUnitMask z) := by
        simp only [newFactorRing]
        exact Finset.prod_ite _ _
    _ = _ := by
      have hchar (S : Finset R) :
          (∏ z ∈ S, (χ z) ^ 4) = (χ (∏ z ∈ S, z)) ^ 4 := by
        induction S using Finset.induction_on with
        | empty => simp
        | @insert z S hz ih => simp [hz, ih, map_mul, mul_pow]
      have hmask (S : Finset R) :
          (∏ z ∈ S, quotientUnitMask z) =
            quotientUnitMask (∏ z ∈ S, z) := by
        induction S using Finset.induction_on with
        | empty => simp [quotientUnitMask]
        | @insert z S hz ih =>
            simp [hz, ih, quotientUnitMask_mul]
      rw [hchar, hmask]

end PoissonFirstLocal

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase

noncomputable def quadraticGammaNegTraceLambda : ℂ := by
  let c : O := -traceLambda
  let hc : c ≠ 0 := neg_ne_zero.mpr traceLambda_ne_zero
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  exact (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)

theorem quadraticGammaNegTraceLambda_eq_neg_I :
    quadraticGammaNegTraceLambda = -Complex.I := by
  let c : O := -traceLambda
  let hc : c ≠ 0 := neg_ne_zero.mpr traceLambda_ne_zero
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  have hspan : Ideal.span {c} = Ideal.span {traceLambda} := by
    change Ideal.span {-traceLambda} = Ideal.span {traceLambda}
    rw [show -traceLambda = (-1 : O) * traceLambda by ring]
    exact Ideal.span_singleton_mul_left_unit isUnit_neg_one traceLambda
  have hcard : Fintype.card (O ⧸ Ideal.span {c}) = 3 := by
    have hcardNat : Nat.card (O ⧸ Ideal.span {c}) = 3 := by
      rw [hspan]
      exact traceLambda_quotient_card
    simpa only [Nat.card_eq_fintype_card] using hcardNat
  let e : ZMod 3 ≃+* (O ⧸ Ideal.span {c}) :=
    ZMod.ringEquivOfPrime _ Nat.prime_three hcard
  have hphase : ψ 1 = omega3⁻¹ := by
    change ShortDraftTrace.breveE
      (eisEmbedding 1 / (eisEmbedding c * eisLam)) = omega3⁻¹
    rw [map_one, show eisEmbedding c = -eisLam by
      simp only [c, map_neg, eisEmbedding_traceLambda]]
    have harg : (1 : ℂ) / (-eisLam * eisLam) =
        -((1 : ℂ) / (eisLam * eisLam)) := by ring
    rw [harg, ShortDraftTrace.breveE.map_neg_eq_inv,
      breveE_traceLambda_square]
  have hsum : (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) =
      1 + 2 * omega3⁻¹ := by
    have hreindex := (e.toEquiv.sum_comp (fun x : O ⧸ Ideal.span {c} => ψ (x ^ 2))).symm
    rw [hreindex]
    have hfin : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
    rw [hfin]
    rw [Finset.sum_insert (by decide : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3))),
      Finset.sum_insert (by decide : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3))),
      Finset.sum_singleton]
    have h2sq : (2 : ZMod 3) ^ 2 = 1 := by decide
    have he2 : e (2 : ZMod 3) ^ 2 = 1 := by
      rw [← map_pow, h2sq, map_one]
    change ψ (e (0 : ZMod 3) ^ 2) +
      (ψ (e (1 : ZMod 3) ^ 2) + ψ (e (2 : ZMod 3) ^ 2)) =
        1 + 2 * omega3⁻¹
    simp only [map_zero, map_one, zero_pow (by decide : 2 ≠ 0),
      one_pow, he2, map_zero_eq_one, hphase]
    ring
  have hωcube : omega3 ^ 3 = 1 := by
    linear_combination (omega3 - 1) * omega3_sq
  have hωinv : omega3⁻¹ = omega3 ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_succ'] using hωcube
  have hsumval : 1 + 2 * omega3⁻¹ = -eisLam := by
    rw [hωinv]
    dsimp [eisLam]
    linear_combination 2 * omega3_sq
  have hLam : eisLam = (Real.sqrt 3 : ℝ) * Complex.I := by
    unfold eisLam omega3
    ring
  have hnorm : ‖eisEmbedding c‖ = Real.sqrt 3 := by
    rw [show eisEmbedding c = -eisLam by
      simp only [c, map_neg, eisEmbedding_traceLambda], norm_neg, hLam,
      norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 (by norm_num))]
  unfold quadraticGammaNegTraceLambda
  change (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) /
      (‖eisEmbedding c‖ : ℂ) = -Complex.I
  rw [hsum, hsumval, hnorm, hLam]
  field_simp

end

noncomputable def finiteSquarefreeRow
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (u : O) : ℂ :=
  ∏ i ∈ S, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) u)

theorem finiteSquarefreeRow_sixth_power
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    finiteSquarefreeRow P hgood S (a ^ 6) =
      if ∃ i ∈ S, a ∈ P i then 0 else 1 := by
  classical
  simp only [finiteSquarefreeRow]
  by_cases hex : ∃ i ∈ S, a ∈ P i
  · obtain ⟨i, hi, hai⟩ := hex
    rw [if_pos ⟨i, hi, hai⟩]
    apply Finset.prod_eq_zero hi
    rw [canonicalSextic_sixth_power_mask]
    simp [hai]
  · rw [if_neg hex]
    apply Finset.prod_eq_one
    intro i hi
    rw [canonicalSextic_sixth_power_mask]
    simp [show a ∉ P i by intro hai; exact hex ⟨i, hi, hai⟩]

theorem finiteSquarefreeRow_difference
    {ι N : Type*} [DecidableEq N]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset N) (support : N → Finset ι)
    (weight : N → ℂ) (a : O) :
    (∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (a ^ 6)) =
      ∑ n ∈ columns.filter (fun n => ∃ i ∈ support n, a ∈ P i), weight n := by
  classical
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [finiteSquarefreeRow_sixth_power]
  by_cases h : ∃ i ∈ support n, a ∈ P i <;> simp [h]

theorem finiteSquarefreeRow_difference_norm
    {ι N : Type*} [DecidableEq N]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset N) (support : N → Finset ι)
    (weight : N → ℂ) (a : O) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (a ^ 6))‖ ≤
      ∑ n ∈ columns.filter (fun n => ∃ i ∈ support n, a ∈ P i), ‖weight n‖ := by
  rw [finiteSquarefreeRow_difference]
  exact norm_sum_le _ _

theorem first_local_identity_canonicalSextic
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (side parityBit ε₁ ε₂ : Bool) (z : O ⧸ P) :
    PoissonFirstLocal.oldFactorRing side parityBit ε₁ ε₂ z
        (canonicalSextic P hgood) =
      PoissonFirstLocal.newFactorRing parityBit ε₁ ε₂ z
        (canonicalSextic P hgood) := by
  exact PoissonFirstLocal.first_local_identity_ring
    side parityBit ε₁ ε₂ z (canonicalSextic P hgood)
    (canonicalSextic_pow_six P hgood)

theorem first_prime_product_canonicalSextic
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (S : Finset (O ⧸ P))
    (parityBit ε₁ ε₂ : O ⧸ P → Bool) (side : Bool) :
    (∏ z ∈ S,
      PoissonFirstLocal.oldFactorRing side
        (parityBit z) (ε₁ z) (ε₂ z) z
        (canonicalSextic P hgood)) =
      (canonicalSextic P hgood
        (∏ z ∈ S with
          PoissonFirstLocal.retained (parityBit z) (ε₁ z) (ε₂ z), z)) ^ 4 *
      PoissonFirstLocal.quotientUnitMask
        (∏ z ∈ S with
          ¬PoissonFirstLocal.retained (parityBit z) (ε₁ z) (ε₂ z), z) := by
  exact PoissonFirstLocal.first_prime_product_identity_ring side S
    parityBit ε₁ ε₂ (canonicalSextic P hgood)
    (canonicalSextic_pow_six P hgood)

end ActualEisensteinCubic

namespace AnalyticBridge

theorem first_poisson_y_ball_of_scale_identity
    (L B F K A1 A2 C d c E s J2 J h y Y : ℝ)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hK : 0 < K) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hC : 0 < C) (hd : 0 ≤ d) (hc : 0 ≤ c)
    (hE : 0 ≤ E) (hs : 0 ≤ s) (hJ2 : 1 ≤ J2)
    (hJ : J = s * J2) (hJpos : 0 < J)
    (hJdyad : J ≤ B ^ 2) (hh : 0 ≤ h)
    (hscale : c * E * J2 ^ 2 = A1 * A2 * s)
    (hfrequency : h ≤ L ^ 2 * c * d / (K * A1 * A2 * C ^ 2))
    (hy : y ≤ h * F ^ 2 * E)
    (hY : Y = L ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J)) :
    y ≤ Y := by
  have hdenA : A1 * A2 ≠ 0 := (mul_pos hA1 hA2).ne'
  have hdenJ2 : J2 ^ 2 ≠ 0 := by positivity
  have hratioeq : c * E / (A1 * A2) = s / J2 ^ 2 := by
    apply (div_eq_div_iff hdenA hdenJ2).mpr
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hscale
  have hratio := first_poisson_local_ratio_bound c E A1 A2 s J2 J B
    hc hE hA1 hA2 hs hJ2 hB hJ hJpos hJdyad hratioeq
  exact first_poisson_y_ball L B F K A1 A2 C d c E J h y Y
    hL hB hF hK hA1 hA2 hC hd hc hE hJpos hh
    hfrequency hy hratio hY

end AnalyticBridge

namespace ShortDraftCusp

variable {R : Type*} [CommRing R]

private def cuspMatrix (a b c d : R) : Matrix (Fin 2) (Fin 2) R := !![a,b;c,d]
private def unramifiedH (u : R) : Matrix (Fin 2) (Fin 2) R := U u * E
private def unramifiedHInv (u : R) : Matrix (Fin 2) (Fin 2) R := !![0,1;-1,u]

theorem A3_principal_matrix (a b c d : R) :
    cuspMatrix a b c d * (1 : Matrix (Fin 2) (Fin 2) R) =
      !![a,b;c,d] := by
  simp [cuspMatrix]

theorem A3_ramified_inverse (u : R) :
    L u * L (-u) = (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [lower_add]
  simp [L, Matrix.one_fin_two]

theorem A3_ramified_inverse_left (u : R) :
    L (-u) * L u = (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [lower_add]
  simp [L, Matrix.one_fin_two]

theorem A3_ramified_matrix (a b c d u : R) :
    cuspMatrix a b c d * L (-u) =
      !![a - u * b,b;c - u * d,d] := by
  simp [cuspMatrix, L, mul_comm, sub_eq_add_neg]

theorem A3_unramified_H (u : R) :
    unramifiedH u = !![u,-1;1,0] := by
  simp [unramifiedH, U, E]

theorem A3_unramified_inverse_right (u : R) :
    unramifiedH u * unramifiedHInv u =
      (1 : Matrix (Fin 2) (Fin 2) R) := by
  simp [unramifiedH, unramifiedHInv, U, E, Matrix.one_fin_two]

theorem A3_unramified_inverse_left (u : R) :
    unramifiedHInv u * unramifiedH u =
      (1 : Matrix (Fin 2) (Fin 2) R) := by
  simp [unramifiedH, unramifiedHInv, U, E, Matrix.one_fin_two]

theorem A3_unramified_matrix (a b c d u : R) :
    cuspMatrix a b c d * unramifiedHInv u =
      !![-b,a + u * b;-d,c + u * d] := by
  simp [cuspMatrix, unramifiedHInv, mul_comm]

theorem A3_ramified_det_relation (a b c d u : R)
    (hdet : a * d - b * c = 1) :
    a * (c - u * d) - c * (a - u * b) = -u := by
  calc
    a * (c - u * d) - c * (a - u * b) =
        -u * (a * d - b * c) := by ring
    _ = -u := by rw [hdet]; ring

theorem A3_ramified_reciprocity_congr (a b cprime d u : R)
    (hdet : a * d - b * (u * cprime) = 1) :
    (a - u * b) * cprime = 1 + a * (cprime - d) := by
  calc
    (a - u * b) * cprime =
        a * cprime + (a * d - b * (u * cprime)) - a * d := by ring
    _ = 1 + a * (cprime - d) := by rw [hdet]; ring

theorem A3_unramified_det_relation (a b c d : R)
    (hdet : a * d - b * c = 1) :
    (-b) * c = 1 - a * d := by linear_combination hdet

theorem A3_unramified_inverse_congr (a b c d : R)
    (hdet : a * d - b * c = 1) :
    a * d = 1 + b * c := by linear_combination hdet

end ShortDraftCusp

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem breveE_quarter_trace (a b : ℤ) :
    ShortDraftTrace.breveE
      ((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) =
      Complex.I ^ b := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj a b
  have hconj : ∀ z : ℂ, star (z / 4) = star z / 4 := by
    intro z
    simp
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) +
      star (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4)))) = _
  rw [hconj]
  have hL : ((a : ℂ) + (b : ℂ) * omega3) / eisLam +
      star (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = (b : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  have harg : 2 * Real.pi * Complex.I *
      (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) +
        (star (((a : ℂ) + (b : ℂ) * omega3) / eisLam)) / 4) =
      (b : ℂ) * (Real.pi / 2 * Complex.I) := by
    rw [← add_div, hL]
    ring
  rw [harg, Complex.exp_int_mul, Complex.exp_pi_div_two_mul_I]

noncomputable def breveGaussianFourTerms (a b : ℤ) : ℂ :=
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  (ShortDraftTrace.breveE (0 : ℂ) +
      ShortDraftTrace.breveE (((-c) / eisLam) / 4) +
      ShortDraftTrace.breveE (((-c * omega3 ^ 2) / eisLam) / 4) +
      ShortDraftTrace.breveE (((-c * (1 + omega3) ^ 2) / eisLam) / 4)) / 2

theorem breveGaussianFourTerms_formula (a b : ℤ) :
    breveGaussianFourTerms a b =
      (1 + Complex.I ^ (-b) + Complex.I ^ a + Complex.I ^ (b-a)) / 2 := by
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  have hfirst : ShortDraftTrace.breveE (((-c) / eisLam) / 4) =
      Complex.I ^ (-b) := by
    have hc : -c = ((-a : ℤ) : ℂ) + ((-b : ℤ) : ℂ) * omega3 := by
      dsimp [c]
      push_cast
      ring
    rw [hc]
    exact breveE_quarter_trace (-a) (-b)
  have hsecond : ShortDraftTrace.breveE
      (((-c * omega3 ^ 2) / eisLam) / 4) = Complex.I ^ a := by
    have hc : -c * omega3 ^ 2 = ((a-b : ℤ) : ℂ) + (a : ℂ) * omega3 := by
      dsimp [c]
      push_cast
      linear_combination -(a : ℂ) * omega3_sq -
        (b : ℂ) * (omega3 - 1) * omega3_sq
    rw [hc]
    exact breveE_quarter_trace (a-b) a
  have hthird : ShortDraftTrace.breveE
      (((-c * (1 + omega3) ^ 2) / eisLam) / 4) =
      Complex.I ^ (b-a) := by
    have hω : (1 + omega3) ^ 2 = omega3 := by
      linear_combination omega3_sq
    have hc : -c * (1 + omega3) ^ 2 =
        (b : ℂ) + ((b-a : ℤ) : ℂ) * omega3 := by
      rw [hω]
      dsimp [c]
      push_cast
      linear_combination -(b : ℂ) * omega3_sq
    rw [hc]
    exact breveE_quarter_trace b (b-a)
  dsimp [breveGaussianFourTerms]
  rw [hfirst, hsecond, hthird]
  simp only [map_zero_eq_one]

end ActualEisensteinCubic

end

end OAI

end


