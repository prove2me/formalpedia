-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0010
-- name    : PNT_ZeroFree_433_0010
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:07:32.068781+00:00
-- url     : https://prove2.me/theorems/5a98a46e-1f34-4a21-bef3-d1a3eede9ef7
-- title:
--   Zero-free region foundations: GaussSum.CubicNormalization [0010]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.CubicNormalization
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L24-L622

import Definitions.Def_PNT_ZeroFree_433_0009

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L24-L622
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.CubicNormalization
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

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

theorem cubicGauss_normalized_cube_breveE
    (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) (hprimary : lambda ^ 2 ∣ p - 1) :
    (gaussSum ((cubicChar P hgood).ringHomComp eisEmbedding)
      (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)) ^ 3 =
      -(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ) := by
  subst P
  exact cubicGauss_normalized_cube_eis (Ideal.span {p}) hgood p rfl hprimary
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp)
    (eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp)

end

open EisensteinEmbedding ConcreteTraceCRT

noncomputable def breveGamma2 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood ^ 2)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

theorem canonicalSextic_pow_two (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    canonicalSextic P hgood ^ 2 =
      (cubicChar P hgood).ringHomComp eisEmbedding := by
  change ((sexticChar P hgood).ringHomComp eisEmbedding) ^ 2 = _
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).1]

theorem breveGamma2_cube (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) (hprimary : lambda ^ 2 ∣ p - 1) :
    (breveGamma2 P hgood p hP hp) ^ 3 =
      -(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ) := by
  unfold breveGamma2
  rw [canonicalSextic_pow_two]
  exact cubicGauss_normalized_cube_breveE P hgood p hP hp hprimary

end ActualEisensteinCubic

namespace ShortDraftLocal

open AddChar MulChar

theorem general_inversion_gauss {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (a : F) :
    (∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum (χ ^ (j + 2)) (ψ.mulShift a) := by
  classical
  calc
    (∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) (y⁻¹)) *
          ψ (a * (y : F)) := by
            apply Fintype.sum_equiv (Equiv.inv Fˣ)
            intro y
            simp
    _ = ∑ y : Fˣ, (χ ^ (j + 2)) y * ψ (a * (y : F)) := by
      congr 1
      funext y
      congr 1
      have hchar : (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2)⁻¹) = χ ^ (j + 2) := by group
      rw [← hchar, MulChar.inv_apply']
    _ = gaussSum (χ ^ (j + 2)) (ψ.mulShift a) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]

theorem sextic_fourier_theta_row_general
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ)
    (hχj : χ ^ j ≠ 1) (hχj2 : χ ^ (j + 2) ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ * gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        (∑ h : Fˣ,
          (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
            ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient (χ ^ j) ψ hχj h, map_mul]
    simp only [MulChar.mul_apply]
    ring
  rw [hsum, general_inversion_gauss χ ψ j (ε * x),
    gaussSum_mulShift_any (χ ^ (j + 2)) ψ hχj2 (ε * x), map_mul]
  ring

end ShortDraftLocal

namespace ActualEisensteinCubic

section

open AddChar MulChar

theorem canonical_A5_nonexceptional (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (j : ℕ)
    (hj0 : j ≠ 0) (hj6 : j < 6) (hj4 : j ≠ 4)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      ((χ⁻¹) ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχj : χ ^ j ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar hj0 hj6
  have hχj2 : χ ^ (j + 2) ≠ 1 := by
    have hcases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (3:ℕ) ≠ 0) (by decide : (3:ℕ) < 6)
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (4:ℕ) ≠ 0) (by decide : (4:ℕ) < 6)
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (5:ℕ) ≠ 0) (by decide : (5:ℕ) < 6)
    · have hχ1 : χ ≠ 1 := by
        simpa only [pow_one, χ] using canonicalSextic_pow_ne_one P hgood hchar
          (by decide : (1:ℕ) ≠ 0) (by decide : (1:ℕ) < 6)
      have hχ7 : χ ^ (5 + 2) = χ := by
        calc
          χ ^ (5 + 2) = χ ^ (6 + 1) := by congr 1
          _ = χ ^ 6 * χ := by rw [pow_add, pow_one]
          _ = χ := by rw [canonicalSextic_pow_six P hgood, one_mul]
      rw [hχ7]
      exact hχ1
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.sextic_fourier_theta_row_general χ ψ j hχj hχj2 σ ε x

end

open ConcreteTraceCRT PrimitiveTrace

theorem canonical_A5_jone_breveE (p : O) (hp : p ≠ 0)
    [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (σ : (O ⧸ Ideal.span {p})ˣ) (ε x : O ⧸ Ideal.span {p}) :
    let P := Ideal.span {p}
    let χ := canonicalSextic P hgood
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      ((χ⁻¹) ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum (χ ^ 3) ψ * (χ ^ 3) ε) *
      (χ ^ 3) x := by
  exact canonical_A5_jone (Ideal.span {p}) hgood hchar
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) σ ε x

theorem canonical_A5_jfour_breveE (p : O) (hp : p ≠ 0)
    [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (σ : (O ⧸ Ideal.span {p})ˣ) (ε x : O ⧸ Ideal.span {p}) :
    let P := Ideal.span {p}
    let χ := canonicalSextic P hgood
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 4) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1)) := by
  exact canonical_A5_jfour (Ideal.span {p}) hgood hchar
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp)
    (eisTraceModChar_breveE_ne_one (Ideal.span {p}) p rfl hp) σ ε x

theorem canonical_A5_jzero_active_breveE (p : O) (hp : p ≠ 0)
    [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (σ : (O ⧸ Ideal.span {p})ˣ) (ε x : O ⧸ Ideal.span {p}) :
    let P := Ideal.span {p}
    let χ := canonicalSextic P hgood
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        ((χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x)) := by
  exact canonical_A5_jzero_active (Ideal.span {p}) hgood hchar
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp)
    (eisTraceModChar_breveE_ne_one (Ideal.span {p}) p rfl hp) σ ε x

end ActualEisensteinCubic

namespace AnalyticBridge

theorem first_poisson_local_ratio_bound
    (c E A1 A2 s J2 J B : ℝ)
    (_hc : 0 ≤ c) (_hE : 0 ≤ E)
    (_hA1 : 0 < A1) (_hA2 : 0 < A2)
    (hs : 0 ≤ s) (hJ2 : 1 ≤ J2) (_hB : 0 ≤ B)
    (hJ : J = s * J2) (hJpos : 0 < J)
    (hJdyad : J ≤ B ^ 2)
    (hlocal : c * E / (A1 * A2) = s / J2 ^ 2) :
    c * E / (A1 * A2) ≤ B ^ 4 / J := by
  have hJ2sq : 1 ≤ J2 ^ 2 := by nlinarith
  have hsJ : s ≤ J := by rw [hJ]; nlinarith
  have hratio : s / J2 ^ 2 ≤ s :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hJself : J ≤ B ^ 4 / J :=
    (le_div_iff₀ hJpos).mpr (by nlinarith [sq_nonneg (B ^ 2 - J)])
  rw [hlocal]
  exact hratio.trans (hsJ.trans hJself)

theorem first_poisson_y_ball
    (L B F K A1 A2 C d c E J h y Y : ℝ)
    (_hL : 0 ≤ L) (_hB : 0 ≤ B) (_hF : 0 ≤ F)
    (hK : 0 < K) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hC : 0 < C) (hd : 0 ≤ d) (_hc : 0 ≤ c)
    (hE : 0 ≤ E) (hJ : 0 < J) (_hh : 0 ≤ h)
    (hfrequency : h ≤ L ^ 2 * c * d / (K * A1 * A2 * C ^ 2))
    (hy : y ≤ h * F ^ 2 * E)
    (hratio : c * E / (A1 * A2) ≤ B ^ 4 / J)
    (hY : Y = L ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J)) :
    y ≤ Y := by
  have hfactor : 0 ≤ F ^ 2 * E := by positivity
  calc
    y ≤ h * F ^ 2 * E := hy
    _ ≤ (L ^ 2 * c * d / (K * A1 * A2 * C ^ 2)) * F ^ 2 * E :=
      by convert! mul_le_mul_of_nonneg_right hfrequency hfactor using 1 <;> ring
    _ = (L ^ 2 * d * F ^ 2 / (K * C ^ 2)) * (c * E / (A1 * A2)) := by
      field_simp
    _ ≤ (L ^ 2 * d * F ^ 2 / (K * C ^ 2)) * (B ^ 4 / J) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = Y := by rw [hY]; field_simp

theorem restrict_positive_side_to_weight_support
    {Ω : Type*} (S : Finset Ω) (w : Ω → ℂ) (U : Ω → ℂ) :
    (∑ ω ∈ S with w ω ≠ 0, ‖w ω‖ * ‖U ω‖ ^ 2) =
      (∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ ^ 2) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hw : w ω = 0 <;> simp [hw]

theorem weighted_cauchy_ball_enlargement
    {Ω Λ : Type*} [DecidableEq Λ]
    (S : Finset Ω) (T : Finset Λ) (label : Ω → Λ)
    (w : Ω → ℂ) (A B : Λ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁)
    (hsupport : ∀ ω ∈ S, w ω ≠ 0 → label ω ∈ T)
    (hfiber : ∀ a ∈ T,
      (∑ ω ∈ S with label ω = a, ‖w ω‖) ≤ M₁)
    (hfiber₂ : ∀ a ∈ T,
      (∑ ω ∈ S with label ω = a, ‖w ω‖) ≤ M₂) :
    ‖∑ ω ∈ S, w ω * A (label ω) * star (B (label ω))‖ ^ 2 ≤
      (M₁ * ∑ a ∈ T, ‖A a‖ ^ 2) *
        (M₂ * ∑ a ∈ T, ‖B a‖ ^ 2) := by
  classical
  let S' : Finset Ω := S.filter (fun ω => w ω ≠ 0)
  have hmap : ∀ ω ∈ S', label ω ∈ T := by
    intro ω hω
    exact hsupport ω (Finset.mem_filter.mp hω).1 (Finset.mem_filter.mp hω).2
  have hsum :
      (∑ ω ∈ S', w ω * A (label ω) * star (B (label ω))) =
      (∑ ω ∈ S, w ω * A (label ω) * star (B (label ω))) := by
    dsimp [S']
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases hw : w ω = 0 <;> simp [hw]
  have hfiber' : ∀ a ∈ T,
      (∑ ω ∈ S' with label ω = a, ‖w ω‖) ≤ M₁ := by
    intro a ha
    have heq : (∑ ω ∈ S' with label ω = a, ‖w ω‖) =
        (∑ ω ∈ S with label ω = a, ‖w ω‖) := by
      dsimp [S']
      simp only [Finset.filter_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hl : label ω = a <;> by_cases hw : w ω = 0 <;> simp [hl, hw]
    rw [heq]
    exact hfiber a ha
  have hfiber₂' : ∀ a ∈ T,
      (∑ ω ∈ S' with label ω = a, ‖w ω‖) ≤ M₂ := by
    intro a ha
    have heq : (∑ ω ∈ S' with label ω = a, ‖w ω‖) =
        (∑ ω ∈ S with label ω = a, ‖w ω‖) := by
      dsimp [S']
      simp only [Finset.filter_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hl : label ω = a <;> by_cases hw : w ω = 0 <;> simp [hl, hw]
    rw [heq]
    exact hfiber₂ a ha
  rw [← hsum]
  exact reassembled_bilinear_bound S' T T label label w A B M₁ M₂
    hM₁ hmap hmap hfiber' hfiber₂'

theorem weighted_fourier_minkowski
    {Ω : Type*} (S : Finset Ω)
    (b : ℝ → ℂ) (φ : Ω → ℝ → ℂ) (J : ℕ) (H : ℝ)
    (_hH : 0 ≤ H)
    (hint : ∀ ω ∈ S,
      Integrable (fun t : ℝ => b t * φ ω t) volume)
    (hweight : Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume)
    (hφ : ∀ t : ℝ,
      ‖∑ ω ∈ S, φ ω t‖ ≤ H * (1 + ‖t‖) ^ J) :
    ‖∑ ω ∈ S, ∫ t : ℝ, b t * φ ω t‖ ≤
      H * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖ := by
  have hR : Integrable
      (fun t : ℝ => H * ((1 + ‖t‖) ^ J * ‖b t‖)) volume :=
    hweight.const_mul H
  calc
    ‖∑ ω ∈ S, ∫ t : ℝ, b t * φ ω t‖ =
        ‖∫ t : ℝ, ∑ ω ∈ S, b t * φ ω t‖ := by
      rw [integral_finsetSum S hint]
    _ ≤ ∫ t : ℝ, ‖∑ ω ∈ S, b t * φ ω t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, H * ((1 + ‖t‖) ^ J * ‖b t‖) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (by intro t; positivity))
        hR
      filter_upwards [] with t
      rw [← Finset.mul_sum, norm_mul]
      calc
        ‖b t‖ * ‖∑ ω ∈ S, φ ω t‖ ≤
            ‖b t‖ * (H * (1 + ‖t‖) ^ J) :=
          mul_le_mul_of_nonneg_left (hφ t) (norm_nonneg _)
        _ = H * ((1 + ‖t‖) ^ J * ‖b t‖) := by ring
    _ = H * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖ := by
      rw [integral_const_mul]

theorem weighted_fourier_minkowski_with_decay
    {Ω : Type*} (S : Finset Ω)
    (b : ℝ → ℂ) (φ : Ω → ℝ → ℂ)
    (A J : ℕ) (R H C : ℝ)
    (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hint : ∀ ω ∈ S,
      Integrable (fun t : ℝ => b t * φ ω t) volume)
    (hweight : Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume)
    (hφ : ∀ t : ℝ,
      ‖∑ ω ∈ S, φ ω t‖ ≤ H * (1 + ‖t‖) ^ J)
    (hcoeff : (1 + R) ^ A *
      (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C) :
    (1 + R) ^ A *
      ‖∑ ω ∈ S, ∫ t : ℝ, b t * φ ω t‖ ≤ H * C := by
  have hM := weighted_fourier_minkowski S b φ J H hH hint hweight hφ
  calc
    (1 + R) ^ A *
      ‖∑ ω ∈ S, ∫ t : ℝ, b t * φ ω t‖ ≤
        (1 + R) ^ A *
          (H * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ = H * ((1 + R) ^ A *
      ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) := by ring
    _ ≤ H * C := mul_le_mul_of_nonneg_left hcoeff hH

theorem schwartz_fourier_one_plus_integrable
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ =>
      (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) volume := by
  let b := 𝓕 g
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa [b] using b.integrable_pow_mul volume 0
  have hIJ : Integrable
      (fun t : ℝ => ‖t‖ ^ J * ‖b t‖) volume :=
    b.integrable_pow_mul volume J
  have hR : Integrable
      (fun t : ℝ => (2 : ℝ) ^ J *
        (‖b t‖ + ‖t‖ ^ J * ‖b t‖)) volume :=
    (hI0.add hIJ).const_mul _
  have hpoint (t : ℝ) :
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
        (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
    have hp := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num)
      (norm_nonneg t) J
    have htwo : (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
    calc
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
          (2 : ℝ) ^ (J - 1) * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ J * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ := by
        gcongr
      _ = (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
        simp; ring
  have hcont : Continuous
      (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
    fun_prop
  exact hR.mono_nonneg hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (by intro t; positivity))
    (Filter.Eventually.of_forall hpoint)

end AnalyticBridge

namespace JacobiQuadratic

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private def affineDouble (hchar : ringChar F ≠ 2) : F ≃ F where
  toFun x := 2 * x - 1
  invFun t := (t + 1) / 2
  left_inv := by
    intro x
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    field_simp
    ring
  right_inv := by
    intro t
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    field_simp
    ring

private def oneSub : F ≃ F where
  toFun y := 1 - y
  invFun y := 1 - y
  left_inv := by intro y; ring
  right_inv := by intro y; ring

private theorem square_fiber (χ : MulChar F ℂ)
    (hchar : ringChar F ≠ 2) :
    (∑ t : F, χ (1 - t ^ 2)) =
      ∑ y : F, ((quadraticChar F y : ℂ) + 1) * χ (1 - y) := by
  classical
  have hfiber : (∑ t : F, χ (1 - t ^ 2)) =
      ∑ y : F, (#{t : F | t ^ 2 = y}.toFinset : ℂ) * χ (1 - y) := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun t : F => t ^ 2) (f := fun t : F => χ (1 - t ^ 2))]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_congr rfl (fun t ht => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [ht])]
    simp
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact_mod_cast quadraticChar_card_sqrts hchar y

theorem jacobi_quadratic (χ : MulChar F ℂ)
    (hchar : ringChar F ≠ 2) (hχ : χ ≠ 1) :
    jacobiSum χ ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) =
      χ (4 : F) * jacobiSum χ χ := by
  classical
  let q : MulChar F ℂ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
  have hsum0 : (∑ y : F, χ (1 - y)) = 0 := by
    have ht := (Equiv.sum_comp (oneSub (F := F)) χ)
    change (∑ y : F, χ ((oneSub (F := F)) y)) = 0
    exact ht.trans (MulChar.sum_eq_zero_of_ne_one hχ)
  have hfiber := square_fiber χ hchar
  have hsq : (∑ t : F, χ (1 - t ^ 2)) = jacobiSum χ q := by
    rw [hfiber]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    simp only [one_mul, hsum0, add_zero]
    exact jacobiSum_comm q χ
  have hchange : (∑ t : F, χ (1 - t ^ 2)) =
      ∑ x : F, χ (4 * x * (1 - x)) := by
    have ht := Equiv.sum_comp (affineDouble (F := F) hchar)
      (fun t : F => χ (1 - t ^ 2))
    convert! ht.symm using 1
    · apply Finset.sum_congr rfl
      intro x _
      congr 1
      change 4 * x * (1 - x) = 1 - (2 * x - 1) ^ 2
      ring
  calc
    jacobiSum χ q = ∑ x : F, χ (4 * x * (1 - x)) := hsq.symm.trans hchange
    _ = χ (4 : F) * jacobiSum χ χ := by
      rw [jacobiSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [ map_mul]
      ring

theorem gauss_sextic_relation (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ.IsPrimitive)
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) (hχ4 : χ ^ 4 ≠ 1)
    (hχ3 : χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ))
    (hχ6 : χ ^ 6 = 1) :
    χ (4 : F) * gaussSum χ ψ * (Fintype.card F : ℂ) =
      gaussSum (χ ^ 3) ψ * gaussSum (χ ^ 2) ψ ^ 2 := by

  let g1 := gaussSum χ ψ
  let g2 := gaussSum (χ ^ 2) ψ
  let g3 := gaussSum (χ ^ 3) ψ
  let g4 := gaussSum (χ ^ 4) ψ
  let J11 := jacobiSum χ χ
  let J13 := jacobiSum χ (χ ^ 3)
  have hprod2 : χ * χ = χ ^ 2 := (pow_two χ).symm
  have hprod4 : χ * χ ^ 3 = χ ^ 4 := by group
  have hJ12 : g2 * J11 = g1 * g1 := by
    have h := jacobiSum_mul_nontrivial (by rw [hprod2]; exact hχ2) ψ
      (χ := χ) (φ := χ)
    rw [hprod2] at h
    exact h
  have hJ13 : g4 * J13 = g1 * g3 := by
    have h := jacobiSum_mul_nontrivial (by rw [hprod4]; exact hχ4) ψ
      (χ := χ) (φ := χ ^ 3)
    rw [hprod4] at h
    exact h
  have hJquad : J13 = χ (4 : F) * J11 := by
    simpa only [J13, J11, hχ3] using jacobi_quadratic χ hchar hχ1
  have hg1ne : g1 ≠ 0 := by
    apply gaussSum_ne_zero_of_nontrivial
    · exact_mod_cast Fintype.card_pos.ne'
    · exact hχ1
    · exact hψ
  have h4inv : χ ^ 4 = (χ ^ 2)⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    calc
      χ ^ 2 * χ ^ 4 = χ ^ 6 := by group
      _ = 1 := hχ6
  have h4minus : (χ ^ 4) (-1 : F) = 1 := by
    rw [χ.pow_apply' (by decide : (4 : ℕ) ≠ 0), ← map_pow,
      show (-1 : F) ^ 4 = 1 by ring, map_one]
  have hG4inv : gaussSum (χ ^ 4) ψ⁻¹ = g4 := by
    have h := mul_gaussSum_inv_eq_gaussSum (χ ^ 4) ψ
    rw [h4minus, one_mul] at h
    exact h
  have hG24 : g2 * g4 = (Fintype.card F : ℂ) := by
    have h := gaussSum_mul_gaussSum_eq_card hχ2 hψ
    rw [← h4inv, hG4inv] at h
    exact h
  have hbasic : g1 * g3 * g2 = χ (4 : F) * g4 * g1 ^ 2 := by
    calc
      g1 * g3 * g2 = (g4 * J13) * g2 := by rw [hJ13]
      _ = χ (4 : F) * g4 * (g2 * J11) := by rw [hJquad]; ring
      _ = χ (4 : F) * g4 * g1 ^ 2 := by rw [hJ12]; ring
  have hbasic' : g3 * g2 = χ (4 : F) * g4 * g1 := by
    apply mul_left_cancel₀ hg1ne
    calc
      g1 * (g3 * g2) = g1 * g3 * g2 := by ring
      _ = χ (4 : F) * g4 * g1 ^ 2 := hbasic
      _ = g1 * (χ (4 : F) * g4 * g1) := by ring
  calc
    χ (4 : F) * g1 * (Fintype.card F : ℂ) =
        χ (4 : F) * g1 * (g2 * g4) := by rw [hG24]
    _ = (χ (4 : F) * g4 * g1) * g2 := by ring
    _ = g3 * g2 ^ 2 := by rw [← hbasic']; ring

theorem normalized_gauss_sextic_relation (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ.IsPrimitive)
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) (hχ4 : χ ^ 4 ≠ 1)
    (hχ3 : χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ))
    (hχ6 : χ ^ 6 = 1)
    (s : ℂ) (hs : s ^ 2 = (Fintype.card F : ℂ)) (hs0 : s ≠ 0) :
    χ (4 : F) * (gaussSum χ ψ / s) * (gaussSum (χ ^ 2) ψ / s) =
      (gaussSum (χ ^ 3) ψ / s) * (gaussSum (χ ^ 2) ψ / s) ^ 3 := by
  have hraw := gauss_sextic_relation χ ψ hchar hψ hχ1 hχ2 hχ4 hχ3 hχ6
  rw [← hs] at hraw
  field_simp
  linear_combination (gaussSum (χ ^ 2) ψ) * hraw

end JacobiQuadratic

end

end OAI

end


