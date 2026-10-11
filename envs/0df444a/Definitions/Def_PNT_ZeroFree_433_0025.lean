-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0025
-- name    : PNT_ZeroFree_433_0025
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T13:31:18.246339+00:00
-- url     : https://prove2.me/theorems/a2ee7759-1dfe-4707-ae47-12448ad1a318
-- title:
--   Zero-free region foundations: Mellin.LocalNonvanishing [0025]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Mellin.LocalNonvanishing
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/LocalNonvanishing.lean#L31-L585

import Definitions.Def_PNT_ZeroFree_433_0024

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/LocalNonvanishing.lean#L31-L585
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Mellin.LocalNonvanishing
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

namespace TargetLocalReduction

def LocalExponentialMobiusBound : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
      ∃ σ : ℝ, 0 < σ ∧ σ < ρ.re ∧ σ < 1 ∧
        (fun D : ℝ => ShortDraftMellin.mobiusExpSum χ D⁻¹) =O[atTop]
          (fun D : ℝ => D ^ σ)

theorem dirichletTarget_of_localBound
    (hbound : LocalExponentialMobiusBound) : ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρ : ρ.re < 1
  · obtain ⟨σ, hσpos, hσρ, hσone, htop⟩ := hbound q χ ρ h23 hρ
    by_cases hχ : χ = 1
    · subst χ
      have hρone : ρ ≠ 1 := by
        intro h
        exact hprincipal ⟨rfl, h⟩
      exact ShortDraftMellin.principal_dirichlet_exp_zero_free_of_power_bound_only
        q σ hσpos hσone htop ρ hσρ hρone
    · exact ShortDraftMellin.dirichlet_exp_zero_free_of_power_bound_only
        χ hχ σ hσpos hσone htop ρ hσρ
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρ) hprincipal

end TargetLocalReduction

namespace ActualEisensteinCubic

open AddChar MulChar

theorem canonical_A5_jone_direct (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (χ ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) * χ x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hχ : canonicalSextic P hgood ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one P hgood hchar
        (j := 1) (by decide) (by decide))
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.direct_theta_jone_local_row
    (canonicalSextic P hgood) ψ hχ σ ε x

theorem canonical_A5_jone_direct_not_quadratic (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    canonicalSextic P hgood ≠ (canonicalSextic P hgood) ^ 3 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let hχ₂ : canonicalSextic P hgood ^ 2 ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar
      (j := 2) (by decide) (by decide)
  exact ShortDraftLocal.direct_theta_jone_not_quadratic
    (canonicalSextic P hgood) hχ₂

theorem canonical_A5_jone_direct_scalar_ne_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (ε : O ⧸ P) (hε : ε ≠ 0) :
    let χ := canonicalSextic P hgood
    ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
      gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) ≠ 0 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ P) ℂ := canonicalSextic P hgood
  have hχ : χ ≠ 1 := by
    simpa only [χ, pow_one] using
      (canonicalSextic_pow_ne_one P hgood hchar
        (j := 1) (by decide) (by decide))
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by group
      _ = 1 := by rw [h]; simp
  have hcard : (Fintype.card (O ⧸ P) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : O ⧸ P)⟩).ne'
  have hψshift : (ψ.mulShift (-1)).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one
      (hψ (neg_ne_zero.mpr (one_ne_zero : (1 : O ⧸ P) ≠ 0)))
  have hg1 : gaussSum χ (ψ.mulShift (-1)) ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcard hχ hψshift
  have hg2 : gaussSum χ⁻¹ ψ ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcard hχinv hψ
  have hχε : χ ε ≠ 0 := χ.apply_ne_zero_iff.mpr
    (isUnit_iff_ne_zero.mpr hε)
  dsimp only
  rw [Nat.card_eq_fintype_card]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero hcard) hg1) hg2) hχε

theorem canonical_A5_jone_trace_scalar_ne_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (ε : O ⧸ P) (hε : ε ≠ 0) :
    let χ := canonicalSextic P hgood
    let ψ : AddChar (O ⧸ P) ℂ := hP.symm ▸
      ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates p hp
    ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
      gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) ≠ 0 := by
  subst P
  exact canonical_A5_jone_direct_scalar_ne_zero (Ideal.span {p}) hgood hchar
    (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp)
    (PrimitiveTrace.eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp)
    ε hε

end ActualEisensteinCubic

open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter

namespace ShortDraftHeckeBridge

abbrev O := ActualEisensteinSieve.O

noncomputable def normFiberCoeff (weight : Ideal O → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset, weight I

noncomputable def pairInverseCoeff
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ℕ → ℂ :=
  (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) ⍟
    (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ))

theorem normFiber_LSeries_eq_pair_inverse
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (s : ℂ) :
    LSeries (normFiberCoeff weight) s = LSeries (pairInverseCoeff χ ψ) s := by
  exact LSeries_congr (fun {n} hn => hcoeff n hn) s

theorem pair_inverse_euler_identity
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (s : ℂ) (hs : 1 < s.re) :
    χ.LFunction s * ψ.LFunction s * LSeries (pairInverseCoeff χ ψ) s = 1 := by
  have hχsum : LSeriesSummable (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s := by
    exact DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hψsum : LSeriesSummable (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s := by
    exact DirichletCharacter.LSeriesSummable_mul ψ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  rw [pairInverseCoeff, LSeries_convolution' hχsum hψsum,
    χ.LFunction_eq_LSeries hs, ψ.LFunction_eq_LSeries hs]
  have hχ := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hψ := DirichletCharacter.LSeries.mul_mu_eq_one ψ hs
  change LSeries (χ ·) s * LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s = 1 at hχ
  change LSeries (ψ ·) s * LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s = 1 at hψ
  calc
    LSeries (χ ·) s * LSeries (ψ ·) s *
      (LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s *
        LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s) =
      (LSeries (χ ·) s * LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s) *
      (LSeries (ψ ·) s * LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s) := by ring
    _ = 1 := by rw [hχ, hψ]; ring

theorem pair_zero_free_of_normFiber_continuation
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (σ : ℝ) (hσ : σ < 1) (M : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hMseries : ∀ s : ℂ, 1 < s.re → M s = LSeries (normFiberCoeff weight) s)
    (ρ : ℂ) (hρ : σ < ρ.re) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hLχ : AnalyticOnNhd ℂ χ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (χ.differentiable_LFunction hχ).differentiableOn
  have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (ψ.differentiable_LFunction hψ).differentiableOn
  have hL : AnalyticOnNhd ℂ (fun s => χ.LFunction s * ψ.LFunction s) U :=
    hLχ.mul hLψ
  have hW : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) U := analyticOnNhd_const
  have heq : ∀ s : ℂ, 1 < s.re →
      (χ.LFunction s * ψ.LFunction s) * M s = 1 := by
    intro s hs
    rw [hMseries s hs, normFiber_LSeries_eq_pair_inverse χ ψ weight hcoeff s]
    exact pair_inverse_euler_identity χ ψ s hs
  have hprod : χ.LFunction ρ * ψ.LFunction ρ ≠ 0 :=
    ShortDraft.zero_free_of_analytic_identity σ hσ
      (fun s => χ.LFunction s * ψ.LFunction s) M (fun _ => (1 : ℂ))
      hL hM hW heq ρ hρ one_ne_zero
  exact mul_ne_zero_iff.mp hprod

theorem pair_zero_free_of_normFiber_continuation_principal_left
    {q r : ℕ} [NeZero q] [NeZero r]
    (ψ : DirichletCharacter ℂ r) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff (1 : DirichletCharacter ℂ q) ψ n)
    (σ : ℝ) (hσ : σ < 1) (M : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hMseries : ∀ s : ℂ, 1 < s.re → M s = LSeries (normFiberCoeff weight) s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ ≠ 0 ∧
      ψ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hLregular₁ : AnalyticOnNhd ℂ
      (DirichletCharacter.LFunctionTrivChar₁ q) U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn
  have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (ψ.differentiable_LFunction hψ).differentiableOn
  have hLregular : AnalyticOnNhd ℂ
      (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) U :=
    hLregular₁.mul hLψ
  have hW : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) U := analyticOnNhd_const
  have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s =
        (s - 1) *
          (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s *
            ψ.LFunction s) := by
    intro s _ hs
    simp [DirichletCharacter.LFunctionTrivChar₁,
      DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
    ring
  have heq : ∀ s : ℂ, 1 < s.re →
      (DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) * M s =
        (s - 1) * 1 := by
    intro s hs
    rw [hregular s (lt_trans hσ hs) (by
      intro h; subst s; norm_num at hs)]
    rw [hMseries s hs, normFiber_LSeries_eq_pair_inverse 1 ψ weight hcoeff s]
    calc
      (s - 1) * (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s *
          ψ.LFunction s) * LSeries (pairInverseCoeff 1 ψ) s =
        (s - 1) * (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s *
          ψ.LFunction s * LSeries (pairInverseCoeff 1 ψ) s) := by ring
      _ = (s - 1) * 1 := by rw [pair_inverse_euler_identity 1 ψ s hs]
  have hprod :
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ *
        ψ.LFunction ρ ≠ 0 :=
    ShortDraft.zero_free_of_regularized_analytic_identity σ hσ
      (fun s => DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s *
        ψ.LFunction s)
      (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s)
      M (fun _ => (1 : ℂ)) hLregular hM hW hregular heq ρ hρ hρone
      one_ne_zero
  exact mul_ne_zero_iff.mp hprod

theorem pairInverseCoeff_comm
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    pairInverseCoeff χ ψ = pairInverseCoeff ψ χ := by
  simp only [pairInverseCoeff, LSeries.convolution, mul_comm]

theorem pair_zero_free_of_normFiber_continuation_principal_right
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff χ (1 : DirichletCharacter ℂ r) n)
    (σ : ℝ) (hσ : σ < 1) (M : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hMseries : ∀ s : ℂ, 1 < s.re → M s = LSeries (normFiberCoeff weight) s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    χ.LFunction ρ ≠ 0 ∧
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ r) ρ ≠ 0 := by
  have hcoeff' : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff (1 : DirichletCharacter ℂ r) χ n := by
    intro n hn
    rw [hcoeff n hn, pairInverseCoeff_comm]
  have h := pair_zero_free_of_normFiber_continuation_principal_left
    (q := r) (r := q) χ hχ weight hcoeff' σ hσ M hM hMseries ρ hρ hρone
  exact ⟨h.2, h.1⟩

end ShortDraftHeckeBridge
private theorem pairing_algebra
    (g1 g2 gm G alpha eps t : ℂ)
    (halpha : alpha * star alpha = 1)
    (hg1 : g1 * star g1 = 1)
    (hprod : g1 * g2 = -alpha * G)
    (hpair : g1 * gm = eps) :
    (-star g1) * G * t = (star alpha * g2) * t ∧
    (-gm) * G * t = eps * (star alpha * g2) * t ∧
    (-g1) * star G * t⁻¹ = (alpha * star g2) * t⁻¹ ∧
    (-star gm) * star G * t⁻¹ = star eps * (alpha * star g2) * t⁻¹ := by
  have h2 : g2 = -(star g1) * alpha * G := by
    calc
      g2 = (g1 * star g1) * g2 := by rw [hg1]; ring
      _ = star g1 * (g1 * g2) := by ring
      _ = star g1 * (-alpha * G) := by rw [hprod]
      _ = _ := by ring
  have hA : star alpha * g2 = (-star g1) * G := by
    rw [h2]
    calc
      star alpha * (-(star g1) * alpha * G) =
          (alpha * star alpha) * ((-star g1) * G) := by ring
      _ = (-star g1) * G := by rw [halpha]; ring
  have hm : gm = eps * star g1 := by
    calc
      gm = (g1 * star g1) * gm := by rw [hg1]; ring
      _ = star g1 * (g1 * gm) := by ring
      _ = eps * star g1 := by rw [hpair]; ring
  have hB : (-gm) * G = eps * (star alpha * g2) := by
    rw [hm, hA]
    ring
  have hC : (-g1) * star G = alpha * star g2 := by
    have h := congrArg (fun z : ℂ => star z) hA
    simp only [star_mul, star_neg, star_star] at h
    calc
      (-g1) * star G = star G * (-g1) := by ring
      _ = star g2 * alpha := h.symm
      _ = alpha * star g2 := by ring
  have hD : (-star gm) * star G = star eps * (alpha * star g2) := by
    have h := congrArg (fun z : ℂ => star z) hB
    simpa only [star_mul, star_neg, star_star, mul_comm, mul_left_comm, mul_assoc] using h
  exact ⟨by rw [hA], by rw [hB], by rw [hC], by rw [hD]⟩

namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
open scoped ComplexConjugate

private theorem breveGamma1_mul_star_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * star (breveGamma1 P hgood p hP hp) = 1 := by
  subst P
  let χ := canonicalSextic (Ideal.span {p}) hgood
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates p hp
  let s : ℝ := ‖eisEmbedding p‖
  have hψ : ψ.IsPrimitive :=
    eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp
  have hχ1 : χ ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
        (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) < 6))
  have hnormO := primary_generator_mul_conj_eq_card
    (Ideal.span {p}) hgood p rfl hprimary
  have hnormC := congrArg eisEmbedding hnormO
  rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
  have hs : (s : ℂ) ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℂ) := by
    simpa only [s, ← starRingEnd_apply, Complex.mul_conj',
      Nat.card_eq_fintype_card] using hnormC
  have hsreal : s ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℝ) := by
    exact Complex.ofReal_injective (by exact_mod_cast hs)
  have hcard : 0 < (Fintype.card (O ⧸ Ideal.span {p}) : ℝ) := by positivity
  have hsroot : s = Real.sqrt (Fintype.card (O ⧸ Ideal.span {p})) := by
    nlinarith [Real.sq_sqrt hcard.le, Real.sqrt_nonneg
      (Fintype.card (O ⧸ Ideal.span {p})), norm_nonneg (eisEmbedding p)]
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  have hnorm : ‖breveGamma1 (Ideal.span {p}) hgood p rfl hp‖ = 1 := by
    change ‖gaussSum χ ψ / (s : ℂ)‖ = 1
    rw [norm_div, ShortDraftGauss.norm_gaussSum_eq_sqrt_card χ ψ hχ1 hψ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (eisEmbedding p))]
    rw [← hsroot]
    exact div_self hs0
  rw [← starRingEnd_apply, Complex.mul_conj', hnorm]
  norm_num

theorem first_poisson_prime_sign_pairing
    (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) :
    let alpha : ℂ := eisEmbedding p / (‖eisEmbedding p‖ : ℂ)
    let g1 := breveGamma1 P hgood p hP hp
    let g2 := breveGamma2 P hgood p hP hp
    let gm := breveGammaMinus1 P hgood p hP hp
    let G := breveLocalG P hgood p hP hp
    let t := canonicalSextic P hgood (Ideal.Quotient.mk P h)
    let eps := canonicalSextic P hgood (Ideal.Quotient.mk P (-1 : O))
    (-star g1) * G * t = (star alpha * g2) * t ∧
    (-gm) * G * t = eps * (star alpha * g2) * t ∧
    (-g1) * star G * t⁻¹ = (alpha * star g2) * t⁻¹ ∧
    (-star gm) * star G * t⁻¹ = star eps * (alpha * star g2) * t⁻¹ := by
  have hz : eisEmbedding p ≠ 0 := eisEmbedding_ne_zero hp
  have hs : (‖eisEmbedding p‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have hanorm : ‖eisEmbedding p / (‖eisEmbedding p‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (eisEmbedding p))]
    exact div_self (norm_ne_zero_iff.mpr hz)
  have ha : (eisEmbedding p / (‖eisEmbedding p‖ : ℂ)) *
      star (eisEmbedding p / (‖eisEmbedding p‖ : ℂ)) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', hanorm]
    norm_num
  have hg1 := breveGamma1_mul_star_one P hgood hchar p hP hp hprimary
  have hprod := breveGamma1_gamma2_eq_neg_alpha_G
    P hgood hchar p hP hp hprimary
  have hprod' :
      breveGamma1 P hgood p hP hp * breveGamma2 P hgood p hP hp =
        -(eisEmbedding p / (‖eisEmbedding p‖ : ℂ)) *
          breveLocalG P hgood p hP hp := by
    simpa only [neg_div] using hprod
  have hpair := breveGamma1_gammaMinus1
    P hgood hchar p hP hp hprimary
  dsimp only
  exact pairing_algebra
    (breveGamma1 P hgood p hP hp)
    (breveGamma2 P hgood p hP hp)
    (breveGammaMinus1 P hgood p hP hp)
    (breveLocalG P hgood p hP hp)
    (eisEmbedding p / (‖eisEmbedding p‖ : ℂ))
    (canonicalSextic P hgood (Ideal.Quotient.mk P (-1 : O)))
    (canonicalSextic P hgood (Ideal.Quotient.mk P h))
    ha hg1 hprod' hpair

end ActualEisensteinCubic

open MulChar AddChar

namespace ShortDraftLocal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem direct_theta_jtwo_mask (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (a : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 2 * χ ^ 2) (h : F) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  have hchar : (χ⁻¹) ^ 2 * χ ^ 2 = 1 := by group
  rw [hchar]
  simp only [MulChar.one_apply_coe, one_mul]
  calc
    (∑ h : Fˣ, ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, ψ (a * (y : F)) := by
      apply Fintype.sum_equiv (Equiv.inv Fˣ)
      intro h
      simp
    _ = _ := additive_unit_sum ψ hψ a

theorem direct_theta_jtwo_fourier_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ₂ : χ ^ 2 ≠ 1) (hψ : ψ ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ 2) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum (χ ^ 2) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card Fˣ : ℂ) else -1)) := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ 2) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        (χ ^ 2) σ * gaussSum (χ ^ 2) (ψ.mulShift (-1)) *
          (∑ h : Fˣ,
            (((χ⁻¹) ^ 2 * χ ^ 2) (h : F)) *
              ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient (χ ^ 2) ψ hχ₂, map_mul]
    simp only [MulChar.mul_apply]
    have hpow : (χ ^ 2)⁻¹ = (χ⁻¹) ^ 2 := by group
    rw [hpow]
    ring
  rw [hsum, direct_theta_jtwo_mask χ ψ hψ (ε * x)]
  ring

theorem direct_theta_active_zero_inversion (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (a : F) :
    (∑ h : Fˣ, (χ ^ 2) (h : F) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum ((χ ^ 2)⁻¹) (ψ.mulShift a) := by
  classical
  calc
    (∑ h : Fˣ, (χ ^ 2) (h : F) * ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, ((χ ^ 2)⁻¹) (y : F) * ψ (a * (y : F)) := by
      apply Fintype.sum_equiv (Equiv.inv Fˣ)
      intro y
      simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
      rw [MulChar.inv_apply']
      simp
    _ = gaussSum ((χ ^ 2)⁻¹) (ψ.mulShift a) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]

theorem direct_theta_active_zero_fourier_row (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hχ₂ : χ ^ 2 ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (-(Fintype.card F : ℂ)⁻¹) *
      (∑ h : Fˣ, (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      -(χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum ((χ ^ 2)⁻¹) ψ * (χ ^ 2) ε) * (χ ^ 2) x := by
  classical
  have hχ₂inv : (χ ^ 2)⁻¹ ≠ 1 := by
    intro h
    apply hχ₂
    calc χ ^ 2 = ((χ ^ 2)⁻¹)⁻¹ := by group
      _ = 1 := by rw [h]; simp
  have hsum :
      (∑ h : Fˣ, (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        (χ ^ 2) σ *
          (∑ h : Fˣ, (χ ^ 2) (h : F) *
            ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [map_mul]
    ring
  rw [hsum, direct_theta_active_zero_inversion χ ψ (ε * x)]
  rw [gaussSum_mulShift_any ((χ ^ 2)⁻¹) ψ hχ₂inv (ε * x)]
  simp only [inv_inv, map_mul]
  ring

theorem direct_theta_active_zero_full_row (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hχ₂ : χ ^ 2 ≠ 1) (hψ : ψ ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ 0) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      -(χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum ((χ ^ 2)⁻¹) ψ * (χ ^ 2) ε) * (χ ^ 2) x := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ 0) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      -(∑ h : Fˣ, (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro h _
    rw [pow_zero, trivial_fourier_coefficient ψ hψ h,
      if_neg (Units.ne_zero h)]
    ring
  rw [hsum]
  convert! direct_theta_active_zero_fourier_row χ ψ hχ₂ σ ε x using 1 ; ring

end ShortDraftLocal

end

end OAI

end


