-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0300_parallel1
-- name    : PNT_ZeroFree_433_0300_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:22:12.931591+00:00
-- url     : https://prove2.me/theorems/c54a82a9-a073-46af-aa94-8a6ce285a6a0
-- title:
--   Zero-free region foundations: Supremum, Continuation [0300_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Supremum
--   - OAI.NumberTheory.DirichletL.Continuation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Supremum.lean#L10-L95
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Continuation.lean#L15-L158

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.MellinTransform
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Tactic.Linarith
import Definitions.Def_PNT_ZeroFree_433_0147
import Definitions.Def_PNT_ZeroFree_433_0149
import Definitions.Def_PNT_ZeroFree_433_0345_parallel1
import Definitions.Def_PNT_ZeroFree_433_0377_parallel1
import Definitions.Def_PNT_ZeroFree_433_0419_parallel1
import Definitions.Def_PNT_ZeroFree_433_0475_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Supremum.lean#L10-L95
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Continuation.lean#L15-L158
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Supremum
section
namespace OAI

namespace SevenEighths.Supremum

noncomputable section

def continuationMargin (β ω σ : ℝ) : ℝ := min (β - 7 / 8 - ω) σ

theorem continuationMargin_pos {β ω σ : ℝ}
    (hω : ω < β - 7 / 8) (hσ : 0 < σ) :
    0 < continuationMargin β ω σ := by
  exact lt_min (sub_pos.mpr hω) hσ

theorem continuationMargin_le_gap (β ω σ : ℝ) :
    continuationMargin β ω σ ≤ β - 7 / 8 - ω :=
  min_le_left _ _

theorem continuationMargin_le_sigma (β ω σ : ℝ) :
    continuationMargin β ω σ ≤ σ :=
  min_le_right _ _

theorem continuation_boundary_gt {β ω σ : ℝ} (hω : 0 < ω) :
    7 / 8 < β - continuationMargin β ω σ := by
  have h := continuationMargin_le_gap β ω σ
  linarith

theorem max_signal_exponents (β ω σ c : ℝ) :
    max (7 / 8 + c + ω) (β + c - σ) =
      β + c - continuationMargin β ω σ := by
  unfold continuationMargin
  rcases le_total (β - 7 / 8 - ω) σ with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    linarith
  · rw [min_eq_right h, max_eq_right (by linarith)]

theorem max_normalized_signal_exponents (β ω σ : ℝ) :
    max (3 / 16 + ω) (β - 11 / 16 - σ) =
      β - 11 / 16 - continuationMargin β ω σ := by
  have h : (7 / 8 : ℝ) + -(11 / 16) = 3 / 16 := by norm_num
  simpa only [sub_eq_add_neg, h] using max_signal_exponents β ω σ (-(11 / 16))

theorem exists_gt_supremum_sub {S : Set ℝ} (hne : S.Nonempty)
    (hbounded : BddAbove S) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x := by
  apply (lt_csSup_iff hbounded hne).mp
  linarith

theorem uniform_bound_below_supremum_false {S : Set ℝ}
    (hne : S.Nonempty) (hbounded : BddAbove S) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ x ∈ S, x ≤ sSup S - ε) : False := by
  obtain ⟨x, hx, hlt⟩ := exists_gt_supremum_sub hne hbounded hε
  exact (not_lt_of_ge (hbound x hx)) hlt

theorem exists_gt_supremum_sub_of_insert {S : Set ℝ} {a ε : ℝ}
    (hbounded : BddAbove (insert a S)) (hε : 0 < ε)
    (ha : a ≤ sSup (insert a S) - ε) :
    ∃ x ∈ S, sSup (insert a S) - ε < x := by
  obtain ⟨x, hx, hlt⟩ :=
    exists_gt_supremum_sub (Set.insert_nonempty a S) hbounded hε
  rcases Set.mem_insert_iff.mp hx with hxa | hxS
  · subst x
    exact False.elim ((not_lt_of_ge ha) hlt)
  · exact ⟨x, hxS, hlt⟩

theorem seven_eighths_of_uniform_margin {S : Set ℝ}
    (hne : S.Nonempty) (hbounded : BddAbove S)
    (hbound : 7 / 8 < sSup S →
      ∃ ω σ : ℝ, ω < sSup S - 7 / 8 ∧ 0 < σ ∧
        ∀ x ∈ S, x ≤ sSup S - continuationMargin (sSup S) ω σ) :
    sSup S ≤ 7 / 8 := by
  by_contra h
  obtain ⟨ω, σ, hω, hσ, hbound⟩ := hbound (lt_of_not_ge h)
  exact uniform_bound_below_supremum_false hne hbounded
    (continuationMargin_pos hω hσ) hbound

theorem seven_eighths_of_uniform_margin_with_sentinel {S : Set ℝ}
    (hbounded : BddAbove (insert (1 / 2 : ℝ) S))
    (hbound : 7 / 8 < sSup (insert (1 / 2 : ℝ) S) →
      ∃ ω σ : ℝ, 0 < ω ∧ ω < sSup (insert (1 / 2 : ℝ) S) - 7 / 8 ∧
        0 < σ ∧ ∀ x ∈ S, x ≤ sSup (insert (1 / 2 : ℝ) S) -
          continuationMargin (sSup (insert (1 / 2 : ℝ) S)) ω σ) :
    sSup (insert (1 / 2 : ℝ) S) ≤ 7 / 8 := by
  by_contra h
  obtain ⟨ω, σ, hω0, hω, hσ, hbound⟩ := hbound (lt_of_not_ge h)
  have hε := continuationMargin_pos hω hσ
  have hboundary := continuation_boundary_gt (β := sSup (insert (1 / 2 : ℝ) S))
    (σ := σ) hω0
  have hsentinel : (1 / 2 : ℝ) ≤ sSup (insert (1 / 2 : ℝ) S) -
      continuationMargin (sSup (insert (1 / 2 : ℝ) S)) ω σ := by
    linarith
  obtain ⟨x, hx, hlt⟩ := exists_gt_supremum_sub_of_insert hbounded hε hsentinel
  exact (not_lt_of_ge (hbound x hx)) hlt

end

end SevenEighths.Supremum

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Continuation
section
namespace OAI

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace SevenEighths.Continuation

def signalMellin (f : ℝ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  mellin f (-(s + (c : ℂ)))

def RapidDecayAtZero (f : ℝ → ℂ) : Prop :=
  ∀ B : ℝ, f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ B)

theorem rpow_isBigO_atTop_of_le {a b : ℝ} (h : a ≤ b) :
    (fun x : ℝ => x ^ a) =O[atTop] (fun x : ℝ => x ^ b) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa only [one_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] using
    Real.rpow_le_rpow_of_exponent_le hx h

theorem common_signal_bound (J f : ℝ → ℂ) (a b : ℝ)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ a))
    (herror : (fun x => J x - f x) =O[atTop] (fun x : ℝ => x ^ b)) :
    f =O[atTop] (fun x : ℝ => x ^ max a b) := by
  have h₁ := hJ.trans (rpow_isBigO_atTop_of_le (le_max_left a b))
  have h₂ := herror.trans (rpow_isBigO_atTop_of_le (le_max_right a b))
  simpa only [sub_sub_cancel] using h₁.sub h₂

theorem common_signal_bound_with_margin (J f : ℝ → ℂ) (β ω σ c : ℝ)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (7 / 8 + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ))) :
    f =O[atTop] (fun x : ℝ =>
      x ^ (β + c - Supremum.continuationMargin β ω σ)) := by
  simpa only [Supremum.max_signal_exponents] using
    common_signal_bound J f (7 / 8 + c + ω) (β + c - σ) hJ herror

theorem signalMellin_convergent (f : ℝ → ℂ) (a c : ℝ)
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f) {s : ℂ} (hs : a < s.re) :
    MellinConvergent f (-(s + (c : ℂ))) := by
  apply mellinConvergent_of_isBigO_rpow (a := -(a+c))
    (b := (-(s + (c : ℂ))).re - 1) hlocal
  · simpa only [neg_neg] using htop
  · simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
    linarith
  · exact hzero _
  · linarith

theorem signalMellin_analytic (f : ℝ → ℂ) (a c : ℝ)
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f) :
    AnalyticOnNhd ℂ (signalMellin f c) {s : ℂ | a < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt a)).2
  intro s hs
  have hd : DifferentiableAt ℂ (mellin f) (-(s + (c : ℂ))) := by
    apply mellin_differentiableAt_of_isBigO_rpow (a := -(a+c))
      (b := (-(s + (c : ℂ))).re - 1) hlocal
    · simpa only [neg_neg] using htop
    · simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
      change a < s.re at hs
      linarith
    · exact hzero _
    · linarith
  exact (hd.comp s ((differentiableAt_id.add_const (c : ℂ)).neg)).differentiableWithinAt

theorem product_identity_on_halfPlane (a b : ℝ) (L M W : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {s : ℂ | a < s.re})
    (hM : AnalyticOnNhd ℂ M {s : ℂ | a < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | a < s.re})
    (heq : ∀ s : ℂ, max a b < s.re → L s * M s = W s) :
    Set.EqOn (fun s => L s * M s) W {s : ℂ | a < s.re} := by
  let z : ℂ := (max a b + 1 : ℝ)
  have hz : a < z.re := by dsimp [z]; linarith [le_max_left a b]
  have hz' : max a b < z.re := by dsimp [z]; simp
  have hev : (fun s => L s * M s) =ᶠ[𝓝 z] W := by
    filter_upwards [(Complex.isOpen_re_gt (max a b)).mem_nhds hz'] with s hs
    exact heq s hs
  exact (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
    (convex_halfSpace_re_gt a).isPreconnected hz hev

theorem nonzero_of_regularized_signal (a b c : ℝ)
    (L Lregular R W : ℂ → ℂ) (f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular {s : ℂ | a < s.re})
    (hR : AnalyticOnNhd ℂ R {s : ℂ | a < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | a < s.re})
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f)
    (heq : ∀ s : ℂ, max a b < s.re →
      Lregular s * signalMellin f c s = R s * W s)
    {ρ : ℂ} (hρ : a < ρ.re)
    (hregular : Lregular ρ = R ρ * L ρ)
    (hRρ : R ρ ≠ 0) (hWρ : W ρ ≠ 0) : L ρ ≠ 0 := by
  have hid := product_identity_on_halfPlane a b Lregular (signalMellin f c)
    (fun s => R s * W s) hL (signalMellin_analytic f a c hlocal htop hzero)
    (hR.mul hW) heq hρ
  intro hz
  change Lregular ρ * signalMellin f c ρ = R ρ * W ρ at hid
  rw [hregular, hz, mul_zero, zero_mul] at hid
  exact (mul_ne_zero hRρ hWρ) hid.symm

theorem multiplier_ne_zero {H : ℂ → ℂ} {s : ℂ}
    (h : ‖H s - 1‖ ≤ (1 / 2 : ℝ)) : H s ≠ 0 := by
  intro hz
  simp [hz] at h
  norm_num at h

def gaussianMultiplier (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5 / 6) ^ 2) * H s

theorem gaussianMultiplier_analytic {H : ℂ → ℂ} {U : Set ℂ}
    (hH : AnalyticOnNhd ℂ H U) : AnalyticOnNhd ℂ (gaussianMultiplier H) U := by
  exact ((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).cexp.mul hH

theorem gaussianMultiplier_ne_zero {H : ℂ → ℂ} {s : ℂ}
    (hH : ‖H s - 1‖ ≤ (1 / 2 : ℝ)) : gaussianMultiplier H s ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (multiplier_ne_zero hH)

theorem nonzero_of_common_signal (β ω σ c : ℝ) (hω : 0 < ω)
    (L Lregular R H : ℂ → ℂ) (J f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular
      {s : ℂ | β - Supremum.continuationMargin β ω σ < s.re})
    (hR : AnalyticOnNhd ℂ R
      {s : ℂ | β - Supremum.continuationMargin β ω σ < s.re})
    (hH : AnalyticOnNhd ℂ H {s : ℂ | 7 / 8 < s.re})
    (hcontract : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ))
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (hzero : RapidDecayAtZero f)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (7 / 8 + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ)))
    (heq : ∀ s : ℂ, max (β - Supremum.continuationMargin β ω σ) 1 < s.re →
      Lregular s * signalMellin f c s = R s * gaussianMultiplier H s)
    {ρ : ℂ} (hρ : β - Supremum.continuationMargin β ω σ < ρ.re)
    (hregular : Lregular ρ = R ρ * L ρ) (hRρ : R ρ ≠ 0) : L ρ ≠ 0 := by
  have hboundary := Supremum.continuation_boundary_gt (β := β) (σ := σ) hω
  have hH' : AnalyticOnNhd ℂ H
      {s : ℂ | β - Supremum.continuationMargin β ω σ < s.re} :=
    hH.mono (fun s hs => lt_trans hboundary hs)
  have htop : f =O[atTop] (fun x : ℝ =>
      x ^ ((β - Supremum.continuationMargin β ω σ) + c)) := by
    have hexp : (β - Supremum.continuationMargin β ω σ) + c =
        β + c - Supremum.continuationMargin β ω σ := by ring
    simpa only [hexp] using common_signal_bound_with_margin J f β ω σ c hJ herror
  exact nonzero_of_regularized_signal _ 1 c L Lregular R (gaussianMultiplier H) f
    hL hR (gaussianMultiplier_analytic hH') hlocal htop hzero heq hρ hregular
    hRρ (gaussianMultiplier_ne_zero (hcontract ρ (lt_trans hboundary hρ)))

end SevenEighths.Continuation

end

end OAI

end


