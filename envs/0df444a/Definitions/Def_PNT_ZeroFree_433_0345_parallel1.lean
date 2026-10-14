-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0345_parallel1
-- name    : PNT_ZeroFree_433_0345_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:13:51.262473+00:00
-- url     : https://prove2.me/theorems/58a2074c-d5d4-4233-87ad-2b7a7e890f6a
-- title:
--   Zero-free region foundations: Hecke.Strip [0345_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Hecke.Strip
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/Strip.lean#L12-L316

import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Definitions.Def_PNT_ZeroFree_433_0057_1
import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/Strip.lean#L12-L316
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Hecke.Strip
section
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter Asymptotics Set MeasureTheory

namespace SevenEighths.HeckeStrip

def gammaConstant : ℝ := Real.Gamma (11 / 10) / Real.Gamma (19 / 10)

theorem gammaConstant_pos : 0 < gammaConstant :=
  div_pos (Real.Gamma_pos_of_pos (by norm_num)) (Real.Gamma_pos_of_pos (by norm_num))

theorem gamma_ratio_left_bound (t : ℝ) :
    ‖Complex.Gamma (1 - ((-(1 / 10) : ℂ) + t * Complex.I)) /
      Complex.Gamma ((-(1 / 10) : ℂ) + t * Complex.I)‖ ≤
        gammaConstant * (3 + |t|) ^ 2 := by
  let s : ℂ := -(1 / 10) + t * Complex.I
  have hb := CubicReflectionKernel.Gamma_shifted_pair_bound
    (1 / 2) (3 / 5) (-t) 2 (by norm_num) (by norm_num)
  simp only [Complex.ofReal_neg] at hb
  have hnum : ((1 / 2 : ℝ) : ℂ) + ((3 / 5 : ℝ) + (-t) * Complex.I) = 1 - s := by
    dsimp [s]; push_cast; ring
  have hden : ((1 / 2 : ℝ) : ℂ) - ((3 / 5 : ℝ) + (-t) * Complex.I) + (2 : ℕ) = s + 2 := by
    dsimp [s]; push_cast; ring
  rw [hnum, hden] at hb
  norm_num only [show (1 / 2 : ℝ) + 3 / 5 = 11 / 10 by norm_num,
    show (1 / 2 : ℝ) - 3 / 5 + (2 : ℕ) = 19 / 10 by norm_num] at hb
  have heq : Complex.Gamma (1 - s) / Complex.Gamma s =
      (∏ k ∈ Finset.range 2, (s + k)) *
        (Complex.Gamma (1 - s) / Complex.Gamma (s + 2)) := by
    rw [div_eq_mul_inv, CubicReflectionKernel.inverse_Gamma_shift s 2]
    simp only [Nat.cast_ofNat, div_eq_mul_inv]
    ring
  have hs : ‖s‖ ≤ 1 / 10 + |t| := by
    simpa [s, norm_mul] using norm_add_le (-(1 / 10) : ℂ) ((t : ℂ) * Complex.I)
  have hf := CubicReflectionKernel.norm_Gamma_shift_factor s 2
  have hf' : ‖∏ k ∈ Finset.range 2, (s + k)‖ ≤ (3 + |t|) ^ 2 := by
    have hs2 : ‖s‖ + (2 : ℝ) ≤ 3 + |t| := by linarith
    exact hf.trans (pow_le_pow_left₀ (by positivity) hs2 2)
  change ‖Complex.Gamma (1 - s) / Complex.Gamma s‖ ≤ _
  rw [heq, norm_mul]
  exact (mul_le_mul hf' hb (norm_nonneg _) (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem gamma_ratio_left_bound_of_re (z : ℂ) (hz : z.re = -(1 / 10)) :
    ‖Complex.Gamma (1 - z) / Complex.Gamma z‖ ≤ gammaConstant * (3 + |z.im|) ^ 2 := by
  have he : (-(1 / 10) : ℂ) + z.im * Complex.I = z := by
    simpa only [hz, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using Complex.re_add_im z
  simpa only [he] using gamma_ratio_left_bound z.im

def completionScale (Q : ℝ) : ℝ := Real.sqrt (3 * Q) / (2 * Real.pi)

theorem completionScale_pos (Q : ℝ) (hQ : 0 < Q) : 0 < completionScale Q := by
  unfold completionScale
  positivity

theorem completionScale_left_power (Q : ℝ) (hQ : 0 < Q) :
    completionScale Q ^ (6 / 5 : ℝ) =
      (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ) := by
  have he : completionScale Q = (Real.sqrt 3 / (2 * Real.pi)) * Real.sqrt Q := by
    unfold completionScale
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  rw [he, Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)]
  congr 1
  rw [Real.sqrt_eq_rpow Q, ← Real.rpow_mul hQ.le]
  norm_num

def leftConstant : ℝ :=
  (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * gammaConstant

theorem leftConstant_pos : 0 < leftConstant :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) gammaConstant_pos

theorem left_boundary_of_functional_equation (Q D : ℝ) (hQ : 0 < Q) (_hD : 0 ≤ D)
    (L Ldual : ℂ → ℂ) (ε : ℂ) (hε : ‖ε‖ = 1)
    (hfe : ∀ z : ℂ, z.re = -(1 / 10) → L z =
      ε * (completionScale Q : ℂ) ^ (1 - 2 * z) *
        (Complex.Gamma (1 - z) / Complex.Gamma z) * Ldual (1 - z))
    (hdual : ∀ z : ℂ, z.re = 11 / 10 → ‖Ldual z‖ ≤ D)
    (z : ℂ) (hz : z.re = -(1 / 10)) :
    ‖L z‖ ≤ leftConstant * D * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hscale : ‖(completionScale Q : ℂ) ^ (1 - 2 * z)‖ =
      (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (completionScale_pos Q hQ)]
    have hre : (1 - 2 * z).re = 6 / 5 := by simp [hz]; norm_num
    rw [hre, completionScale_left_power Q hQ]
  have hd : ‖Ldual (1 - z)‖ ≤ D := hdual _ (by simp [hz]; norm_num)
  rw [hfe z hz, norm_mul, norm_mul, norm_mul, hε, one_mul, hscale]
  have hg := gamma_ratio_left_bound_of_re z hz
  have hc := gammaConstant_pos
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_left hg (by positivity)) hd (norm_nonneg _)
    (by positivity : 0 ≤ ((Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ)) *
      (gammaConstant * (3 + |z.im|) ^ 2))
  calc
    _ ≤ ((Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ)) *
        (gammaConstant * (3 + |z.im|) ^ 2) * D := hm
    _ = _ := by unfold leftConstant; ring

def strip : Set ℂ := Complex.re ⁻¹' Ioo (-(1 / 10)) (11 / 10)
def closedStrip : Set ℂ := Complex.re ⁻¹' Icc (-(1 / 10)) (11 / 10)

theorem vertical_strip_of_exp_bound (F : ℂ → ℂ) (C : ℝ)
    (hF : DiffContOnCl ℂ F strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖F z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) → ‖F z‖ ≤ C)
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖F z‖ ≤ C)
    (z : ℂ) (hz : z ∈ closedStrip) : ‖F z‖ ≤ C := by
  obtain ⟨A, B, hA, hB, hgrowth⟩ := hgrowth
  apply PhragmenLindelof.vertical_strip hF ?_ hleft hright hz.1 hz.2
  refine ⟨1, ?_, B, ?_⟩
  · apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 11 / 10 - -(1 / 10))).mpr
    linarith [Real.two_le_pi]
  · apply isBigO_iff.mpr
    refine ⟨A, eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_)⟩
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply (hgrowth z hz).trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    simp only [one_mul]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp |z.im|]) hB

theorem closure_strip_subset : closure strip ⊆ closedStrip :=
  closure_minimal (fun _ hz => ⟨hz.1.le, hz.2.le⟩)
    (isClosed_Icc.preimage Complex.continuous_re)

theorem shift_norm_lower (z : ℂ) (hz : z ∈ closedStrip) : 1 ≤ ‖z + 2‖ := by
  have h := Complex.re_le_norm (z + 2)
  norm_num at h
  linarith [hz.1]

theorem shift_ne_zero (z : ℂ) (hz : z ∈ closedStrip) : z + 2 ≠ 0 := by
  have h := shift_norm_lower z hz
  intro hzero
  rw [hzero, norm_zero] at h
  norm_num at h

theorem height_le_shift_norm (z : ℂ) (hz : z ∈ closedStrip) :
    3 + |z.im| ≤ 3 * ‖z + 2‖ := by
  have hr := Complex.re_le_norm (z + 2)
  have hi := Complex.abs_im_le_norm (z + 2)
  norm_num at hr hi
  linarith [hz.1]

theorem shift_norm_le_height (z : ℂ) (hz : z ∈ closedStrip) :
    ‖z + 2‖ ≤ 2 * (3 + |z.im|) := by
  have hr : 0 ≤ z.re + 2 := by linarith [hz.1]
  have h := Complex.norm_le_abs_re_add_abs_im (z + 2)
  norm_num [abs_of_nonneg hr] at h
  linarith [hz.2, abs_nonneg z.im]

def normalized (Q : ℝ) (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  L z / (((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) * (z + 2) ^ 2)

theorem norm_normalized (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ) (z : ℂ) :
    ‖normalized Q L z‖ = ‖L z‖ / (Q ^ (3 / 5 : ℝ) * ‖z + 2‖ ^ 2) := by
  simp [normalized, norm_pow,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hQ _)]

theorem normalized_diffContOnCl (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ)
    (hL : DiffContOnCl ℂ L strip) : DiffContOnCl ℂ (normalized Q L) strip := by
  have hqn : ((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)).ne'
  have hd : Differentiable ℂ (fun z : ℂ => ((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) * (z + 2) ^ 2) := by
    fun_prop
  refine ⟨hL.differentiableOn.div hd.differentiableOn ?_, hL.continuousOn.div hd.continuous.continuousOn ?_⟩
  · intro z hz
    exact mul_ne_zero hqn (pow_ne_zero _ (shift_ne_zero z ⟨hz.1.le, hz.2.le⟩))
  · intro z hz
    exact mul_ne_zero hqn (pow_ne_zero _ (shift_ne_zero z (closure_strip_subset hz)))

theorem normalized_exp_bound (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖normalized Q L z‖ ≤ A * Real.exp (B * |z.im|) := by
  obtain ⟨A, B, hA, hB, hg⟩ := hgrowth
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  refine ⟨A / Q ^ (3 / 5 : ℝ), B, div_nonneg hA hq.le, hB, ?_⟩
  intro z hz
  have hn := shift_norm_lower z ⟨hz.1.le, hz.2.le⟩
  have hn2 : 1 ≤ ‖z + 2‖ ^ 2 := by nlinarith
  rw [norm_normalized Q hQ]
  calc
    _ ≤ ‖L z‖ / Q ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hq (by nlinarith)
    _ ≤ (A * Real.exp (B * |z.im|)) / Q ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_right (hg z hz) hq.le
    _ = _ := by ring

theorem normalized_boundary_bound (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (z : ℂ) (hz : z ∈ closedStrip)
    (hL : ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2) :
    ‖normalized Q L z‖ ≤ 9 * C := by
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  have hn : 0 < ‖z + 2‖ := lt_of_lt_of_le zero_lt_one (shift_norm_lower z hz)
  have hh := height_le_shift_norm z hz
  have hh2 : (3 + |z.im|) ^ 2 ≤ 9 * ‖z + 2‖ ^ 2 := by
    nlinarith [abs_nonneg z.im, norm_nonneg (z + 2)]
  rw [norm_normalized Q hQ]
  apply (div_le_iff₀ (mul_pos hq (sq_pos_of_pos hn))).mpr
  apply hL.trans
  have h := mul_le_mul_of_nonneg_left hh2 (mul_nonneg hC hq.le)
  nlinarith

theorem uniform_strip_bound_of_edges (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (hright : ∀ z : ℂ, z.re = 11 / 10 →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hn : ‖normalized Q L z‖ ≤ 9 * C := by
    apply vertical_strip_of_exp_bound _ _ (normalized_diffContOnCl Q hQ L hL)
      (normalized_exp_bound Q hQ L hgrowth) ?_ ?_ z hz
    · intro w hw
      apply normalized_boundary_bound Q C hQ hC L w
        (show w ∈ closedStrip from ⟨by rw [hw], by rw [hw]; norm_num⟩) (hleft w hw)
    · intro w hw
      apply normalized_boundary_bound Q C hQ hC L w
        (show w ∈ closedStrip from ⟨by rw [hw]; norm_num, by rw [hw]⟩) (hright w hw)
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  have hnz : 0 < ‖z + 2‖ := lt_of_lt_of_le zero_lt_one (shift_norm_lower z hz)
  rw [norm_normalized Q hQ] at hn
  have hb := (div_le_iff₀ (mul_pos hq (sq_pos_of_pos hnz))).mp hn
  have hh := shift_norm_le_height z hz
  have hh2 : ‖z + 2‖ ^ 2 ≤ 4 * (3 + |z.im|) ^ 2 := by
    nlinarith [norm_nonneg (z + 2), abs_nonneg z.im]
  have h := mul_le_mul_of_nonneg_left hh2 (mul_nonneg (by positivity : 0 ≤ 9 * C) hq.le)
  nlinarith

theorem uniform_strip_bound (Q C : ℝ) (hQ : 1 ≤ Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖L z‖ ≤ C)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  apply uniform_strip_bound_of_edges Q C (lt_of_lt_of_le zero_lt_one hQ) hC L hL
    hgrowth hleft ?_ z hz
  intro w hw
  apply (hright w hw).trans
  have hq : 1 ≤ Q ^ (3 / 5 : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hh : 1 ≤ (3 + |w.im|) ^ 2 := by nlinarith [abs_nonneg w.im]
  calc
    C ≤ C * Q ^ (3 / 5 : ℝ) := le_mul_of_one_le_right hC hq
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hC (le_trans zero_le_one hq)) hh

theorem uniform_strip_bound_of_functional_equation
    (Q D : ℝ) (hQ : 1 ≤ Q) (hD : 0 ≤ D) (L Ldual : ℂ → ℂ)
    (ε : ℂ) (hε : ‖ε‖ = 1) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hfe : ∀ z : ℂ, z.re = -(1 / 10) → L z =
      ε * (completionScale Q : ℂ) ^ (1 - 2 * z) *
        (Complex.Gamma (1 - z) / Complex.Gamma z) * Ldual (1 - z))
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖L z‖ ≤ D)
    (hdual : ∀ z : ℂ, z.re = 11 / 10 → ‖Ldual z‖ ≤ D)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * ((1 + leftConstant) * D) * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hQ0 := lt_of_lt_of_le zero_lt_one hQ
  have hc := leftConstant_pos
  apply uniform_strip_bound Q ((1 + leftConstant) * D) hQ (by positivity) L hL hgrowth ?_ ?_ z hz
  · intro w hw
    apply (left_boundary_of_functional_equation Q D hQ0 hD L Ldual ε hε hfe hdual w hw).trans
    have hbase : leftConstant * D ≤ (1 + leftConstant) * D := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hQ0.le _)) (sq_nonneg _)
  · intro w hw
    apply (hright w hw).trans
    nlinarith

theorem uncompleted_exp_bound (a : ℝ) (ha : 0 < a) (F : ℂ → ℂ)
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closedStrip, ‖F z‖ ≤ C) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ strip,
      ‖(a : ℂ) ^ (-z) * (Complex.Gamma z)⁻¹ * F z‖ ≤
        A * Real.exp (B * |z.im|) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨G, hG, hg⟩ := CubicGammaExponential.inverse_Gamma_strip_exp_bound_complex
    (-(1 / 10)) (11 / 10)
  let S : ℝ := a ^ (-(11 / 10) : ℝ) + a ^ (1 / 10 : ℝ)
  have hS : 0 ≤ S := add_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg ha.le _)
  refine ⟨S * G * C, Real.pi, by positivity, Real.pi_pos.le, ?_⟩
  intro z hz
  have hzc : z ∈ closedStrip := ⟨hz.1.le, hz.2.le⟩
  have haBound : ‖(a : ℂ) ^ (-z)‖ ≤ S := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.neg_re]
    exact VerticalContourShift.rpow_between_endpoints a (-(11 / 10)) (1 / 10) (-z.re)
      ha (by linarith [hz.2]) (by linarith [hz.1])
  rw [norm_mul, norm_mul]
  have hgamma := hg z hzc
  have hprod := mul_le_mul (mul_le_mul haBound hgamma (norm_nonneg _) hS)
    (hF z hzc) (norm_nonneg _) (mul_nonneg hS (mul_nonneg hG.le (Real.exp_nonneg _)))
  nlinarith

theorem mellin_uncompleted_exp_bound (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ)
    (hleft : MellinConvergent f (-(1 / 10) : ℂ))
    (hright : MellinConvergent f (11 / 10 : ℂ)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ strip,
      ‖(a : ℂ) ^ (-z) * (Complex.Gamma z)⁻¹ * mellin f z‖ ≤
        A * Real.exp (B * |z.im|) := by
  apply uncompleted_exp_bound a ha (mellin f)
  obtain ⟨C, hC, hb⟩ := VerticalContourShift.mellin_uniform_strip_bound f
    (-(1 / 10)) (11 / 10) (by simpa using hleft) (by simpa using hright)
  exact ⟨C, hC, fun z hz => hb z hz.1 hz.2⟩

end SevenEighths.HeckeStrip
end

end OAI

end


