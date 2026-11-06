-- Prove2me | Definitions.Def_PrimeNumberTheoremAnd_Sobolev
-- name    : PrimeNumberTheoremAnd_Sobolev
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:09.451698+00:00
-- url     : https://prove2.me/theorems/865aad23-c644-4cf6-aa06-b805c80f57cc
-- title:
--   Sobolev
-- statement:
--   Definitions and structural lemmas for Sobolev, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where

  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun
@[ext] protected theorem CS.ext {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {x y : CS n E}
    (h : x.toFun = y.toFun) : x = y := by
  cases x
  cases y
  cases h
  rfl
structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1
structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where

  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)
abbrev W21 := W1 2 ℂ
section lemmas
noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)
theorem contDiff_ofReal : ContDiff ℝ ∞ ofReal := Complex.ofRealCLM.contDiff
end lemmas
namespace CS
variable {f : CS n E} {R x v : ℝ}
instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun
instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩
def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := f.h2.neg
instance : Neg (CS n E) where neg := neg
@[simp] theorem neg_apply {x : ℝ} : (-f) x = - (f x) := rfl
def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩
instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul
@[simp] theorem smul_apply : (R • f) x = R • f x := rfl
theorem continuous (f : CS n E) : Continuous f := f.h1.continuous
noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv
noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)
end CS
namespace trunc
instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun
instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS
theorem le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x
theorem zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))
@[simp] theorem zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds
end trunc
namespace W1
instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun
theorem continuous (f : W1 n E) : Continuous f := f.smooth.continuous
theorem iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  funext x
  exact _root_.iteratedDeriv_sub hf.contDiffAt hg.contDiffAt
noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)
def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)
instance : Sub (W1 n E) where sub := sub
theorem integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : (SchwartzMap.derivCLM ℝ ℂ f : ℝ → ℂ) = _root_.deriv f := by
      funext x
      exact SchwartzMap.derivCLM_apply ℝ f x
    rw [← hd]
    exact ih (f := SchwartzMap.derivCLM ℝ ℂ f)
noncomputable def ofSchwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz
end W1
namespace W21
variable {f : W21}
noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)
noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun
noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.ofSchwartz
def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, ?_⟩
  intro k hk
  cases k with
  | zero => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | succ k =>
    cases k with
    | zero =>
      simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
    | succ k =>
      have hk0 : k = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk))
      subst k
      simpa [iteratedDeriv_succ] using
        (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv
instance : Coe (CS 2 ℂ) W21 where coe := ofCS2
instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩
instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f
end W21


