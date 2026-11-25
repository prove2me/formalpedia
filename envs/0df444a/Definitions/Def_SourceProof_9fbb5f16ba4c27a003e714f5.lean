-- Prove2me | Definitions.Def_SourceProof_9fbb5f16ba4c27a003e714f5
-- name    : SourceProof_9fbb5f16ba4c27a003e714f5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:12.697099+00:00
-- url     : https://prove2.me/theorems/6f0bbc79-fb79-440c-b2e2-fcc06615ebc4
-- title:
--   StochLean source theorem: StochLean.tendsto_quadraticTaylorSlope_of_contDiff

import Definitions.Def_SourceProof_1cf1f1d77236c2b817d0e363
import Definitions.Def_SourceProof_7d2789077033a79150308442

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The continuous quadratic Taylor quotient of a real C2 function

The diagonal is filled with one half of the second derivative, not the
totalized quotient's zero value. This is the coefficient of squared increments
in the exact finite-cell Taylor identity used for Ito's formula.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_9fbb5f16ba4c27a003e714f5 {α : Type*} {l : Filter α}
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b : α → ℝ} {x y : ℝ}
    (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 y)) :
    Tendsto (fun i ↦ quadraticTaylorSlope f (a i) (b i)) l
      (𝓝 (quadraticTaylorSlope f x y)) := by
  have hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  by_cases h : y = x
  · subst y
    choose c hc he using fun i ↦ _root_.Prove2MeSourceProof.h_7d2789077033a79150308442 hf (a i) (b i)
    have hmin : Tendsto (fun i ↦ min (a i) (b i)) l (𝓝 x) := by
      simpa only [min_self] using ha.min hb
    have hmax : Tendsto (fun i ↦ max (a i) (b i)) l (𝓝 x) := by
      simpa only [max_self] using ha.max hb
    have hlim : Tendsto c l (𝓝 x) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le hmin hmax
        (fun i ↦ (hc i).1) (fun i ↦ (hc i).2)
    rw [_root_.Prove2MeSourceProof.h_1cf1f1d77236c2b817d0e363]
    exact (((hd.continuous_deriv_one.tendsto x).comp hlim).div_const 2).congr he
  · have hn : ∀ᶠ i in l, b i - a i ≠ 0 := (hb.sub ha).eventually_ne (sub_ne_zero.mpr h)
    rw [StochLean.quadraticTaylorSlope, if_neg (Ne.symm h)]
    have hlim := ((((hf.continuous.tendsto y).comp hb).sub
      ((hf.continuous.tendsto x).comp ha)).sub
      (((hf.continuous_deriv (by decide)).tendsto x).comp ha |>.mul (hb.sub ha))).div
      ((hb.sub ha).pow 2) (pow_ne_zero 2 (sub_ne_zero.mpr h))
    apply hlim.congr'
    filter_upwards [hn] with i hi
    rw [StochLean.quadraticTaylorSlope, if_neg (Ne.symm (sub_ne_zero.mp hi))]
    rfl
end StochLean


