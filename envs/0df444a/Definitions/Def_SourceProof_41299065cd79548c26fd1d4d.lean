-- Prove2me | Definitions.Def_SourceProof_41299065cd79548c26fd1d4d
-- name    : SourceProof_41299065cd79548c26fd1d4d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:44:46.744873+00:00
-- url     : https://prove2.me/theorems/d911eb9a-0916-4512-93b3-09cc64759916
-- title:
--   StochLean source theorem: StochLean.locallyBoundedVariationOn_tsum_Ioc

import Definitions.Def_SourceProof_798d59aac4a0874192da8eb2
import Definitions.Def_SourceProof_7e65c00b693d38d872360fac
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Local finite variation of actual absolutely summable jump series

Positive and negative cumulative series are monotone. Their difference
is the original series, so no enumeration of its countable support or
expected-variation bound is needed.
-/

@[expose] public section

open Set
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_41299065cd79548c26fd1d4d {g : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |g s|)) :
    LocallyBoundedVariationOn (fun T : ℝ≥0 ↦ ∑' s : Ioc 0 T, g s) univ := by
  let p : ℝ≥0 → ℝ := fun s ↦ (|g s| + g s) / 2
  let n : ℝ≥0 → ℝ := fun s ↦ (|g s| - g s) / 2
  have hp (T : ℝ≥0) : Summable (fun s : Ioc 0 T ↦ p s) :=
    ((hs T).add (hs T).of_abs).div_const 2
  have hn (T : ℝ≥0) : Summable (fun s : Ioc 0 T ↦ n s) :=
    ((hs T).sub (hs T).of_abs).div_const 2
  have hp0 (s : ℝ≥0) : 0 ≤ p s := by
    have h := neg_abs_le (g s)
    dsimp only [p]
    linarith only [h]
  have hn0 (s : ℝ≥0) : 0 ≤ n s := by
    have h := le_abs_self (g s)
    dsimp only [n]
    linarith only [h]
  have hpm := _root_.Prove2MeSourceProof.h_7e65c00b693d38d872360fac (g := p) hp hp0
  have hnm := _root_.Prove2MeSourceProof.h_7e65c00b693d38d872360fac (g := n) hn hn0
  have hv := _root_.Prove2MeSourceProof.h_798d59aac4a0874192da8eb2 (hpm.monotoneOn univ).locallyBoundedVariationOn
    (hnm.monotoneOn univ).locallyBoundedVariationOn
  have heq : (fun T : ℝ≥0 ↦ (∑' s : Ioc 0 T, p s) - ∑' s : Ioc 0 T, n s) =
      fun T : ℝ≥0 ↦ ∑' s : Ioc 0 T, g s := by
    funext T
    rw [← (hp T).tsum_sub (hn T)]
    apply tsum_congr
    intro s
    dsimp only [p, n]
    ring
  rwa [heq] at hv
end StochLean


