-- Prove2me | Definitions.Def_SourceProof_ea2a7fd3e5f3c080bfd2c0f2
-- name    : SourceProof_ea2a7fd3e5f3c080bfd2c0f2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:12:09.363723+00:00
-- url     : https://prove2.me/theorems/eb2d291d-aa9a-4ce0-9fbb-c4eacfee69bb
-- title:
--   StochLean source theorem: StochLean.tendsto_normSquarePairSum_cadlag_jump_series

import Definitions.Def_SourceProof_0b68fc1889a4f1b551a9937b
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f
import Definitions.Def_SourceProof_4c4273b3af9659bfd1d5f6ba
import Definitions.Def_SourceProof_cbd52fe4240da8fb5dbbffd9
import Definitions.Def_SourceProof_f44216808b938d01cef25be0
import Definitions.Def_SourceProof_f81d4c461f298be40223e563
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5
import Definitions.Def_SourceProof_fe99abf0fa61825b02b3d95f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Cadlag vector norm-square pair sums converge to their actual jump series

Only bounded square sums, vanishing mesh, and actual summability of the
target series are assumed. A finite selection handles both large crossings
and the tail of the target series. No monotonicity or convergence of the
square sums themselves is required by this deterministic lemma.
-/

@[expose] public section

open Set Finset Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_ea2a7fd3e5f3c080bfd2c0f2 {E : Type*}
    [NormedAddCommGroup E] [ProperSpace E] {T : ℝ≥0}
    {π : ℕ → TimePartition T} {x : ℝ≥0 → E} (hx : IsCadlagPath x)
    {Φ : E → E → ℝ} (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2))
    (hdiag : ∀ a, Φ a a = 0)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᶠ n in atTop, normSquareVariationSum (π n) x ≤ B)
    (hsum : Summable (fun s : Ioc 0 T ↦
      Φ (Function.leftLim x s) (x s) * ‖x s - Function.leftLim x s‖ ^ 2)) :
    Tendsto (fun n ↦ normSquarePairSum (π n) Φ x T) atTop
      (𝓝 (∑' s : Ioc 0 T,
        Φ (Function.leftLim x s) (x s) * ‖x s - Function.leftLim x s‖ ^ 2)) := by
  classical
  let ψ : E → E → ℝ := fun a b ↦ Φ a b * ‖b - a‖ ^ 2
  let g : Ioc 0 T → ℝ := fun s ↦ ψ (Function.leftLim x s) (x s)
  have hψ : Continuous (fun p : E × E ↦ ψ p.1 p.2) :=
    hΦ.mul ((continuous_snd.sub continuous_fst).norm.pow 2)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / 3 := div_pos hε (by norm_num)
  let C : ℝ := (ε / 3) / (B + 1)
  have hC : 0 < C := div_pos he (by linarith)
  have hCB : C * B ≤ ε / 3 := by
    calc
      C * B ≤ C * (B + 1) := mul_le_mul_of_nonneg_left (by linarith) hC.le
      _ = ε / 3 := div_mul_cancel₀ _ (by linarith)
  obtain ⟨A₀, hA₀, δ, hδ, hmod⟩ := _root_.Prove2MeSourceProof.h_fe99abf0fa61825b02b3d95f hx T hΦ hdiag hC
  have hfinite : ∀ᶠ J : Finset (Ioc 0 T) in atTop,
      dist (∑ s ∈ J, g s) (∑' s, g s) < ε / 3 :=
    hsum.hasSum.eventually (Metric.ball_mem_nhds _ he)
  obtain ⟨K, hK⟩ := eventually_atTop.mp hfinite
  let E₀ : Finset (Ioc 0 T) := A₀.attach.image (fun s ↦ ⟨s.1, hA₀ s.1 s.2⟩)
  let J : Finset (Ioc 0 T) := E₀ ∪ K
  let A : Finset ℝ≥0 := J.image Subtype.val
  have hA (s : ℝ≥0) (hs : s ∈ A) : s ∈ Ioc 0 T := by
    obtain ⟨r, _, rfl⟩ := mem_image.mp hs
    exact r.2
  have hA₀A (s : ℝ≥0) (hs : s ∈ A₀) : s ∈ A := by
    apply mem_image.mpr
    refine ⟨⟨s, hA₀ s hs⟩, mem_union_left K ?_, rfl⟩
    exact mem_image.mpr ⟨⟨s, hs⟩, mem_attach _ _, rfl⟩
  have hfiniteClose : dist (∑ s ∈ A, ψ (Function.leftLim x s) (x s)) (∑' s, g s) < ε / 3 := by
    have hj : K ⊆ J := subset_union_right
    have heq : (∑ s ∈ A, ψ (Function.leftLim x s) (x s)) = ∑ s ∈ J, g s := by
      rw [show A = J.image Subtype.val from rfl, sum_image]
      intro a _ b _ hab
      exact Subtype.ext hab
    rw [heq]
    exact hK J hj
  have hselected := _root_.Prove2MeSourceProof.h_cbd52fe4240da8fb5dbbffd9 A hA hψ hx hmesh
  filter_upwards [hmesh.eventually_lt_const hδ, hb,
    _root_.Prove2MeSourceProof.h_4c4273b3af9659bfd1d5f6ba hmesh A,
    hselected.eventually (Metric.ball_mem_nhds _ he)] with n hn hbn hsep happ
  let L : ℝ := ∑ s ∈ A, (π n).endpointPairStep ψ x s
  have htail : dist (StochLean.normSquarePairSum (π n) Φ x T) L ≤ ε / 3 := by
    have hc (i : Fin (π n).size)
        (hi : ∀ s ∈ A, s ∉ Ioc ((π n).left i) ((π n).right i)) :
        ‖Φ (x ((π n).left i)) (x ((π n).right i))‖ ≤ C := by
      apply (hmod _ ⟨bot_le, (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π n)) i.castSucc⟩
        _ ⟨bot_le, (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π n)) i.succ⟩ ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (π n)) i) ?_ ?_).le
      · exact ((_root_.Prove2MeSourceProof.h_f81d4c461f298be40223e563 (π n))
          ⟨le_rfl, (_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (π n)) i⟩ ⟨(_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (π n)) i, le_rfl⟩).trans_lt hn
      · exact fun s hs ↦ hi s (hA₀A s hs)
    have heq : L = ∑ i : Fin (π n).size,
        if ∃ s ∈ A, s ∈ Ioc ((π n).left i) ((π n).right i)
          then Φ (x ((π n).left i)) (x ((π n).right i)) * ‖x ((π n).right i) - x ((π n).left i)‖ ^ 2
          else 0 := (_root_.Prove2MeSourceProof.h_f44216808b938d01cef25be0 (π n)) A hA hsep ψ x
    rw [dist_eq_norm, heq]
    exact ((_root_.Prove2MeSourceProof.h_0b68fc1889a4f1b551a9937b (π n) A Φ x hC.le hc).trans
      (mul_le_mul_of_nonneg_left hbn hC.le)).trans hCB
  have htri := dist_triangle (StochLean.normSquarePairSum (π n) Φ x T) L (∑' s, g s)
  have htri' := dist_triangle L (∑ s ∈ A, ψ (Function.leftLim x s) (x s)) (∑' s, g s)
  change dist L (∑ s ∈ A, ψ (Function.leftLim x s) (x s)) < ε / 3 at happ
  change dist (StochLean.normSquarePairSum (π n) Φ x T) (∑' s, g s) < ε
  linarith only [htail, happ, hfiniteClose, htri, htri']
end StochLean


