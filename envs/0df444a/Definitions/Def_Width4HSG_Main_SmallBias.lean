-- Prove2me | Definitions.Def_Width4HSG_Main_SmallBias
-- name    : Width4HSG_Main_SmallBias
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:17:14.903454+00:00
-- url     : https://prove2.me/theorems/a43881c3-2df6-4c69-8e93-29ec87a8296b
-- title:
--   Definitions 3.2 and 3.4 — small bias and almost independence
-- statement:
--   Small bias bounds the absolute expected parity character of every nonempty coordinate subset by δ. Almost k-wise independence bounds the expectation error by γ for every [-1,1]-valued test depending on at most k coordinates. A generator is sampled on independent uniform seed bits.
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, p. 16, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib
import Definitions.Def_Width4HSG_Main_FiniteCube

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

def character {α : Type} [Fintype α] (S : Finset α) (x : α → Bool) : ℝ :=
  (-1 : ℝ) ^ (∑ i ∈ S, if x i then 1 else 0 : ℕ)

def SmallBias {α : Type} [Fintype α] (D : PMF (α → Bool)) (δ : ℝ) : Prop := by
  classical
  exact ∀ S : Finset α, S.Nonempty → |expectation D (character S)| ≤ δ

def AlmostKWise {α : Type} [Fintype α] (D : PMF (α → Bool)) (γ : ℝ) (k : ℕ) : Prop := by
  classical
  exact ∀ (S : Finset α), S.card ≤ k → ∀ f : (α → Bool) → ℝ,
    (∀ x, -1 ≤ f x ∧ f x ≤ 1) →
    (∀ x y, (∀ i ∈ S, x i = y i) → f x = f y) →
    |expectation D f - average f| ≤ γ

def sampleLaw {n s : ℕ} (G : Bits s → Bits n) : PMF (Bits n) :=
  PMF.map G (PMF.uniformOfFintype (Bits s))

end Width4HSG.Main


