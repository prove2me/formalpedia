-- Prove2me | Definitions.Def_CK_GeneralCK_Distribution
-- name    : CK_GeneralCK_Distribution
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:17:31.184237+00:00
-- url     : https://prove2.me/theorems/49e7e66d-8972-4dda-bfc1-b59dcf398007
-- title:
--   Courtade–Kumar proof module `GeneralCK.Distribution` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Distribution` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Distribution` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Distribution (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Distribution.lean)

import Definitions.Def_CK_GeneralCK_Statement

namespace GeneralCK
open scoped BigOperators

theorem noiseKernel_nonneg {n : ℕ} {p : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1)
    (x y : Cube n) : 0 ≤ noiseKernel p x y := by
  unfold noiseKernel
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

/-- Exact normalization of the independently flipped output coordinates. -/
theorem noiseKernel_sum {n : ℕ} (p : ℝ) (x : Cube n) :
    ∑ y, noiseKernel p x y = 1 := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
    (fun i b => if x i = b then 1 - p else p)
  have hb (i : Fin n) : (∑ b : Bool, if x i = b then 1 - p else p) = 1 := by
    cases x i <;> simp
  simpa only [noiseKernel, Fintype.piFinset_univ, hb, Finset.prod_const_one] using h.symm

theorem jointMass_nonneg {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (h₀ : 0 ≤ p) (h₁ : p ≤ 1) (b : Bool) (y : Cube n) :
    0 ≤ jointMass f p b y := by
  unfold jointMass
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact noiseKernel_nonneg h₀ h₁ x y
  · exact le_rfl

theorem jointMass_sum {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    ∑ b, ∑ y, jointMass f p b y = 1 := by
  classical
  have hb (x y : Cube n) :
      (∑ b : Bool, if f x = b then noiseKernel p x y else 0) = noiseKernel p x y := by
    cases f x <;> simp
  simp only [jointMass, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; arg 2; ext y; rw [Finset.sum_comm]
  simp only [hb]
  rw [Finset.sum_comm]
  simp [noiseKernel_sum, Cube, zpow_neg, zpow_natCast]

end GeneralCK


