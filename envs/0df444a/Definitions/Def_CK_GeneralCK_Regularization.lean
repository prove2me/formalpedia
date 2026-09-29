-- Prove2me | Definitions.Def_CK_GeneralCK_Regularization
-- name    : CK_GeneralCK_Regularization
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:20:36.663331+00:00
-- url     : https://prove2.me/theorems/92549546-77c9-480f-b0e0-240734b20744
-- title:
--   Courtade–Kumar proof module `GeneralCK.Regularization` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Regularization` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Regularization` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Regularization (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Regularization.lean)

import Definitions.Def_CK_GeneralCK_InformationIdentity
import Mathlib.Tactic.FunProp
import Definitions.Def_GeneralCK_regularization

namespace GeneralCK.Regularization
open scoped BigOperators

theorem kernel_continuous {n : ℕ} (x y : Cube n) :
    Continuous (fun p => noiseKernel p x y) := by
  unfold noiseKernel
  apply continuous_finsetProd
  intro i _
  split_ifs <;> fun_prop

theorem posterior_continuous {n : ℕ} (f : Cube n → Bool) (y : Cube n) :
    Continuous (fun p => Information.posterior f p y) := by
  unfold Information.posterior
  apply continuous_finsetSum
  intro x _
  split_ifs
  · exact kernel_continuous x y
  · fun_prop

theorem mutualInformation_continuous {n : ℕ} (f : Cube n → Bool) :
    Continuous (mutualInformation f) := by
  change Continuous (fun p => mutualInformation f p)
  simp_rw [Information.mutualInformation_eq]
  apply Continuous.sub continuous_const
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro y _
  exact H_continuous.comp (posterior_continuous f y)







theorem kernel_complement {n : ℕ} (p : ℝ) (x y : Cube n) :
    noiseKernel (1 - p) x y = noiseKernel p x (complementEquiv n y) := by
  apply Finset.prod_congr rfl
  intro i _
  change (if x i = y i then 1 - (1 - p) else 1 - p) =
    (if x i = !(y i) then 1 - p else p)
  cases x i <;> cases y i <;> simp

theorem posterior_complement {n : ℕ} (f : Cube n → Bool) (p : ℝ) (y : Cube n) :
    Information.posterior f (1 - p) y =
      Information.posterior f p (complementEquiv n y) := by
  simp only [Information.posterior, kernel_complement]

theorem mutualInformation_complement {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    mutualInformation f (1 - p) = mutualInformation f p := by
  simp only [Information.mutualInformation_eq, posterior_complement]
  rw [Equiv.sum_comp (complementEquiv n) (fun y => H (Information.posterior f p y))]

theorem mutualInformation_le_one {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : mutualInformation f p ≤ 1 := by
  rw [Information.mutualInformation_eq]
  have hsum : 0 ≤ ∑ y, H (Information.posterior f p y) := by
    apply Finset.sum_nonneg
    intro y _
    exact H_nonneg (Information.posterior_nonneg f hp hp' y)
      (Information.posterior_le_one f hp hp' y)
  have hw : 0 ≤ Information.cubeWeight n := by unfold Information.cubeWeight; positivity
  have := mul_nonneg hw hsum
  have := H_le_one (Information.meanIndicator f)
  linarith

theorem CK_zero {n : ℕ} (f : Cube n → Bool) : mutualInformation f 0 ≤ 1 - H 0 := by
  simpa using mutualInformation_le_one f (p := 0) (by norm_num) (by norm_num)

theorem CK_one {n : ℕ} (f : Cube n → Bool) : mutualInformation f 1 ≤ 1 - H 1 := by
  simpa using mutualInformation_le_one f (p := 1) (by norm_num) (by norm_num)

/-- Symmetry and the elementary endpoints reduce CK to strictly positive
crossover below one half. -/
theorem CK_of_open_lower_half
    (h : ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ),
      0 < p → p < 1 / 2 → mutualInformation f p ≤ 1 - H p) :
    GeneralCourtadeKumar := by
  intro n f p hp hp'
  by_cases hzero : p = 0
  · subst p; exact CK_zero f
  by_cases hone : p = 1
  · subst p; exact CK_one f
  by_cases hhalf : p = 1 / 2
  · subst p
    rw [Information.mutualInformation_half, H_half]
    norm_num
  by_cases hlower : p < 1 / 2
  · exact h n f p (lt_of_le_of_ne hp (Ne.symm hzero)) hlower
  · have hpstrict : p < 1 := lt_of_le_of_ne hp' hone
    have hphalf : 1 / 2 < p := lt_of_le_of_ne (le_of_not_gt hlower) (Ne.symm hhalf)
    have hc := h n f (1 - p) (by linarith) (by linarith)
    simpa only [mutualInformation_complement, H_complement] using hc

end GeneralCK.Regularization


