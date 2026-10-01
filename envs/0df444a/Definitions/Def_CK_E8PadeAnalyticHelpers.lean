-- Prove2me | Definitions.Def_CK_E8PadeAnalyticHelpers
-- name    : CK_E8PadeAnalyticHelpers
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:00:54.153068+00:00
-- url     : https://prove2.me/theorems/34acf953-6d96-42c9-8eea-791d9c3d02d1
-- title:
--   Courtade–Kumar proof module `E8PadeAnalyticHelpers` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8PadeAnalyticHelpers` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8PadeAnalyticHelpers` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8PadeAnalyticHelpers (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8PadeAnalyticHelpers.lean)

import Definitions.Def_CK_E8CompactQuadraticSign

-- ===== source module E8PadeAnalyticHelpers =====
section

namespace GeneralCK.E8RatioMonotonicity

open Set Filter
open Certificates.E8TAxisStableScalar

noncomputable def padeLogGap (u : ℝ) : ℝ :=
  u * (2 + u) / (2 * (1 + u)) - Real.log (1 + u)

theorem hasDerivAt_padeLogGap {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt padeLogGap (u ^ 2 / (2 * (1 + u) ^ 2)) u := by
  have h1 : 1 + u ≠ 0 := by linarith
  have h2 : 2 * (1 + u) ≠ 0 := by positivity
  have hi := hasDerivAt_id u
  have hn := hi.mul ((hasDerivAt_const u 2).add hi)
  have hd := (hasDerivAt_const u 2).mul ((hasDerivAt_const u 1).add hi)
  have hl := ((hasDerivAt_const u 1).add hi).log h1
  have hf := (hn.div hd h2).sub hl
  convert! hf using 1
  simp only [Pi.mul_apply, Pi.add_apply, id_eq]
  field_simp [h1]
  ring

/-- The rational upper bound for the logarithm used by the Padé tail. -/
theorem log_one_add_le_pade {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ u * (2 + u) / (2 * (1 + u)) := by
  have hm : MonotoneOn padeLogGap (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x hx
      exact (hasDerivAt_padeLogGap hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_padeLogGap (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hasDerivAt_padeLogGap (interior_subset hx)).deriv]
      positivity
  have hh := hm (show (0 : ℝ) ∈ Ici 0 by simp) hu hu
  simpa [padeLogGap] using hh

theorem twenty_le_exp_three : (20 : ℝ) ≤ Real.exp 3 := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  linarith

theorem z_le_one_twentieth_of_three_halves {a : ℝ} (ha : 3 / 2 ≤ a) :
    z a ≤ 1 / 20 := by
  have hexp : (20 : ℝ) ≤ Real.exp (2 * a) :=
    twenty_le_exp_three.trans (Real.exp_le_exp.mpr (by linarith))
  have hid : z a * Real.exp (2 * a) = 1 := by
    rw [z, ← Real.exp_add]
    norm_num
  have hh := mul_le_mul_of_nonneg_left hexp (z_pos a).le
  rw [hid] at hh
  linarith

#print axioms log_one_add_le_pade
#print axioms twenty_le_exp_three
#print axioms z_le_one_twentieth_of_three_halves

end GeneralCK.E8RatioMonotonicity

end


