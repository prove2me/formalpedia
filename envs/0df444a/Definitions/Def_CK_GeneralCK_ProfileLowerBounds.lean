-- Prove2me | Definitions.Def_CK_GeneralCK_ProfileLowerBounds
-- name    : CK_GeneralCK_ProfileLowerBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:27:53.638055+00:00
-- url     : https://prove2.me/theorems/871bf969-1465-4ba4-8983-2c39c97cbff3
-- title:
--   Courtade–Kumar proof module `GeneralCK.ProfileLowerBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ProfileLowerBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ProfileLowerBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ProfileLowerBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ProfileLowerBounds.lean)

import Definitions.Def_CK_GeneralCK_ProfileConvexity

namespace GeneralCK.Scalar
open Set

/-- An elementary logit inequality that controls the slope of `P`. -/
theorem logit_slope_bound {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1 / 2) :
    2 * v * (1 - v) * Real.log 2 * J v ≤ 1 - 2 * v := by
  let g : ℝ → ℝ := fun u => 1 - 2 * u - 2 * u * (1 - u) * Real.log 2 * J u
  have hd : ∀ u ∈ Ioc (0 : ℝ) (1 / 2),
      HasDerivAt g (-2 * (1 - 2 * u) * Real.log 2 * J u) u := by
    intro u hu
    have hu1 : u < 1 := by linarith [hu.2]
    have h := (((hasDerivAt_id u).const_mul 2).const_sub 1).sub
      (((((hasDerivAt_id u).const_mul 2).mul
        ((hasDerivAt_id u).const_sub 1)).mul_const (Real.log 2)).mul
        (hasDerivAt_J hu.1 hu1))
    convert! h using 1
    dsimp
    field_simp [hu.1.ne', show 1 - u ≠ 0 by linarith, log_two_pos.ne']
    ring
  have hm : AntitoneOn g (Ioc 0 (1 / 2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 (1 / 2))
      (f' := fun u => -2 * (1 - 2 * u) * Real.log 2 * J u)
    · intro u hu
      exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu
      exact (hd u (interior_subset hu)).hasDerivWithinAt
    · intro u hu
      have hu' := interior_subset hu
      have hj := J_nonneg hu'.1 hu'.2
      have hr : 0 ≤ 1 - 2 * u := by linarith [hu'.2]
      have hpos : 0 ≤ 2 * (1 - 2 * u) * Real.log 2 * J u := by positivity
      nlinarith
  have hh : g (1 / 2) = 0 := by norm_num [g, J]
  have h := hm ⟨hv, hv'⟩ ⟨by norm_num, le_rfl⟩ hv'
  rw [hh] at h
  dsimp [g] at h
  linarith

/-- The ordinary derivative is asserted only in the physical interior. -/
theorem hasDerivAt_P {I : ℝ} (hI : 0 < I) (hI' : I < 1) :
    HasDerivAt P
      (2 + (1 - 2 * entropyInverse (1 - I)) /
        (Real.log 2 * entropyInverse (1 - I) * (1 - entropyInverse (1 - I)) *
          J (entropyInverse (1 - I)))) I := by
  have hd := (hasDerivAt_eta (by linarith : 0 < 1 - I) (by linarith : 1 - I < 1)).comp I
    ((hasDerivAt_id I).const_sub 1)
  convert! hd using 1
  ring

theorem deriv_P {I : ℝ} (hI : 0 < I) (hI' : I < 1) :
    deriv P I = 2 + (1 - 2 * entropyInverse (1 - I)) /
      (Real.log 2 * entropyInverse (1 - I) * (1 - entropyInverse (1 - I)) *
        J (entropyInverse (1 - I))) := (hasDerivAt_P hI hI').deriv

theorem four_le_deriv_P {I : ℝ} (hI : 0 < I) (hI' : I < 1) : 4 ≤ deriv P I := by
  have hv := entropyInverse_pos (show 0 < 1 - I by linarith) (show 1 - I ≤ 1 by linarith)
  have hv' := entropyInverse_lt_half (show 0 ≤ 1 - I by linarith) (show 1 - I < 1 by linarith)
  have hJ := J_pos hv hv'
  have hvc : 0 < 1 - entropyInverse (1 - I) := by linarith
  have hD : 0 < Real.log 2 * entropyInverse (1 - I) * (1 - entropyInverse (1 - I)) *
      J (entropyInverse (1 - I)) := by positivity
  have hbound := logit_slope_bound hv hv'.le
  rw [deriv_P hI hI']
  have hr : 2 ≤ (1 - 2 * entropyInverse (1 - I)) /
      (Real.log 2 * entropyInverse (1 - I) * (1 - entropyInverse (1 - I)) *
        J (entropyInverse (1 - I))) := (le_div_iff₀ hD).2 (by nlinarith)
  linarith

theorem P_continuousOn : ContinuousOn P (Ico 0 1) := by
  apply eta_continuousOn.comp (continuous_const.sub continuous_id).continuousOn
  intro I hI
  change 0 < 1 - I ∧ 1 - I ≤ 1
  constructor <;> linarith [hI.1, hI.2]

@[simp] theorem P_zero : P 0 = 0 := by simp [P]

/-- The slope lower bound extends to increments based at zero by continuity,
without making an assertion about a two-sided derivative at zero. -/
theorem P_sub_four_mul_monotone : MonotoneOn (fun I => P I - 4 * I) (Ico 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
    (f' := fun I => deriv P I - 4)
  · exact P_continuousOn.sub (continuous_const.mul continuous_id).continuousOn
  · intro I hI
    rw [interior_Ico] at hI
    have hd := (hasDerivAt_P hI.1 hI.2).sub ((hasDerivAt_id I).const_mul 4)
    rw [← deriv_P hI.1 hI.2] at hd
    convert! hd.hasDerivWithinAt using 1
    simp
  · intro I hI
    rw [interior_Ico] at hI
    linarith [four_le_deriv_P hI.1 hI.2]

theorem P_increment_lower {a b : ℝ} (ha : 0 ≤ a) (hb : b < 1) (hab : a ≤ b) :
    4 * (b - a) ≤ P b - P a := by
  have h := P_sub_four_mul_monotone ⟨ha, hab.trans_lt hb⟩ ⟨ha.trans hab, hb⟩ hab
  linarith

theorem four_mul_le_P {I : ℝ} (hI : 0 ≤ I) (hI' : I < 1) : 4 * I ≤ P I := by
  simpa using P_increment_lower (a := 0) le_rfl hI' hI

end GeneralCK.Scalar


