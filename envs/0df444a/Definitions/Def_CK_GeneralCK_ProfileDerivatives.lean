-- Prove2me | Definitions.Def_CK_GeneralCK_ProfileDerivatives
-- name    : CK_GeneralCK_ProfileDerivatives
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:24:34.100135+00:00
-- url     : https://prove2.me/theorems/86e9b754-6270-4b9c-9738-b41af4b10ca7
-- title:
--   Courtade–Kumar proof module `GeneralCK.ProfileDerivatives` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ProfileDerivatives` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ProfileDerivatives` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ProfileDerivatives (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ProfileDerivatives.lean)

import Definitions.Def_CK_GeneralCK_EntropyComparison
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity

namespace GeneralCK
open Set Filter
open scoped Topology

theorem entropyInverse_lt_half {h : ℝ} (h0 : 0 ≤ h) (h1 : h < 1) :
    entropyInverse h < 1 / 2 := by
  obtain ⟨_, hv, heq⟩ := entropyInverse_spec h0 h1.le
  apply lt_of_le_of_ne hv
  intro hh
  rw [hh, H_half] at heq
  linarith

theorem entropyInverse_strictMonoOn : StrictMonoOn entropyInverse (Icc 0 1) := by
  intro a ha b hb hab
  apply lt_of_le_of_ne (entropyInverse_mono ha.1 hb.2 hab.le)
  intro he
  have h := congrArg H he
  rw [(entropyInverse_spec ha.1 ha.2).2.2, (entropyInverse_spec hb.1 hb.2).2.2] at h
  exact ne_of_lt hab h

theorem entropyInverse_image : entropyInverse '' Icc 0 1 = Icc 0 (1 / 2) := by
  ext v
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨(entropyInverse_spec hh.1 hh.2).1, (entropyInverse_spec hh.1 hh.2).2.1⟩
  · intro hv
    exact ⟨H v, ⟨H_nonneg hv.1 (by linarith [hv.2]), H_le_one v⟩,
      entropyInverse_H_lower hv.1 hv.2⟩

theorem continuousAt_entropyInverse {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    ContinuousAt entropyInverse h := by
  apply entropyInverse_strictMonoOn.continuousAt_of_image_mem_nhds
    (Icc_mem_nhds h0 h1)
  rw [entropyInverse_image]
  exact Icc_mem_nhds (entropyInverse_pos h0 h1.le) (entropyInverse_lt_half h0.le h1)

theorem J_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) : 0 < J v := by
  apply div_pos _ log_two_pos
  apply Real.log_pos
  apply (lt_div_iff₀ hv).2
  linarith

theorem hasDerivAt_entropyInverse {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    HasDerivAt entropyInverse (1 / J (entropyInverse h)) h := by
  have hv := entropyInverse_pos h0 h1.le
  have hv' := entropyInverse_lt_half h0.le h1
  have hd := (Comparison.hasDerivAt_H hv (by linarith)).of_local_left_inverse
    (continuousAt_entropyInverse h0 h1) (ne_of_gt (J_pos hv hv')) (by
      filter_upwards [Ioo_mem_nhds h0 h1] with y hy
      exact (entropyInverse_spec hy.1.le hy.2.le).2.2)
  simpa only [one_div] using hd

theorem hasDerivAt_J {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt J (-1 / (Real.log 2 * v * (1 - v))) v := by
  have hv1 : 1 - v ≠ 0 := by linarith
  have hlog : J =ᶠ[𝓝 v] (fun p => (Real.log (1 - p) - Real.log p) / Real.log 2) := by
    filter_upwards [Ioo_mem_nhds hv hv'] with p hp
    simp only [J, Real.log_div (by linarith [hp.2] : 1 - p ≠ 0) (ne_of_gt hp.1)]
  have hd := (((hasDerivAt_id v).const_sub 1).log (by simpa using hv1)).sub
    ((hasDerivAt_id v).log (ne_of_gt hv))
  have hd' := (hd.div_const (Real.log 2)).congr_of_eventuallyEq hlog
  convert! hd' using 1
  simp only [id_eq]
  field_simp [hv1]
  ring

/-- First entropy-coordinate derivative of the scalar production profile. -/
theorem hasDerivAt_eta {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    HasDerivAt eta
      (-2 - (1 - 2 * entropyInverse h) /
        (Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h))) h := by
  have hv := entropyInverse_pos h0 h1.le
  have hv' := entropyInverse_lt_half h0.le h1
  have hJ : J (entropyInverse h) ≠ 0 := ne_of_gt (J_pos hv hv')
  have hi := hasDerivAt_entropyInverse h0 h1
  have hd := (hi.const_mul 2).const_sub 1 |>.mul
    ((hasDerivAt_J hv (by linarith)).comp h hi)
  have heq : eta =ᶠ[𝓝 h] (fun y => (1 - 2 * entropyInverse y) * J (entropyInverse y)) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with y hy
    exact eta_eq_profile hy.1.le hy.2.le
  have hd' := hd.congr_of_eventuallyEq heq
  convert! hd' using 1
  simp only [Function.comp_apply]
  field_simp [hJ]
  ring

theorem deriv_entropyInverse {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    deriv entropyInverse h = 1 / J (entropyInverse h) :=
  (hasDerivAt_entropyInverse h0 h1).deriv

theorem deriv_J {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    deriv J v = -1 / (Real.log 2 * v * (1 - v)) :=
  (hasDerivAt_J hv hv').deriv

theorem deriv_eta {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    deriv eta h = -2 - (1 - 2 * entropyInverse h) /
      (Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h)) :=
  (hasDerivAt_eta h0 h1).deriv

end GeneralCK


