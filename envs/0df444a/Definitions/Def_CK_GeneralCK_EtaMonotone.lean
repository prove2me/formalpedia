-- Prove2me | Definitions.Def_CK_GeneralCK_EtaMonotone
-- name    : CK_GeneralCK_EtaMonotone
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:20:32.107029+00:00
-- url     : https://prove2.me/theorems/317faadb-ea02-4fae-b72b-82a04921963a
-- title:
--   Courtade–Kumar proof module `GeneralCK.EtaMonotone` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.EtaMonotone` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.EtaMonotone` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.EtaMonotone (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EtaMonotone.lean)

import Definitions.Def_CK_GeneralCK_ProfileBasics

namespace GeneralCK

theorem entropyInverse_spec {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    0 ≤ entropyInverse h ∧ entropyInverse h ≤ 1 / 2 ∧ H (entropyInverse h) = h := by
  have himage := intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    H_continuous.continuousOn
  obtain ⟨v, hv, heq⟩ := himage (show h ∈ Set.Icc (H 0) (H (1 / 2)) by
    simpa only [H_zero, H_half, Set.mem_Icc] using And.intro h0 h1)
  rw [← heq, entropyInverse_H_lower hv.1 hv.2]
  exact ⟨hv.1, hv.2, rfl⟩

theorem entropyInverse_pos {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
    0 < entropyInverse h := by
  obtain ⟨hv, _, heq⟩ := entropyInverse_spec h0.le h1
  apply lt_of_le_of_ne hv
  intro he
  rw [← he, H_zero] at heq
  linarith

theorem entropyInverse_mono {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    entropyInverse a ≤ entropyInverse b := by
  obtain ⟨ha0, ha1, hea⟩ := entropyInverse_spec ha (hab.trans hb)
  obtain ⟨hb0, hb1, heb⟩ := entropyInverse_spec (ha.trans hab) hb
  by_contra hn
  have := H_strictMonoOn ⟨hb0, hb1⟩ ⟨ha0, ha1⟩ (lt_of_not_ge hn)
  rw [hea, heb] at this
  linarith

theorem J_nonneg {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1 / 2) : 0 ≤ J v := by
  apply div_nonneg _ log_two_pos.le
  apply Real.log_nonneg
  apply (le_div_iff₀ hv).2
  linarith

theorem J_antitone {u v : ℝ} (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u ≤ v) :
    J v ≤ J u := by
  have hv0 : 0 < v := hu.trans_le huv
  apply (div_le_div_iff_of_pos_right log_two_pos).2
  apply Real.log_le_log (div_pos (by linarith) hv0)
  apply (div_le_div_iff₀ hv0 hu).2
  nlinarith

theorem eta_eq_profile {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    eta h = (1 - 2 * entropyInverse h) * J (entropyInverse h) := by
  by_cases heq : h = 1
  · subst h
    have hv : entropyInverse 1 = 1 / 2 := by
      simpa only [H_half] using entropyInverse_H_lower (v := (1 / 2 : ℝ))
        (by norm_num) le_rfl
    simp [eta, hv]
  · simp [eta, heq]

theorem eta_antitoneOn : AntitoneOn eta (Set.Ioc 0 1) := by
  intro a ha b hb hab
  rw [eta_eq_profile ha.1.le ha.2, eta_eq_profile hb.1.le hb.2]
  have huv := entropyInverse_mono ha.1.le hb.2 hab
  have hu := entropyInverse_pos ha.1 ha.2
  have hv := entropyInverse_pos hb.1 hb.2
  have hu' := (entropyInverse_spec ha.1.le ha.2).2.1
  have hv' := (entropyInverse_spec hb.1.le hb.2).2.1
  exact mul_le_mul (by linarith) (J_antitone hu hv' huv)
    (J_nonneg hv hv') (by linarith)

end GeneralCK


