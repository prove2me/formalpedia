-- Prove2me | Definitions.Def_CK_CKLaneA1_R5Assembly
-- name    : CK_CKLaneA1_R5Assembly
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T14:27:37.78532+00:00
-- url     : https://prove2.me/theorems/c53df48b-b34d-474c-8428-072cdd0001d6
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5Assembly` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5Assembly` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5Assembly` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5Assembly (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5Assembly.lean)

import Definitions.Def_CK_CKLaneA1_R5Corner
import Definitions.Def_CK_CKLaneA1_R5Tail

-- ===== source module CKLaneA1.R5Assembly =====
section

/-!
# CKLaneA1.R5Assembly — CE-stat row 5 from a checked cover

`highTC_of_cover`: a checked (`stripOK`), chained (`chainOK T0N`) strip list implies
`CKLaneN1.CEStat.HighTCExclusion`.  At a retained stationary Case-E point with `t_C ≥ 1/100`
(`chart_point`, `chart_ids`) `D(A, W, λ) = 0`, but `D > 0` by `tail_sound` (`A ≥ 4`), `corner_sound`
(`t_C ≥ 11/32 + 2A`, hence `a ≥ 11/32`), or `cover_sound` (otherwise).
-/

set_option autoImplicit false

namespace CKLaneA1.R5

open GeneralCK GeneralCK.Certificates.Mixed CKLaneP Set CKLaneN1.CEStat

/-- **CE-stat S.3 row 5 from a checked cover.** -/
theorem highTC_of_cover (l : List Strip) (hall : l.all stripOK = true) (hch : chainOK T0N l = true) :
    HighTCExclusion := by
  intro e f c hp ht
  have hcp := chart_point hp ht
  simp only at hcp
  obtain ⟨ha, hat, htc, hc, hHa, he, hf, hcont, ht1, hD⟩ := hcp
  obtain ⟨hW, hL, hcase⟩ := chart_ids ha hat htc hc hHa he hf hcont
  have hef : e < f := hp.1.2.1
  have hf1 : f ≤ 1 := hp.1.2.2.1
  have hbc : entropyInverse f < c := hp.1.2.2.2.1
  set a := entropyInverse e with ha_def
  set t := chartTC f c with ht_def
  have hE0 : 0 < e + f := by linarith
  have hA0 : 0 < (c - a) / (e + f) := div_pos (by linarith) hE0
  have hlam0 : 0 < f / (e + f) := div_pos hf hE0
  have hlam1 : f / (e + f) < 1 := by rw [div_lt_one hE0]; linarith
  have P : PtFacts a t ((c - a) / (e + f)) ((1 - 2 * c) / (2 * f)) (f / (e + f)) :=
    ⟨ha, hat, by linarith, hA0, hlam0, hlam1, hW, hL, hcase⟩
  by_cases hA4 : 4 ≤ (c - a) / (e + f)
  · have := tail_sound P ht1 hA4
    linarith
  by_cases hcor : 11 / 32 + 2 * ((c - a) / (e + f)) ≤ t
  · have hE2 : e + f ≤ 2 := by
      have := H_le_one a
      rw [hHa] at this
      linarith
    have hAE : (c - a) / (e + f) * (e + f) = c - a := div_mul_cancel₀ _ hE0.ne'
    have hle := mul_le_mul_of_nonneg_left hE2 hA0.le
    have ha11 : 11 / 32 ≤ a := by linarith
    have hfc : f < H c := by
      obtain ⟨hb0, -, hHb⟩ := entropyInverse_spec hf.le hf1
      calc f = H (entropyInverse f) := hHb.symm
        _ < H c := H_lt hb0 hbc hc.le
    have := corner_sound ha (hat.trans htc) hc hHa hef hf1 hfc ha11
    linarith
  · have hT0 : ((dyq T0N : ℚ) : ℝ) ≤ t := by
      refine le_trans ?_ ht1
      unfold dyq T0N; push_cast; norm_num
    have := cover_sound l hall hch P hT0 (lt_of_not_ge hA4)
      (lt_of_not_ge hcor)
    linarith

#print axioms highTC_of_cover

end CKLaneA1.R5

end


