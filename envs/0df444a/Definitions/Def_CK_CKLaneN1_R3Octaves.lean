-- Prove2me | Definitions.Def_CK_CKLaneN1_R3Octaves
-- name    : CK_CKLaneN1_R3Octaves
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T11:41:36.421004+00:00
-- url     : https://prove2.me/theorems/e50f09e8-cfe3-4022-aa73-699fadb5f5c3
-- title:
--   Courtade–Kumar proof module `CKLaneN1.R3Octaves` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.R3Octaves` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.R3Octaves` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.R3Octaves (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/R3Octaves.lean)

import Definitions.Def_CK_CKLaneN1_R3Assembly

-- ===== source module CKLaneN1.R3Octaves =====
section

/-!
# Lane N1 — CE-stat row 3: octave dispatch over `[2^-17, 1/100)`

`cover_of_octaves` gives `CoverStmt` from `Sem` on the eleven dyadic octave roots
`octBox (2^-k) (2^-(k-1)) Y_k` (`k = 17 … 7`, written with literal numerals, matching the cover's
`root<k>` literals by `exact`) and the height side conditions `yupOK (2^-(k-1)) Y_k`.
CONDITIONAL adapter: the numeric cover (M07 `CKLaneM07.CE.R3Cover`) supplies the hypotheses.
-/

set_option autoImplicit false

namespace CKLaneN1.R3

open GeneralCK CKLaneN1

/-- **Octave dispatch** (conditional on the per-octave cover). -/
theorem cover_of_octaves (Y7 Y8 Y9 Y10 Y11 Y12 Y13 Y14 Y15 Y16 Y17 : ℚ)
    (s17 : Sem (octBox (1 / 131072) (1 / 65536) Y17)) (u17 : yupOK (1 / 65536) Y17 = true)
    (s16 : Sem (octBox (1 / 65536) (1 / 32768) Y16)) (u16 : yupOK (1 / 32768) Y16 = true)
    (s15 : Sem (octBox (1 / 32768) (1 / 16384) Y15)) (u15 : yupOK (1 / 16384) Y15 = true)
    (s14 : Sem (octBox (1 / 16384) (1 / 8192) Y14)) (u14 : yupOK (1 / 8192) Y14 = true)
    (s13 : Sem (octBox (1 / 8192) (1 / 4096) Y13)) (u13 : yupOK (1 / 4096) Y13 = true)
    (s12 : Sem (octBox (1 / 4096) (1 / 2048) Y12)) (u12 : yupOK (1 / 2048) Y12 = true)
    (s11 : Sem (octBox (1 / 2048) (1 / 1024) Y11)) (u11 : yupOK (1 / 1024) Y11 = true)
    (s10 : Sem (octBox (1 / 1024) (1 / 512) Y10)) (u10 : yupOK (1 / 512) Y10 = true)
    (s9 : Sem (octBox (1 / 512) (1 / 256) Y9)) (u9 : yupOK (1 / 256) Y9 = true)
    (s8 : Sem (octBox (1 / 256) (1 / 128) Y8)) (u8 : yupOK (1 / 128) Y8 = true)
    (s7 : Sem (octBox (1 / 128) (1 / 64) Y7)) (u7 : yupOK (1 / 64) Y7 = true) :
    CoverStmt := by
  intro a z y hlo hhi hz0 hz1 hy hc hA hret htc
  have ha : 0 < a := by linarith
  have go : ∀ {a0 a1 Y : ℚ}, Sem (octBox a0 a1 Y) → yupOK a1 Y = true → (a0 : ℝ) ≤ a →
      a ≤ (a1 : ℝ) → 0 ≤ CKLaneM07.CE.gapLB (H a) (H (a + z * y)) (a + y) :=
    fun hs hu h0 h1 => cover_octave hs hu h0 h1 ha hz0 hz1 hy hc hA hret htc
  by_cases h16 : a ≤ 1 / 65536
  · exact go s17 u17 (by push_cast; linarith) (by push_cast; linarith)
  by_cases h15 : a ≤ 1 / 32768
  · exact go s16 u16 (by push_cast; linarith) (by push_cast; linarith)
  by_cases h14 : a ≤ 1 / 16384
  · exact go s15 u15 (by push_cast; linarith) (by push_cast; linarith)
  by_cases h13 : a ≤ 1 / 8192
  · exact go s14 u14 (by push_cast; linarith) (by push_cast; linarith)
  by_cases h12 : a ≤ 1 / 4096
  · exact go s13 u13 (by push_cast; linarith) (by push_cast; linarith)
  by_cases h11 : a ≤ 1 / 2048
  · exact go s12 u12 (by push_cast; linarith) (by push_cast; linarith)
  by_cases h10 : a ≤ 1 / 1024
  · exact go s11 u11 (by push_cast; linarith) (by push_cast; linarith)
  by_cases h9 : a ≤ 1 / 512
  · exact go s10 u10 (by push_cast; linarith) (by push_cast; linarith)
  by_cases h8 : a ≤ 1 / 256
  · exact go s9 u9 (by push_cast; linarith) (by push_cast; linarith)
  by_cases h7 : a ≤ 1 / 128
  · exact go s8 u8 (by push_cast; linarith) (by push_cast; linarith)
  · exact go s7 u7 (by push_cast; linarith) (by push_cast; linarith)

/-- the full row-3 reduction to the per-octave cover (CONDITIONAL) -/
theorem transverse_of_octaves (Y7 Y8 Y9 Y10 Y11 Y12 Y13 Y14 Y15 Y16 Y17 : ℚ)
    (s17 : Sem (octBox (1 / 131072) (1 / 65536) Y17)) (u17 : yupOK (1 / 65536) Y17 = true)
    (s16 : Sem (octBox (1 / 65536) (1 / 32768) Y16)) (u16 : yupOK (1 / 32768) Y16 = true)
    (s15 : Sem (octBox (1 / 32768) (1 / 16384) Y15)) (u15 : yupOK (1 / 16384) Y15 = true)
    (s14 : Sem (octBox (1 / 16384) (1 / 8192) Y14)) (u14 : yupOK (1 / 8192) Y14 = true)
    (s13 : Sem (octBox (1 / 8192) (1 / 4096) Y13)) (u13 : yupOK (1 / 4096) Y13 = true)
    (s12 : Sem (octBox (1 / 4096) (1 / 2048) Y12)) (u12 : yupOK (1 / 2048) Y12 = true)
    (s11 : Sem (octBox (1 / 2048) (1 / 1024) Y11)) (u11 : yupOK (1 / 1024) Y11 = true)
    (s10 : Sem (octBox (1 / 1024) (1 / 512) Y10)) (u10 : yupOK (1 / 512) Y10 = true)
    (s9 : Sem (octBox (1 / 512) (1 / 256) Y9)) (u9 : yupOK (1 / 256) Y9 = true)
    (s8 : Sem (octBox (1 / 256) (1 / 128) Y8)) (u8 : yupOK (1 / 128) Y8 = true)
    (s7 : Sem (octBox (1 / 128) (1 / 64) Y7)) (u7 : yupOK (1 / 64) Y7 = true) :
    CKLaneN1.CEStat.TransverseCurvatureOwner :=
  transverse_of_cover (cover_of_octaves Y7 Y8 Y9 Y10 Y11 Y12 Y13 Y14 Y15 Y16 Y17
    s17 u17 s16 u16 s15 u15 s14 u14 s13 u13 s12 u12 s11 u11 s10 u10 s9 u9 s8 u8 s7 u7)

end CKLaneN1.R3

end


