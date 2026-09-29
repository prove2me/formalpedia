-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S04
-- name    : CK_CKLaneC2R_CompactCover_S04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T10:52:12.697852+00:00
-- url     : https://prove2.me/theorems/d982f284-1502-4d8d-ba48-1726792ea70c
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S04` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S04` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S04` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S04 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S04.lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S04_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B003
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B015
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S04_B018

-- ===== source module CKLaneC2R.CompactCover.S04 =====
section

namespace CKLaneC2R.CompactCover

/-- Compact cover of strip 4: a ∈ [7/10,9/10], z ∈ [43/500,999/1000] (374 cells, BSP depth 13). -/
theorem strip4 {a z : ℝ} (ha1 : ((7/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((9/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h0 : a ≤ ((4/5 : ℚ) : ℝ)
  · -- left
    by_cases h1 : a ≤ ((3/4 : ℚ) : ℝ)
    · -- left
      by_cases h2 : a ≤ ((29/40 : ℚ) : ℝ)
      · -- left
        by_cases h3 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h4 : z ≤ ((1257/4000 : ℚ) : ℝ)
          · -- left
            by_cases h5 : z ≤ ((1601/8000 : ℚ) : ℝ)
            · -- left
              by_cases h6 : z ≤ ((2289/16000 : ℚ) : ℝ)
              · -- left
                by_cases h7 : z ≤ ((733/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h8 : z ≤ ((6417/64000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B008.c173_pos ha1 h2 hz1 h8
                  · -- right
                    exact CKLaneC2R.Cells.S04.B008.c174_pos ha1 h2 (not_le.mp h8).le h7
                · -- right
                  by_cases h9 : a ≤ ((57/80 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B008.c175_pos ha1 h9 (not_le.mp h7).le h6
                  · -- right
                    exact CKLaneC2R.Cells.S04.B008.c176_pos (not_le.mp h9).le h2 (not_le.mp h7).le h6
              · -- right
                by_cases h10 : z ≤ ((5491/32000 : ℚ) : ℝ)
                · -- left
                  by_cases h11 : a ≤ ((57/80 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B009.c181_pos ha1 h11 (not_le.mp h6).le h10
                  · -- right
                    exact CKLaneC2R.Cells.S04.B009.c182_pos (not_le.mp h11).le h2 (not_le.mp h6).le h10
                · -- right
                  exact CKLaneC2R.Cells.S04.B001.c20_pos ha1 h2 (not_le.mp h10).le h5
            · -- right
              by_cases h12 : z ≤ ((823/3200 : ℚ) : ℝ)
              · -- left
                by_cases h13 : z ≤ ((7317/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B001.c27_pos ha1 h2 (not_le.mp h5).le h13
                · -- right
                  exact CKLaneC2R.Cells.S04.B001.c28_pos ha1 h2 (not_le.mp h13).le h12
              · -- right
                by_cases h14 : z ≤ ((9143/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B001.c31_pos ha1 h2 (not_le.mp h12).le h14
                · -- right
                  exact CKLaneC2R.Cells.S04.B001.c32_pos ha1 h2 (not_le.mp h14).le h4
          · -- right
            by_cases h15 : z ≤ ((3427/8000 : ℚ) : ℝ)
            · -- left
              by_cases h16 : z ≤ ((5941/16000 : ℚ) : ℝ)
              · -- left
                by_cases h17 : z ≤ ((10969/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B003.c70_pos ha1 h2 (not_le.mp h4).le h17
                · -- right
                  exact CKLaneC2R.Cells.S04.B003.c71_pos ha1 h2 (not_le.mp h17).le h16
              · -- right
                by_cases h18 : a ≤ ((57/80 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B003.c72_pos ha1 h18 (not_le.mp h16).le h15
                · -- right
                  exact CKLaneC2R.Cells.S04.B003.c73_pos (not_le.mp h18).le h2 (not_le.mp h16).le h15
            · -- right
              by_cases h19 : z ≤ ((7767/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S04.B000.c4_pos ha1 h2 (not_le.mp h15).le h19
              · -- right
                exact CKLaneC2R.Cells.S04.B000.c5_pos ha1 h2 (not_le.mp h19).le h3
        · -- right
          by_cases h20 : z ≤ ((3083/4000 : ℚ) : ℝ)
          · -- left
            by_cases h21 : a ≤ ((57/80 : ℚ) : ℝ)
            · -- left
              by_cases h22 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h23 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B004.c94_pos ha1 h21 (not_le.mp h3).le h23
                · -- right
                  exact CKLaneC2R.Cells.S04.B004.c96_pos ha1 h21 (not_le.mp h23).le h22
              · -- right
                by_cases h24 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B005.c102_pos ha1 h21 (not_le.mp h22).le h24
                · -- right
                  exact CKLaneC2R.Cells.S04.B005.c104_pos ha1 h21 (not_le.mp h24).le h20
            · -- right
              by_cases h25 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h26 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B004.c95_pos (not_le.mp h21).le h2 (not_le.mp h3).le h26
                · -- right
                  exact CKLaneC2R.Cells.S04.B004.c97_pos (not_le.mp h21).le h2 (not_le.mp h26).le h25
              · -- right
                by_cases h27 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B005.c103_pos (not_le.mp h21).le h2 (not_le.mp h25).le h27
                · -- right
                  exact CKLaneC2R.Cells.S04.B005.c105_pos (not_le.mp h21).le h2 (not_le.mp h27).le h20
          · -- right
            by_cases h28 : z ≤ ((7079/8000 : ℚ) : ℝ)
            · -- left
              by_cases h29 : z ≤ ((2649/3200 : ℚ) : ℝ)
              · -- left
                by_cases h30 : z ≤ ((25577/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B007.c158_pos ha1 h2 (not_le.mp h20).le h30
                · -- right
                  exact CKLaneC2R.Cells.S04.B007.c159_pos ha1 h2 (not_le.mp h30).le h29
              · -- right
                by_cases h31 : z ≤ ((27403/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B008.c162_pos ha1 h2 (not_le.mp h29).le h31
                · -- right
                  exact CKLaneC2R.Cells.S04.B008.c163_pos ha1 h2 (not_le.mp h31).le h28
            · -- right
              by_cases h32 : z ≤ ((15071/16000 : ℚ) : ℝ)
              · -- left
                by_cases h33 : a ≤ ((57/80 : ℚ) : ℝ)
                · -- left
                  by_cases h34 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B011.c235_pos ha1 h33 (not_le.mp h28).le h34
                  · -- right
                    exact CKLaneC2R.Cells.S04.B011.c237_pos ha1 h33 (not_le.mp h34).le h32
                · -- right
                  by_cases h35 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B011.c236_pos (not_le.mp h33).le h2 (not_le.mp h28).le h35
                  · -- right
                    exact CKLaneC2R.Cells.S04.B011.c238_pos (not_le.mp h33).le h2 (not_le.mp h35).le h32
              · -- right
                by_cases h36 : z ≤ ((6211/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h37 : z ≤ ((61197/64000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B013.c264_pos ha1 h2 (not_le.mp h32).le h37
                  · -- right
                    by_cases h38 : a ≤ ((57/80 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B013.c272_pos ha1 h38 (not_le.mp h37).le h36
                    · -- right
                      exact CKLaneC2R.Cells.S04.B013.c273_pos (not_le.mp h38).le h2 (not_le.mp h37).le h36
                · -- right
                  by_cases h39 : z ≤ ((63023/64000 : ℚ) : ℝ)
                  · -- left
                    by_cases h40 : a ≤ ((57/80 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B014.c284_pos ha1 h40 (not_le.mp h36).le h39
                    · -- right
                      exact CKLaneC2R.Cells.S04.B014.c285_pos (not_le.mp h40).le h2 (not_le.mp h36).le h39
                  · -- right
                    by_cases h41 : z ≤ ((126959/128000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B014.c292_pos ha1 h2 (not_le.mp h39).le h41
                    · -- right
                      by_cases h42 : z ≤ ((254831/256000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B016.c321_pos ha1 h2 (not_le.mp h41).le h42
                      · -- right
                        by_cases h43 : z ≤ ((20423/20480 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B016.c335_pos ha1 h2 (not_le.mp h42).le h43
                        · -- right
                          exact CKLaneC2R.Cells.S04.B016.c336_pos ha1 h2 (not_le.mp h43).le hz2
      · -- right
        by_cases h44 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h45 : z ≤ ((1257/4000 : ℚ) : ℝ)
          · -- left
            by_cases h46 : z ≤ ((1601/8000 : ℚ) : ℝ)
            · -- left
              by_cases h47 : z ≤ ((2289/16000 : ℚ) : ℝ)
              · -- left
                by_cases h48 : z ≤ ((733/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h49 : z ≤ ((6417/64000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B008.c177_pos (not_le.mp h2).le h1 hz1 h49
                  · -- right
                    exact CKLaneC2R.Cells.S04.B008.c178_pos (not_le.mp h2).le h1 (not_le.mp h49).le h48
                · -- right
                  by_cases h50 : a ≤ ((59/80 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B008.c179_pos (not_le.mp h2).le h50 (not_le.mp h48).le h47
                  · -- right
                    exact CKLaneC2R.Cells.S04.B009.c180_pos (not_le.mp h50).le h1 (not_le.mp h48).le h47
              · -- right
                by_cases h51 : z ≤ ((5491/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B001.c21_pos (not_le.mp h2).le h1 (not_le.mp h47).le h51
                · -- right
                  exact CKLaneC2R.Cells.S04.B001.c22_pos (not_le.mp h2).le h1 (not_le.mp h51).le h46
            · -- right
              by_cases h52 : z ≤ ((823/3200 : ℚ) : ℝ)
              · -- left
                by_cases h53 : z ≤ ((7317/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B001.c29_pos (not_le.mp h2).le h1 (not_le.mp h46).le h53
                · -- right
                  exact CKLaneC2R.Cells.S04.B001.c30_pos (not_le.mp h2).le h1 (not_le.mp h53).le h52
              · -- right
                by_cases h54 : z ≤ ((9143/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B001.c33_pos (not_le.mp h2).le h1 (not_le.mp h52).le h54
                · -- right
                  exact CKLaneC2R.Cells.S04.B001.c34_pos (not_le.mp h2).le h1 (not_le.mp h54).le h45
          · -- right
            by_cases h55 : z ≤ ((3427/8000 : ℚ) : ℝ)
            · -- left
              by_cases h56 : z ≤ ((5941/16000 : ℚ) : ℝ)
              · -- left
                by_cases h57 : z ≤ ((10969/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B003.c74_pos (not_le.mp h2).le h1 (not_le.mp h45).le h57
                · -- right
                  exact CKLaneC2R.Cells.S04.B003.c75_pos (not_le.mp h2).le h1 (not_le.mp h57).le h56
              · -- right
                exact CKLaneC2R.Cells.S04.B000.c0_pos (not_le.mp h2).le h1 (not_le.mp h56).le h55
            · -- right
              by_cases h58 : z ≤ ((7767/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S04.B000.c6_pos (not_le.mp h2).le h1 (not_le.mp h55).le h58
              · -- right
                exact CKLaneC2R.Cells.S04.B000.c7_pos (not_le.mp h2).le h1 (not_le.mp h58).le h44
        · -- right
          by_cases h59 : z ≤ ((3083/4000 : ℚ) : ℝ)
          · -- left
            by_cases h60 : a ≤ ((59/80 : ℚ) : ℝ)
            · -- left
              by_cases h61 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h62 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B004.c98_pos (not_le.mp h2).le h60 (not_le.mp h44).le h62
                · -- right
                  exact CKLaneC2R.Cells.S04.B005.c100_pos (not_le.mp h2).le h60 (not_le.mp h62).le h61
              · -- right
                by_cases h63 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B005.c106_pos (not_le.mp h2).le h60 (not_le.mp h61).le h63
                · -- right
                  exact CKLaneC2R.Cells.S04.B005.c108_pos (not_le.mp h2).le h60 (not_le.mp h63).le h59
            · -- right
              by_cases h64 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h65 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B004.c99_pos (not_le.mp h60).le h1 (not_le.mp h44).le h65
                · -- right
                  exact CKLaneC2R.Cells.S04.B005.c101_pos (not_le.mp h60).le h1 (not_le.mp h65).le h64
              · -- right
                by_cases h66 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B005.c107_pos (not_le.mp h60).le h1 (not_le.mp h64).le h66
                · -- right
                  exact CKLaneC2R.Cells.S04.B005.c109_pos (not_le.mp h60).le h1 (not_le.mp h66).le h59
          · -- right
            by_cases h67 : z ≤ ((7079/8000 : ℚ) : ℝ)
            · -- left
              by_cases h68 : z ≤ ((2649/3200 : ℚ) : ℝ)
              · -- left
                by_cases h69 : a ≤ ((59/80 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B008.c160_pos (not_le.mp h2).le h69 (not_le.mp h59).le h68
                · -- right
                  exact CKLaneC2R.Cells.S04.B008.c161_pos (not_le.mp h69).le h1 (not_le.mp h59).le h68
              · -- right
                by_cases h70 : z ≤ ((27403/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B008.c164_pos (not_le.mp h2).le h1 (not_le.mp h68).le h70
                · -- right
                  by_cases h71 : a ≤ ((59/80 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B010.c201_pos (not_le.mp h2).le h71 (not_le.mp h70).le h67
                  · -- right
                    exact CKLaneC2R.Cells.S04.B010.c202_pos (not_le.mp h71).le h1 (not_le.mp h70).le h67
            · -- right
              by_cases h72 : z ≤ ((15071/16000 : ℚ) : ℝ)
              · -- left
                by_cases h73 : a ≤ ((59/80 : ℚ) : ℝ)
                · -- left
                  by_cases h74 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B011.c239_pos (not_le.mp h2).le h73 (not_le.mp h67).le h74
                  · -- right
                    exact CKLaneC2R.Cells.S04.B012.c241_pos (not_le.mp h2).le h73 (not_le.mp h74).le h72
                · -- right
                  by_cases h75 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B012.c240_pos (not_le.mp h73).le h1 (not_le.mp h67).le h75
                  · -- right
                    exact CKLaneC2R.Cells.S04.B012.c242_pos (not_le.mp h73).le h1 (not_le.mp h75).le h72
              · -- right
                by_cases h76 : z ≤ ((6211/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h77 : z ≤ ((61197/64000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B013.c265_pos (not_le.mp h2).le h1 (not_le.mp h72).le h77
                  · -- right
                    by_cases h78 : a ≤ ((59/80 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B013.c274_pos (not_le.mp h2).le h78 (not_le.mp h77).le h76
                    · -- right
                      exact CKLaneC2R.Cells.S04.B013.c275_pos (not_le.mp h78).le h1 (not_le.mp h77).le h76
                · -- right
                  by_cases h79 : z ≤ ((63023/64000 : ℚ) : ℝ)
                  · -- left
                    by_cases h80 : a ≤ ((59/80 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B014.c286_pos (not_le.mp h2).le h80 (not_le.mp h76).le h79
                    · -- right
                      exact CKLaneC2R.Cells.S04.B014.c287_pos (not_le.mp h80).le h1 (not_le.mp h76).le h79
                  · -- right
                    by_cases h81 : z ≤ ((126959/128000 : ℚ) : ℝ)
                    · -- left
                      by_cases h82 : a ≤ ((59/80 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B015.c315_pos (not_le.mp h2).le h82 (not_le.mp h79).le h81
                      · -- right
                        exact CKLaneC2R.Cells.S04.B015.c316_pos (not_le.mp h82).le h1 (not_le.mp h79).le h81
                    · -- right
                      by_cases h83 : z ≤ ((254831/256000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B016.c322_pos (not_le.mp h2).le h1 (not_le.mp h81).le h83
                      · -- right
                        by_cases h84 : z ≤ ((20423/20480 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B016.c337_pos (not_le.mp h2).le h1 (not_le.mp h83).le h84
                        · -- right
                          exact CKLaneC2R.Cells.S04.B016.c338_pos (not_le.mp h2).le h1 (not_le.mp h84).le hz2
    · -- right
      by_cases h85 : a ≤ ((31/40 : ℚ) : ℝ)
      · -- left
        by_cases h86 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h87 : z ≤ ((1257/4000 : ℚ) : ℝ)
          · -- left
            by_cases h88 : z ≤ ((1601/8000 : ℚ) : ℝ)
            · -- left
              by_cases h89 : z ≤ ((2289/16000 : ℚ) : ℝ)
              · -- left
                by_cases h90 : z ≤ ((733/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h91 : z ≤ ((6417/64000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B009.c183_pos (not_le.mp h1).le h85 hz1 h91
                  · -- right
                    exact CKLaneC2R.Cells.S04.B009.c184_pos (not_le.mp h1).le h85 (not_le.mp h91).le h90
                · -- right
                  by_cases h92 : a ≤ ((61/80 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B009.c185_pos (not_le.mp h1).le h92 (not_le.mp h90).le h89
                  · -- right
                    exact CKLaneC2R.Cells.S04.B009.c186_pos (not_le.mp h92).le h85 (not_le.mp h90).le h89
              · -- right
                by_cases h93 : z ≤ ((5491/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B001.c23_pos (not_le.mp h1).le h85 (not_le.mp h89).le h93
                · -- right
                  exact CKLaneC2R.Cells.S04.B001.c24_pos (not_le.mp h1).le h85 (not_le.mp h93).le h88
            · -- right
              by_cases h94 : z ≤ ((823/3200 : ℚ) : ℝ)
              · -- left
                by_cases h95 : z ≤ ((7317/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B001.c35_pos (not_le.mp h1).le h85 (not_le.mp h88).le h95
                · -- right
                  exact CKLaneC2R.Cells.S04.B001.c36_pos (not_le.mp h1).le h85 (not_le.mp h95).le h94
              · -- right
                by_cases h96 : z ≤ ((9143/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B001.c39_pos (not_le.mp h1).le h85 (not_le.mp h94).le h96
                · -- right
                  exact CKLaneC2R.Cells.S04.B002.c40_pos (not_le.mp h1).le h85 (not_le.mp h96).le h87
          · -- right
            by_cases h97 : z ≤ ((3427/8000 : ℚ) : ℝ)
            · -- left
              by_cases h98 : z ≤ ((5941/16000 : ℚ) : ℝ)
              · -- left
                by_cases h99 : a ≤ ((61/80 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B003.c76_pos (not_le.mp h1).le h99 (not_le.mp h87).le h98
                · -- right
                  exact CKLaneC2R.Cells.S04.B003.c77_pos (not_le.mp h99).le h85 (not_le.mp h87).le h98
              · -- right
                exact CKLaneC2R.Cells.S04.B000.c1_pos (not_le.mp h1).le h85 (not_le.mp h98).le h97
            · -- right
              by_cases h100 : z ≤ ((7767/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S04.B000.c8_pos (not_le.mp h1).le h85 (not_le.mp h97).le h100
              · -- right
                exact CKLaneC2R.Cells.S04.B000.c9_pos (not_le.mp h1).le h85 (not_le.mp h100).le h86
        · -- right
          by_cases h101 : z ≤ ((3083/4000 : ℚ) : ℝ)
          · -- left
            by_cases h102 : a ≤ ((61/80 : ℚ) : ℝ)
            · -- left
              by_cases h103 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h104 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B005.c110_pos (not_le.mp h1).le h102 (not_le.mp h86).le h104
                · -- right
                  exact CKLaneC2R.Cells.S04.B005.c112_pos (not_le.mp h1).le h102 (not_le.mp h104).le h103
              · -- right
                by_cases h105 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B005.c118_pos (not_le.mp h1).le h102 (not_le.mp h103).le h105
                · -- right
                  exact CKLaneC2R.Cells.S04.B006.c120_pos (not_le.mp h1).le h102 (not_le.mp h105).le h101
            · -- right
              by_cases h106 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h107 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B005.c111_pos (not_le.mp h102).le h85 (not_le.mp h86).le h107
                · -- right
                  exact CKLaneC2R.Cells.S04.B005.c113_pos (not_le.mp h102).le h85 (not_le.mp h107).le h106
              · -- right
                by_cases h108 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B005.c119_pos (not_le.mp h102).le h85 (not_le.mp h106).le h108
                · -- right
                  exact CKLaneC2R.Cells.S04.B006.c121_pos (not_le.mp h102).le h85 (not_le.mp h108).le h101
          · -- right
            by_cases h109 : z ≤ ((7079/8000 : ℚ) : ℝ)
            · -- left
              by_cases h110 : z ≤ ((2649/3200 : ℚ) : ℝ)
              · -- left
                by_cases h111 : a ≤ ((61/80 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B008.c165_pos (not_le.mp h1).le h111 (not_le.mp h101).le h110
                · -- right
                  exact CKLaneC2R.Cells.S04.B008.c166_pos (not_le.mp h111).le h85 (not_le.mp h101).le h110
              · -- right
                by_cases h112 : z ≤ ((27403/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B008.c167_pos (not_le.mp h1).le h85 (not_le.mp h110).le h112
                · -- right
                  by_cases h113 : a ≤ ((61/80 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B010.c203_pos (not_le.mp h1).le h113 (not_le.mp h112).le h109
                  · -- right
                    exact CKLaneC2R.Cells.S04.B010.c204_pos (not_le.mp h113).le h85 (not_le.mp h112).le h109
            · -- right
              by_cases h114 : z ≤ ((15071/16000 : ℚ) : ℝ)
              · -- left
                by_cases h115 : a ≤ ((61/80 : ℚ) : ℝ)
                · -- left
                  by_cases h116 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B012.c243_pos (not_le.mp h1).le h115 (not_le.mp h109).le h116
                  · -- right
                    exact CKLaneC2R.Cells.S04.B012.c245_pos (not_le.mp h1).le h115 (not_le.mp h116).le h114
                · -- right
                  by_cases h117 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B012.c244_pos (not_le.mp h115).le h85 (not_le.mp h109).le h117
                  · -- right
                    exact CKLaneC2R.Cells.S04.B012.c246_pos (not_le.mp h115).le h85 (not_le.mp h117).le h114
              · -- right
                by_cases h118 : z ≤ ((6211/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h119 : a ≤ ((61/80 : ℚ) : ℝ)
                  · -- left
                    by_cases h120 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B013.c276_pos (not_le.mp h1).le h119 (not_le.mp h114).le h120
                    · -- right
                      exact CKLaneC2R.Cells.S04.B013.c277_pos (not_le.mp h1).le h119 (not_le.mp h120).le h118
                  · -- right
                    by_cases h121 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B013.c278_pos (not_le.mp h119).le h85 (not_le.mp h114).le h121
                    · -- right
                      exact CKLaneC2R.Cells.S04.B013.c279_pos (not_le.mp h119).le h85 (not_le.mp h121).le h118
                · -- right
                  by_cases h122 : z ≤ ((63023/64000 : ℚ) : ℝ)
                  · -- left
                    by_cases h123 : a ≤ ((61/80 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B014.c288_pos (not_le.mp h1).le h123 (not_le.mp h118).le h122
                    · -- right
                      exact CKLaneC2R.Cells.S04.B014.c289_pos (not_le.mp h123).le h85 (not_le.mp h118).le h122
                  · -- right
                    by_cases h124 : z ≤ ((126959/128000 : ℚ) : ℝ)
                    · -- left
                      by_cases h125 : a ≤ ((61/80 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B015.c317_pos (not_le.mp h1).le h125 (not_le.mp h122).le h124
                      · -- right
                        exact CKLaneC2R.Cells.S04.B015.c318_pos (not_le.mp h125).le h85 (not_le.mp h122).le h124
                    · -- right
                      by_cases h126 : z ≤ ((254831/256000 : ℚ) : ℝ)
                      · -- left
                        by_cases h127 : a ≤ ((61/80 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B016.c339_pos (not_le.mp h1).le h127 (not_le.mp h124).le h126
                        · -- right
                          exact CKLaneC2R.Cells.S04.B017.c340_pos (not_le.mp h127).le h85 (not_le.mp h124).le h126
                      · -- right
                        by_cases h128 : z ≤ ((20423/20480 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B017.c343_pos (not_le.mp h1).le h85 (not_le.mp h126).le h128
                        · -- right
                          by_cases h129 : a ≤ ((61/80 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S04.B017.c352_pos (not_le.mp h1).le h129 (not_le.mp h128).le hz2
                          · -- right
                            exact CKLaneC2R.Cells.S04.B017.c353_pos (not_le.mp h129).le h85 (not_le.mp h128).le hz2
      · -- right
        by_cases h130 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h131 : z ≤ ((1257/4000 : ℚ) : ℝ)
          · -- left
            by_cases h132 : z ≤ ((1601/8000 : ℚ) : ℝ)
            · -- left
              by_cases h133 : z ≤ ((2289/16000 : ℚ) : ℝ)
              · -- left
                by_cases h134 : a ≤ ((63/80 : ℚ) : ℝ)
                · -- left
                  by_cases h135 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B009.c187_pos (not_le.mp h85).le h134 hz1 h135
                  · -- right
                    exact CKLaneC2R.Cells.S04.B009.c189_pos (not_le.mp h85).le h134 (not_le.mp h135).le h133
                · -- right
                  by_cases h136 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B009.c188_pos (not_le.mp h134).le h0 hz1 h136
                  · -- right
                    exact CKLaneC2R.Cells.S04.B009.c190_pos (not_le.mp h134).le h0 (not_le.mp h136).le h133
              · -- right
                by_cases h137 : z ≤ ((5491/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B001.c25_pos (not_le.mp h85).le h0 (not_le.mp h133).le h137
                · -- right
                  exact CKLaneC2R.Cells.S04.B001.c26_pos (not_le.mp h85).le h0 (not_le.mp h137).le h132
            · -- right
              by_cases h138 : z ≤ ((823/3200 : ℚ) : ℝ)
              · -- left
                by_cases h139 : z ≤ ((7317/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B001.c37_pos (not_le.mp h85).le h0 (not_le.mp h132).le h139
                · -- right
                  exact CKLaneC2R.Cells.S04.B001.c38_pos (not_le.mp h85).le h0 (not_le.mp h139).le h138
              · -- right
                by_cases h140 : z ≤ ((9143/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B002.c41_pos (not_le.mp h85).le h0 (not_le.mp h138).le h140
                · -- right
                  exact CKLaneC2R.Cells.S04.B002.c42_pos (not_le.mp h85).le h0 (not_le.mp h140).le h131
          · -- right
            by_cases h141 : z ≤ ((3427/8000 : ℚ) : ℝ)
            · -- left
              by_cases h142 : z ≤ ((5941/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S04.B000.c2_pos (not_le.mp h85).le h0 (not_le.mp h131).le h142
              · -- right
                exact CKLaneC2R.Cells.S04.B000.c3_pos (not_le.mp h85).le h0 (not_le.mp h142).le h141
            · -- right
              by_cases h143 : z ≤ ((7767/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S04.B000.c10_pos (not_le.mp h85).le h0 (not_le.mp h141).le h143
              · -- right
                exact CKLaneC2R.Cells.S04.B000.c11_pos (not_le.mp h85).le h0 (not_le.mp h143).le h130
        · -- right
          by_cases h144 : a ≤ ((63/80 : ℚ) : ℝ)
          · -- left
            by_cases h145 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h146 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h147 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B005.c114_pos (not_le.mp h85).le h144 (not_le.mp h130).le h147
                · -- right
                  exact CKLaneC2R.Cells.S04.B005.c116_pos (not_le.mp h85).le h144 (not_le.mp h147).le h146
              · -- right
                by_cases h148 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B006.c122_pos (not_le.mp h85).le h144 (not_le.mp h146).le h148
                · -- right
                  exact CKLaneC2R.Cells.S04.B006.c124_pos (not_le.mp h85).le h144 (not_le.mp h148).le h145
            · -- right
              by_cases h149 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h150 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B008.c168_pos (not_le.mp h85).le h144 (not_le.mp h145).le h150
                · -- right
                  by_cases h151 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B010.c205_pos (not_le.mp h85).le h144 (not_le.mp h150).le h151
                  · -- right
                    exact CKLaneC2R.Cells.S04.B010.c207_pos (not_le.mp h85).le h144 (not_le.mp h151).le h149
              · -- right
                by_cases h152 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h153 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B012.c247_pos (not_le.mp h85).le h144 (not_le.mp h149).le h153
                  · -- right
                    exact CKLaneC2R.Cells.S04.B012.c249_pos (not_le.mp h85).le h144 (not_le.mp h153).le h152
                · -- right
                  by_cases h154 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h155 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B014.c280_pos (not_le.mp h85).le h144 (not_le.mp h152).le h155
                    · -- right
                      exact CKLaneC2R.Cells.S04.B014.c281_pos (not_le.mp h85).le h144 (not_le.mp h155).le h154
                  · -- right
                    by_cases h156 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B014.c290_pos (not_le.mp h85).le h144 (not_le.mp h154).le h156
                    · -- right
                      by_cases h157 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B015.c319_pos (not_le.mp h85).le h144 (not_le.mp h156).le h157
                      · -- right
                        by_cases h158 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B017.c341_pos (not_le.mp h85).le h144 (not_le.mp h157).le h158
                        · -- right
                          by_cases h159 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S04.B017.c354_pos (not_le.mp h85).le h144 (not_le.mp h158).le h159
                          · -- right
                            exact CKLaneC2R.Cells.S04.B017.c356_pos (not_le.mp h85).le h144 (not_le.mp h159).le hz2
          · -- right
            by_cases h160 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h161 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h162 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B005.c115_pos (not_le.mp h144).le h0 (not_le.mp h130).le h162
                · -- right
                  exact CKLaneC2R.Cells.S04.B005.c117_pos (not_le.mp h144).le h0 (not_le.mp h162).le h161
              · -- right
                by_cases h163 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B006.c123_pos (not_le.mp h144).le h0 (not_le.mp h161).le h163
                · -- right
                  exact CKLaneC2R.Cells.S04.B006.c125_pos (not_le.mp h144).le h0 (not_le.mp h163).le h160
            · -- right
              by_cases h164 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h165 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B008.c169_pos (not_le.mp h144).le h0 (not_le.mp h160).le h165
                · -- right
                  by_cases h166 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B010.c206_pos (not_le.mp h144).le h0 (not_le.mp h165).le h166
                  · -- right
                    exact CKLaneC2R.Cells.S04.B010.c208_pos (not_le.mp h144).le h0 (not_le.mp h166).le h164
              · -- right
                by_cases h167 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h168 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B012.c248_pos (not_le.mp h144).le h0 (not_le.mp h164).le h168
                  · -- right
                    exact CKLaneC2R.Cells.S04.B012.c250_pos (not_le.mp h144).le h0 (not_le.mp h168).le h167
                · -- right
                  by_cases h169 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h170 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B014.c282_pos (not_le.mp h144).le h0 (not_le.mp h167).le h170
                    · -- right
                      exact CKLaneC2R.Cells.S04.B014.c283_pos (not_le.mp h144).le h0 (not_le.mp h170).le h169
                  · -- right
                    by_cases h171 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B014.c291_pos (not_le.mp h144).le h0 (not_le.mp h169).le h171
                    · -- right
                      by_cases h172 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B016.c320_pos (not_le.mp h144).le h0 (not_le.mp h171).le h172
                      · -- right
                        by_cases h173 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B017.c342_pos (not_le.mp h144).le h0 (not_le.mp h172).le h173
                        · -- right
                          by_cases h174 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S04.B017.c355_pos (not_le.mp h144).le h0 (not_le.mp h173).le h174
                          · -- right
                            exact CKLaneC2R.Cells.S04.B017.c357_pos (not_le.mp h144).le h0 (not_le.mp h174).le hz2
  · -- right
    by_cases h175 : a ≤ ((17/20 : ℚ) : ℝ)
    · -- left
      by_cases h176 : a ≤ ((33/40 : ℚ) : ℝ)
      · -- left
        by_cases h177 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h178 : z ≤ ((1257/4000 : ℚ) : ℝ)
          · -- left
            by_cases h179 : z ≤ ((1601/8000 : ℚ) : ℝ)
            · -- left
              by_cases h180 : z ≤ ((2289/16000 : ℚ) : ℝ)
              · -- left
                by_cases h181 : z ≤ ((733/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h182 : a ≤ ((13/16 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B009.c191_pos (not_le.mp h0).le h182 hz1 h181
                  · -- right
                    exact CKLaneC2R.Cells.S04.B009.c192_pos (not_le.mp h182).le h176 hz1 h181
                · -- right
                  exact CKLaneC2R.Cells.S04.B002.c43_pos (not_le.mp h0).le h176 (not_le.mp h181).le h180
              · -- right
                by_cases h183 : z ≤ ((5491/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B002.c45_pos (not_le.mp h0).le h176 (not_le.mp h180).le h183
                · -- right
                  exact CKLaneC2R.Cells.S04.B002.c46_pos (not_le.mp h0).le h176 (not_le.mp h183).le h179
            · -- right
              by_cases h184 : z ≤ ((823/3200 : ℚ) : ℝ)
              · -- left
                by_cases h185 : z ≤ ((7317/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B002.c54_pos (not_le.mp h0).le h176 (not_le.mp h179).le h185
                · -- right
                  exact CKLaneC2R.Cells.S04.B002.c55_pos (not_le.mp h0).le h176 (not_le.mp h185).le h184
              · -- right
                by_cases h186 : a ≤ ((13/16 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B002.c58_pos (not_le.mp h0).le h186 (not_le.mp h184).le h178
                · -- right
                  exact CKLaneC2R.Cells.S04.B002.c59_pos (not_le.mp h186).le h176 (not_le.mp h184).le h178
          · -- right
            by_cases h187 : z ≤ ((3427/8000 : ℚ) : ℝ)
            · -- left
              by_cases h188 : z ≤ ((5941/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S04.B000.c12_pos (not_le.mp h0).le h176 (not_le.mp h178).le h188
              · -- right
                exact CKLaneC2R.Cells.S04.B000.c13_pos (not_le.mp h0).le h176 (not_le.mp h188).le h187
            · -- right
              by_cases h189 : z ≤ ((7767/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S04.B000.c17_pos (not_le.mp h0).le h176 (not_le.mp h187).le h189
              · -- right
                exact CKLaneC2R.Cells.S04.B000.c18_pos (not_le.mp h0).le h176 (not_le.mp h189).le h177
        · -- right
          by_cases h190 : a ≤ ((13/16 : ℚ) : ℝ)
          · -- left
            by_cases h191 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h192 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h193 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B006.c126_pos (not_le.mp h0).le h190 (not_le.mp h177).le h193
                · -- right
                  exact CKLaneC2R.Cells.S04.B006.c128_pos (not_le.mp h0).le h190 (not_le.mp h193).le h192
              · -- right
                by_cases h194 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B007.c142_pos (not_le.mp h0).le h190 (not_le.mp h192).le h194
                · -- right
                  exact CKLaneC2R.Cells.S04.B007.c144_pos (not_le.mp h0).le h190 (not_le.mp h194).le h191
            · -- right
              by_cases h195 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h196 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B008.c170_pos (not_le.mp h0).le h190 (not_le.mp h191).le h196
                · -- right
                  by_cases h197 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B010.c209_pos (not_le.mp h0).le h190 (not_le.mp h196).le h197
                  · -- right
                    exact CKLaneC2R.Cells.S04.B010.c211_pos (not_le.mp h0).le h190 (not_le.mp h197).le h195
              · -- right
                by_cases h198 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h199 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B012.c251_pos (not_le.mp h0).le h190 (not_le.mp h195).le h199
                  · -- right
                    exact CKLaneC2R.Cells.S04.B012.c253_pos (not_le.mp h0).le h190 (not_le.mp h199).le h198
                · -- right
                  by_cases h200 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h201 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B014.c293_pos (not_le.mp h0).le h190 (not_le.mp h198).le h201
                    · -- right
                      exact CKLaneC2R.Cells.S04.B014.c294_pos (not_le.mp h0).le h190 (not_le.mp h201).le h200
                  · -- right
                    by_cases h202 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B015.c309_pos (not_le.mp h0).le h190 (not_le.mp h200).le h202
                    · -- right
                      by_cases h203 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B016.c323_pos (not_le.mp h0).le h190 (not_le.mp h202).le h203
                      · -- right
                        by_cases h204 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B017.c344_pos (not_le.mp h0).le h190 (not_le.mp h203).le h204
                        · -- right
                          by_cases h205 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S04.B017.c358_pos (not_le.mp h0).le h190 (not_le.mp h204).le h205
                          · -- right
                            exact CKLaneC2R.Cells.S04.B018.c360_pos (not_le.mp h0).le h190 (not_le.mp h205).le hz2
          · -- right
            by_cases h206 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h207 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h208 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B006.c127_pos (not_le.mp h190).le h176 (not_le.mp h177).le h208
                · -- right
                  exact CKLaneC2R.Cells.S04.B006.c129_pos (not_le.mp h190).le h176 (not_le.mp h208).le h207
              · -- right
                by_cases h209 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B007.c143_pos (not_le.mp h190).le h176 (not_le.mp h207).le h209
                · -- right
                  exact CKLaneC2R.Cells.S04.B007.c145_pos (not_le.mp h190).le h176 (not_le.mp h209).le h206
            · -- right
              by_cases h210 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h211 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B008.c171_pos (not_le.mp h190).le h176 (not_le.mp h206).le h211
                · -- right
                  by_cases h212 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B010.c210_pos (not_le.mp h190).le h176 (not_le.mp h211).le h212
                  · -- right
                    exact CKLaneC2R.Cells.S04.B010.c212_pos (not_le.mp h190).le h176 (not_le.mp h212).le h210
              · -- right
                by_cases h213 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h214 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B012.c252_pos (not_le.mp h190).le h176 (not_le.mp h210).le h214
                  · -- right
                    exact CKLaneC2R.Cells.S04.B012.c254_pos (not_le.mp h190).le h176 (not_le.mp h214).le h213
                · -- right
                  by_cases h215 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h216 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B014.c295_pos (not_le.mp h190).le h176 (not_le.mp h213).le h216
                    · -- right
                      exact CKLaneC2R.Cells.S04.B014.c296_pos (not_le.mp h190).le h176 (not_le.mp h216).le h215
                  · -- right
                    by_cases h217 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B015.c310_pos (not_le.mp h190).le h176 (not_le.mp h215).le h217
                    · -- right
                      by_cases h218 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B016.c324_pos (not_le.mp h190).le h176 (not_le.mp h217).le h218
                      · -- right
                        by_cases h219 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B017.c345_pos (not_le.mp h190).le h176 (not_le.mp h218).le h219
                        · -- right
                          by_cases h220 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S04.B017.c359_pos (not_le.mp h190).le h176 (not_le.mp h219).le h220
                          · -- right
                            exact CKLaneC2R.Cells.S04.B018.c361_pos (not_le.mp h190).le h176 (not_le.mp h220).le hz2
      · -- right
        by_cases h221 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h222 : z ≤ ((1257/4000 : ℚ) : ℝ)
          · -- left
            by_cases h223 : z ≤ ((1601/8000 : ℚ) : ℝ)
            · -- left
              by_cases h224 : z ≤ ((2289/16000 : ℚ) : ℝ)
              · -- left
                by_cases h225 : z ≤ ((733/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h226 : a ≤ ((67/80 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B009.c193_pos (not_le.mp h176).le h226 hz1 h225
                  · -- right
                    exact CKLaneC2R.Cells.S04.B009.c194_pos (not_le.mp h226).le h175 hz1 h225
                · -- right
                  exact CKLaneC2R.Cells.S04.B002.c44_pos (not_le.mp h176).le h175 (not_le.mp h225).le h224
              · -- right
                by_cases h227 : z ≤ ((5491/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B002.c47_pos (not_le.mp h176).le h175 (not_le.mp h224).le h227
                · -- right
                  exact CKLaneC2R.Cells.S04.B002.c48_pos (not_le.mp h176).le h175 (not_le.mp h227).le h223
            · -- right
              by_cases h228 : z ≤ ((823/3200 : ℚ) : ℝ)
              · -- left
                by_cases h229 : z ≤ ((7317/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B002.c56_pos (not_le.mp h176).le h175 (not_le.mp h223).le h229
                · -- right
                  exact CKLaneC2R.Cells.S04.B002.c57_pos (not_le.mp h176).le h175 (not_le.mp h229).le h228
              · -- right
                by_cases h230 : a ≤ ((67/80 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B003.c60_pos (not_le.mp h176).le h230 (not_le.mp h228).le h222
                · -- right
                  exact CKLaneC2R.Cells.S04.B003.c61_pos (not_le.mp h230).le h175 (not_le.mp h228).le h222
          · -- right
            by_cases h231 : z ≤ ((3427/8000 : ℚ) : ℝ)
            · -- left
              by_cases h232 : z ≤ ((5941/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S04.B000.c14_pos (not_le.mp h176).le h175 (not_le.mp h222).le h232
              · -- right
                exact CKLaneC2R.Cells.S04.B000.c15_pos (not_le.mp h176).le h175 (not_le.mp h232).le h231
            · -- right
              by_cases h233 : z ≤ ((7767/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S04.B000.c19_pos (not_le.mp h176).le h175 (not_le.mp h231).le h233
              · -- right
                by_cases h234 : a ≤ ((67/80 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B004.c84_pos (not_le.mp h176).le h234 (not_le.mp h233).le h221
                · -- right
                  exact CKLaneC2R.Cells.S04.B004.c85_pos (not_le.mp h234).le h175 (not_le.mp h233).le h221
        · -- right
          by_cases h235 : a ≤ ((67/80 : ℚ) : ℝ)
          · -- left
            by_cases h236 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h237 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h238 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B006.c130_pos (not_le.mp h176).le h235 (not_le.mp h221).le h238
                · -- right
                  exact CKLaneC2R.Cells.S04.B006.c132_pos (not_le.mp h176).le h235 (not_le.mp h238).le h237
              · -- right
                by_cases h239 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B007.c146_pos (not_le.mp h176).le h235 (not_le.mp h237).le h239
                · -- right
                  exact CKLaneC2R.Cells.S04.B007.c148_pos (not_le.mp h176).le h235 (not_le.mp h239).le h236
            · -- right
              by_cases h240 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h241 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B008.c172_pos (not_le.mp h176).le h235 (not_le.mp h236).le h241
                · -- right
                  by_cases h242 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B010.c215_pos (not_le.mp h176).le h235 (not_le.mp h241).le h242
                  · -- right
                    exact CKLaneC2R.Cells.S04.B010.c216_pos (not_le.mp h176).le h235 (not_le.mp h242).le h240
              · -- right
                by_cases h243 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h244 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B012.c255_pos (not_le.mp h176).le h235 (not_le.mp h240).le h244
                  · -- right
                    exact CKLaneC2R.Cells.S04.B012.c257_pos (not_le.mp h176).le h235 (not_le.mp h244).le h243
                · -- right
                  by_cases h245 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h246 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B014.c297_pos (not_le.mp h176).le h235 (not_le.mp h243).le h246
                    · -- right
                      exact CKLaneC2R.Cells.S04.B014.c298_pos (not_le.mp h176).le h235 (not_le.mp h246).le h245
                  · -- right
                    by_cases h247 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B015.c311_pos (not_le.mp h176).le h235 (not_le.mp h245).le h247
                    · -- right
                      by_cases h248 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B016.c325_pos (not_le.mp h176).le h235 (not_le.mp h247).le h248
                      · -- right
                        by_cases h249 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B017.c346_pos (not_le.mp h176).le h235 (not_le.mp h248).le h249
                        · -- right
                          by_cases h250 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S04.B018.c362_pos (not_le.mp h176).le h235 (not_le.mp h249).le h250
                          · -- right
                            exact CKLaneC2R.Cells.S04.B018.c364_pos (not_le.mp h176).le h235 (not_le.mp h250).le hz2
          · -- right
            by_cases h251 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h252 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h253 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B006.c131_pos (not_le.mp h235).le h175 (not_le.mp h221).le h253
                · -- right
                  exact CKLaneC2R.Cells.S04.B006.c133_pos (not_le.mp h235).le h175 (not_le.mp h253).le h252
              · -- right
                by_cases h254 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B007.c147_pos (not_le.mp h235).le h175 (not_le.mp h252).le h254
                · -- right
                  exact CKLaneC2R.Cells.S04.B007.c149_pos (not_le.mp h235).le h175 (not_le.mp h254).le h251
            · -- right
              by_cases h255 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h256 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h257 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B010.c213_pos (not_le.mp h235).le h175 (not_le.mp h251).le h257
                  · -- right
                    exact CKLaneC2R.Cells.S04.B010.c214_pos (not_le.mp h235).le h175 (not_le.mp h257).le h256
                · -- right
                  by_cases h258 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B010.c217_pos (not_le.mp h235).le h175 (not_le.mp h256).le h258
                  · -- right
                    exact CKLaneC2R.Cells.S04.B010.c218_pos (not_le.mp h235).le h175 (not_le.mp h258).le h255
              · -- right
                by_cases h259 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h260 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B012.c256_pos (not_le.mp h235).le h175 (not_le.mp h255).le h260
                  · -- right
                    exact CKLaneC2R.Cells.S04.B012.c258_pos (not_le.mp h235).le h175 (not_le.mp h260).le h259
                · -- right
                  by_cases h261 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h262 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B014.c299_pos (not_le.mp h235).le h175 (not_le.mp h259).le h262
                    · -- right
                      exact CKLaneC2R.Cells.S04.B015.c300_pos (not_le.mp h235).le h175 (not_le.mp h262).le h261
                  · -- right
                    by_cases h263 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B015.c312_pos (not_le.mp h235).le h175 (not_le.mp h261).le h263
                    · -- right
                      by_cases h264 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B016.c326_pos (not_le.mp h235).le h175 (not_le.mp h263).le h264
                      · -- right
                        by_cases h265 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B017.c347_pos (not_le.mp h235).le h175 (not_le.mp h264).le h265
                        · -- right
                          by_cases h266 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S04.B018.c363_pos (not_le.mp h235).le h175 (not_le.mp h265).le h266
                          · -- right
                            exact CKLaneC2R.Cells.S04.B018.c365_pos (not_le.mp h235).le h175 (not_le.mp h266).le hz2
    · -- right
      by_cases h267 : a ≤ ((7/8 : ℚ) : ℝ)
      · -- left
        by_cases h268 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h269 : z ≤ ((1257/4000 : ℚ) : ℝ)
          · -- left
            by_cases h270 : z ≤ ((1601/8000 : ℚ) : ℝ)
            · -- left
              by_cases h271 : z ≤ ((2289/16000 : ℚ) : ℝ)
              · -- left
                by_cases h272 : z ≤ ((733/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h273 : a ≤ ((69/80 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B009.c195_pos (not_le.mp h175).le h273 hz1 h272
                  · -- right
                    exact CKLaneC2R.Cells.S04.B009.c196_pos (not_le.mp h273).le h267 hz1 h272
                · -- right
                  exact CKLaneC2R.Cells.S04.B002.c49_pos (not_le.mp h175).le h267 (not_le.mp h272).le h271
              · -- right
                by_cases h274 : z ≤ ((5491/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B002.c50_pos (not_le.mp h175).le h267 (not_le.mp h271).le h274
                · -- right
                  exact CKLaneC2R.Cells.S04.B002.c51_pos (not_le.mp h175).le h267 (not_le.mp h274).le h270
            · -- right
              by_cases h275 : a ≤ ((69/80 : ℚ) : ℝ)
              · -- left
                by_cases h276 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B003.c62_pos (not_le.mp h175).le h275 (not_le.mp h270).le h276
                · -- right
                  exact CKLaneC2R.Cells.S04.B003.c64_pos (not_le.mp h175).le h275 (not_le.mp h276).le h269
              · -- right
                by_cases h277 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B003.c63_pos (not_le.mp h275).le h267 (not_le.mp h270).le h277
                · -- right
                  exact CKLaneC2R.Cells.S04.B003.c65_pos (not_le.mp h275).le h267 (not_le.mp h277).le h269
          · -- right
            by_cases h278 : z ≤ ((3427/8000 : ℚ) : ℝ)
            · -- left
              by_cases h279 : z ≤ ((5941/16000 : ℚ) : ℝ)
              · -- left
                by_cases h280 : a ≤ ((69/80 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B003.c78_pos (not_le.mp h175).le h280 (not_le.mp h269).le h279
                · -- right
                  exact CKLaneC2R.Cells.S04.B003.c79_pos (not_le.mp h280).le h267 (not_le.mp h269).le h279
              · -- right
                exact CKLaneC2R.Cells.S04.B000.c16_pos (not_le.mp h175).le h267 (not_le.mp h279).le h278
            · -- right
              by_cases h281 : a ≤ ((69/80 : ℚ) : ℝ)
              · -- left
                by_cases h282 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B004.c86_pos (not_le.mp h175).le h281 (not_le.mp h278).le h282
                · -- right
                  exact CKLaneC2R.Cells.S04.B004.c88_pos (not_le.mp h175).le h281 (not_le.mp h282).le h268
              · -- right
                by_cases h283 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B004.c87_pos (not_le.mp h281).le h267 (not_le.mp h278).le h283
                · -- right
                  exact CKLaneC2R.Cells.S04.B004.c89_pos (not_le.mp h281).le h267 (not_le.mp h283).le h268
        · -- right
          by_cases h284 : a ≤ ((69/80 : ℚ) : ℝ)
          · -- left
            by_cases h285 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h286 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h287 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B006.c134_pos (not_le.mp h175).le h284 (not_le.mp h268).le h287
                · -- right
                  exact CKLaneC2R.Cells.S04.B006.c136_pos (not_le.mp h175).le h284 (not_le.mp h287).le h286
              · -- right
                by_cases h288 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B007.c150_pos (not_le.mp h175).le h284 (not_le.mp h286).le h288
                · -- right
                  exact CKLaneC2R.Cells.S04.B007.c152_pos (not_le.mp h175).le h284 (not_le.mp h288).le h285
            · -- right
              by_cases h289 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h290 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h291 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B010.c219_pos (not_le.mp h175).le h284 (not_le.mp h285).le h291
                  · -- right
                    exact CKLaneC2R.Cells.S04.B011.c220_pos (not_le.mp h175).le h284 (not_le.mp h291).le h290
                · -- right
                  by_cases h292 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B011.c227_pos (not_le.mp h175).le h284 (not_le.mp h290).le h292
                  · -- right
                    exact CKLaneC2R.Cells.S04.B011.c228_pos (not_le.mp h175).le h284 (not_le.mp h292).le h289
              · -- right
                by_cases h293 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h294 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B012.c259_pos (not_le.mp h175).le h284 (not_le.mp h289).le h294
                  · -- right
                    exact CKLaneC2R.Cells.S04.B013.c261_pos (not_le.mp h175).le h284 (not_le.mp h294).le h293
                · -- right
                  by_cases h295 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h296 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B015.c301_pos (not_le.mp h175).le h284 (not_le.mp h293).le h296
                    · -- right
                      exact CKLaneC2R.Cells.S04.B015.c302_pos (not_le.mp h175).le h284 (not_le.mp h296).le h295
                  · -- right
                    by_cases h297 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B015.c313_pos (not_le.mp h175).le h284 (not_le.mp h295).le h297
                    · -- right
                      by_cases h298 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B016.c331_pos (not_le.mp h175).le h284 (not_le.mp h297).le h298
                      · -- right
                        by_cases h299 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B017.c348_pos (not_le.mp h175).le h284 (not_le.mp h298).le h299
                        · -- right
                          by_cases h300 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S04.B018.c366_pos (not_le.mp h175).le h284 (not_le.mp h299).le h300
                          · -- right
                            exact CKLaneC2R.Cells.S04.B018.c367_pos (not_le.mp h175).le h284 (not_le.mp h300).le hz2
          · -- right
            by_cases h301 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h302 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h303 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B006.c135_pos (not_le.mp h284).le h267 (not_le.mp h268).le h303
                · -- right
                  exact CKLaneC2R.Cells.S04.B006.c137_pos (not_le.mp h284).le h267 (not_le.mp h303).le h302
              · -- right
                by_cases h304 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B007.c151_pos (not_le.mp h284).le h267 (not_le.mp h302).le h304
                · -- right
                  exact CKLaneC2R.Cells.S04.B007.c153_pos (not_le.mp h284).le h267 (not_le.mp h304).le h301
            · -- right
              by_cases h305 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h306 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h307 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B011.c221_pos (not_le.mp h284).le h267 (not_le.mp h301).le h307
                  · -- right
                    exact CKLaneC2R.Cells.S04.B011.c222_pos (not_le.mp h284).le h267 (not_le.mp h307).le h306
                · -- right
                  by_cases h308 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B011.c229_pos (not_le.mp h284).le h267 (not_le.mp h306).le h308
                  · -- right
                    exact CKLaneC2R.Cells.S04.B011.c230_pos (not_le.mp h284).le h267 (not_le.mp h308).le h305
              · -- right
                by_cases h309 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h310 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B013.c260_pos (not_le.mp h284).le h267 (not_le.mp h305).le h310
                  · -- right
                    by_cases h311 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B013.c266_pos (not_le.mp h284).le h267 (not_le.mp h310).le h311
                    · -- right
                      exact CKLaneC2R.Cells.S04.B013.c267_pos (not_le.mp h284).le h267 (not_le.mp h311).le h309
                · -- right
                  by_cases h312 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h313 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B015.c303_pos (not_le.mp h284).le h267 (not_le.mp h309).le h313
                    · -- right
                      exact CKLaneC2R.Cells.S04.B015.c304_pos (not_le.mp h284).le h267 (not_le.mp h313).le h312
                  · -- right
                    by_cases h314 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B015.c314_pos (not_le.mp h284).le h267 (not_le.mp h312).le h314
                    · -- right
                      by_cases h315 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B016.c332_pos (not_le.mp h284).le h267 (not_le.mp h314).le h315
                      · -- right
                        by_cases h316 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B017.c349_pos (not_le.mp h284).le h267 (not_le.mp h315).le h316
                        · -- right
                          by_cases h317 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S04.B018.c368_pos (not_le.mp h284).le h267 (not_le.mp h316).le h317
                          · -- right
                            exact CKLaneC2R.Cells.S04.B018.c369_pos (not_le.mp h284).le h267 (not_le.mp h317).le hz2
      · -- right
        by_cases h318 : a ≤ ((71/80 : ℚ) : ℝ)
        · -- left
          by_cases h319 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h320 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h321 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h322 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h323 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B009.c197_pos (not_le.mp h267).le h318 hz1 h323
                  · -- right
                    exact CKLaneC2R.Cells.S04.B009.c199_pos (not_le.mp h267).le h318 (not_le.mp h323).le h322
                · -- right
                  exact CKLaneC2R.Cells.S04.B002.c52_pos (not_le.mp h267).le h318 (not_le.mp h322).le h321
              · -- right
                by_cases h324 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B003.c66_pos (not_le.mp h267).le h318 (not_le.mp h321).le h324
                · -- right
                  exact CKLaneC2R.Cells.S04.B003.c68_pos (not_le.mp h267).le h318 (not_le.mp h324).le h320
            · -- right
              by_cases h325 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h326 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B004.c80_pos (not_le.mp h267).le h318 (not_le.mp h320).le h326
                · -- right
                  exact CKLaneC2R.Cells.S04.B004.c82_pos (not_le.mp h267).le h318 (not_le.mp h326).le h325
              · -- right
                by_cases h327 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B004.c90_pos (not_le.mp h267).le h318 (not_le.mp h325).le h327
                · -- right
                  exact CKLaneC2R.Cells.S04.B004.c92_pos (not_le.mp h267).le h318 (not_le.mp h327).le h319
          · -- right
            by_cases h328 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h329 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h330 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B006.c138_pos (not_le.mp h267).le h318 (not_le.mp h319).le h330
                · -- right
                  exact CKLaneC2R.Cells.S04.B007.c140_pos (not_le.mp h267).le h318 (not_le.mp h330).le h329
              · -- right
                by_cases h331 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B007.c154_pos (not_le.mp h267).le h318 (not_le.mp h329).le h331
                · -- right
                  exact CKLaneC2R.Cells.S04.B007.c156_pos (not_le.mp h267).le h318 (not_le.mp h331).le h328
            · -- right
              by_cases h332 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h333 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h334 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B011.c223_pos (not_le.mp h267).le h318 (not_le.mp h328).le h334
                  · -- right
                    exact CKLaneC2R.Cells.S04.B011.c224_pos (not_le.mp h267).le h318 (not_le.mp h334).le h333
                · -- right
                  by_cases h335 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B011.c231_pos (not_le.mp h267).le h318 (not_le.mp h333).le h335
                  · -- right
                    exact CKLaneC2R.Cells.S04.B011.c232_pos (not_le.mp h267).le h318 (not_le.mp h335).le h332
              · -- right
                by_cases h336 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h337 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B013.c262_pos (not_le.mp h267).le h318 (not_le.mp h332).le h337
                  · -- right
                    by_cases h338 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B013.c268_pos (not_le.mp h267).le h318 (not_le.mp h337).le h338
                    · -- right
                      exact CKLaneC2R.Cells.S04.B013.c269_pos (not_le.mp h267).le h318 (not_le.mp h338).le h336
                · -- right
                  by_cases h339 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h340 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B015.c305_pos (not_le.mp h267).le h318 (not_le.mp h336).le h340
                    · -- right
                      exact CKLaneC2R.Cells.S04.B015.c306_pos (not_le.mp h267).le h318 (not_le.mp h340).le h339
                  · -- right
                    by_cases h341 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h342 : a ≤ ((141/160 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B016.c327_pos (not_le.mp h267).le h342 (not_le.mp h339).le h341
                      · -- right
                        exact CKLaneC2R.Cells.S04.B016.c328_pos (not_le.mp h342).le h318 (not_le.mp h339).le h341
                    · -- right
                      by_cases h343 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B016.c333_pos (not_le.mp h267).le h318 (not_le.mp h341).le h343
                      · -- right
                        by_cases h344 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B017.c350_pos (not_le.mp h267).le h318 (not_le.mp h343).le h344
                        · -- right
                          by_cases h345 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S04.B018.c370_pos (not_le.mp h267).le h318 (not_le.mp h344).le h345
                          · -- right
                            exact CKLaneC2R.Cells.S04.B018.c371_pos (not_le.mp h267).le h318 (not_le.mp h345).le hz2
        · -- right
          by_cases h346 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h347 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h348 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h349 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h350 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B009.c198_pos (not_le.mp h318).le ha2 hz1 h350
                  · -- right
                    exact CKLaneC2R.Cells.S04.B010.c200_pos (not_le.mp h318).le ha2 (not_le.mp h350).le h349
                · -- right
                  exact CKLaneC2R.Cells.S04.B002.c53_pos (not_le.mp h318).le ha2 (not_le.mp h349).le h348
              · -- right
                by_cases h351 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B003.c67_pos (not_le.mp h318).le ha2 (not_le.mp h348).le h351
                · -- right
                  exact CKLaneC2R.Cells.S04.B003.c69_pos (not_le.mp h318).le ha2 (not_le.mp h351).le h347
            · -- right
              by_cases h352 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h353 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B004.c81_pos (not_le.mp h318).le ha2 (not_le.mp h347).le h353
                · -- right
                  exact CKLaneC2R.Cells.S04.B004.c83_pos (not_le.mp h318).le ha2 (not_le.mp h353).le h352
              · -- right
                by_cases h354 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B004.c91_pos (not_le.mp h318).le ha2 (not_le.mp h352).le h354
                · -- right
                  exact CKLaneC2R.Cells.S04.B004.c93_pos (not_le.mp h318).le ha2 (not_le.mp h354).le h346
          · -- right
            by_cases h355 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h356 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h357 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B006.c139_pos (not_le.mp h318).le ha2 (not_le.mp h346).le h357
                · -- right
                  exact CKLaneC2R.Cells.S04.B007.c141_pos (not_le.mp h318).le ha2 (not_le.mp h357).le h356
              · -- right
                by_cases h358 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S04.B007.c155_pos (not_le.mp h318).le ha2 (not_le.mp h356).le h358
                · -- right
                  exact CKLaneC2R.Cells.S04.B007.c157_pos (not_le.mp h318).le ha2 (not_le.mp h358).le h355
            · -- right
              by_cases h359 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h360 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h361 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B011.c225_pos (not_le.mp h318).le ha2 (not_le.mp h355).le h361
                  · -- right
                    exact CKLaneC2R.Cells.S04.B011.c226_pos (not_le.mp h318).le ha2 (not_le.mp h361).le h360
                · -- right
                  by_cases h362 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B011.c233_pos (not_le.mp h318).le ha2 (not_le.mp h360).le h362
                  · -- right
                    exact CKLaneC2R.Cells.S04.B011.c234_pos (not_le.mp h318).le ha2 (not_le.mp h362).le h359
              · -- right
                by_cases h363 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h364 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S04.B013.c263_pos (not_le.mp h318).le ha2 (not_le.mp h359).le h364
                  · -- right
                    by_cases h365 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B013.c270_pos (not_le.mp h318).le ha2 (not_le.mp h364).le h365
                    · -- right
                      exact CKLaneC2R.Cells.S04.B013.c271_pos (not_le.mp h318).le ha2 (not_le.mp h365).le h363
                · -- right
                  by_cases h366 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h367 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S04.B015.c307_pos (not_le.mp h318).le ha2 (not_le.mp h363).le h367
                    · -- right
                      exact CKLaneC2R.Cells.S04.B015.c308_pos (not_le.mp h318).le ha2 (not_le.mp h367).le h366
                  · -- right
                    by_cases h368 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h369 : a ≤ ((143/160 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B016.c329_pos (not_le.mp h318).le h369 (not_le.mp h366).le h368
                      · -- right
                        exact CKLaneC2R.Cells.S04.B016.c330_pos (not_le.mp h369).le ha2 (not_le.mp h366).le h368
                    · -- right
                      by_cases h370 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S04.B016.c334_pos (not_le.mp h318).le ha2 (not_le.mp h368).le h370
                      · -- right
                        by_cases h371 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S04.B017.c351_pos (not_le.mp h318).le ha2 (not_le.mp h370).le h371
                        · -- right
                          by_cases h372 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S04.B018.c372_pos (not_le.mp h318).le ha2 (not_le.mp h371).le h372
                          · -- right
                            exact CKLaneC2R.Cells.S04.B018.c373_pos (not_le.mp h318).le ha2 (not_le.mp h372).le hz2

end CKLaneC2R.CompactCover

end


