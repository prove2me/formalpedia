-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q02
-- name    : CK_CKLaneC2R_EndpointCover_b00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:58:12.277219+00:00
-- url     : https://prove2.me/theorems/751b805d-33ca-4681-b312-6a4d3b17e494
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 3 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 3 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 3 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 3 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 1 of 5) (piece 3 of 5).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B029
import Definitions.Def_CK_CKLaneC2R_EpCells_B030
import Definitions.Def_CK_CKLaneC2R_EpCells_B031
namespace CKLaneC2R.EndpointCover
theorem cover_sub_002 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : a ≤ ((20049/128000 : ℚ) : ℝ)) (h7 : ¬ (a ≤ ((39249/256000 : ℚ) : ℝ))) (h263 : a ≤ ((79347/512000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h264 : a ≤ ((31569/204800 : ℚ) : ℝ)
  · -- left
    by_cases h265 : a ≤ ((314841/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h266 : a ≤ ((628833/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h267 : a ≤ ((1256817/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h268 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h269 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h270 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1784_pos (not_le.mp h7).le h267 hz1 h270 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1786_pos (not_le.mp h7).le h267 (not_le.mp h270).le h269 hz
            · -- right
              by_cases h271 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1792_pos (not_le.mp h7).le h267 (not_le.mp h269).le h271 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1794_pos (not_le.mp h7).le h267 (not_le.mp h271).le h268 hz
          · -- right
            by_cases h272 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h273 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1816_pos (not_le.mp h7).le h267 (not_le.mp h268).le h273 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1818_pos (not_le.mp h7).le h267 (not_le.mp h273).le h272 hz
            · -- right
              by_cases h274 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1824_pos (not_le.mp h7).le h267 (not_le.mp h272).le h274 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1826_pos (not_le.mp h7).le h267 (not_le.mp h274).le hz2 hz
        · -- right
          by_cases h275 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h276 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h277 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1785_pos (not_le.mp h267).le h266 hz1 h277 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1787_pos (not_le.mp h267).le h266 (not_le.mp h277).le h276 hz
            · -- right
              by_cases h278 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1793_pos (not_le.mp h267).le h266 (not_le.mp h276).le h278 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1795_pos (not_le.mp h267).le h266 (not_le.mp h278).le h275 hz
          · -- right
            by_cases h279 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h280 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1817_pos (not_le.mp h267).le h266 (not_le.mp h275).le h280 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1819_pos (not_le.mp h267).le h266 (not_le.mp h280).le h279 hz
            · -- right
              by_cases h281 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1825_pos (not_le.mp h267).le h266 (not_le.mp h279).le h281 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1827_pos (not_le.mp h267).le h266 (not_le.mp h281).le hz2 hz
      · -- right
        by_cases h282 : a ≤ ((251703/1638400 : ℚ) : ℝ)
        · -- left
          by_cases h283 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h284 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h285 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1788_pos (not_le.mp h266).le h282 hz1 h285 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1790_pos (not_le.mp h266).le h282 (not_le.mp h285).le h284 hz
            · -- right
              by_cases h286 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1796_pos (not_le.mp h266).le h282 (not_le.mp h284).le h286 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1798_pos (not_le.mp h266).le h282 (not_le.mp h286).le h283 hz
          · -- right
            by_cases h287 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h288 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1820_pos (not_le.mp h266).le h282 (not_le.mp h283).le h288 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1822_pos (not_le.mp h266).le h282 (not_le.mp h288).le h287 hz
            · -- right
              by_cases h289 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1828_pos (not_le.mp h266).le h282 (not_le.mp h287).le h289 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1830_pos (not_le.mp h266).le h282 (not_le.mp h289).le hz2 hz
        · -- right
          by_cases h290 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h291 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h292 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1789_pos (not_le.mp h282).le h265 hz1 h292 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1791_pos (not_le.mp h282).le h265 (not_le.mp h292).le h291 hz
            · -- right
              by_cases h293 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B029.e1797_pos (not_le.mp h282).le h265 (not_le.mp h291).le h293 hz
              · -- right
                exact CKLaneC2R.EpCells.B029.e1799_pos (not_le.mp h282).le h265 (not_le.mp h293).le h290 hz
          · -- right
            by_cases h294 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h295 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1821_pos (not_le.mp h282).le h265 (not_le.mp h290).le h295 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1823_pos (not_le.mp h282).le h265 (not_le.mp h295).le h294 hz
            · -- right
              by_cases h296 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1829_pos (not_le.mp h282).le h265 (not_le.mp h294).le h296 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1831_pos (not_le.mp h282).le h265 (not_le.mp h296).le hz2 hz
    · -- right
      by_cases h297 : a ≤ ((630531/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h298 : a ≤ ((1260213/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h299 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h300 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h301 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1800_pos (not_le.mp h265).le h298 hz1 h301 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1802_pos (not_le.mp h265).le h298 (not_le.mp h301).le h300 hz
            · -- right
              by_cases h302 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1808_pos (not_le.mp h265).le h298 (not_le.mp h300).le h302 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1810_pos (not_le.mp h265).le h298 (not_le.mp h302).le h299 hz
          · -- right
            by_cases h303 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h304 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1832_pos (not_le.mp h265).le h298 (not_le.mp h299).le h304 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1834_pos (not_le.mp h265).le h298 (not_le.mp h304).le h303 hz
            · -- right
              by_cases h305 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1840_pos (not_le.mp h265).le h298 (not_le.mp h303).le h305 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1842_pos (not_le.mp h265).le h298 (not_le.mp h305).le hz2 hz
        · -- right
          by_cases h306 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h307 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h308 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1801_pos (not_le.mp h298).le h297 hz1 h308 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1803_pos (not_le.mp h298).le h297 (not_le.mp h308).le h307 hz
            · -- right
              by_cases h309 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1809_pos (not_le.mp h298).le h297 (not_le.mp h307).le h309 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1811_pos (not_le.mp h298).le h297 (not_le.mp h309).le h306 hz
          · -- right
            by_cases h310 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h311 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1833_pos (not_le.mp h298).le h297 (not_le.mp h306).le h311 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1835_pos (not_le.mp h298).le h297 (not_le.mp h311).le h310 hz
            · -- right
              by_cases h312 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1841_pos (not_le.mp h298).le h297 (not_le.mp h310).le h312 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1843_pos (not_le.mp h298).le h297 (not_le.mp h312).le hz2 hz
      · -- right
        by_cases h313 : a ≤ ((1261911/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h314 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h315 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h316 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1804_pos (not_le.mp h297).le h313 hz1 h316 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1806_pos (not_le.mp h297).le h313 (not_le.mp h316).le h315 hz
            · -- right
              by_cases h317 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1812_pos (not_le.mp h297).le h313 (not_le.mp h315).le h317 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1814_pos (not_le.mp h297).le h313 (not_le.mp h317).le h314 hz
          · -- right
            by_cases h318 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h319 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1836_pos (not_le.mp h297).le h313 (not_le.mp h314).le h319 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1838_pos (not_le.mp h297).le h313 (not_le.mp h319).le h318 hz
            · -- right
              by_cases h320 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1844_pos (not_le.mp h297).le h313 (not_le.mp h318).le h320 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1846_pos (not_le.mp h297).le h313 (not_le.mp h320).le hz2 hz
        · -- right
          by_cases h321 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h322 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h323 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1805_pos (not_le.mp h313).le h264 hz1 h323 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1807_pos (not_le.mp h313).le h264 (not_le.mp h323).le h322 hz
            · -- right
              by_cases h324 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1813_pos (not_le.mp h313).le h264 (not_le.mp h322).le h324 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1815_pos (not_le.mp h313).le h264 (not_le.mp h324).le h321 hz
          · -- right
            by_cases h325 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h326 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1837_pos (not_le.mp h313).le h264 (not_le.mp h321).le h326 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1839_pos (not_le.mp h313).le h264 (not_le.mp h326).le h325 hz
            · -- right
              by_cases h327 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1845_pos (not_le.mp h313).le h264 (not_le.mp h325).le h327 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1847_pos (not_le.mp h313).le h264 (not_le.mp h327).le hz2 hz
  · -- right
    by_cases h328 : a ≤ ((316539/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h329 : a ≤ ((632229/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h330 : a ≤ ((1263609/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h331 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h332 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h333 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1848_pos (not_le.mp h264).le h330 hz1 h333 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1850_pos (not_le.mp h264).le h330 (not_le.mp h333).le h332 hz
            · -- right
              by_cases h334 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1856_pos (not_le.mp h264).le h330 (not_le.mp h332).le h334 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1858_pos (not_le.mp h264).le h330 (not_le.mp h334).le h331 hz
          · -- right
            by_cases h335 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h336 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1880_pos (not_le.mp h264).le h330 (not_le.mp h331).le h336 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1882_pos (not_le.mp h264).le h330 (not_le.mp h336).le h335 hz
            · -- right
              by_cases h337 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1888_pos (not_le.mp h264).le h330 (not_le.mp h335).le h337 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1890_pos (not_le.mp h264).le h330 (not_le.mp h337).le hz2 hz
        · -- right
          by_cases h338 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h339 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h340 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1849_pos (not_le.mp h330).le h329 hz1 h340 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1851_pos (not_le.mp h330).le h329 (not_le.mp h340).le h339 hz
            · -- right
              by_cases h341 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1857_pos (not_le.mp h330).le h329 (not_le.mp h339).le h341 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1859_pos (not_le.mp h330).le h329 (not_le.mp h341).le h338 hz
          · -- right
            by_cases h342 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h343 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1881_pos (not_le.mp h330).le h329 (not_le.mp h338).le h343 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1883_pos (not_le.mp h330).le h329 (not_le.mp h343).le h342 hz
            · -- right
              by_cases h344 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1889_pos (not_le.mp h330).le h329 (not_le.mp h342).le h344 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1891_pos (not_le.mp h330).le h329 (not_le.mp h344).le hz2 hz
      · -- right
        by_cases h345 : a ≤ ((1265307/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h346 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h347 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h348 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1852_pos (not_le.mp h329).le h345 hz1 h348 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1854_pos (not_le.mp h329).le h345 (not_le.mp h348).le h347 hz
            · -- right
              by_cases h349 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1860_pos (not_le.mp h329).le h345 (not_le.mp h347).le h349 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1862_pos (not_le.mp h329).le h345 (not_le.mp h349).le h346 hz
          · -- right
            by_cases h350 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h351 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1884_pos (not_le.mp h329).le h345 (not_le.mp h346).le h351 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1886_pos (not_le.mp h329).le h345 (not_le.mp h351).le h350 hz
            · -- right
              by_cases h352 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1892_pos (not_le.mp h329).le h345 (not_le.mp h350).le h352 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1894_pos (not_le.mp h329).le h345 (not_le.mp h352).le hz2 hz
        · -- right
          by_cases h353 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h354 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h355 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B030.e1853_pos (not_le.mp h345).le h328 hz1 h355 hz
              · -- right
                exact CKLaneC2R.EpCells.B030.e1855_pos (not_le.mp h345).le h328 (not_le.mp h355).le h354 hz
            · -- right
              by_cases h356 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1861_pos (not_le.mp h345).le h328 (not_le.mp h354).le h356 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1863_pos (not_le.mp h345).le h328 (not_le.mp h356).le h353 hz
          · -- right
            by_cases h357 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h358 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1885_pos (not_le.mp h345).le h328 (not_le.mp h353).le h358 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1887_pos (not_le.mp h345).le h328 (not_le.mp h358).le h357 hz
            · -- right
              by_cases h359 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1893_pos (not_le.mp h345).le h328 (not_le.mp h357).le h359 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1895_pos (not_le.mp h345).le h328 (not_le.mp h359).le hz2 hz
    · -- right
      by_cases h360 : a ≤ ((633927/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h361 : a ≤ ((253401/1638400 : ℚ) : ℝ)
        · -- left
          by_cases h362 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h363 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h364 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1864_pos (not_le.mp h328).le h361 hz1 h364 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1866_pos (not_le.mp h328).le h361 (not_le.mp h364).le h363 hz
            · -- right
              by_cases h365 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1872_pos (not_le.mp h328).le h361 (not_le.mp h363).le h365 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1874_pos (not_le.mp h328).le h361 (not_le.mp h365).le h362 hz
          · -- right
            by_cases h366 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h367 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1896_pos (not_le.mp h328).le h361 (not_le.mp h362).le h367 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1898_pos (not_le.mp h328).le h361 (not_le.mp h367).le h366 hz
            · -- right
              by_cases h368 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1904_pos (not_le.mp h328).le h361 (not_le.mp h366).le h368 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1906_pos (not_le.mp h328).le h361 (not_le.mp h368).le hz2 hz
        · -- right
          by_cases h369 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h370 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h371 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1865_pos (not_le.mp h361).le h360 hz1 h371 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1867_pos (not_le.mp h361).le h360 (not_le.mp h371).le h370 hz
            · -- right
              by_cases h372 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1873_pos (not_le.mp h361).le h360 (not_le.mp h370).le h372 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1875_pos (not_le.mp h361).le h360 (not_le.mp h372).le h369 hz
          · -- right
            by_cases h373 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h374 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1897_pos (not_le.mp h361).le h360 (not_le.mp h369).le h374 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1899_pos (not_le.mp h361).le h360 (not_le.mp h374).le h373 hz
            · -- right
              by_cases h375 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1905_pos (not_le.mp h361).le h360 (not_le.mp h373).le h375 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1907_pos (not_le.mp h361).le h360 (not_le.mp h375).le hz2 hz
      · -- right
        by_cases h376 : a ≤ ((1268703/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h377 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h378 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h379 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1868_pos (not_le.mp h360).le h376 hz1 h379 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1870_pos (not_le.mp h360).le h376 (not_le.mp h379).le h378 hz
            · -- right
              by_cases h380 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1876_pos (not_le.mp h360).le h376 (not_le.mp h378).le h380 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1878_pos (not_le.mp h360).le h376 (not_le.mp h380).le h377 hz
          · -- right
            by_cases h381 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h382 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1900_pos (not_le.mp h360).le h376 (not_le.mp h377).le h382 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1902_pos (not_le.mp h360).le h376 (not_le.mp h382).le h381 hz
            · -- right
              by_cases h383 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1908_pos (not_le.mp h360).le h376 (not_le.mp h381).le h383 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1910_pos (not_le.mp h360).le h376 (not_le.mp h383).le hz2 hz
        · -- right
          by_cases h384 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h385 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h386 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1869_pos (not_le.mp h376).le h263 hz1 h386 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1871_pos (not_le.mp h376).le h263 (not_le.mp h386).le h385 hz
            · -- right
              by_cases h387 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1877_pos (not_le.mp h376).le h263 (not_le.mp h385).le h387 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1879_pos (not_le.mp h376).le h263 (not_le.mp h387).le h384 hz
          · -- right
            by_cases h388 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h389 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1901_pos (not_le.mp h376).le h263 (not_le.mp h384).le h389 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1903_pos (not_le.mp h376).le h263 (not_le.mp h389).le h388 hz
            · -- right
              by_cases h390 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1909_pos (not_le.mp h376).le h263 (not_le.mp h388).le h390 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1911_pos (not_le.mp h376).le h263 (not_le.mp h390).le hz2 hz

end CKLaneC2R.EndpointCover


