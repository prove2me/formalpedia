-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q03
-- name    : CK_CKLaneC2R_EndpointCover_b00_q03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:50:38.90093+00:00
-- url     : https://prove2.me/theorems/ef8f81e5-8b2b-4bed-9242-5200ee0a6e84
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 4 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 4 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 4 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 4 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 1 of 5) (piece 4 of 5).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B031
import Definitions.Def_CK_CKLaneC2R_EpCells_B032__2
namespace CKLaneC2R.EndpointCover
theorem cover_sub_003 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : a ≤ ((20049/128000 : ℚ) : ℝ)) (h7 : ¬ (a ≤ ((39249/256000 : ℚ) : ℝ))) (h263 : ¬ (a ≤ ((79347/512000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h391 : a ≤ ((159543/1024000 : ℚ) : ℝ)
  · -- left
    by_cases h392 : a ≤ ((318237/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h393 : a ≤ ((5085/32768 : ℚ) : ℝ)
      · -- left
        by_cases h394 : a ≤ ((1270401/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h395 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h396 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h397 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1912_pos (not_le.mp h263).le h394 hz1 h397 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1914_pos (not_le.mp h263).le h394 (not_le.mp h397).le h396 hz
            · -- right
              by_cases h398 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1920_pos (not_le.mp h263).le h394 (not_le.mp h396).le h398 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1922_pos (not_le.mp h263).le h394 (not_le.mp h398).le h395 hz
          · -- right
            by_cases h399 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h400 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1944_pos (not_le.mp h263).le h394 (not_le.mp h395).le h400 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1946_pos (not_le.mp h263).le h394 (not_le.mp h400).le h399 hz
            · -- right
              by_cases h401 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1952_pos (not_le.mp h263).le h394 (not_le.mp h399).le h401 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1954_pos (not_le.mp h263).le h394 (not_le.mp h401).le hz2 hz
        · -- right
          by_cases h402 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h403 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h404 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1913_pos (not_le.mp h394).le h393 hz1 h404 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1915_pos (not_le.mp h394).le h393 (not_le.mp h404).le h403 hz
            · -- right
              by_cases h405 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1921_pos (not_le.mp h394).le h393 (not_le.mp h403).le h405 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1923_pos (not_le.mp h394).le h393 (not_le.mp h405).le h402 hz
          · -- right
            by_cases h406 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h407 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1945_pos (not_le.mp h394).le h393 (not_le.mp h402).le h407 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1947_pos (not_le.mp h394).le h393 (not_le.mp h407).le h406 hz
            · -- right
              by_cases h408 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1953_pos (not_le.mp h394).le h393 (not_le.mp h406).le h408 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1955_pos (not_le.mp h394).le h393 (not_le.mp h408).le hz2 hz
      · -- right
        by_cases h409 : a ≤ ((1272099/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h410 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h411 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h412 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1916_pos (not_le.mp h393).le h409 hz1 h412 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1918_pos (not_le.mp h393).le h409 (not_le.mp h412).le h411 hz
            · -- right
              by_cases h413 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1924_pos (not_le.mp h393).le h409 (not_le.mp h411).le h413 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1926_pos (not_le.mp h393).le h409 (not_le.mp h413).le h410 hz
          · -- right
            by_cases h414 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h415 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1948_pos (not_le.mp h393).le h409 (not_le.mp h410).le h415 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1950_pos (not_le.mp h393).le h409 (not_le.mp h415).le h414 hz
            · -- right
              by_cases h416 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1956_pos (not_le.mp h393).le h409 (not_le.mp h414).le h416 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1958_pos (not_le.mp h393).le h409 (not_le.mp h416).le hz2 hz
        · -- right
          by_cases h417 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h418 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h419 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B031.e1917_pos (not_le.mp h409).le h392 hz1 h419 hz
              · -- right
                exact CKLaneC2R.EpCells.B031.e1919_pos (not_le.mp h409).le h392 (not_le.mp h419).le h418 hz
            · -- right
              by_cases h420 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1925_pos (not_le.mp h409).le h392 (not_le.mp h418).le h420 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1927_pos (not_le.mp h409).le h392 (not_le.mp h420).le h417 hz
          · -- right
            by_cases h421 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h422 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1949_pos (not_le.mp h409).le h392 (not_le.mp h417).le h422 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1951_pos (not_le.mp h409).le h392 (not_le.mp h422).le h421 hz
            · -- right
              by_cases h423 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1957_pos (not_le.mp h409).le h392 (not_le.mp h421).le h423 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1959_pos (not_le.mp h409).le h392 (not_le.mp h423).le hz2 hz
    · -- right
      by_cases h424 : a ≤ ((637323/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h425 : a ≤ ((1273797/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h426 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h427 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h428 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1928_pos (not_le.mp h392).le h425 hz1 h428 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1930_pos (not_le.mp h392).le h425 (not_le.mp h428).le h427 hz
            · -- right
              by_cases h429 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1936_pos (not_le.mp h392).le h425 (not_le.mp h427).le h429 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1938_pos (not_le.mp h392).le h425 (not_le.mp h429).le h426 hz
          · -- right
            by_cases h430 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h431 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1960_pos (not_le.mp h392).le h425 (not_le.mp h426).le h431 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1962_pos (not_le.mp h392).le h425 (not_le.mp h431).le h430 hz
            · -- right
              by_cases h432 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1968_pos (not_le.mp h392).le h425 (not_le.mp h430).le h432 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1970_pos (not_le.mp h392).le h425 (not_le.mp h432).le hz2 hz
        · -- right
          by_cases h433 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h434 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h435 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1929_pos (not_le.mp h425).le h424 hz1 h435 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1931_pos (not_le.mp h425).le h424 (not_le.mp h435).le h434 hz
            · -- right
              by_cases h436 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1937_pos (not_le.mp h425).le h424 (not_le.mp h434).le h436 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1939_pos (not_le.mp h425).le h424 (not_le.mp h436).le h433 hz
          · -- right
            by_cases h437 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h438 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1961_pos (not_le.mp h425).le h424 (not_le.mp h433).le h438 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1963_pos (not_le.mp h425).le h424 (not_le.mp h438).le h437 hz
            · -- right
              by_cases h439 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1969_pos (not_le.mp h425).le h424 (not_le.mp h437).le h439 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1971_pos (not_le.mp h425).le h424 (not_le.mp h439).le hz2 hz
      · -- right
        by_cases h440 : a ≤ ((255099/1638400 : ℚ) : ℝ)
        · -- left
          by_cases h441 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h442 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h443 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1932_pos (not_le.mp h424).le h440 hz1 h443 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1934_pos (not_le.mp h424).le h440 (not_le.mp h443).le h442 hz
            · -- right
              by_cases h444 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1940_pos (not_le.mp h424).le h440 (not_le.mp h442).le h444 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1942_pos (not_le.mp h424).le h440 (not_le.mp h444).le h441 hz
          · -- right
            by_cases h445 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h446 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1964_pos (not_le.mp h424).le h440 (not_le.mp h441).le h446 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1966_pos (not_le.mp h424).le h440 (not_le.mp h446).le h445 hz
            · -- right
              by_cases h447 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1972_pos (not_le.mp h424).le h440 (not_le.mp h445).le h447 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1974_pos (not_le.mp h424).le h440 (not_le.mp h447).le hz2 hz
        · -- right
          by_cases h448 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h449 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h450 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1933_pos (not_le.mp h440).le h391 hz1 h450 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1935_pos (not_le.mp h440).le h391 (not_le.mp h450).le h449 hz
            · -- right
              by_cases h451 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1941_pos (not_le.mp h440).le h391 (not_le.mp h449).le h451 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1943_pos (not_le.mp h440).le h391 (not_le.mp h451).le h448 hz
          · -- right
            by_cases h452 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h453 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1965_pos (not_le.mp h440).le h391 (not_le.mp h448).le h453 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1967_pos (not_le.mp h440).le h391 (not_le.mp h453).le h452 hz
            · -- right
              by_cases h454 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1973_pos (not_le.mp h440).le h391 (not_le.mp h452).le h454 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1975_pos (not_le.mp h440).le h391 (not_le.mp h454).le hz2 hz
  · -- right
    by_cases h455 : a ≤ ((63987/409600 : ℚ) : ℝ)
    · -- left
      by_cases h456 : a ≤ ((639021/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h457 : a ≤ ((1277193/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h458 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h459 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h460 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1976_pos (not_le.mp h391).le h457 hz1 h460 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1978_pos (not_le.mp h391).le h457 (not_le.mp h460).le h459 hz
            · -- right
              by_cases h461 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e1984_pos (not_le.mp h391).le h457 (not_le.mp h459).le h461 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e1986_pos (not_le.mp h391).le h457 (not_le.mp h461).le h458 hz
          · -- right
            by_cases h462 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h463 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2008_pos (not_le.mp h391).le h457 (not_le.mp h458).le h463 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2010_pos (not_le.mp h391).le h457 (not_le.mp h463).le h462 hz
            · -- right
              by_cases h464 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2016_pos (not_le.mp h391).le h457 (not_le.mp h462).le h464 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2018_pos (not_le.mp h391).le h457 (not_le.mp h464).le hz2 hz
        · -- right
          by_cases h465 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h466 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h467 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B032.e1977_pos (not_le.mp h457).le h456 hz1 h467 hz
              · -- right
                exact CKLaneC2R.EpCells.B032.e1979_pos (not_le.mp h457).le h456 (not_le.mp h467).le h466 hz
            · -- right
              by_cases h468 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e1985_pos (not_le.mp h457).le h456 (not_le.mp h466).le h468 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e1987_pos (not_le.mp h457).le h456 (not_le.mp h468).le h465 hz
          · -- right
            by_cases h469 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h470 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2009_pos (not_le.mp h457).le h456 (not_le.mp h465).le h470 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2011_pos (not_le.mp h457).le h456 (not_le.mp h470).le h469 hz
            · -- right
              by_cases h471 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2017_pos (not_le.mp h457).le h456 (not_le.mp h469).le h471 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2019_pos (not_le.mp h457).le h456 (not_le.mp h471).le hz2 hz
      · -- right
        by_cases h472 : a ≤ ((1278891/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h473 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h474 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h475 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e1980_pos (not_le.mp h456).le h472 hz1 h475 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e1982_pos (not_le.mp h456).le h472 (not_le.mp h475).le h474 hz
            · -- right
              by_cases h476 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e1988_pos (not_le.mp h456).le h472 (not_le.mp h474).le h476 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e1990_pos (not_le.mp h456).le h472 (not_le.mp h476).le h473 hz
          · -- right
            by_cases h477 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h478 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2012_pos (not_le.mp h456).le h472 (not_le.mp h473).le h478 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2014_pos (not_le.mp h456).le h472 (not_le.mp h478).le h477 hz
            · -- right
              by_cases h479 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2020_pos (not_le.mp h456).le h472 (not_le.mp h477).le h479 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2022_pos (not_le.mp h456).le h472 (not_le.mp h479).le hz2 hz
        · -- right
          by_cases h480 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h481 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h482 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e1981_pos (not_le.mp h472).le h455 hz1 h482 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e1983_pos (not_le.mp h472).le h455 (not_le.mp h482).le h481 hz
            · -- right
              by_cases h483 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e1989_pos (not_le.mp h472).le h455 (not_le.mp h481).le h483 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e1991_pos (not_le.mp h472).le h455 (not_le.mp h483).le h480 hz
          · -- right
            by_cases h484 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h485 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2013_pos (not_le.mp h472).le h455 (not_le.mp h480).le h485 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2015_pos (not_le.mp h472).le h455 (not_le.mp h485).le h484 hz
            · -- right
              by_cases h486 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2021_pos (not_le.mp h472).le h455 (not_le.mp h484).le h486 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2023_pos (not_le.mp h472).le h455 (not_le.mp h486).le hz2 hz
    · -- right
      by_cases h487 : a ≤ ((640719/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h488 : a ≤ ((1280589/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h489 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h490 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h491 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e1992_pos (not_le.mp h455).le h488 hz1 h491 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e1994_pos (not_le.mp h455).le h488 (not_le.mp h491).le h490 hz
            · -- right
              by_cases h492 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2000_pos (not_le.mp h455).le h488 (not_le.mp h490).le h492 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2002_pos (not_le.mp h455).le h488 (not_le.mp h492).le h489 hz
          · -- right
            by_cases h493 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h494 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2024_pos (not_le.mp h455).le h488 (not_le.mp h489).le h494 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2026_pos (not_le.mp h455).le h488 (not_le.mp h494).le h493 hz
            · -- right
              by_cases h495 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2032_pos (not_le.mp h455).le h488 (not_le.mp h493).le h495 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2034_pos (not_le.mp h455).le h488 (not_le.mp h495).le hz2 hz
        · -- right
          by_cases h496 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h497 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h498 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e1993_pos (not_le.mp h488).le h487 hz1 h498 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e1995_pos (not_le.mp h488).le h487 (not_le.mp h498).le h497 hz
            · -- right
              by_cases h499 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2001_pos (not_le.mp h488).le h487 (not_le.mp h497).le h499 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2003_pos (not_le.mp h488).le h487 (not_le.mp h499).le h496 hz
          · -- right
            by_cases h500 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h501 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2025_pos (not_le.mp h488).le h487 (not_le.mp h496).le h501 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2027_pos (not_le.mp h488).le h487 (not_le.mp h501).le h500 hz
            · -- right
              by_cases h502 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2033_pos (not_le.mp h488).le h487 (not_le.mp h500).le h502 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2035_pos (not_le.mp h488).le h487 (not_le.mp h502).le hz2 hz
      · -- right
        by_cases h503 : a ≤ ((1282287/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h504 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h505 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h506 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e1996_pos (not_le.mp h487).le h503 hz1 h506 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e1998_pos (not_le.mp h487).le h503 (not_le.mp h506).le h505 hz
            · -- right
              by_cases h507 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2004_pos (not_le.mp h487).le h503 (not_le.mp h505).le h507 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2006_pos (not_le.mp h487).le h503 (not_le.mp h507).le h504 hz
          · -- right
            by_cases h508 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h509 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2028_pos (not_le.mp h487).le h503 (not_le.mp h504).le h509 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2030_pos (not_le.mp h487).le h503 (not_le.mp h509).le h508 hz
            · -- right
              by_cases h510 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2036_pos (not_le.mp h487).le h503 (not_le.mp h508).le h510 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2038_pos (not_le.mp h487).le h503 (not_le.mp h510).le hz2 hz
        · -- right
          by_cases h511 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h512 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h513 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e1997_pos (not_le.mp h503).le h6 hz1 h513 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e1999_pos (not_le.mp h503).le h6 (not_le.mp h513).le h512 hz
            · -- right
              by_cases h514 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2005_pos (not_le.mp h503).le h6 (not_le.mp h512).le h514 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2007_pos (not_le.mp h503).le h6 (not_le.mp h514).le h511 hz
          · -- right
            by_cases h515 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h516 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2029_pos (not_le.mp h503).le h6 (not_le.mp h511).le h516 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2031_pos (not_le.mp h503).le h6 (not_le.mp h516).le h515 hz
            · -- right
              by_cases h517 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B033.e2037_pos (not_le.mp h503).le h6 (not_le.mp h515).le h517 hz
              · -- right
                exact CKLaneC2R.EpCells.B033.e2039_pos (not_le.mp h503).le h6 (not_le.mp h517).le hz2 hz

end CKLaneC2R.EndpointCover


