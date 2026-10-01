-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b03
-- name    : CK_CKLaneC2R_EndpointCover_b03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:47:30.42234+00:00
-- url     : https://prove2.me/theorems/07ec8048-fac2-4c1d-b81f-8da346e7f1d5
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 4 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 4 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 4 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 4 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 4 of 5).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B015__2
import Definitions.Def_CK_CKLaneC2R_EpCells_B017
import Definitions.Def_CK_CKLaneC2R_EpCells_B018
namespace CKLaneC2R.EndpointCover

theorem cover_sub_014 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : ¬ (a ≤ ((5649/32000 : ℚ) : ℝ))) (h1613 : ¬ (a ≤ ((12147/64000 : ℚ) : ℝ))) (h1869 : a ≤ ((25143/128000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1870 : a ≤ ((49437/256000 : ℚ) : ℝ)
  · -- left
    by_cases h1871 : a ≤ ((3921/20480 : ℚ) : ℝ)
    · -- left
      by_cases h1872 : a ≤ ((195201/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h1873 : a ≤ ((389553/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1874 : a ≤ ((778257/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1875 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1876 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e957_pos (not_le.mp h1613).le h1874 hz1 h1876 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e959_pos (not_le.mp h1613).le h1874 (not_le.mp h1876).le h1875 hz
            · -- right
              by_cases h1877 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e965_pos (not_le.mp h1613).le h1874 (not_le.mp h1875).le h1877 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e967_pos (not_le.mp h1613).le h1874 (not_le.mp h1877).le hz2 hz
          · -- right
            by_cases h1878 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1879 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e958_pos (not_le.mp h1874).le h1873 hz1 h1879 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e960_pos (not_le.mp h1874).le h1873 (not_le.mp h1879).le h1878 hz
            · -- right
              by_cases h1880 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e966_pos (not_le.mp h1874).le h1873 (not_le.mp h1878).le h1880 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e968_pos (not_le.mp h1874).le h1873 (not_le.mp h1880).le hz2 hz
        · -- right
          by_cases h1881 : a ≤ ((155991/819200 : ℚ) : ℝ)
          · -- left
            by_cases h1882 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1883 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e961_pos (not_le.mp h1873).le h1881 hz1 h1883 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e963_pos (not_le.mp h1873).le h1881 (not_le.mp h1883).le h1882 hz
            · -- right
              by_cases h1884 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e969_pos (not_le.mp h1873).le h1881 (not_le.mp h1882).le h1884 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e971_pos (not_le.mp h1873).le h1881 (not_le.mp h1884).le hz2 hz
          · -- right
            by_cases h1885 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1886 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e962_pos (not_le.mp h1881).le h1872 hz1 h1886 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e964_pos (not_le.mp h1881).le h1872 (not_le.mp h1886).le h1885 hz
            · -- right
              by_cases h1887 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e970_pos (not_le.mp h1881).le h1872 (not_le.mp h1885).le h1887 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e972_pos (not_le.mp h1881).le h1872 (not_le.mp h1887).le hz2 hz
      · -- right
        by_cases h1888 : a ≤ ((391251/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1889 : a ≤ ((781653/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1890 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1891 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e973_pos (not_le.mp h1872).le h1889 hz1 h1891 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e975_pos (not_le.mp h1872).le h1889 (not_le.mp h1891).le h1890 hz
            · -- right
              by_cases h1892 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e981_pos (not_le.mp h1872).le h1889 (not_le.mp h1890).le h1892 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e983_pos (not_le.mp h1872).le h1889 (not_le.mp h1892).le hz2 hz
          · -- right
            by_cases h1893 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1894 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e974_pos (not_le.mp h1889).le h1888 hz1 h1894 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e976_pos (not_le.mp h1889).le h1888 (not_le.mp h1894).le h1893 hz
            · -- right
              by_cases h1895 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e982_pos (not_le.mp h1889).le h1888 (not_le.mp h1893).le h1895 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e984_pos (not_le.mp h1889).le h1888 (not_le.mp h1895).le hz2 hz
        · -- right
          by_cases h1896 : a ≤ ((783351/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1897 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1898 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e977_pos (not_le.mp h1888).le h1896 hz1 h1898 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e979_pos (not_le.mp h1888).le h1896 (not_le.mp h1898).le h1897 hz
            · -- right
              by_cases h1899 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e985_pos (not_le.mp h1888).le h1896 (not_le.mp h1897).le h1899 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e987_pos (not_le.mp h1888).le h1896 (not_le.mp h1899).le hz2 hz
          · -- right
            by_cases h1900 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1901 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e978_pos (not_le.mp h1896).le h1871 hz1 h1901 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e980_pos (not_le.mp h1896).le h1871 (not_le.mp h1901).le h1900 hz
            · -- right
              by_cases h1902 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e986_pos (not_le.mp h1896).le h1871 (not_le.mp h1900).le h1902 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e988_pos (not_le.mp h1896).le h1871 (not_le.mp h1902).le hz2 hz
    · -- right
      by_cases h1903 : a ≤ ((196899/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h1904 : a ≤ ((392949/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1905 : a ≤ ((785049/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1906 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1907 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e989_pos (not_le.mp h1871).le h1905 hz1 h1907 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e991_pos (not_le.mp h1871).le h1905 (not_le.mp h1907).le h1906 hz
            · -- right
              by_cases h1908 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e997_pos (not_le.mp h1871).le h1905 (not_le.mp h1906).le h1908 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e999_pos (not_le.mp h1871).le h1905 (not_le.mp h1908).le hz2 hz
          · -- right
            by_cases h1909 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1910 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e990_pos (not_le.mp h1905).le h1904 hz1 h1910 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e992_pos (not_le.mp h1905).le h1904 (not_le.mp h1910).le h1909 hz
            · -- right
              by_cases h1911 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e998_pos (not_le.mp h1905).le h1904 (not_le.mp h1909).le h1911 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e1000_pos (not_le.mp h1905).le h1904 (not_le.mp h1911).le hz2 hz
        · -- right
          by_cases h1912 : a ≤ ((786747/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1913 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1914 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e993_pos (not_le.mp h1904).le h1912 hz1 h1914 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e995_pos (not_le.mp h1904).le h1912 (not_le.mp h1914).le h1913 hz
            · -- right
              by_cases h1915 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e1001_pos (not_le.mp h1904).le h1912 (not_le.mp h1913).le h1915 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e1003_pos (not_le.mp h1904).le h1912 (not_le.mp h1915).le hz2 hz
          · -- right
            by_cases h1916 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1917 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e994_pos (not_le.mp h1912).le h1903 hz1 h1917 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e996_pos (not_le.mp h1912).le h1903 (not_le.mp h1917).le h1916 hz
            · -- right
              by_cases h1918 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e1002_pos (not_le.mp h1912).le h1903 (not_le.mp h1916).le h1918 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e1004_pos (not_le.mp h1912).le h1903 (not_le.mp h1918).le hz2 hz
      · -- right
        by_cases h1919 : a ≤ ((394647/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1920 : a ≤ ((157689/819200 : ℚ) : ℝ)
          · -- left
            by_cases h1921 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1922 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e1005_pos (not_le.mp h1903).le h1920 hz1 h1922 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e1007_pos (not_le.mp h1903).le h1920 (not_le.mp h1922).le h1921 hz
            · -- right
              by_cases h1923 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e1013_pos (not_le.mp h1903).le h1920 (not_le.mp h1921).le h1923 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e1015_pos (not_le.mp h1903).le h1920 (not_le.mp h1923).le hz2 hz
          · -- right
            by_cases h1924 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1925 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e1006_pos (not_le.mp h1920).le h1919 hz1 h1925 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e1008_pos (not_le.mp h1920).le h1919 (not_le.mp h1925).le h1924 hz
            · -- right
              by_cases h1926 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e1014_pos (not_le.mp h1920).le h1919 (not_le.mp h1924).le h1926 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e1016_pos (not_le.mp h1920).le h1919 (not_le.mp h1926).le hz2 hz
        · -- right
          by_cases h1927 : a ≤ ((790143/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1928 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1929 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e1009_pos (not_le.mp h1919).le h1927 hz1 h1929 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e1011_pos (not_le.mp h1919).le h1927 (not_le.mp h1929).le h1928 hz
            · -- right
              by_cases h1930 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e1017_pos (not_le.mp h1919).le h1927 (not_le.mp h1928).le h1930 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e1019_pos (not_le.mp h1919).le h1927 (not_le.mp h1930).le hz2 hz
          · -- right
            by_cases h1931 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1932 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e1010_pos (not_le.mp h1927).le h1870 hz1 h1932 hz
              · -- right
                exact CKLaneC2R.EpCells.B016.e1012_pos (not_le.mp h1927).le h1870 (not_le.mp h1932).le h1931 hz
            · -- right
              by_cases h1933 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B016.e1018_pos (not_le.mp h1927).le h1870 (not_le.mp h1931).le h1933 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1020_pos (not_le.mp h1927).le h1870 (not_le.mp h1933).le hz2 hz
  · -- right
    by_cases h1934 : a ≤ ((99723/512000 : ℚ) : ℝ)
    · -- left
      by_cases h1935 : a ≤ ((198597/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h1936 : a ≤ ((79269/409600 : ℚ) : ℝ)
        · -- left
          by_cases h1937 : a ≤ ((791841/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1938 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1939 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1021_pos (not_le.mp h1870).le h1937 hz1 h1939 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1023_pos (not_le.mp h1870).le h1937 (not_le.mp h1939).le h1938 hz
            · -- right
              by_cases h1940 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1029_pos (not_le.mp h1870).le h1937 (not_le.mp h1938).le h1940 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1031_pos (not_le.mp h1870).le h1937 (not_le.mp h1940).le hz2 hz
          · -- right
            by_cases h1941 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1942 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1022_pos (not_le.mp h1937).le h1936 hz1 h1942 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1024_pos (not_le.mp h1937).le h1936 (not_le.mp h1942).le h1941 hz
            · -- right
              by_cases h1943 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1030_pos (not_le.mp h1937).le h1936 (not_le.mp h1941).le h1943 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1032_pos (not_le.mp h1937).le h1936 (not_le.mp h1943).le hz2 hz
        · -- right
          by_cases h1944 : a ≤ ((793539/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1945 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1946 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1025_pos (not_le.mp h1936).le h1944 hz1 h1946 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1027_pos (not_le.mp h1936).le h1944 (not_le.mp h1946).le h1945 hz
            · -- right
              by_cases h1947 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1033_pos (not_le.mp h1936).le h1944 (not_le.mp h1945).le h1947 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1035_pos (not_le.mp h1936).le h1944 (not_le.mp h1947).le hz2 hz
          · -- right
            by_cases h1948 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1949 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1026_pos (not_le.mp h1944).le h1935 hz1 h1949 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1028_pos (not_le.mp h1944).le h1935 (not_le.mp h1949).le h1948 hz
            · -- right
              by_cases h1950 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1034_pos (not_le.mp h1944).le h1935 (not_le.mp h1948).le h1950 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1036_pos (not_le.mp h1944).le h1935 (not_le.mp h1950).le hz2 hz
      · -- right
        by_cases h1951 : a ≤ ((398043/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1952 : a ≤ ((795237/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1953 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1954 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1037_pos (not_le.mp h1935).le h1952 hz1 h1954 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1039_pos (not_le.mp h1935).le h1952 (not_le.mp h1954).le h1953 hz
            · -- right
              by_cases h1955 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1045_pos (not_le.mp h1935).le h1952 (not_le.mp h1953).le h1955 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1047_pos (not_le.mp h1935).le h1952 (not_le.mp h1955).le hz2 hz
          · -- right
            by_cases h1956 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1957 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1038_pos (not_le.mp h1952).le h1951 hz1 h1957 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1040_pos (not_le.mp h1952).le h1951 (not_le.mp h1957).le h1956 hz
            · -- right
              by_cases h1958 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1046_pos (not_le.mp h1952).le h1951 (not_le.mp h1956).le h1958 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1048_pos (not_le.mp h1952).le h1951 (not_le.mp h1958).le hz2 hz
        · -- right
          by_cases h1959 : a ≤ ((159387/819200 : ℚ) : ℝ)
          · -- left
            by_cases h1960 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1961 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1041_pos (not_le.mp h1951).le h1959 hz1 h1961 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1043_pos (not_le.mp h1951).le h1959 (not_le.mp h1961).le h1960 hz
            · -- right
              by_cases h1962 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1049_pos (not_le.mp h1951).le h1959 (not_le.mp h1960).le h1962 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1051_pos (not_le.mp h1951).le h1959 (not_le.mp h1962).le hz2 hz
          · -- right
            by_cases h1963 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1964 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1042_pos (not_le.mp h1959).le h1934 hz1 h1964 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1044_pos (not_le.mp h1959).le h1934 (not_le.mp h1964).le h1963 hz
            · -- right
              by_cases h1965 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1050_pos (not_le.mp h1959).le h1934 (not_le.mp h1963).le h1965 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1052_pos (not_le.mp h1959).le h1934 (not_le.mp h1965).le hz2 hz
    · -- right
      by_cases h1966 : a ≤ ((40059/204800 : ℚ) : ℝ)
      · -- left
        by_cases h1967 : a ≤ ((399741/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1968 : a ≤ ((798633/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1969 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1970 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1053_pos (not_le.mp h1934).le h1968 hz1 h1970 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1055_pos (not_le.mp h1934).le h1968 (not_le.mp h1970).le h1969 hz
            · -- right
              by_cases h1971 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1061_pos (not_le.mp h1934).le h1968 (not_le.mp h1969).le h1971 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1063_pos (not_le.mp h1934).le h1968 (not_le.mp h1971).le hz2 hz
          · -- right
            by_cases h1972 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1973 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1054_pos (not_le.mp h1968).le h1967 hz1 h1973 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1056_pos (not_le.mp h1968).le h1967 (not_le.mp h1973).le h1972 hz
            · -- right
              by_cases h1974 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1062_pos (not_le.mp h1968).le h1967 (not_le.mp h1972).le h1974 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1064_pos (not_le.mp h1968).le h1967 (not_le.mp h1974).le hz2 hz
        · -- right
          by_cases h1975 : a ≤ ((800331/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1976 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1977 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1057_pos (not_le.mp h1967).le h1975 hz1 h1977 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1059_pos (not_le.mp h1967).le h1975 (not_le.mp h1977).le h1976 hz
            · -- right
              by_cases h1978 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1065_pos (not_le.mp h1967).le h1975 (not_le.mp h1976).le h1978 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1067_pos (not_le.mp h1967).le h1975 (not_le.mp h1978).le hz2 hz
          · -- right
            by_cases h1979 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1980 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1058_pos (not_le.mp h1975).le h1966 hz1 h1980 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1060_pos (not_le.mp h1975).le h1966 (not_le.mp h1980).le h1979 hz
            · -- right
              by_cases h1981 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1066_pos (not_le.mp h1975).le h1966 (not_le.mp h1979).le h1981 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1068_pos (not_le.mp h1975).le h1966 (not_le.mp h1981).le hz2 hz
      · -- right
        by_cases h1982 : a ≤ ((401439/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1983 : a ≤ ((802029/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1984 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1985 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1069_pos (not_le.mp h1966).le h1983 hz1 h1985 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1071_pos (not_le.mp h1966).le h1983 (not_le.mp h1985).le h1984 hz
            · -- right
              by_cases h1986 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1077_pos (not_le.mp h1966).le h1983 (not_le.mp h1984).le h1986 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1079_pos (not_le.mp h1966).le h1983 (not_le.mp h1986).le hz2 hz
          · -- right
            by_cases h1987 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1988 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1070_pos (not_le.mp h1983).le h1982 hz1 h1988 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1072_pos (not_le.mp h1983).le h1982 (not_le.mp h1988).le h1987 hz
            · -- right
              by_cases h1989 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1078_pos (not_le.mp h1983).le h1982 (not_le.mp h1987).le h1989 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1080_pos (not_le.mp h1983).le h1982 (not_le.mp h1989).le hz2 hz
        · -- right
          by_cases h1990 : a ≤ ((803727/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1991 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1992 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1073_pos (not_le.mp h1982).le h1990 hz1 h1992 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1075_pos (not_le.mp h1982).le h1990 (not_le.mp h1992).le h1991 hz
            · -- right
              by_cases h1993 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1081_pos (not_le.mp h1982).le h1990 (not_le.mp h1991).le h1993 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1083_pos (not_le.mp h1982).le h1990 (not_le.mp h1993).le hz2 hz
          · -- right
            by_cases h1994 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1995 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B017.e1074_pos (not_le.mp h1990).le h1869 hz1 h1995 hz
              · -- right
                exact CKLaneC2R.EpCells.B017.e1076_pos (not_le.mp h1990).le h1869 (not_le.mp h1995).le h1994 hz
            · -- right
              by_cases h1996 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B018.e1082_pos (not_le.mp h1990).le h1869 (not_le.mp h1994).le h1996 hz
              · -- right
                exact CKLaneC2R.EpCells.B018.e1084_pos (not_le.mp h1990).le h1869 (not_le.mp h1996).le hz2 hz

end CKLaneC2R.EndpointCover


