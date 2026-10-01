-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b02_t03
-- name    : CK_CKLaneC2R_EndpointCover_b02_t03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:57:29.165704+00:00
-- url     : https://prove2.me/theorems/d8156c10-4ef0-41dc-a046-3e6fa65fcee3
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 4 of 4 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 4 of 4 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 4 of 4 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 4 of 4 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 4 of 4 of 2).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B013
import Definitions.Def_CK_CKLaneC2R_EpCells_B014
import Definitions.Def_CK_CKLaneC2R_EpCells_B015__2
namespace CKLaneC2R.EndpointCover

theorem cover_sub_013 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : ¬ (a ≤ ((5649/32000 : ℚ) : ℝ))) (h1613 : a ≤ ((12147/64000 : ℚ) : ℝ)) (h1614 : ¬ (a ≤ ((4689/25600 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1742 : a ≤ ((47739/256000 : ℚ) : ℝ)
  · -- left
    by_cases h1743 : a ≤ ((94629/512000 : ℚ) : ℝ)
    · -- left
      by_cases h1744 : a ≤ ((188409/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h1745 : a ≤ ((375969/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1746 : a ≤ ((751089/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1747 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1748 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e829_pos (not_le.mp h1614).le h1746 hz1 h1748 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e831_pos (not_le.mp h1614).le h1746 (not_le.mp h1748).le h1747 hz
            · -- right
              by_cases h1749 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e837_pos (not_le.mp h1614).le h1746 (not_le.mp h1747).le h1749 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e839_pos (not_le.mp h1614).le h1746 (not_le.mp h1749).le hz2 hz
          · -- right
            by_cases h1750 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1751 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e830_pos (not_le.mp h1746).le h1745 hz1 h1751 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e832_pos (not_le.mp h1746).le h1745 (not_le.mp h1751).le h1750 hz
            · -- right
              by_cases h1752 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e838_pos (not_le.mp h1746).le h1745 (not_le.mp h1750).le h1752 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e840_pos (not_le.mp h1746).le h1745 (not_le.mp h1752).le hz2 hz
        · -- right
          by_cases h1753 : a ≤ ((752787/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1754 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1755 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e833_pos (not_le.mp h1745).le h1753 hz1 h1755 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e835_pos (not_le.mp h1745).le h1753 (not_le.mp h1755).le h1754 hz
            · -- right
              by_cases h1756 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e841_pos (not_le.mp h1745).le h1753 (not_le.mp h1754).le h1756 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e843_pos (not_le.mp h1745).le h1753 (not_le.mp h1756).le hz2 hz
          · -- right
            by_cases h1757 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1758 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B013.e834_pos (not_le.mp h1753).le h1744 hz1 h1758 hz
              · -- right
                exact CKLaneC2R.EpCells.B013.e836_pos (not_le.mp h1753).le h1744 (not_le.mp h1758).le h1757 hz
            · -- right
              by_cases h1759 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e842_pos (not_le.mp h1753).le h1744 (not_le.mp h1757).le h1759 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e844_pos (not_le.mp h1753).le h1744 (not_le.mp h1759).le hz2 hz
      · -- right
        by_cases h1760 : a ≤ ((377667/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1761 : a ≤ ((150897/819200 : ℚ) : ℝ)
          · -- left
            by_cases h1762 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1763 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e845_pos (not_le.mp h1744).le h1761 hz1 h1763 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e847_pos (not_le.mp h1744).le h1761 (not_le.mp h1763).le h1762 hz
            · -- right
              by_cases h1764 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e853_pos (not_le.mp h1744).le h1761 (not_le.mp h1762).le h1764 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e855_pos (not_le.mp h1744).le h1761 (not_le.mp h1764).le hz2 hz
          · -- right
            by_cases h1765 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1766 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e846_pos (not_le.mp h1761).le h1760 hz1 h1766 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e848_pos (not_le.mp h1761).le h1760 (not_le.mp h1766).le h1765 hz
            · -- right
              by_cases h1767 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e854_pos (not_le.mp h1761).le h1760 (not_le.mp h1765).le h1767 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e856_pos (not_le.mp h1761).le h1760 (not_le.mp h1767).le hz2 hz
        · -- right
          by_cases h1768 : a ≤ ((756183/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1769 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1770 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e849_pos (not_le.mp h1760).le h1768 hz1 h1770 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e851_pos (not_le.mp h1760).le h1768 (not_le.mp h1770).le h1769 hz
            · -- right
              by_cases h1771 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e857_pos (not_le.mp h1760).le h1768 (not_le.mp h1769).le h1771 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e859_pos (not_le.mp h1760).le h1768 (not_le.mp h1771).le hz2 hz
          · -- right
            by_cases h1772 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1773 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e850_pos (not_le.mp h1768).le h1743 hz1 h1773 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e852_pos (not_le.mp h1768).le h1743 (not_le.mp h1773).le h1772 hz
            · -- right
              by_cases h1774 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e858_pos (not_le.mp h1768).le h1743 (not_le.mp h1772).le h1774 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e860_pos (not_le.mp h1768).le h1743 (not_le.mp h1774).le hz2 hz
    · -- right
      by_cases h1775 : a ≤ ((190107/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h1776 : a ≤ ((75873/409600 : ℚ) : ℝ)
        · -- left
          by_cases h1777 : a ≤ ((757881/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1778 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1779 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e861_pos (not_le.mp h1743).le h1777 hz1 h1779 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e863_pos (not_le.mp h1743).le h1777 (not_le.mp h1779).le h1778 hz
            · -- right
              by_cases h1780 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e869_pos (not_le.mp h1743).le h1777 (not_le.mp h1778).le h1780 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e871_pos (not_le.mp h1743).le h1777 (not_le.mp h1780).le hz2 hz
          · -- right
            by_cases h1781 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1782 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e862_pos (not_le.mp h1777).le h1776 hz1 h1782 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e864_pos (not_le.mp h1777).le h1776 (not_le.mp h1782).le h1781 hz
            · -- right
              by_cases h1783 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e870_pos (not_le.mp h1777).le h1776 (not_le.mp h1781).le h1783 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e872_pos (not_le.mp h1777).le h1776 (not_le.mp h1783).le hz2 hz
        · -- right
          by_cases h1784 : a ≤ ((759579/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1785 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1786 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e865_pos (not_le.mp h1776).le h1784 hz1 h1786 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e867_pos (not_le.mp h1776).le h1784 (not_le.mp h1786).le h1785 hz
            · -- right
              by_cases h1787 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e873_pos (not_le.mp h1776).le h1784 (not_le.mp h1785).le h1787 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e875_pos (not_le.mp h1776).le h1784 (not_le.mp h1787).le hz2 hz
          · -- right
            by_cases h1788 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1789 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e866_pos (not_le.mp h1784).le h1775 hz1 h1789 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e868_pos (not_le.mp h1784).le h1775 (not_le.mp h1789).le h1788 hz
            · -- right
              by_cases h1790 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e874_pos (not_le.mp h1784).le h1775 (not_le.mp h1788).le h1790 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e876_pos (not_le.mp h1784).le h1775 (not_le.mp h1790).le hz2 hz
      · -- right
        by_cases h1791 : a ≤ ((381063/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1792 : a ≤ ((761277/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1793 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1794 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e877_pos (not_le.mp h1775).le h1792 hz1 h1794 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e879_pos (not_le.mp h1775).le h1792 (not_le.mp h1794).le h1793 hz
            · -- right
              by_cases h1795 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e885_pos (not_le.mp h1775).le h1792 (not_le.mp h1793).le h1795 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e887_pos (not_le.mp h1775).le h1792 (not_le.mp h1795).le hz2 hz
          · -- right
            by_cases h1796 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1797 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e878_pos (not_le.mp h1792).le h1791 hz1 h1797 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e880_pos (not_le.mp h1792).le h1791 (not_le.mp h1797).le h1796 hz
            · -- right
              by_cases h1798 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e886_pos (not_le.mp h1792).le h1791 (not_le.mp h1796).le h1798 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e888_pos (not_le.mp h1792).le h1791 (not_le.mp h1798).le hz2 hz
        · -- right
          by_cases h1799 : a ≤ ((30519/163840 : ℚ) : ℝ)
          · -- left
            by_cases h1800 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1801 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e881_pos (not_le.mp h1791).le h1799 hz1 h1801 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e883_pos (not_le.mp h1791).le h1799 (not_le.mp h1801).le h1800 hz
            · -- right
              by_cases h1802 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e889_pos (not_le.mp h1791).le h1799 (not_le.mp h1800).le h1802 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e891_pos (not_le.mp h1791).le h1799 (not_le.mp h1802).le hz2 hz
          · -- right
            by_cases h1803 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1804 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e882_pos (not_le.mp h1799).le h1742 hz1 h1804 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e884_pos (not_le.mp h1799).le h1742 (not_le.mp h1804).le h1803 hz
            · -- right
              by_cases h1805 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e890_pos (not_le.mp h1799).le h1742 (not_le.mp h1803).le h1805 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e892_pos (not_le.mp h1799).le h1742 (not_le.mp h1805).le hz2 hz
  · -- right
    by_cases h1806 : a ≤ ((96327/512000 : ℚ) : ℝ)
    · -- left
      by_cases h1807 : a ≤ ((38361/204800 : ℚ) : ℝ)
      · -- left
        by_cases h1808 : a ≤ ((382761/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1809 : a ≤ ((764673/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1810 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1811 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e893_pos (not_le.mp h1742).le h1809 hz1 h1811 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e895_pos (not_le.mp h1742).le h1809 (not_le.mp h1811).le h1810 hz
            · -- right
              by_cases h1812 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e901_pos (not_le.mp h1742).le h1809 (not_le.mp h1810).le h1812 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e903_pos (not_le.mp h1742).le h1809 (not_le.mp h1812).le hz2 hz
          · -- right
            by_cases h1813 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1814 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e894_pos (not_le.mp h1809).le h1808 hz1 h1814 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e896_pos (not_le.mp h1809).le h1808 (not_le.mp h1814).le h1813 hz
            · -- right
              by_cases h1815 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e902_pos (not_le.mp h1809).le h1808 (not_le.mp h1813).le h1815 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e904_pos (not_le.mp h1809).le h1808 (not_le.mp h1815).le hz2 hz
        · -- right
          by_cases h1816 : a ≤ ((766371/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1817 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1818 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e897_pos (not_le.mp h1808).le h1816 hz1 h1818 hz
              · -- right
                exact CKLaneC2R.EpCells.B014.e899_pos (not_le.mp h1808).le h1816 (not_le.mp h1818).le h1817 hz
            · -- right
              by_cases h1819 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e905_pos (not_le.mp h1808).le h1816 (not_le.mp h1817).le h1819 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e907_pos (not_le.mp h1808).le h1816 (not_le.mp h1819).le hz2 hz
          · -- right
            by_cases h1820 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1821 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B014.e898_pos (not_le.mp h1816).le h1807 hz1 h1821 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e900_pos (not_le.mp h1816).le h1807 (not_le.mp h1821).le h1820 hz
            · -- right
              by_cases h1822 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e906_pos (not_le.mp h1816).le h1807 (not_le.mp h1820).le h1822 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e908_pos (not_le.mp h1816).le h1807 (not_le.mp h1822).le hz2 hz
      · -- right
        by_cases h1823 : a ≤ ((384459/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1824 : a ≤ ((768069/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1825 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1826 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e909_pos (not_le.mp h1807).le h1824 hz1 h1826 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e911_pos (not_le.mp h1807).le h1824 (not_le.mp h1826).le h1825 hz
            · -- right
              by_cases h1827 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e917_pos (not_le.mp h1807).le h1824 (not_le.mp h1825).le h1827 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e919_pos (not_le.mp h1807).le h1824 (not_le.mp h1827).le hz2 hz
          · -- right
            by_cases h1828 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1829 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e910_pos (not_le.mp h1824).le h1823 hz1 h1829 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e912_pos (not_le.mp h1824).le h1823 (not_le.mp h1829).le h1828 hz
            · -- right
              by_cases h1830 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e918_pos (not_le.mp h1824).le h1823 (not_le.mp h1828).le h1830 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e920_pos (not_le.mp h1824).le h1823 (not_le.mp h1830).le hz2 hz
        · -- right
          by_cases h1831 : a ≤ ((769767/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1832 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1833 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e913_pos (not_le.mp h1823).le h1831 hz1 h1833 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e915_pos (not_le.mp h1823).le h1831 (not_le.mp h1833).le h1832 hz
            · -- right
              by_cases h1834 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e921_pos (not_le.mp h1823).le h1831 (not_le.mp h1832).le h1834 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e923_pos (not_le.mp h1823).le h1831 (not_le.mp h1834).le hz2 hz
          · -- right
            by_cases h1835 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1836 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e914_pos (not_le.mp h1831).le h1806 hz1 h1836 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e916_pos (not_le.mp h1831).le h1806 (not_le.mp h1836).le h1835 hz
            · -- right
              by_cases h1837 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e922_pos (not_le.mp h1831).le h1806 (not_le.mp h1835).le h1837 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e924_pos (not_le.mp h1831).le h1806 (not_le.mp h1837).le hz2 hz
    · -- right
      by_cases h1838 : a ≤ ((193503/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h1839 : a ≤ ((386157/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1840 : a ≤ ((154293/819200 : ℚ) : ℝ)
          · -- left
            by_cases h1841 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1842 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e925_pos (not_le.mp h1806).le h1840 hz1 h1842 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e927_pos (not_le.mp h1806).le h1840 (not_le.mp h1842).le h1841 hz
            · -- right
              by_cases h1843 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e933_pos (not_le.mp h1806).le h1840 (not_le.mp h1841).le h1843 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e935_pos (not_le.mp h1806).le h1840 (not_le.mp h1843).le hz2 hz
          · -- right
            by_cases h1844 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1845 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e926_pos (not_le.mp h1840).le h1839 hz1 h1845 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e928_pos (not_le.mp h1840).le h1839 (not_le.mp h1845).le h1844 hz
            · -- right
              by_cases h1846 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e934_pos (not_le.mp h1840).le h1839 (not_le.mp h1844).le h1846 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e936_pos (not_le.mp h1840).le h1839 (not_le.mp h1846).le hz2 hz
        · -- right
          by_cases h1847 : a ≤ ((773163/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1848 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1849 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e929_pos (not_le.mp h1839).le h1847 hz1 h1849 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e931_pos (not_le.mp h1839).le h1847 (not_le.mp h1849).le h1848 hz
            · -- right
              by_cases h1850 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e937_pos (not_le.mp h1839).le h1847 (not_le.mp h1848).le h1850 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e939_pos (not_le.mp h1839).le h1847 (not_le.mp h1850).le hz2 hz
          · -- right
            by_cases h1851 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1852 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e930_pos (not_le.mp h1847).le h1838 hz1 h1852 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e932_pos (not_le.mp h1847).le h1838 (not_le.mp h1852).le h1851 hz
            · -- right
              by_cases h1853 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e938_pos (not_le.mp h1847).le h1838 (not_le.mp h1851).le h1853 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e940_pos (not_le.mp h1847).le h1838 (not_le.mp h1853).le hz2 hz
      · -- right
        by_cases h1854 : a ≤ ((77571/409600 : ℚ) : ℝ)
        · -- left
          by_cases h1855 : a ≤ ((774861/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1856 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1857 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e941_pos (not_le.mp h1838).le h1855 hz1 h1857 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e943_pos (not_le.mp h1838).le h1855 (not_le.mp h1857).le h1856 hz
            · -- right
              by_cases h1858 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e949_pos (not_le.mp h1838).le h1855 (not_le.mp h1856).le h1858 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e951_pos (not_le.mp h1838).le h1855 (not_le.mp h1858).le hz2 hz
          · -- right
            by_cases h1859 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1860 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e942_pos (not_le.mp h1855).le h1854 hz1 h1860 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e944_pos (not_le.mp h1855).le h1854 (not_le.mp h1860).le h1859 hz
            · -- right
              by_cases h1861 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e950_pos (not_le.mp h1855).le h1854 (not_le.mp h1859).le h1861 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e952_pos (not_le.mp h1855).le h1854 (not_le.mp h1861).le hz2 hz
        · -- right
          by_cases h1862 : a ≤ ((776559/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1863 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1864 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e945_pos (not_le.mp h1854).le h1862 hz1 h1864 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e947_pos (not_le.mp h1854).le h1862 (not_le.mp h1864).le h1863 hz
            · -- right
              by_cases h1865 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e953_pos (not_le.mp h1854).le h1862 (not_le.mp h1863).le h1865 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e955_pos (not_le.mp h1854).le h1862 (not_le.mp h1865).le hz2 hz
          · -- right
            by_cases h1866 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1867 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e946_pos (not_le.mp h1862).le h1613 hz1 h1867 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e948_pos (not_le.mp h1862).le h1613 (not_le.mp h1867).le h1866 hz
            · -- right
              by_cases h1868 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B015.e954_pos (not_le.mp h1862).le h1613 (not_le.mp h1866).le h1868 hz
              · -- right
                exact CKLaneC2R.EpCells.B015.e956_pos (not_le.mp h1862).le h1613 (not_le.mp h1868).le hz2 hz

end CKLaneC2R.EndpointCover


