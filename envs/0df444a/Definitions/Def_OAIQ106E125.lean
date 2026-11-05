-- Prove2me | Definitions.Def_OAIQ106E125
-- name    : OAIQ106E125
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T23:06:10.91291+00:00
-- url     : https://prove2.me/theorems/a8a4f576-5e9a-4250-b4eb-fa3c968c710f
-- title:
--   Definitions bundle OAIQ106E125 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 348 declarations of OpenAI's Lean: 348 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1659`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1660`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1661`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1662`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1663`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1664`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1665`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1666`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1667`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1668`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1669`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1670`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1671`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1672`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1673`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1674`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1675`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1676`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1677`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1678`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1679`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1680`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1681`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1682`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1683`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1684`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1685`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1686`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1687`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1688`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1689`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource169`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1690`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1691`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1692`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1693`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1694`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1695`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1696`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1697` and 308 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSources_Arithmetic1`, `MutuallyUnbiased_MixedSources_Arithmetic10`, `MutuallyUnbiased_MixedSources_Arithmetic103`, `MutuallyUnbiased_MixedSources_Arithmetic104`, `MutuallyUnbiased_MixedSources_Arithmetic105`, `MutuallyUnbiased_MixedSources_Arithmetic106`, `MutuallyUnbiased_MixedSources_Arithmetic107`, `MutuallyUnbiased_MixedSources_Arithmetic108`, `MutuallyUnbiased_MixedSources_Arithmetic109`, `MutuallyUnbiased_MixedSources_Arithmetic11`, `MutuallyUnbiased_MixedSources_Arithmetic110`, `MutuallyUnbiased_MixedSources_Arithmetic111`, `MutuallyUnbiased_MixedSources_Arithmetic112`, `MutuallyUnbiased_MixedSources_Arithmetic113`, `MutuallyUnbiased_MixedSources_Arithmetic114`, `MutuallyUnbiased_MixedSources_Arithmetic115`, `MutuallyUnbiased_MixedSources_Arithmetic116`, `MutuallyUnbiased_MixedSources_Arithmetic117`, `MutuallyUnbiased_MixedSources_Arithmetic118`, `MutuallyUnbiased_MixedSources_Arithmetic119`, `MutuallyUnbiased_MixedSources_Arithmetic12`, `MutuallyUnbiased_MixedSources_Arithmetic120`, `MutuallyUnbiased_MixedSources_Arithmetic121`, `MutuallyUnbiased_MixedSources_Arithmetic122`, `MutuallyUnbiased_MixedSources_Arithmetic123`, `MutuallyUnbiased_MixedSources_Arithmetic132`.
--
--   **Imports.** It imports the bundles `OAIQ106E043` and `OAIQ106E084` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e` and `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`; the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound104_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound11_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound132_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E084

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource17 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5306 x + ((4 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((4 : ℝ) * Sparse.eval nodeValue5485 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5501 x + 0))))))))))))

noncomputable def reducedSource18 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((3 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((2 : ℝ) * Sparse.eval nodeValue5499 x + ((1 : ℝ) * Sparse.eval nodeValue5500 x + ((1 : ℝ) * Sparse.eval nodeValue5501 x + 0))))))))))))))))))))))))

noncomputable def reducedSource19 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((1 : ℝ) * Sparse.eval nodeValue3999 x + ((1 : ℝ) * Sparse.eval nodeValue4009 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4015 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + ((1 : ℝ) * Sparse.eval nodeValue4050 x + ((1 : ℝ) * Sparse.eval nodeValue4052 x + ((1 : ℝ) * Sparse.eval nodeValue4053 x + ((1 : ℝ) * Sparse.eval nodeValue4054 x + ((1 : ℝ) * Sparse.eval nodeValue4055 x + 0))))))))))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource169 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2497 x + ((1 : ℝ) * Sparse.eval nodeValue2716 x + ((1 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource170 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1465 x + ((1 : ℝ) * Sparse.eval nodeValue2474 x + ((1 : ℝ) * Sparse.eval nodeValue2486 x + ((1 : ℝ) * Sparse.eval nodeValue2497 x + ((1 : ℝ) * Sparse.eval nodeValue2716 x + ((1 : ℝ) * Sparse.eval nodeValue3222 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource171 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2233 x + ((3 : ℝ) * Sparse.eval nodeValue3567 x + ((1 : ℝ) * Sparse.eval nodeValue3618 x + ((1 : ℝ) * Sparse.eval nodeValue3619 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource172 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1014 x + ((1 : ℝ) * Sparse.eval nodeValue1015 x + ((3 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource173 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1021 x + ((2 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource174 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2083 x + ((1 : ℝ) * Sparse.eval nodeValue2084 x + ((2 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource175 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1015 x + ((3 : ℝ) * Sparse.eval nodeValue2084 x + ((2 : ℝ) * Sparse.eval nodeValue2233 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1659 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue953 x + ((1 : ℝ) * Sparse.eval nodeValue1831 x + ((2 : ℝ) * Sparse.eval nodeValue1979 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1660 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1336 x + ((1 : ℝ) * Sparse.eval nodeValue1973 x + ((1 : ℝ) * Sparse.eval nodeValue1979 x + ((1 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2952 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1661 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4486 x + ((1 : ℝ) * Sparse.eval nodeValue4490 x + ((1 : ℝ) * Sparse.eval nodeValue4492 x + ((1 : ℝ) * Sparse.eval nodeValue4504 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4808 x + ((2 : ℝ) * Sparse.eval nodeValue4824 x + ((2 : ℝ) * Sparse.eval nodeValue4827 x + ((2 : ℝ) * Sparse.eval nodeValue4829 x + ((2 : ℝ) * Sparse.eval nodeValue4840 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((2 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4844 x + ((2 : ℝ) * Sparse.eval nodeValue4853 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4872 x + ((1 : ℝ) * Sparse.eval nodeValue4881 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((2 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + 0)))))))))))))))))))

noncomputable def reducedSource1662 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1639 x + ((1 : ℝ) * Sparse.eval nodeValue1650 x + ((1 : ℝ) * Sparse.eval nodeValue1651 x + ((1 : ℝ) * Sparse.eval nodeValue1659 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2060 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((2 : ℝ) * Sparse.eval nodeValue2071 x + ((2 : ℝ) * Sparse.eval nodeValue2079 x + ((2 : ℝ) * Sparse.eval nodeValue2080 x + ((2 : ℝ) * Sparse.eval nodeValue2090 x + ((2 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((2 : ℝ) * Sparse.eval nodeValue2121 x + ((1 : ℝ) * Sparse.eval nodeValue2134 x + ((1 : ℝ) * Sparse.eval nodeValue2136 x + ((1 : ℝ) * Sparse.eval nodeValue2601 x + ((2 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2640 x + ((1 : ℝ) * Sparse.eval nodeValue2642 x + 0))))))))))))))))))))

noncomputable def reducedSource1663 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1159 x + ((1 : ℝ) * Sparse.eval nodeValue2355 x + ((1 : ℝ) * Sparse.eval nodeValue2436 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2569 x + ((1 : ℝ) * Sparse.eval nodeValue2590 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1664 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1320 x + ((1 : ℝ) * Sparse.eval nodeValue2815 x + ((1 : ℝ) * Sparse.eval nodeValue2847 x + ((2 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1665 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1334 x + ((1 : ℝ) * Sparse.eval nodeValue2797 x + ((1 : ℝ) * Sparse.eval nodeValue2802 x + ((1 : ℝ) * Sparse.eval nodeValue2815 x + ((1 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1666 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2018 x + ((1 : ℝ) * Sparse.eval nodeValue2074 x + ((1 : ℝ) * Sparse.eval nodeValue2081 x + ((1 : ℝ) * Sparse.eval nodeValue2099 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1667 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2015 x + ((1 : ℝ) * Sparse.eval nodeValue2018 x + ((1 : ℝ) * Sparse.eval nodeValue2027 x + ((1 : ℝ) * Sparse.eval nodeValue2047 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1668 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4327 x + ((1 : ℝ) * Sparse.eval nodeValue4330 x + ((1 : ℝ) * Sparse.eval nodeValue4335 x + ((1 : ℝ) * Sparse.eval nodeValue4347 x + ((1 : ℝ) * Sparse.eval nodeValue4440 x + ((1 : ℝ) * Sparse.eval nodeValue4528 x + ((1 : ℝ) * Sparse.eval nodeValue4535 x + ((1 : ℝ) * Sparse.eval nodeValue4551 x + ((1 : ℝ) * Sparse.eval nodeValue4591 x + ((2 : ℝ) * Sparse.eval nodeValue4930 x + ((1 : ℝ) * Sparse.eval nodeValue4935 x + ((1 : ℝ) * Sparse.eval nodeValue4944 x + ((1 : ℝ) * Sparse.eval nodeValue4948 x + ((1 : ℝ) * Sparse.eval nodeValue5034 x + ((1 : ℝ) * Sparse.eval nodeValue5037 x + ((1 : ℝ) * Sparse.eval nodeValue5065 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((1 : ℝ) * Sparse.eval nodeValue5128 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5252 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1669 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue905 x + ((1 : ℝ) * Sparse.eval nodeValue908 x + ((1 : ℝ) * Sparse.eval nodeValue913 x + ((1 : ℝ) * Sparse.eval nodeValue925 x + ((1 : ℝ) * Sparse.eval nodeValue1022 x + ((1 : ℝ) * Sparse.eval nodeValue1148 x + ((1 : ℝ) * Sparse.eval nodeValue1154 x + ((1 : ℝ) * Sparse.eval nodeValue1163 x + ((1 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue2320 x + ((1 : ℝ) * Sparse.eval nodeValue2326 x + ((1 : ℝ) * Sparse.eval nodeValue2335 x + ((1 : ℝ) * Sparse.eval nodeValue2422 x + ((1 : ℝ) * Sparse.eval nodeValue2426 x + ((1 : ℝ) * Sparse.eval nodeValue2470 x + ((1 : ℝ) * Sparse.eval nodeValue2526 x + ((1 : ℝ) * Sparse.eval nodeValue2531 x + ((1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2570 x + ((1 : ℝ) * Sparse.eval nodeValue2572 x + ((1 : ℝ) * Sparse.eval nodeValue2576 x + ((1 : ℝ) * Sparse.eval nodeValue2596 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue2987 x + ((1 : ℝ) * Sparse.eval nodeValue2991 x + ((1 : ℝ) * Sparse.eval nodeValue3000 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3996 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1670 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1670 x + ((1 : ℝ) * Sparse.eval nodeValue1672 x + ((1 : ℝ) * Sparse.eval nodeValue1676 x + ((1 : ℝ) * Sparse.eval nodeValue1689 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((1 : ℝ) * Sparse.eval nodeValue3260 x + ((1 : ℝ) * Sparse.eval nodeValue3272 x + ((1 : ℝ) * Sparse.eval nodeValue3273 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((2 : ℝ) * Sparse.eval nodeValue3408 x + ((1 : ℝ) * Sparse.eval nodeValue3413 x + ((1 : ℝ) * Sparse.eval nodeValue3419 x + ((1 : ℝ) * Sparse.eval nodeValue3420 x + ((1 : ℝ) * Sparse.eval nodeValue3451 x + ((1 : ℝ) * Sparse.eval nodeValue3455 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((1 : ℝ) * Sparse.eval nodeValue3467 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3483 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1671 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1136 x + ((1 : ℝ) * Sparse.eval nodeValue2339 x + ((1 : ℝ) * Sparse.eval nodeValue2429 x + ((2 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2514 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1672 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4199 x + ((1 : ℝ) * Sparse.eval nodeValue4202 x + ((1 : ℝ) * Sparse.eval nodeValue4205 x + ((1 : ℝ) * Sparse.eval nodeValue4219 x + ((1 : ℝ) * Sparse.eval nodeValue4253 x + ((1 : ℝ) * Sparse.eval nodeValue4521 x + ((1 : ℝ) * Sparse.eval nodeValue4525 x + ((1 : ℝ) * Sparse.eval nodeValue4543 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4633 x + ((1 : ℝ) * Sparse.eval nodeValue4638 x + ((1 : ℝ) * Sparse.eval nodeValue4650 x + ((1 : ℝ) * Sparse.eval nodeValue4707 x + ((1 : ℝ) * Sparse.eval nodeValue4713 x + ((1 : ℝ) * Sparse.eval nodeValue4729 x + ((1 : ℝ) * Sparse.eval nodeValue4764 x + ((1 : ℝ) * Sparse.eval nodeValue4770 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1673 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4327 x + ((1 : ℝ) * Sparse.eval nodeValue4331 x + ((1 : ℝ) * Sparse.eval nodeValue4333 x + ((1 : ℝ) * Sparse.eval nodeValue4335 x + ((1 : ℝ) * Sparse.eval nodeValue4336 x + ((1 : ℝ) * Sparse.eval nodeValue4352 x + ((1 : ℝ) * Sparse.eval nodeValue4353 x + ((1 : ℝ) * Sparse.eval nodeValue4442 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4664 x + ((1 : ℝ) * Sparse.eval nodeValue4670 x + ((1 : ℝ) * Sparse.eval nodeValue4686 x + ((1 : ℝ) * Sparse.eval nodeValue4757 x + ((1 : ℝ) * Sparse.eval nodeValue4764 x + ((1 : ℝ) * Sparse.eval nodeValue4772 x + ((1 : ℝ) * Sparse.eval nodeValue4777 x + ((1 : ℝ) * Sparse.eval nodeValue4792 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5151 x + ((1 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1674 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue909 x + ((1 : ℝ) * Sparse.eval nodeValue911 x + ((1 : ℝ) * Sparse.eval nodeValue914 x + ((1 : ℝ) * Sparse.eval nodeValue931 x + ((1 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue1327 x + ((1 : ℝ) * Sparse.eval nodeValue1333 x + ((1 : ℝ) * Sparse.eval nodeValue1340 x + ((1 : ℝ) * Sparse.eval nodeValue1413 x + ((1 : ℝ) * Sparse.eval nodeValue2323 x + ((1 : ℝ) * Sparse.eval nodeValue2327 x + ((1 : ℝ) * Sparse.eval nodeValue2340 x + ((1 : ℝ) * Sparse.eval nodeValue2423 x + ((1 : ℝ) * Sparse.eval nodeValue2430 x + ((1 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue2528 x + ((1 : ℝ) * Sparse.eval nodeValue2532 x + ((1 : ℝ) * Sparse.eval nodeValue2573 x + ((2 : ℝ) * Sparse.eval nodeValue2574 x + ((1 : ℝ) * Sparse.eval nodeValue2575 x + ((1 : ℝ) * Sparse.eval nodeValue2600 x + ((1 : ℝ) * Sparse.eval nodeValue2602 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3204 x + ((1 : ℝ) * Sparse.eval nodeValue3207 x + ((1 : ℝ) * Sparse.eval nodeValue3213 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1675 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1670 x + ((1 : ℝ) * Sparse.eval nodeValue1684 x + ((1 : ℝ) * Sparse.eval nodeValue1685 x + ((1 : ℝ) * Sparse.eval nodeValue1686 x + ((1 : ℝ) * Sparse.eval nodeValue1688 x + ((1 : ℝ) * Sparse.eval nodeValue1689 x + ((1 : ℝ) * Sparse.eval nodeValue1690 x + ((1 : ℝ) * Sparse.eval nodeValue1744 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue2147 x + ((1 : ℝ) * Sparse.eval nodeValue2164 x + ((1 : ℝ) * Sparse.eval nodeValue2165 x + ((1 : ℝ) * Sparse.eval nodeValue2181 x + ((1 : ℝ) * Sparse.eval nodeValue2182 x + ((1 : ℝ) * Sparse.eval nodeValue2198 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2223 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((1 : ℝ) * Sparse.eval nodeValue2227 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2700 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1676 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue913 x + ((1 : ℝ) * Sparse.eval nodeValue1796 x + ((1 : ℝ) * Sparse.eval nodeValue1956 x + ((1 : ℝ) * Sparse.eval nodeValue1979 x + ((1 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2029 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1677 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1326 x + ((1 : ℝ) * Sparse.eval nodeValue1956 x + ((1 : ℝ) * Sparse.eval nodeValue1964 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2923 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1678 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue930 x + ((1 : ℝ) * Sparse.eval nodeValue1812 x + ((1 : ℝ) * Sparse.eval nodeValue1964 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2057 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1679 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4414 x + ((1 : ℝ) * Sparse.eval nodeValue4418 x + ((1 : ℝ) * Sparse.eval nodeValue4420 x + ((1 : ℝ) * Sparse.eval nodeValue4425 x + ((1 : ℝ) * Sparse.eval nodeValue4486 x + ((1 : ℝ) * Sparse.eval nodeValue4729 x + ((1 : ℝ) * Sparse.eval nodeValue4741 x + ((1 : ℝ) * Sparse.eval nodeValue4742 x + ((1 : ℝ) * Sparse.eval nodeValue4747 x + ((1 : ℝ) * Sparse.eval nodeValue4779 x + ((1 : ℝ) * Sparse.eval nodeValue4780 x + ((1 : ℝ) * Sparse.eval nodeValue4783 x + ((1 : ℝ) * Sparse.eval nodeValue4792 x + ((1 : ℝ) * Sparse.eval nodeValue4793 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4808 x + ((1 : ℝ) * Sparse.eval nodeValue4817 x + ((1 : ℝ) * Sparse.eval nodeValue4819 x + ((1 : ℝ) * Sparse.eval nodeValue4824 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4853 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5128 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + 0))))))))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1680 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2390 x + ((1 : ℝ) * Sparse.eval nodeValue2393 x + ((1 : ℝ) * Sparse.eval nodeValue2395 x + ((1 : ℝ) * Sparse.eval nodeValue2404 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

noncomputable def reducedSource1681 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1898 x + ((1 : ℝ) * Sparse.eval nodeValue1901 x + ((2 : ℝ) * Sparse.eval nodeValue1912 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue3460 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0)))))

noncomputable def reducedSource1682 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2076 x + ((1 : ℝ) * Sparse.eval nodeValue2080 x + ((1 : ℝ) * Sparse.eval nodeValue2082 x + ((1 : ℝ) * Sparse.eval nodeValue2102 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1683 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1325 x + ((2 : ℝ) * Sparse.eval nodeValue2811 x + ((1 : ℝ) * Sparse.eval nodeValue2820 x + ((1 : ℝ) * Sparse.eval nodeValue2886 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1684 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4367 x + ((1 : ℝ) * Sparse.eval nodeValue4370 x + ((1 : ℝ) * Sparse.eval nodeValue4374 x + ((1 : ℝ) * Sparse.eval nodeValue4476 x + ((2 : ℝ) * Sparse.eval nodeValue4547 x + ((1 : ℝ) * Sparse.eval nodeValue4559 x + ((1 : ℝ) * Sparse.eval nodeValue4609 x + ((2 : ℝ) * Sparse.eval nodeValue4944 x + ((1 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4972 x + ((2 : ℝ) * Sparse.eval nodeValue5034 x + ((2 : ℝ) * Sparse.eval nodeValue5087 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5139 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((1 : ℝ) * Sparse.eval nodeValue5268 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + 0))))))))))))))))))))

noncomputable def reducedSource1685 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1720 x + ((1 : ℝ) * Sparse.eval nodeValue1722 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1748 x + ((2 : ℝ) * Sparse.eval nodeValue3266 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((2 : ℝ) * Sparse.eval nodeValue3413 x + ((1 : ℝ) * Sparse.eval nodeValue3423 x + ((2 : ℝ) * Sparse.eval nodeValue3451 x + ((2 : ℝ) * Sparse.eval nodeValue3457 x + ((2 : ℝ) * Sparse.eval nodeValue3471 x + ((2 : ℝ) * Sparse.eval nodeValue3472 x + ((1 : ℝ) * Sparse.eval nodeValue3485 x + ((2 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((2 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + 0))))))))))))))))))))

noncomputable def reducedSource1686 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4219 x + ((1 : ℝ) * Sparse.eval nodeValue4225 x + ((1 : ℝ) * Sparse.eval nodeValue4229 x + ((1 : ℝ) * Sparse.eval nodeValue4270 x + ((2 : ℝ) * Sparse.eval nodeValue4514 x + ((1 : ℝ) * Sparse.eval nodeValue4519 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((2 : ℝ) * Sparse.eval nodeValue4650 x + ((1 : ℝ) * Sparse.eval nodeValue4657 x + ((2 : ℝ) * Sparse.eval nodeValue4713 x + ((2 : ℝ) * Sparse.eval nodeValue4719 x + ((2 : ℝ) * Sparse.eval nodeValue4742 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + 0))))))))))))))))))))

noncomputable def reducedSource1687 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4347 x + ((1 : ℝ) * Sparse.eval nodeValue4358 x + ((1 : ℝ) * Sparse.eval nodeValue4361 x + ((2 : ℝ) * Sparse.eval nodeValue4371 x + ((1 : ℝ) * Sparse.eval nodeValue4375 x + ((1 : ℝ) * Sparse.eval nodeValue4478 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((2 : ℝ) * Sparse.eval nodeValue4682 x + ((1 : ℝ) * Sparse.eval nodeValue4693 x + ((2 : ℝ) * Sparse.eval nodeValue4761 x + ((2 : ℝ) * Sparse.eval nodeValue4770 x + ((2 : ℝ) * Sparse.eval nodeValue4817 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((2 : ℝ) * Sparse.eval nodeValue5205 x + ((1 : ℝ) * Sparse.eval nodeValue5206 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + 0))))))))))))))))))))

noncomputable def reducedSource1688 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1676 x + ((1 : ℝ) * Sparse.eval nodeValue1694 x + ((1 : ℝ) * Sparse.eval nodeValue1695 x + ((2 : ℝ) * Sparse.eval nodeValue1742 x + ((1 : ℝ) * Sparse.eval nodeValue1743 x + ((1 : ℝ) * Sparse.eval nodeValue1746 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((2 : ℝ) * Sparse.eval nodeValue2153 x + ((1 : ℝ) * Sparse.eval nodeValue2169 x + ((2 : ℝ) * Sparse.eval nodeValue2175 x + ((2 : ℝ) * Sparse.eval nodeValue2186 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((2 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((2 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((2 : ℝ) * Sparse.eval nodeValue2706 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + 0))))))))))))))))))))

noncomputable def reducedSource1689 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue939 x + ((1 : ℝ) * Sparse.eval nodeValue1819 x + ((2 : ℝ) * Sparse.eval nodeValue1970 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2066 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1690 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1315 x + ((1 : ℝ) * Sparse.eval nodeValue1961 x + ((1 : ℝ) * Sparse.eval nodeValue1970 x + ((2 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2879 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1691 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2128 x + ((1 : ℝ) * Sparse.eval nodeValue2130 x + ((1 : ℝ) * Sparse.eval nodeValue2137 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1692 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2085 x + ((1 : ℝ) * Sparse.eval nodeValue2087 x + ((1 : ℝ) * Sparse.eval nodeValue2093 x + ((1 : ℝ) * Sparse.eval nodeValue2101 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1693 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2492 x + ((1 : ℝ) * Sparse.eval nodeValue2606 x + ((1 : ℝ) * Sparse.eval nodeValue2608 x + ((1 : ℝ) * Sparse.eval nodeValue2629 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

noncomputable def reducedSource1694 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2030 x + ((1 : ℝ) * Sparse.eval nodeValue2032 x + ((1 : ℝ) * Sparse.eval nodeValue2038 x + ((1 : ℝ) * Sparse.eval nodeValue2048 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1695 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2469 x + ((1 : ℝ) * Sparse.eval nodeValue2609 x + ((2 : ℝ) * Sparse.eval nodeValue2613 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1696 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2008 x + ((1 : ℝ) * Sparse.eval nodeValue2011 x + ((2 : ℝ) * Sparse.eval nodeValue2016 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1697 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2117 x + ((1 : ℝ) * Sparse.eval nodeValue2119 x + ((1 : ℝ) * Sparse.eval nodeValue2122 x + ((1 : ℝ) * Sparse.eval nodeValue2128 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1698 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2070 x + ((1 : ℝ) * Sparse.eval nodeValue2072 x + ((1 : ℝ) * Sparse.eval nodeValue2075 x + ((1 : ℝ) * Sparse.eval nodeValue2085 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1699 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2453 x + ((1 : ℝ) * Sparse.eval nodeValue2455 x + ((1 : ℝ) * Sparse.eval nodeValue2459 x + ((1 : ℝ) * Sparse.eval nodeValue2490 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

noncomputable def reducedSource1700 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2453 x + ((1 : ℝ) * Sparse.eval nodeValue2533 x + ((1 : ℝ) * Sparse.eval nodeValue2536 x + ((1 : ℝ) * Sparse.eval nodeValue2565 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

noncomputable def reducedSource1701 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1991 x + ((1 : ℝ) * Sparse.eval nodeValue1993 x + ((1 : ℝ) * Sparse.eval nodeValue1997 x + ((1 : ℝ) * Sparse.eval nodeValue2030 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1702 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4365 x + ((1 : ℝ) * Sparse.eval nodeValue4370 x + ((1 : ℝ) * Sparse.eval nodeValue4373 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((2 : ℝ) * Sparse.eval nodeValue4552 x + ((1 : ℝ) * Sparse.eval nodeValue4560 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((2 : ℝ) * Sparse.eval nodeValue4697 x + ((1 : ℝ) * Sparse.eval nodeValue4704 x + ((2 : ℝ) * Sparse.eval nodeValue4771 x + ((2 : ℝ) * Sparse.eval nodeValue4776 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((2 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((2 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5175 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + 0))))))))))))))))))))

noncomputable def reducedSource1703 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1137 x + ((1 : ℝ) * Sparse.eval nodeValue1142 x + ((1 : ℝ) * Sparse.eval nodeValue1146 x + ((1 : ℝ) * Sparse.eval nodeValue1308 x + ((2 : ℝ) * Sparse.eval nodeValue1320 x + ((1 : ℝ) * Sparse.eval nodeValue1325 x + ((1 : ℝ) * Sparse.eval nodeValue1416 x + ((2 : ℝ) * Sparse.eval nodeValue2816 x + ((1 : ℝ) * Sparse.eval nodeValue2821 x + ((2 : ℝ) * Sparse.eval nodeValue2895 x + ((2 : ℝ) * Sparse.eval nodeValue2899 x + ((2 : ℝ) * Sparse.eval nodeValue2941 x + ((2 : ℝ) * Sparse.eval nodeValue2964 x + ((2 : ℝ) * Sparse.eval nodeValue2966 x + ((1 : ℝ) * Sparse.eval nodeValue2967 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3125 x + ((2 : ℝ) * Sparse.eval nodeValue3185 x + ((1 : ℝ) * Sparse.eval nodeValue3187 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

noncomputable def reducedSource1704 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1704 x + ((1 : ℝ) * Sparse.eval nodeValue1722 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1735 x + ((2 : ℝ) * Sparse.eval nodeValue2189 x + ((2 : ℝ) * Sparse.eval nodeValue2200 x + ((2 : ℝ) * Sparse.eval nodeValue2203 x + ((2 : ℝ) * Sparse.eval nodeValue2212 x + ((2 : ℝ) * Sparse.eval nodeValue2239 x + ((2 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2258 x + ((2 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2273 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((2 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + 0))))))))))))))))))))

noncomputable def reducedSource1705 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue952 x + ((1 : ℝ) * Sparse.eval nodeValue1830 x + ((2 : ℝ) * Sparse.eval nodeValue1978 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1706 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1157 x + ((1 : ℝ) * Sparse.eval nodeValue1972 x + ((1 : ℝ) * Sparse.eval nodeValue1978 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2588 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1707 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue943 x + ((1 : ℝ) * Sparse.eval nodeValue1823 x + ((1 : ℝ) * Sparse.eval nodeValue1972 x + ((1 : ℝ) * Sparse.eval nodeValue2106 x + ((2 : ℝ) * Sparse.eval nodeValue2109 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1708 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4233 x + ((1 : ℝ) * Sparse.eval nodeValue4235 x + ((1 : ℝ) * Sparse.eval nodeValue4242 x + ((1 : ℝ) * Sparse.eval nodeValue4272 x + ((2 : ℝ) * Sparse.eval nodeValue4338 x + ((1 : ℝ) * Sparse.eval nodeValue4359 x + ((1 : ℝ) * Sparse.eval nodeValue4454 x + ((2 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4692 x + ((2 : ℝ) * Sparse.eval nodeValue4721 x + ((2 : ℝ) * Sparse.eval nodeValue4726 x + ((2 : ℝ) * Sparse.eval nodeValue4744 x + ((2 : ℝ) * Sparse.eval nodeValue4827 x + ((1 : ℝ) * Sparse.eval nodeValue4845 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))

noncomputable def reducedSource1709 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue733 x + ((1 : ℝ) * Sparse.eval nodeValue735 x + ((1 : ℝ) * Sparse.eval nodeValue742 x + ((1 : ℝ) * Sparse.eval nodeValue826 x + ((2 : ℝ) * Sparse.eval nodeValue916 x + ((1 : ℝ) * Sparse.eval nodeValue937 x + ((1 : ℝ) * Sparse.eval nodeValue1037 x + ((2 : ℝ) * Sparse.eval nodeValue1807 x + ((1 : ℝ) * Sparse.eval nodeValue1818 x + ((2 : ℝ) * Sparse.eval nodeValue1875 x + ((2 : ℝ) * Sparse.eval nodeValue1880 x + ((2 : ℝ) * Sparse.eval nodeValue1924 x + ((2 : ℝ) * Sparse.eval nodeValue2079 x + ((2 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + 0))))))))))))))))))))

noncomputable def reducedSource1710 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4527 x + ((1 : ℝ) * Sparse.eval nodeValue4528 x + ((1 : ℝ) * Sparse.eval nodeValue4531 x + ((1 : ℝ) * Sparse.eval nodeValue4534 x + ((1 : ℝ) * Sparse.eval nodeValue4535 x + ((1 : ℝ) * Sparse.eval nodeValue4546 x + ((1 : ℝ) * Sparse.eval nodeValue4547 x + ((1 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4929 x + ((1 : ℝ) * Sparse.eval nodeValue4934 x + ((1 : ℝ) * Sparse.eval nodeValue4943 x + ((1 : ℝ) * Sparse.eval nodeValue4954 x + ((1 : ℝ) * Sparse.eval nodeValue4965 x + ((1 : ℝ) * Sparse.eval nodeValue5033 x + ((1 : ℝ) * Sparse.eval nodeValue5041 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5107 x + ((1 : ℝ) * Sparse.eval nodeValue5127 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1711 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3255 x + ((1 : ℝ) * Sparse.eval nodeValue3260 x + ((1 : ℝ) * Sparse.eval nodeValue3262 x + ((1 : ℝ) * Sparse.eval nodeValue3264 x + ((1 : ℝ) * Sparse.eval nodeValue3266 x + ((1 : ℝ) * Sparse.eval nodeValue3268 x + ((1 : ℝ) * Sparse.eval nodeValue3272 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3403 x + ((1 : ℝ) * Sparse.eval nodeValue3411 x + ((1 : ℝ) * Sparse.eval nodeValue3415 x + ((1 : ℝ) * Sparse.eval nodeValue3449 x + ((1 : ℝ) * Sparse.eval nodeValue3452 x + ((1 : ℝ) * Sparse.eval nodeValue3458 x + ((1 : ℝ) * Sparse.eval nodeValue3459 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3470 x + ((1 : ℝ) * Sparse.eval nodeValue3475 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3484 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3545 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + 0)))))))))))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1712 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1119 x + ((1 : ℝ) * Sparse.eval nodeValue2325 x + ((1 : ℝ) * Sparse.eval nodeValue2347 x + ((1 : ℝ) * Sparse.eval nodeValue2355 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1713 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1111 x + ((1 : ℝ) * Sparse.eval nodeValue2319 x + ((1 : ℝ) * Sparse.eval nodeValue2436 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((2 : ℝ) * Sparse.eval nodeValue2482 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1714 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1131 x + ((1 : ℝ) * Sparse.eval nodeValue2334 x + ((1 : ℝ) * Sparse.eval nodeValue2425 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2511 x + ((1 : ℝ) * Sparse.eval nodeValue2517 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1715 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4287 x + ((1 : ℝ) * Sparse.eval nodeValue4289 x + ((1 : ℝ) * Sparse.eval nodeValue4295 x + ((1 : ℝ) * Sparse.eval nodeValue4303 x + ((1 : ℝ) * Sparse.eval nodeValue4322 x + ((1 : ℝ) * Sparse.eval nodeValue4325 x + ((1 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4401 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4902 x + ((1 : ℝ) * Sparse.eval nodeValue4907 x + ((1 : ℝ) * Sparse.eval nodeValue4913 x + ((1 : ℝ) * Sparse.eval nodeValue4927 x + ((1 : ℝ) * Sparse.eval nodeValue4943 x + ((1 : ℝ) * Sparse.eval nodeValue4986 x + ((1 : ℝ) * Sparse.eval nodeValue5000 x + ((1 : ℝ) * Sparse.eval nodeValue5033 x + ((1 : ℝ) * Sparse.eval nodeValue5047 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1716 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4326 x + ((1 : ℝ) * Sparse.eval nodeValue4330 x + ((1 : ℝ) * Sparse.eval nodeValue4334 x + ((1 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4532 x + ((1 : ℝ) * Sparse.eval nodeValue4536 x + ((1 : ℝ) * Sparse.eval nodeValue4552 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4663 x + ((1 : ℝ) * Sparse.eval nodeValue4669 x + ((1 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4756 x + ((1 : ℝ) * Sparse.eval nodeValue4760 x + ((1 : ℝ) * Sparse.eval nodeValue4771 x + ((1 : ℝ) * Sparse.eval nodeValue4776 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue5133 x + ((1 : ℝ) * Sparse.eval nodeValue5140 x + ((1 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1717 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1116 x + ((1 : ℝ) * Sparse.eval nodeValue1118 x + ((1 : ℝ) * Sparse.eval nodeValue1121 x + ((1 : ℝ) * Sparse.eval nodeValue1137 x + ((1 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1329 x + ((1 : ℝ) * Sparse.eval nodeValue1334 x + ((1 : ℝ) * Sparse.eval nodeValue1342 x + ((1 : ℝ) * Sparse.eval nodeValue1416 x + ((1 : ℝ) * Sparse.eval nodeValue2800 x + ((1 : ℝ) * Sparse.eval nodeValue2803 x + ((1 : ℝ) * Sparse.eval nodeValue2816 x + ((1 : ℝ) * Sparse.eval nodeValue2890 x + ((1 : ℝ) * Sparse.eval nodeValue2895 x + ((1 : ℝ) * Sparse.eval nodeValue2901 x + ((1 : ℝ) * Sparse.eval nodeValue2904 x + ((1 : ℝ) * Sparse.eval nodeValue2940 x + ((2 : ℝ) * Sparse.eval nodeValue2941 x + ((1 : ℝ) * Sparse.eval nodeValue2942 x + ((1 : ℝ) * Sparse.eval nodeValue2964 x + ((1 : ℝ) * Sparse.eval nodeValue2966 x + ((1 : ℝ) * Sparse.eval nodeValue3004 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3113 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3205 x + ((1 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3214 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1718 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1663 x + ((1 : ℝ) * Sparse.eval nodeValue1672 x + ((1 : ℝ) * Sparse.eval nodeValue1674 x + ((1 : ℝ) * Sparse.eval nodeValue1679 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue2140 x + ((1 : ℝ) * Sparse.eval nodeValue2149 x + ((1 : ℝ) * Sparse.eval nodeValue2151 x + ((1 : ℝ) * Sparse.eval nodeValue2155 x + ((1 : ℝ) * Sparse.eval nodeValue2172 x + ((1 : ℝ) * Sparse.eval nodeValue2173 x + ((1 : ℝ) * Sparse.eval nodeValue2176 x + ((1 : ℝ) * Sparse.eval nodeValue2189 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2200 x + ((2 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2212 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2693 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1719 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue912 x + ((1 : ℝ) * Sparse.eval nodeValue1795 x + ((1 : ℝ) * Sparse.eval nodeValue1955 x + ((1 : ℝ) * Sparse.eval nodeValue1978 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1720 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1147 x + ((1 : ℝ) * Sparse.eval nodeValue1955 x + ((1 : ℝ) * Sparse.eval nodeValue1960 x + ((2 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2552 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1721 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue904 x + ((1 : ℝ) * Sparse.eval nodeValue1789 x + ((1 : ℝ) * Sparse.eval nodeValue1972 x + ((1 : ℝ) * Sparse.eval nodeValue2019 x + ((2 : ℝ) * Sparse.eval nodeValue2022 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1722 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue924 x + ((1 : ℝ) * Sparse.eval nodeValue1807 x + ((1 : ℝ) * Sparse.eval nodeValue1960 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2053 x + ((1 : ℝ) * Sparse.eval nodeValue2060 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1723 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4196 x + ((1 : ℝ) * Sparse.eval nodeValue4198 x + ((1 : ℝ) * Sparse.eval nodeValue4204 x + ((1 : ℝ) * Sparse.eval nodeValue4212 x + ((1 : ℝ) * Sparse.eval nodeValue4251 x + ((1 : ℝ) * Sparse.eval nodeValue4320 x + ((1 : ℝ) * Sparse.eval nodeValue4324 x + ((1 : ℝ) * Sparse.eval nodeValue4343 x + ((1 : ℝ) * Sparse.eval nodeValue4398 x + ((1 : ℝ) * Sparse.eval nodeValue4631 x + ((1 : ℝ) * Sparse.eval nodeValue4637 x + ((1 : ℝ) * Sparse.eval nodeValue4644 x + ((1 : ℝ) * Sparse.eval nodeValue4706 x + ((1 : ℝ) * Sparse.eval nodeValue4709 x + ((1 : ℝ) * Sparse.eval nodeValue4728 x + ((1 : ℝ) * Sparse.eval nodeValue4760 x + ((1 : ℝ) * Sparse.eval nodeValue4769 x + ((1 : ℝ) * Sparse.eval nodeValue4779 x + ((1 : ℝ) * Sparse.eval nodeValue4788 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4832 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1724 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2391 x + ((1 : ℝ) * Sparse.eval nodeValue2535 x + ((1 : ℝ) * Sparse.eval nodeValue2539 x + ((1 : ℝ) * Sparse.eval nodeValue2585 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0))))))

noncomputable def reducedSource1725 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1921 x + ((1 : ℝ) * Sparse.eval nodeValue1924 x + ((1 : ℝ) * Sparse.eval nodeValue1928 x + ((1 : ℝ) * Sparse.eval nodeValue1945 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1726 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1924 x + ((1 : ℝ) * Sparse.eval nodeValue2534 x + ((1 : ℝ) * Sparse.eval nodeValue2538 x + ((1 : ℝ) * Sparse.eval nodeValue2584 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1727 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2377 x + ((1 : ℝ) * Sparse.eval nodeValue2379 x + ((2 : ℝ) * Sparse.eval nodeValue2382 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1728 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2377 x + ((1 : ℝ) * Sparse.eval nodeValue2541 x + ((2 : ℝ) * Sparse.eval nodeValue2551 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

noncomputable def reducedSource1729 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1897 x + ((1 : ℝ) * Sparse.eval nodeValue2540 x + ((2 : ℝ) * Sparse.eval nodeValue2550 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue3459 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1730 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2075 x + ((1 : ℝ) * Sparse.eval nodeValue2079 x + ((1 : ℝ) * Sparse.eval nodeValue2082 x + ((1 : ℝ) * Sparse.eval nodeValue2101 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1731 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1123 x + ((1 : ℝ) * Sparse.eval nodeValue1875 x + ((1 : ℝ) * Sparse.eval nodeValue1880 x + ((1 : ℝ) * Sparse.eval nodeValue1914 x + ((1 : ℝ) * Sparse.eval nodeValue2079 x + ((1 : ℝ) * Sparse.eval nodeValue2504 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1732 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue916 x + ((1 : ℝ) * Sparse.eval nodeValue1799 x + ((1 : ℝ) * Sparse.eval nodeValue1874 x + ((1 : ℝ) * Sparse.eval nodeValue1911 x + ((1 : ℝ) * Sparse.eval nodeValue2018 x + ((1 : ℝ) * Sparse.eval nodeValue2047 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

noncomputable def reducedSource1733 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2449 x + ((1 : ℝ) * Sparse.eval nodeValue2452 x + ((1 : ℝ) * Sparse.eval nodeValue2461 x + ((1 : ℝ) * Sparse.eval nodeValue2477 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue3793 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0))))))

noncomputable def reducedSource1734 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4356 x + ((1 : ℝ) * Sparse.eval nodeValue4360 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((2 : ℝ) * Sparse.eval nodeValue4543 x + ((1 : ℝ) * Sparse.eval nodeValue4557 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((2 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4692 x + ((2 : ℝ) * Sparse.eval nodeValue4760 x + ((2 : ℝ) * Sparse.eval nodeValue4769 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((2 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((2 : ℝ) * Sparse.eval nodeValue5099 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + 0))))))))))))))))))))

noncomputable def reducedSource1735 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1674 x + ((1 : ℝ) * Sparse.eval nodeValue1692 x + ((1 : ℝ) * Sparse.eval nodeValue1693 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((2 : ℝ) * Sparse.eval nodeValue2151 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((1 : ℝ) * Sparse.eval nodeValue2168 x + ((2 : ℝ) * Sparse.eval nodeValue2173 x + ((2 : ℝ) * Sparse.eval nodeValue2184 x + ((2 : ℝ) * Sparse.eval nodeValue2185 x + ((2 : ℝ) * Sparse.eval nodeValue2203 x + ((2 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((2 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((2 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))))))))))))))))

noncomputable def reducedSource1736 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2382 x + ((1 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2388 x + ((1 : ℝ) * Sparse.eval nodeValue2403 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

noncomputable def reducedSource1737 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2459 x + ((1 : ℝ) * Sparse.eval nodeValue2468 x + ((1 : ℝ) * Sparse.eval nodeValue2505 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

noncomputable def reducedSource1738 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4287 x + ((1 : ℝ) * Sparse.eval nodeValue4293 x + ((1 : ℝ) * Sparse.eval nodeValue4295 x + ((1 : ℝ) * Sparse.eval nodeValue4308 x + ((1 : ℝ) * Sparse.eval nodeValue4401 x + ((1 : ℝ) * Sparse.eval nodeValue4521 x + ((1 : ℝ) * Sparse.eval nodeValue4525 x + ((1 : ℝ) * Sparse.eval nodeValue4538 x + ((1 : ℝ) * Sparse.eval nodeValue4583 x + ((1 : ℝ) * Sparse.eval nodeValue4631 x + ((1 : ℝ) * Sparse.eval nodeValue4637 x + ((1 : ℝ) * Sparse.eval nodeValue4649 x + ((1 : ℝ) * Sparse.eval nodeValue4706 x + ((1 : ℝ) * Sparse.eval nodeValue4712 x + ((1 : ℝ) * Sparse.eval nodeValue4721 x + ((1 : ℝ) * Sparse.eval nodeValue4726 x + ((1 : ℝ) * Sparse.eval nodeValue4728 x + ((1 : ℝ) * Sparse.eval nodeValue4736 x + ((1 : ℝ) * Sparse.eval nodeValue4741 x + ((1 : ℝ) * Sparse.eval nodeValue4745 x + ((1 : ℝ) * Sparse.eval nodeValue4779 x + ((1 : ℝ) * Sparse.eval nodeValue4827 x + ((1 : ℝ) * Sparse.eval nodeValue4832 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue5014 x + ((1 : ℝ) * Sparse.eval nodeValue5055 x + ((1 : ℝ) * Sparse.eval nodeValue5094 x + ((1 : ℝ) * Sparse.eval nodeValue5099 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1739 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4081 x + ((2 : ℝ) * Sparse.eval nodeValue4304 x + ((1 : ℝ) * Sparse.eval nodeValue4317 x + ((1 : ℝ) * Sparse.eval nodeValue4319 x + ((1 : ℝ) * Sparse.eval nodeValue4431 x + ((2 : ℝ) * Sparse.eval nodeValue4643 x + ((2 : ℝ) * Sparse.eval nodeValue4645 x + ((1 : ℝ) * Sparse.eval nodeValue4655 x + ((1 : ℝ) * Sparse.eval nodeValue4657 x + ((2 : ℝ) * Sparse.eval nodeValue4710 x + ((2 : ℝ) * Sparse.eval nodeValue4719 x + ((2 : ℝ) * Sparse.eval nodeValue4741 x + ((2 : ℝ) * Sparse.eval nodeValue4742 x + ((1 : ℝ) * Sparse.eval nodeValue4754 x + ((2 : ℝ) * Sparse.eval nodeValue4788 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((2 : ℝ) * Sparse.eval nodeValue5000 x + ((1 : ℝ) * Sparse.eval nodeValue5021 x + ((1 : ℝ) * Sparse.eval nodeValue5107 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + 0))))))))))))))))))))

noncomputable def reducedSource1740 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4085 x + ((4 : ℝ) * Sparse.eval nodeValue4343 x + ((1 : ℝ) * Sparse.eval nodeValue4350 x + ((2 : ℝ) * Sparse.eval nodeValue4359 x + ((2 : ℝ) * Sparse.eval nodeValue4501 x + ((4 : ℝ) * Sparse.eval nodeValue4678 x + ((1 : ℝ) * Sparse.eval nodeValue4691 x + ((2 : ℝ) * Sparse.eval nodeValue4759 x + ((4 : ℝ) * Sparse.eval nodeValue4832 x + ((4 : ℝ) * Sparse.eval nodeValue4837 x + ((2 : ℝ) * Sparse.eval nodeValue4845 x + ((2 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + 0))))))))))))

noncomputable def reducedSource1741 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1666 x + ((1 : ℝ) * Sparse.eval nodeValue1677 x + ((2 : ℝ) * Sparse.eval nodeValue1683 x + ((2 : ℝ) * Sparse.eval nodeValue1730 x + ((4 : ℝ) * Sparse.eval nodeValue2143 x + ((1 : ℝ) * Sparse.eval nodeValue2159 x + ((2 : ℝ) * Sparse.eval nodeValue2170 x + ((4 : ℝ) * Sparse.eval nodeValue2193 x + ((4 : ℝ) * Sparse.eval nodeValue2208 x + ((2 : ℝ) * Sparse.eval nodeValue2218 x + ((2 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))))))))))

noncomputable def reducedSource1742 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue937 x + ((2 : ℝ) * Sparse.eval nodeValue1804 x + ((1 : ℝ) * Sparse.eval nodeValue1817 x + ((1 : ℝ) * Sparse.eval nodeValue2056 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

noncomputable def reducedSource1743 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4081 x + ((1 : ℝ) * Sparse.eval nodeValue4286 x + ((1 : ℝ) * Sparse.eval nodeValue4289 x + ((1 : ℝ) * Sparse.eval nodeValue4294 x + ((1 : ℝ) * Sparse.eval nodeValue4302 x + ((1 : ℝ) * Sparse.eval nodeValue4320 x + ((1 : ℝ) * Sparse.eval nodeValue4324 x + ((1 : ℝ) * Sparse.eval nodeValue4338 x + ((1 : ℝ) * Sparse.eval nodeValue4398 x + ((1 : ℝ) * Sparse.eval nodeValue4426 x + ((1 : ℝ) * Sparse.eval nodeValue4630 x + ((1 : ℝ) * Sparse.eval nodeValue4636 x + ((1 : ℝ) * Sparse.eval nodeValue4643 x + ((1 : ℝ) * Sparse.eval nodeValue4658 x + ((1 : ℝ) * Sparse.eval nodeValue4673 x + ((1 : ℝ) * Sparse.eval nodeValue4708 x + ((1 : ℝ) * Sparse.eval nodeValue4720 x + ((1 : ℝ) * Sparse.eval nodeValue4728 x + ((1 : ℝ) * Sparse.eval nodeValue4738 x + ((1 : ℝ) * Sparse.eval nodeValue4741 x + ((1 : ℝ) * Sparse.eval nodeValue4744 x + ((1 : ℝ) * Sparse.eval nodeValue4778 x + ((1 : ℝ) * Sparse.eval nodeValue4779 x + ((1 : ℝ) * Sparse.eval nodeValue4788 x + ((1 : ℝ) * Sparse.eval nodeValue4800 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4827 x + ((1 : ℝ) * Sparse.eval nodeValue4837 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + 0)))))))))))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1744 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4064 x + ((1 : ℝ) * Sparse.eval nodeValue4066 x + ((2 : ℝ) * Sparse.eval nodeValue4067 x + ((2 : ℝ) * Sparse.eval nodeValue4070 x + ((4 : ℝ) * Sparse.eval nodeValue4074 x + ((1 : ℝ) * Sparse.eval nodeValue4076 x + ((2 : ℝ) * Sparse.eval nodeValue4077 x + ((4 : ℝ) * Sparse.eval nodeValue4080 x + ((4 : ℝ) * Sparse.eval nodeValue4081 x + ((2 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + ((1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))))))))

noncomputable def reducedSource1745 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2340 x + ((1 : ℝ) * Sparse.eval nodeValue2816 x + ((1 : ℝ) * Sparse.eval nodeValue3162 x + ((1 : ℝ) * Sparse.eval nodeValue3174 x + ((1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1746 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2213 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1747 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue910 x + ((1 : ℝ) * Sparse.eval nodeValue1794 x + ((1 : ℝ) * Sparse.eval nodeValue1977 x + ((1 : ℝ) * Sparse.eval nodeValue2012 x + ((1 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue2023 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1748 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2323 x + ((1 : ℝ) * Sparse.eval nodeValue2800 x + ((1 : ℝ) * Sparse.eval nodeValue3189 x + ((2 : ℝ) * Sparse.eval nodeValue3199 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1749 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2213 x + ((1 : ℝ) * Sparse.eval nodeValue2396 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((1 : ℝ) * Sparse.eval nodeValue3610 x + ((2 : ℝ) * Sparse.eval nodeValue3612 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1750 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3193 x + ((1 : ℝ) * Sparse.eval nodeValue3648 x + ((1 : ℝ) * Sparse.eval nodeValue3653 x + ((1 : ℝ) * Sparse.eval nodeValue3659 x + ((2 : ℝ) * Sparse.eval nodeValue3762 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

noncomputable def reducedSource1751 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue950 x + ((1 : ℝ) * Sparse.eval nodeValue1829 x + ((1 : ℝ) * Sparse.eval nodeValue1977 x + ((1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2110 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1752 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2327 x + ((1 : ℝ) * Sparse.eval nodeValue2803 x + ((1 : ℝ) * Sparse.eval nodeValue3133 x + ((1 : ℝ) * Sparse.eval nodeValue3138 x + ((1 : ℝ) * Sparse.eval nodeValue3174 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1753 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2401 x + ((1 : ℝ) * Sparse.eval nodeValue3536 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3630 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1754 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1755 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3166 x + ((1 : ℝ) * Sparse.eval nodeValue3658 x + ((1 : ℝ) * Sparse.eval nodeValue3660 x + ((1 : ℝ) * Sparse.eval nodeValue3666 x + ((2 : ℝ) * Sparse.eval nodeValue3772 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0)))))

noncomputable def reducedSource1756 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2346 x + ((1 : ℝ) * Sparse.eval nodeValue2821 x + ((2 : ℝ) * Sparse.eval nodeValue3129 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((1 : ℝ) * Sparse.eval nodeValue3397 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1757 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3147 x + ((1 : ℝ) * Sparse.eval nodeValue3372 x + ((1 : ℝ) * Sparse.eval nodeValue3473 x + ((2 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3611 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1758 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1141 x + ((1 : ℝ) * Sparse.eval nodeValue2343 x + ((1 : ℝ) * Sparse.eval nodeValue2433 x + ((1 : ℝ) * Sparse.eval nodeValue2499 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1759 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2335 x + ((1 : ℝ) * Sparse.eval nodeValue2811 x + ((1 : ℝ) * Sparse.eval nodeValue2846 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((1 : ℝ) * Sparse.eval nodeValue2979 x + ((1 : ℝ) * Sparse.eval nodeValue3705 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource176 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue776 x + ((1 : ℝ) * Sparse.eval nodeValue778 x + ((3 : ℝ) * Sparse.eval nodeValue784 x + ((3 : ℝ) * Sparse.eval nodeValue2009 x + ((3 : ℝ) * Sparse.eval nodeValue2012 x + ((6 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2187 x + ((3 : ℝ) * Sparse.eval nodeValue2192 x + ((1 : ℝ) * Sparse.eval nodeValue2232 x + ((3 : ℝ) * Sparse.eval nodeValue2240 x + ((3 : ℝ) * Sparse.eval nodeValue3847 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + 0))))))))))))

noncomputable def reducedSource177 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3221 x + ((3 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((1 : ℝ) * Sparse.eval nodeValue4025 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource178 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1464 x + ((1 : ℝ) * Sparse.eval nodeValue1467 x + ((1 : ℝ) * Sparse.eval nodeValue1474 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource179 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1464 x + ((1 : ℝ) * Sparse.eval nodeValue3172 x + ((1 : ℝ) * Sparse.eval nodeValue3197 x + ((2 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource180 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue3199 x + ((2 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource181 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1467 x + ((1 : ℝ) * Sparse.eval nodeValue3179 x + ((3 : ℝ) * Sparse.eval nodeValue3199 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource182 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2707 x + ((3 : ℝ) * Sparse.eval nodeValue3197 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource183 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1474 x + ((3 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue2707 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource184 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1354 x + ((1 : ℝ) * Sparse.eval nodeValue1366 x + ((1 : ℝ) * Sparse.eval nodeValue1405 x + ((1 : ℝ) * Sparse.eval nodeValue3058 x + ((1 : ℝ) * Sparse.eval nodeValue3059 x + ((3 : ℝ) * Sparse.eval nodeValue3077 x + ((3 : ℝ) * Sparse.eval nodeValue3146 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((3 : ℝ) * Sparse.eval nodeValue3165 x + ((1 : ℝ) * Sparse.eval nodeValue3179 x + ((6 : ℝ) * Sparse.eval nodeValue3222 x + ((3 : ℝ) * Sparse.eval nodeValue3223 x + ((3 : ℝ) * Sparse.eval nodeValue3227 x + 0))))))))))))

noncomputable def reducedSource185 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2252 x + ((1 : ℝ) * Sparse.eval nodeValue2507 x + ((1 : ℝ) * Sparse.eval nodeValue3576 x + ((3 : ℝ) * Sparse.eval nodeValue3625 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource186 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1056 x + ((1 : ℝ) * Sparse.eval nodeValue2131 x + ((1 : ℝ) * Sparse.eval nodeValue2252 x + ((3 : ℝ) * Sparse.eval nodeValue2277 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource187 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1038 x + ((1 : ℝ) * Sparse.eval nodeValue2104 x + ((1 : ℝ) * Sparse.eval nodeValue2252 x + ((3 : ℝ) * Sparse.eval nodeValue2262 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource188 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2059 x + ((1 : ℝ) * Sparse.eval nodeValue2063 x + ((1 : ℝ) * Sparse.eval nodeValue2064 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((2 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((2 : ℝ) * Sparse.eval nodeValue3015 x + ((2 : ℝ) * Sparse.eval nodeValue3022 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((2 : ℝ) * Sparse.eval nodeValue3035 x + ((2 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3049 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((2 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + 0))))))))))))))))))))

noncomputable def reducedSource189 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((2 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3632 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource190 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1238 x + ((1 : ℝ) * Sparse.eval nodeValue1244 x + ((1 : ℝ) * Sparse.eval nodeValue1245 x + ((1 : ℝ) * Sparse.eval nodeValue1296 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource191 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1296 x + ((1 : ℝ) * Sparse.eval nodeValue2138 x + ((2 : ℝ) * Sparse.eval nodeValue2592 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1760 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3476 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1761 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1928 x + ((1 : ℝ) * Sparse.eval nodeValue2674 x + ((1 : ℝ) * Sparse.eval nodeValue3348 x + ((1 : ℝ) * Sparse.eval nodeValue3430 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1762 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1117 x + ((1 : ℝ) * Sparse.eval nodeValue2324 x + ((1 : ℝ) * Sparse.eval nodeValue2441 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1763 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2320 x + ((1 : ℝ) * Sparse.eval nodeValue2797 x + ((1 : ℝ) * Sparse.eval nodeValue2900 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2981 x + ((1 : ℝ) * Sparse.eval nodeValue3690 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1764 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1941 x + ((1 : ℝ) * Sparse.eval nodeValue3351 x + ((2 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3482 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))

noncomputable def reducedSource1765 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1921 x + ((1 : ℝ) * Sparse.eval nodeValue2668 x + ((1 : ℝ) * Sparse.eval nodeValue3345 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3478 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1766 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1807 x + ((1 : ℝ) * Sparse.eval nodeValue2427 x + ((1 : ℝ) * Sparse.eval nodeValue2435 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((1 : ℝ) * Sparse.eval nodeValue2560 x + ((1 : ℝ) * Sparse.eval nodeValue3391 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1767 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1347 x + ((1 : ℝ) * Sparse.eval nodeValue2831 x + ((1 : ℝ) * Sparse.eval nodeValue2902 x + ((1 : ℝ) * Sparse.eval nodeValue2942 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2964 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1768 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2584 x + ((1 : ℝ) * Sparse.eval nodeValue2668 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2674 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1769 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3614 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1770 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2347 x + ((1 : ℝ) * Sparse.eval nodeValue2423 x + ((1 : ℝ) * Sparse.eval nodeValue2431 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1771 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1151 x + ((1 : ℝ) * Sparse.eval nodeValue2350 x + ((1 : ℝ) * Sparse.eval nodeValue2431 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2557 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1772 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1330 x + ((1 : ℝ) * Sparse.eval nodeValue2824 x + ((1 : ℝ) * Sparse.eval nodeValue2896 x + ((1 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2928 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1773 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2349 x + ((1 : ℝ) * Sparse.eval nodeValue2890 x + ((1 : ℝ) * Sparse.eval nodeValue2896 x + ((2 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1774 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2534 x + ((1 : ℝ) * Sparse.eval nodeValue3430 x + ((1 : ℝ) * Sparse.eval nodeValue3433 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((2 : ℝ) * Sparse.eval nodeValue3516 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1775 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2422 x + ((1 : ℝ) * Sparse.eval nodeValue2432 x + ((1 : ℝ) * Sparse.eval nodeValue2489 x + ((1 : ℝ) * Sparse.eval nodeValue2546 x + ((1 : ℝ) * Sparse.eval nodeValue3779 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1776 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1152 x + ((1 : ℝ) * Sparse.eval nodeValue2351 x + ((1 : ℝ) * Sparse.eval nodeValue2432 x + ((1 : ℝ) * Sparse.eval nodeValue2546 x + ((2 : ℝ) * Sparse.eval nodeValue2556 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1777 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1997 x + ((1 : ℝ) * Sparse.eval nodeValue2002 x + ((1 : ℝ) * Sparse.eval nodeValue2044 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((1 : ℝ) * Sparse.eval nodeValue3520 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1778 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3520 x + ((2 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((1 : ℝ) * Sparse.eval nodeValue3616 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

noncomputable def reducedSource1779 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2905 x + ((1 : ℝ) * Sparse.eval nodeValue3680 x + ((1 : ℝ) * Sparse.eval nodeValue3683 x + ((1 : ℝ) * Sparse.eval nodeValue3696 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0))))))

noncomputable def reducedSource1780 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4553 x + ((1 : ℝ) * Sparse.eval nodeValue4557 x + ((1 : ℝ) * Sparse.eval nodeValue4559 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((2 : ℝ) * Sparse.eval nodeValue4686 x + ((1 : ℝ) * Sparse.eval nodeValue4693 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((2 : ℝ) * Sparse.eval nodeValue4970 x + ((2 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue4979 x + ((2 : ℝ) * Sparse.eval nodeValue5114 x + ((2 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5389 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + 0))))))))))))))))))))

noncomputable def reducedSource1781 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1138 x + ((1 : ℝ) * Sparse.eval nodeValue1143 x + ((1 : ℝ) * Sparse.eval nodeValue1145 x + ((1 : ℝ) * Sparse.eval nodeValue1311 x + ((2 : ℝ) * Sparse.eval nodeValue1812 x + ((1 : ℝ) * Sparse.eval nodeValue1819 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((2 : ℝ) * Sparse.eval nodeValue2815 x + ((2 : ℝ) * Sparse.eval nodeValue2817 x + ((1 : ℝ) * Sparse.eval nodeValue2820 x + ((2 : ℝ) * Sparse.eval nodeValue2896 x + ((2 : ℝ) * Sparse.eval nodeValue2954 x + ((2 : ℝ) * Sparse.eval nodeValue2963 x + ((1 : ℝ) * Sparse.eval nodeValue2965 x + ((2 : ℝ) * Sparse.eval nodeValue2968 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((2 : ℝ) * Sparse.eval nodeValue3739 x + ((1 : ℝ) * Sparse.eval nodeValue3740 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0))))))))))))))))))))

noncomputable def reducedSource1782 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4359 x + ((1 : ℝ) * Sparse.eval nodeValue4361 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((2 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4692 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((2 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4972 x + ((2 : ℝ) * Sparse.eval nodeValue5038 x + ((2 : ℝ) * Sparse.eval nodeValue5080 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5390 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))

noncomputable def reducedSource1783 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue932 x + ((1 : ℝ) * Sparse.eval nodeValue937 x + ((1 : ℝ) * Sparse.eval nodeValue939 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((2 : ℝ) * Sparse.eval nodeValue1807 x + ((1 : ℝ) * Sparse.eval nodeValue1818 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((2 : ℝ) * Sparse.eval nodeValue2341 x + ((1 : ℝ) * Sparse.eval nodeValue2345 x + ((2 : ℝ) * Sparse.eval nodeValue2431 x + ((2 : ℝ) * Sparse.eval nodeValue2434 x + ((2 : ℝ) * Sparse.eval nodeValue2488 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((2 : ℝ) * Sparse.eval nodeValue2599 x + ((1 : ℝ) * Sparse.eval nodeValue2601 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((2 : ℝ) * Sparse.eval nodeValue3737 x + ((1 : ℝ) * Sparse.eval nodeValue3741 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + 0))))))))))))))))))))

noncomputable def reducedSource1784 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((4 : ℝ) * Sparse.eval nodeValue5080 x + ((2 : ℝ) * Sparse.eval nodeValue5110 x + ((2 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5129 x + ((2 : ℝ) * Sparse.eval nodeValue5140 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((2 : ℝ) * Sparse.eval nodeValue5151 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5175 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5206 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + 0)))))))))))))))))

noncomputable def reducedSource1785 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((1 : ℝ) * Sparse.eval nodeValue2523 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((2 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((2 : ℝ) * Sparse.eval nodeValue2916 x + ((2 : ℝ) * Sparse.eval nodeValue2930 x + ((2 : ℝ) * Sparse.eval nodeValue2931 x + ((2 : ℝ) * Sparse.eval nodeValue2942 x + ((2 : ℝ) * Sparse.eval nodeValue2943 x + ((1 : ℝ) * Sparse.eval nodeValue2967 x + ((1 : ℝ) * Sparse.eval nodeValue2969 x + ((2 : ℝ) * Sparse.eval nodeValue2990 x + ((1 : ℝ) * Sparse.eval nodeValue3005 x + ((1 : ℝ) * Sparse.eval nodeValue3006 x + ((1 : ℝ) * Sparse.eval nodeValue3095 x + ((1 : ℝ) * Sparse.eval nodeValue3187 x + ((2 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3216 x + 0))))))))))))))))))))

noncomputable def reducedSource1786 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4554 x + ((2 : ℝ) * Sparse.eval nodeValue4558 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + ((4 : ℝ) * Sparse.eval nodeValue4948 x + ((2 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4974 x + ((2 : ℝ) * Sparse.eval nodeValue5115 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5174 x + ((2 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5390 x + ((2 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + 0)))))))))))))

noncomputable def reducedSource1787 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1139 x + ((2 : ℝ) * Sparse.eval nodeValue1144 x + ((1 : ℝ) * Sparse.eval nodeValue1312 x + ((4 : ℝ) * Sparse.eval nodeValue2339 x + ((2 : ℝ) * Sparse.eval nodeValue2345 x + ((2 : ℝ) * Sparse.eval nodeValue2601 x + ((2 : ℝ) * Sparse.eval nodeValue2818 x + ((2 : ℝ) * Sparse.eval nodeValue2897 x + ((4 : ℝ) * Sparse.eval nodeValue2960 x + ((2 : ℝ) * Sparse.eval nodeValue2969 x + ((2 : ℝ) * Sparse.eval nodeValue3123 x + ((1 : ℝ) * Sparse.eval nodeValue3741 x + ((2 : ℝ) * Sparse.eval nodeValue3933 x + ((2 : ℝ) * Sparse.eval nodeValue4001 x + 0)))))))))))))

noncomputable def reducedSource1788 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4355 x + ((2 : ℝ) * Sparse.eval nodeValue4360 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((4 : ℝ) * Sparse.eval nodeValue4943 x + ((2 : ℝ) * Sparse.eval nodeValue4950 x + ((2 : ℝ) * Sparse.eval nodeValue4952 x + ((2 : ℝ) * Sparse.eval nodeValue5039 x + ((2 : ℝ) * Sparse.eval nodeValue5081 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5171 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((2 : ℝ) * Sparse.eval nodeValue5465 x + ((1 : ℝ) * Sparse.eval nodeValue5466 x + ((2 : ℝ) * Sparse.eval nodeValue5487 x + 0)))))))))))))

noncomputable def reducedSource1789 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue933 x + ((2 : ℝ) * Sparse.eval nodeValue938 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((4 : ℝ) * Sparse.eval nodeValue2334 x + ((2 : ℝ) * Sparse.eval nodeValue2342 x + ((2 : ℝ) * Sparse.eval nodeValue2344 x + ((2 : ℝ) * Sparse.eval nodeValue2432 x + ((2 : ℝ) * Sparse.eval nodeValue2489 x + ((4 : ℝ) * Sparse.eval nodeValue2595 x + ((2 : ℝ) * Sparse.eval nodeValue2598 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((2 : ℝ) * Sparse.eval nodeValue3931 x + ((1 : ℝ) * Sparse.eval nodeValue3934 x + ((2 : ℝ) * Sparse.eval nodeValue4000 x + 0)))))))))))))

noncomputable def reducedSource1790 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((4 : ℝ) * Sparse.eval nodeValue5081 x + ((4 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5130 x + ((4 : ℝ) * Sparse.eval nodeValue5141 x + ((4 : ℝ) * Sparse.eval nodeValue5152 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5189 x + ((2 : ℝ) * Sparse.eval nodeValue5207 x + 0)))))))))))

noncomputable def reducedSource1791 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3482 x + ((2 : ℝ) * Sparse.eval nodeValue3485 x + ((2 : ℝ) * Sparse.eval nodeValue3616 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1792 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1171 x + ((1 : ℝ) * Sparse.eval nodeValue2362 x + ((1 : ℝ) * Sparse.eval nodeValue2529 x + ((1 : ℝ) * Sparse.eval nodeValue2575 x + ((1 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2600 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1793 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1812 x + ((1 : ℝ) * Sparse.eval nodeValue2892 x + ((1 : ℝ) * Sparse.eval nodeValue2899 x + ((2 : ℝ) * Sparse.eval nodeValue2930 x + ((1 : ℝ) * Sparse.eval nodeValue3394 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1794 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2396 x + ((1 : ℝ) * Sparse.eval nodeValue2399 x + ((1 : ℝ) * Sparse.eval nodeValue2401 x + ((1 : ℝ) * Sparse.eval nodeValue2405 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1795 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4332 x + ((1 : ℝ) * Sparse.eval nodeValue4334 x + ((1 : ℝ) * Sparse.eval nodeValue4335 x + ((1 : ℝ) * Sparse.eval nodeValue4357 x + ((1 : ℝ) * Sparse.eval nodeValue4444 x + ((1 : ℝ) * Sparse.eval nodeValue4930 x + ((1 : ℝ) * Sparse.eval nodeValue4933 x + ((1 : ℝ) * Sparse.eval nodeValue4934 x + ((1 : ℝ) * Sparse.eval nodeValue4935 x + ((1 : ℝ) * Sparse.eval nodeValue4948 x + ((1 : ℝ) * Sparse.eval nodeValue4951 x + ((1 : ℝ) * Sparse.eval nodeValue4954 x + ((1 : ℝ) * Sparse.eval nodeValue4970 x + ((1 : ℝ) * Sparse.eval nodeValue5040 x + ((1 : ℝ) * Sparse.eval nodeValue5067 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5117 x + ((1 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1796 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue910 x + ((1 : ℝ) * Sparse.eval nodeValue912 x + ((1 : ℝ) * Sparse.eval nodeValue913 x + ((1 : ℝ) * Sparse.eval nodeValue935 x + ((1 : ℝ) * Sparse.eval nodeValue1026 x + ((1 : ℝ) * Sparse.eval nodeValue2324 x + ((1 : ℝ) * Sparse.eval nodeValue2325 x + ((1 : ℝ) * Sparse.eval nodeValue2326 x + ((1 : ℝ) * Sparse.eval nodeValue2343 x + ((1 : ℝ) * Sparse.eval nodeValue2347 x + ((1 : ℝ) * Sparse.eval nodeValue2357 x + ((1 : ℝ) * Sparse.eval nodeValue2422 x + ((1 : ℝ) * Sparse.eval nodeValue2433 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((1 : ℝ) * Sparse.eval nodeValue2530 x + ((1 : ℝ) * Sparse.eval nodeValue2531 x + ((1 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2569 x + ((1 : ℝ) * Sparse.eval nodeValue2570 x + ((1 : ℝ) * Sparse.eval nodeValue2572 x + ((1 : ℝ) * Sparse.eval nodeValue2576 x + ((1 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue2596 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue3926 x + ((1 : ℝ) * Sparse.eval nodeValue3936 x + ((1 : ℝ) * Sparse.eval nodeValue3940 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue3996 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1797 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1678 x + ((1 : ℝ) * Sparse.eval nodeValue1679 x + ((1 : ℝ) * Sparse.eval nodeValue1682 x + ((1 : ℝ) * Sparse.eval nodeValue1689 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((1 : ℝ) * Sparse.eval nodeValue3408 x + ((1 : ℝ) * Sparse.eval nodeValue3414 x + ((1 : ℝ) * Sparse.eval nodeValue3415 x + ((1 : ℝ) * Sparse.eval nodeValue3418 x + ((1 : ℝ) * Sparse.eval nodeValue3419 x + ((1 : ℝ) * Sparse.eval nodeValue3420 x + ((1 : ℝ) * Sparse.eval nodeValue3452 x + ((1 : ℝ) * Sparse.eval nodeValue3454 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3588 x + ((1 : ℝ) * Sparse.eval nodeValue3599 x + ((1 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3773 x + ((1 : ℝ) * Sparse.eval nodeValue3774 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1798 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2326 x + ((1 : ℝ) * Sparse.eval nodeValue2802 x + ((1 : ℝ) * Sparse.eval nodeValue2822 x + ((1 : ℝ) * Sparse.eval nodeValue2827 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1799 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1328 x + ((1 : ℝ) * Sparse.eval nodeValue2822 x + ((1 : ℝ) * Sparse.eval nodeValue2893 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1800 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1338 x + ((1 : ℝ) * Sparse.eval nodeValue2827 x + ((1 : ℝ) * Sparse.eval nodeValue2900 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2955 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1801 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2399 x + ((1 : ℝ) * Sparse.eval nodeValue3433 x + ((1 : ℝ) * Sparse.eval nodeValue3439 x + ((1 : ℝ) * Sparse.eval nodeValue3485 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1802 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2910 x + ((1 : ℝ) * Sparse.eval nodeValue3346 x + ((1 : ℝ) * Sparse.eval nodeValue3349 x + ((1 : ℝ) * Sparse.eval nodeValue3357 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1803 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2355 x + ((1 : ℝ) * Sparse.eval nodeValue2438 x + ((1 : ℝ) * Sparse.eval nodeValue2443 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1804 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2352 x + ((1 : ℝ) * Sparse.eval nodeValue2798 x + ((1 : ℝ) * Sparse.eval nodeValue2803 x + ((1 : ℝ) * Sparse.eval nodeValue2817 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1805 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1321 x + ((1 : ℝ) * Sparse.eval nodeValue2817 x + ((1 : ℝ) * Sparse.eval nodeValue2848 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2885 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1806 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2538 x + ((1 : ℝ) * Sparse.eval nodeValue3345 x + ((1 : ℝ) * Sparse.eval nodeValue3348 x + ((1 : ℝ) * Sparse.eval nodeValue3354 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

noncomputable def reducedSource1807 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2048 x + ((1 : ℝ) * Sparse.eval nodeValue3386 x + ((1 : ℝ) * Sparse.eval nodeValue3491 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1808 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2799 x + ((2 : ℝ) * Sparse.eval nodeValue2802 x + ((1 : ℝ) * Sparse.eval nodeValue2818 x + ((1 : ℝ) * Sparse.eval nodeValue2868 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1809 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1322 x + ((1 : ℝ) * Sparse.eval nodeValue2818 x + ((1 : ℝ) * Sparse.eval nodeValue2849 x + ((1 : ℝ) * Sparse.eval nodeValue2868 x + ((2 : ℝ) * Sparse.eval nodeValue2884 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1810 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1819 x + ((2 : ℝ) * Sparse.eval nodeValue2812 x + ((1 : ℝ) * Sparse.eval nodeValue2821 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((1 : ℝ) * Sparse.eval nodeValue3397 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1811 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4372 x + ((1 : ℝ) * Sparse.eval nodeValue4373 x + ((1 : ℝ) * Sparse.eval nodeValue4374 x + ((1 : ℝ) * Sparse.eval nodeValue4480 x + ((2 : ℝ) * Sparse.eval nodeValue4944 x + ((1 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4965 x + ((2 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue4979 x + ((2 : ℝ) * Sparse.eval nodeValue5044 x + ((2 : ℝ) * Sparse.eval nodeValue5090 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((2 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5201 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((2 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5371 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + 0))))))))))))))))))))

noncomputable def reducedSource1812 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1734 x + ((1 : ℝ) * Sparse.eval nodeValue1735 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((1 : ℝ) * Sparse.eval nodeValue1748 x + ((2 : ℝ) * Sparse.eval nodeValue3413 x + ((1 : ℝ) * Sparse.eval nodeValue3423 x + ((2 : ℝ) * Sparse.eval nodeValue3474 x + ((2 : ℝ) * Sparse.eval nodeValue3475 x + ((2 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((2 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3579 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((2 : ℝ) * Sparse.eval nodeValue3595 x + ((1 : ℝ) * Sparse.eval nodeValue3596 x + ((2 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((2 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3775 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + 0))))))))))))))))))))

noncomputable def reducedSource1813 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2345 x + ((2 : ℝ) * Sparse.eval nodeValue2813 x + ((1 : ℝ) * Sparse.eval nodeValue2820 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((1 : ℝ) * Sparse.eval nodeValue3707 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1814 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2533 x + ((1 : ℝ) * Sparse.eval nodeValue3679 x + ((1 : ℝ) * Sparse.eval nodeValue3681 x + ((1 : ℝ) * Sparse.eval nodeValue3695 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

noncomputable def reducedSource1815 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4533 x + ((1 : ℝ) * Sparse.eval nodeValue4534 x + ((1 : ℝ) * Sparse.eval nodeValue4535 x + ((1 : ℝ) * Sparse.eval nodeValue4556 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4929 x + ((1 : ℝ) * Sparse.eval nodeValue4934 x + ((1 : ℝ) * Sparse.eval nodeValue4943 x + ((1 : ℝ) * Sparse.eval nodeValue4955 x + ((1 : ℝ) * Sparse.eval nodeValue4956 x + ((1 : ℝ) * Sparse.eval nodeValue4959 x + ((1 : ℝ) * Sparse.eval nodeValue4966 x + ((1 : ℝ) * Sparse.eval nodeValue4972 x + ((1 : ℝ) * Sparse.eval nodeValue5036 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + ((1 : ℝ) * Sparse.eval nodeValue5112 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5135 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1816 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1117 x + ((1 : ℝ) * Sparse.eval nodeValue1119 x + ((1 : ℝ) * Sparse.eval nodeValue1120 x + ((1 : ℝ) * Sparse.eval nodeValue1141 x + ((1 : ℝ) * Sparse.eval nodeValue1274 x + ((1 : ℝ) * Sparse.eval nodeValue2349 x + ((1 : ℝ) * Sparse.eval nodeValue2352 x + ((1 : ℝ) * Sparse.eval nodeValue2358 x + ((1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2801 x + ((1 : ℝ) * Sparse.eval nodeValue2802 x + ((1 : ℝ) * Sparse.eval nodeValue2819 x + ((1 : ℝ) * Sparse.eval nodeValue2823 x + ((1 : ℝ) * Sparse.eval nodeValue2828 x + ((1 : ℝ) * Sparse.eval nodeValue2898 x + ((1 : ℝ) * Sparse.eval nodeValue2903 x + ((1 : ℝ) * Sparse.eval nodeValue2934 x + ((1 : ℝ) * Sparse.eval nodeValue2937 x + ((1 : ℝ) * Sparse.eval nodeValue2939 x + ((1 : ℝ) * Sparse.eval nodeValue2943 x + ((1 : ℝ) * Sparse.eval nodeValue2955 x + ((1 : ℝ) * Sparse.eval nodeValue2961 x + ((1 : ℝ) * Sparse.eval nodeValue3006 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3728 x + ((1 : ℝ) * Sparse.eval nodeValue3937 x + ((1 : ℝ) * Sparse.eval nodeValue3941 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + ((1 : ℝ) * Sparse.eval nodeValue4035 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1817 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3267 x + ((1 : ℝ) * Sparse.eval nodeValue3268 x + ((1 : ℝ) * Sparse.eval nodeValue3271 x + ((1 : ℝ) * Sparse.eval nodeValue3272 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3403 x + ((1 : ℝ) * Sparse.eval nodeValue3411 x + ((1 : ℝ) * Sparse.eval nodeValue3415 x + ((1 : ℝ) * Sparse.eval nodeValue3450 x + ((1 : ℝ) * Sparse.eval nodeValue3457 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3485 x + ((1 : ℝ) * Sparse.eval nodeValue3508 x + ((1 : ℝ) * Sparse.eval nodeValue3510 x + ((1 : ℝ) * Sparse.eval nodeValue3512 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3555 x + ((1 : ℝ) * Sparse.eval nodeValue3556 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1818 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2325 x + ((1 : ℝ) * Sparse.eval nodeValue2348 x + ((1 : ℝ) * Sparse.eval nodeValue2352 x + ((1 : ℝ) * Sparse.eval nodeValue2356 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1819 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1149 x + ((1 : ℝ) * Sparse.eval nodeValue2348 x + ((1 : ℝ) * Sparse.eval nodeValue2428 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2554 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1820 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2319 x + ((1 : ℝ) * Sparse.eval nodeValue2524 x + ((1 : ℝ) * Sparse.eval nodeValue2525 x + ((2 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue3689 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1821 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1160 x + ((1 : ℝ) * Sparse.eval nodeValue2356 x + ((1 : ℝ) * Sparse.eval nodeValue2525 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2591 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1822 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4323 x + ((1 : ℝ) * Sparse.eval nodeValue4324 x + ((1 : ℝ) * Sparse.eval nodeValue4325 x + ((1 : ℝ) * Sparse.eval nodeValue4349 x + ((1 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4631 x + ((1 : ℝ) * Sparse.eval nodeValue4637 x + ((1 : ℝ) * Sparse.eval nodeValue4644 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4902 x + ((1 : ℝ) * Sparse.eval nodeValue4907 x + ((1 : ℝ) * Sparse.eval nodeValue4913 x + ((1 : ℝ) * Sparse.eval nodeValue4928 x + ((1 : ℝ) * Sparse.eval nodeValue4946 x + ((1 : ℝ) * Sparse.eval nodeValue4987 x + ((1 : ℝ) * Sparse.eval nodeValue5003 x + ((1 : ℝ) * Sparse.eval nodeValue5036 x + ((1 : ℝ) * Sparse.eval nodeValue5050 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1823 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2541 x + ((1 : ℝ) * Sparse.eval nodeValue3646 x + ((2 : ℝ) * Sparse.eval nodeValue3650 x + ((2 : ℝ) * Sparse.eval nodeValue3757 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1824 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2456 x + ((1 : ℝ) * Sparse.eval nodeValue2756 x + ((1 : ℝ) * Sparse.eval nodeValue3680 x + ((1 : ℝ) * Sparse.eval nodeValue3776 x + ((2 : ℝ) * Sparse.eval nodeValue3796 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0)))))

noncomputable def reducedSource1825 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4529 x + ((1 : ℝ) * Sparse.eval nodeValue4534 x + ((1 : ℝ) * Sparse.eval nodeValue4536 x + ((1 : ℝ) * Sparse.eval nodeValue4553 x + ((1 : ℝ) * Sparse.eval nodeValue4592 x + ((1 : ℝ) * Sparse.eval nodeValue4664 x + ((1 : ℝ) * Sparse.eval nodeValue4670 x + ((1 : ℝ) * Sparse.eval nodeValue4682 x + ((1 : ℝ) * Sparse.eval nodeValue4853 x + ((1 : ℝ) * Sparse.eval nodeValue4931 x + ((1 : ℝ) * Sparse.eval nodeValue4934 x + ((1 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue4954 x + ((1 : ℝ) * Sparse.eval nodeValue4965 x + ((1 : ℝ) * Sparse.eval nodeValue5038 x + ((1 : ℝ) * Sparse.eval nodeValue5042 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1826 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2147 x + ((1 : ℝ) * Sparse.eval nodeValue2149 x + ((1 : ℝ) * Sparse.eval nodeValue2153 x + ((1 : ℝ) * Sparse.eval nodeValue2164 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue3258 x + ((1 : ℝ) * Sparse.eval nodeValue3268 x + ((1 : ℝ) * Sparse.eval nodeValue3270 x + ((1 : ℝ) * Sparse.eval nodeValue3295 x + ((1 : ℝ) * Sparse.eval nodeValue3406 x + ((1 : ℝ) * Sparse.eval nodeValue3415 x + ((1 : ℝ) * Sparse.eval nodeValue3417 x + ((1 : ℝ) * Sparse.eval nodeValue3452 x + ((1 : ℝ) * Sparse.eval nodeValue3453 x + ((1 : ℝ) * Sparse.eval nodeValue3459 x + ((1 : ℝ) * Sparse.eval nodeValue3462 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3470 x + ((1 : ℝ) * Sparse.eval nodeValue3475 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1827 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2321 x + ((1 : ℝ) * Sparse.eval nodeValue2325 x + ((1 : ℝ) * Sparse.eval nodeValue2327 x + ((1 : ℝ) * Sparse.eval nodeValue2341 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1828 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4530 x + ((2 : ℝ) * Sparse.eval nodeValue4535 x + ((1 : ℝ) * Sparse.eval nodeValue4554 x + ((1 : ℝ) * Sparse.eval nodeValue4593 x + ((2 : ℝ) * Sparse.eval nodeValue4930 x + ((1 : ℝ) * Sparse.eval nodeValue4932 x + ((2 : ℝ) * Sparse.eval nodeValue4935 x + ((2 : ℝ) * Sparse.eval nodeValue4944 x + ((1 : ℝ) * Sparse.eval nodeValue4950 x + ((1 : ℝ) * Sparse.eval nodeValue5039 x + ((1 : ℝ) * Sparse.eval nodeValue5043 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((2 : ℝ) * Sparse.eval nodeValue5104 x + ((1 : ℝ) * Sparse.eval nodeValue5130 x + ((1 : ℝ) * Sparse.eval nodeValue5189 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + 0))))))))))))))))))))

noncomputable def reducedSource1829 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3261 x + ((2 : ℝ) * Sparse.eval nodeValue3272 x + ((1 : ℝ) * Sparse.eval nodeValue3274 x + ((1 : ℝ) * Sparse.eval nodeValue3297 x + ((2 : ℝ) * Sparse.eval nodeValue3408 x + ((1 : ℝ) * Sparse.eval nodeValue3409 x + ((2 : ℝ) * Sparse.eval nodeValue3413 x + ((2 : ℝ) * Sparse.eval nodeValue3419 x + ((1 : ℝ) * Sparse.eval nodeValue3421 x + ((1 : ℝ) * Sparse.eval nodeValue3456 x + ((1 : ℝ) * Sparse.eval nodeValue3465 x + ((2 : ℝ) * Sparse.eval nodeValue3467 x + ((2 : ℝ) * Sparse.eval nodeValue3481 x + ((2 : ℝ) * Sparse.eval nodeValue3483 x + ((1 : ℝ) * Sparse.eval nodeValue3520 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3773 x + ((1 : ℝ) * Sparse.eval nodeValue3797 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + 0))))))))))))))))))))

noncomputable def reducedSource1830 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2322 x + ((2 : ℝ) * Sparse.eval nodeValue2326 x + ((1 : ℝ) * Sparse.eval nodeValue2342 x + ((1 : ℝ) * Sparse.eval nodeValue2489 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1831 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4548 x + ((1 : ℝ) * Sparse.eval nodeValue4557 x + ((1 : ℝ) * Sparse.eval nodeValue4560 x + ((1 : ℝ) * Sparse.eval nodeValue4611 x + ((2 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4692 x + ((2 : ℝ) * Sparse.eval nodeValue4699 x + ((1 : ℝ) * Sparse.eval nodeValue4705 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4881 x + ((2 : ℝ) * Sparse.eval nodeValue4945 x + ((2 : ℝ) * Sparse.eval nodeValue5035 x + ((2 : ℝ) * Sparse.eval nodeValue5099 x + ((2 : ℝ) * Sparse.eval nodeValue5103 x + ((2 : ℝ) * Sparse.eval nodeValue5140 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + 0))))))))))))))))))))

noncomputable def reducedSource1832 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2151 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((1 : ℝ) * Sparse.eval nodeValue2168 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((2 : ℝ) * Sparse.eval nodeValue2256 x + ((1 : ℝ) * Sparse.eval nodeValue2258 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((1 : ℝ) * Sparse.eval nodeValue2286 x + ((2 : ℝ) * Sparse.eval nodeValue2652 x + ((2 : ℝ) * Sparse.eval nodeValue2657 x + ((2 : ℝ) * Sparse.eval nodeValue2658 x + ((2 : ℝ) * Sparse.eval nodeValue2670 x + ((2 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((2 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + 0))))))))))))))))))))

noncomputable def reducedSource1833 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4092 x + ((2 : ℝ) * Sparse.eval nodeValue4549 x + ((1 : ℝ) * Sparse.eval nodeValue4558 x + ((1 : ℝ) * Sparse.eval nodeValue4559 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((2 : ℝ) * Sparse.eval nodeValue4943 x + ((2 : ℝ) * Sparse.eval nodeValue4946 x + ((1 : ℝ) * Sparse.eval nodeValue4952 x + ((1 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4972 x + ((2 : ℝ) * Sparse.eval nodeValue5036 x + ((2 : ℝ) * Sparse.eval nodeValue5101 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5107 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5371 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + 0))))))))))))))))))))

noncomputable def reducedSource1834 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3265 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((2 : ℝ) * Sparse.eval nodeValue3411 x + ((2 : ℝ) * Sparse.eval nodeValue3412 x + ((1 : ℝ) * Sparse.eval nodeValue3422 x + ((1 : ℝ) * Sparse.eval nodeValue3423 x + ((2 : ℝ) * Sparse.eval nodeValue3450 x + ((2 : ℝ) * Sparse.eval nodeValue3457 x + ((2 : ℝ) * Sparse.eval nodeValue3470 x + ((2 : ℝ) * Sparse.eval nodeValue3471 x + ((1 : ℝ) * Sparse.eval nodeValue3484 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((2 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((2 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3775 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))))))))))))))))

noncomputable def reducedSource1835 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4088 x + ((1 : ℝ) * Sparse.eval nodeValue4522 x + ((2 : ℝ) * Sparse.eval nodeValue4526 x + ((1 : ℝ) * Sparse.eval nodeValue4539 x + ((1 : ℝ) * Sparse.eval nodeValue4586 x + ((2 : ℝ) * Sparse.eval nodeValue4902 x + ((2 : ℝ) * Sparse.eval nodeValue4907 x + ((2 : ℝ) * Sparse.eval nodeValue4918 x + ((1 : ℝ) * Sparse.eval nodeValue4926 x + ((1 : ℝ) * Sparse.eval nodeValue4937 x + ((2 : ℝ) * Sparse.eval nodeValue5000 x + ((1 : ℝ) * Sparse.eval nodeValue5025 x + ((1 : ℝ) * Sparse.eval nodeValue5032 x + ((2 : ℝ) * Sparse.eval nodeValue5056 x + ((1 : ℝ) * Sparse.eval nodeValue5063 x + ((2 : ℝ) * Sparse.eval nodeValue5095 x + ((1 : ℝ) * Sparse.eval nodeValue5126 x + ((2 : ℝ) * Sparse.eval nodeValue5248 x + ((1 : ℝ) * Sparse.eval nodeValue5323 x + ((1 : ℝ) * Sparse.eval nodeValue5327 x + ((2 : ℝ) * Sparse.eval nodeValue5367 x + 0))))))))))))))))))))

noncomputable def reducedSource1836 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2379 x + ((1 : ℝ) * Sparse.eval nodeValue3646 x + ((2 : ℝ) * Sparse.eval nodeValue3718 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((1 : ℝ) * Sparse.eval nodeValue3759 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

noncomputable def reducedSource1837 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2388 x + ((1 : ℝ) * Sparse.eval nodeValue3654 x + ((1 : ℝ) * Sparse.eval nodeValue3681 x + ((1 : ℝ) * Sparse.eval nodeValue3702 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3767 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

noncomputable def reducedSource1838 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4089 x + ((2 : ℝ) * Sparse.eval nodeValue4515 x + ((2 : ℝ) * Sparse.eval nodeValue4520 x + ((1 : ℝ) * Sparse.eval nodeValue4575 x + ((4 : ℝ) * Sparse.eval nodeValue4913 x + ((2 : ℝ) * Sparse.eval nodeValue4915 x + ((2 : ℝ) * Sparse.eval nodeValue4924 x + ((2 : ℝ) * Sparse.eval nodeValue4985 x + ((4 : ℝ) * Sparse.eval nodeValue5015 x + ((2 : ℝ) * Sparse.eval nodeValue5021 x + ((2 : ℝ) * Sparse.eval nodeValue5125 x + ((2 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5327 x + ((2 : ℝ) * Sparse.eval nodeValue5371 x + 0)))))))))))))

noncomputable def reducedSource1839 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4368 x + ((1 : ℝ) * Sparse.eval nodeValue4373 x + ((1 : ℝ) * Sparse.eval nodeValue4375 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((2 : ℝ) * Sparse.eval nodeValue4687 x + ((1 : ℝ) * Sparse.eval nodeValue4694 x + ((2 : ℝ) * Sparse.eval nodeValue4700 x + ((1 : ℝ) * Sparse.eval nodeValue4704 x + ((2 : ℝ) * Sparse.eval nodeValue4773 x + ((2 : ℝ) * Sparse.eval nodeValue4776 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((2 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4872 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5297 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1840 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1321 x + ((1 : ℝ) * Sparse.eval nodeValue1323 x + ((1 : ℝ) * Sparse.eval nodeValue1325 x + ((1 : ℝ) * Sparse.eval nodeValue1419 x + ((2 : ℝ) * Sparse.eval nodeValue1813 x + ((1 : ℝ) * Sparse.eval nodeValue1820 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((2 : ℝ) * Sparse.eval nodeValue2816 x + ((1 : ℝ) * Sparse.eval nodeValue2821 x + ((1 : ℝ) * Sparse.eval nodeValue2966 x + ((2 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((2 : ℝ) * Sparse.eval nodeValue3131 x + ((2 : ℝ) * Sparse.eval nodeValue3163 x + ((2 : ℝ) * Sparse.eval nodeValue3180 x + ((2 : ℝ) * Sparse.eval nodeValue3185 x + ((2 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

noncomputable def reducedSource1841 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1712 x + ((1 : ℝ) * Sparse.eval nodeValue1735 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1743 x + ((2 : ℝ) * Sparse.eval nodeValue2162 x + ((1 : ℝ) * Sparse.eval nodeValue2163 x + ((2 : ℝ) * Sparse.eval nodeValue2194 x + ((2 : ℝ) * Sparse.eval nodeValue2212 x + ((2 : ℝ) * Sparse.eval nodeValue2215 x + ((2 : ℝ) * Sparse.eval nodeValue2242 x + ((2 : ℝ) * Sparse.eval nodeValue2249 x + ((2 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2273 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2282 x + ((2 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2771 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + 0))))))))))))))))))))

noncomputable def reducedSource1842 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1826 x + ((1 : ℝ) * Sparse.eval nodeValue1830 x + ((1 : ℝ) * Sparse.eval nodeValue1832 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1843 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue946 x + ((1 : ℝ) * Sparse.eval nodeValue1826 x + ((1 : ℝ) * Sparse.eval nodeValue1974 x + ((1 : ℝ) * Sparse.eval nodeValue2106 x + ((1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1844 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4238 x + ((1 : ℝ) * Sparse.eval nodeValue4241 x + ((1 : ℝ) * Sparse.eval nodeValue4243 x + ((1 : ℝ) * Sparse.eval nodeValue4278 x + ((2 : ℝ) * Sparse.eval nodeValue4673 x + ((2 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4691 x + ((1 : ℝ) * Sparse.eval nodeValue4693 x + ((2 : ℝ) * Sparse.eval nodeValue4724 x + ((2 : ℝ) * Sparse.eval nodeValue4727 x + ((2 : ℝ) * Sparse.eval nodeValue4749 x + ((2 : ℝ) * Sparse.eval nodeValue4860 x + ((1 : ℝ) * Sparse.eval nodeValue4862 x + ((2 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5389 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + 0))))))))))))))))))))

noncomputable def reducedSource1845 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue738 x + ((1 : ℝ) * Sparse.eval nodeValue741 x + ((1 : ℝ) * Sparse.eval nodeValue743 x + ((1 : ℝ) * Sparse.eval nodeValue830 x + ((2 : ℝ) * Sparse.eval nodeValue1799 x + ((2 : ℝ) * Sparse.eval nodeValue1814 x + ((1 : ℝ) * Sparse.eval nodeValue1817 x + ((1 : ℝ) * Sparse.eval nodeValue1819 x + ((2 : ℝ) * Sparse.eval nodeValue1878 x + ((2 : ℝ) * Sparse.eval nodeValue1881 x + ((2 : ℝ) * Sparse.eval nodeValue1928 x + ((2 : ℝ) * Sparse.eval nodeValue2101 x + ((1 : ℝ) * Sparse.eval nodeValue2103 x + ((2 : ℝ) * Sparse.eval nodeValue2110 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((2 : ℝ) * Sparse.eval nodeValue3732 x + ((1 : ℝ) * Sparse.eval nodeValue3740 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

noncomputable def reducedSource1846 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1640 x + ((1 : ℝ) * Sparse.eval nodeValue1652 x + ((1 : ℝ) * Sparse.eval nodeValue1653 x + ((1 : ℝ) * Sparse.eval nodeValue1660 x + ((2 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((1 : ℝ) * Sparse.eval nodeValue2066 x + ((2 : ℝ) * Sparse.eval nodeValue2072 x + ((2 : ℝ) * Sparse.eval nodeValue2081 x + ((2 : ℝ) * Sparse.eval nodeValue2082 x + ((2 : ℝ) * Sparse.eval nodeValue2093 x + ((2 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2114 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((2 : ℝ) * Sparse.eval nodeValue2122 x + ((1 : ℝ) * Sparse.eval nodeValue2137 x + ((1 : ℝ) * Sparse.eval nodeValue2138 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((2 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((1 : ℝ) * Sparse.eval nodeValue2644 x + 0))))))))))))))))))))

noncomputable def reducedSource1847 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1371 x + ((1 : ℝ) * Sparse.eval nodeValue1373 x + ((1 : ℝ) * Sparse.eval nodeValue1374 x + ((1 : ℝ) * Sparse.eval nodeValue1444 x + ((2 : ℝ) * Sparse.eval nodeValue2867 x + ((2 : ℝ) * Sparse.eval nodeValue2872 x + ((1 : ℝ) * Sparse.eval nodeValue2887 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((1 : ℝ) * Sparse.eval nodeValue2968 x + ((1 : ℝ) * Sparse.eval nodeValue3095 x + ((2 : ℝ) * Sparse.eval nodeValue3151 x + ((2 : ℝ) * Sparse.eval nodeValue3159 x + ((1 : ℝ) * Sparse.eval nodeValue3160 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((2 : ℝ) * Sparse.eval nodeValue3168 x + ((2 : ℝ) * Sparse.eval nodeValue3174 x + ((2 : ℝ) * Sparse.eval nodeValue3178 x + ((1 : ℝ) * Sparse.eval nodeValue3188 x + ((2 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3216 x + 0))))))))))))))))))))

noncomputable def reducedSource1848 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4369 x + ((2 : ℝ) * Sparse.eval nodeValue4374 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((2 : ℝ) * Sparse.eval nodeValue4701 x + ((2 : ℝ) * Sparse.eval nodeValue4705 x + ((2 : ℝ) * Sparse.eval nodeValue4774 x + ((4 : ℝ) * Sparse.eval nodeValue4777 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((4 : ℝ) * Sparse.eval nodeValue4866 x + ((2 : ℝ) * Sparse.eval nodeValue4871 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue5269 x + ((1 : ℝ) * Sparse.eval nodeValue5303 x + ((2 : ℝ) * Sparse.eval nodeValue5304 x + 0)))))))))))))

noncomputable def reducedSource1849 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1322 x + ((2 : ℝ) * Sparse.eval nodeValue1324 x + ((1 : ℝ) * Sparse.eval nodeValue1420 x + ((4 : ℝ) * Sparse.eval nodeValue2340 x + ((2 : ℝ) * Sparse.eval nodeValue2346 x + ((2 : ℝ) * Sparse.eval nodeValue2602 x + ((2 : ℝ) * Sparse.eval nodeValue3108 x + ((1 : ℝ) * Sparse.eval nodeValue3118 x + ((2 : ℝ) * Sparse.eval nodeValue3119 x + ((2 : ℝ) * Sparse.eval nodeValue3132 x + ((2 : ℝ) * Sparse.eval nodeValue3164 x + ((4 : ℝ) * Sparse.eval nodeValue3184 x + ((2 : ℝ) * Sparse.eval nodeValue3207 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0)))))))))))))

noncomputable def reducedSource1850 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1721 x + ((2 : ℝ) * Sparse.eval nodeValue1748 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((2 : ℝ) * Sparse.eval nodeValue2199 x + ((4 : ℝ) * Sparse.eval nodeValue2223 x + ((2 : ℝ) * Sparse.eval nodeValue2225 x + ((2 : ℝ) * Sparse.eval nodeValue2257 x + ((4 : ℝ) * Sparse.eval nodeValue2260 x + ((2 : ℝ) * Sparse.eval nodeValue2286 x + ((2 : ℝ) * Sparse.eval nodeValue2287 x + ((2 : ℝ) * Sparse.eval nodeValue2291 x + ((2 : ℝ) * Sparse.eval nodeValue2736 x + ((1 : ℝ) * Sparse.eval nodeValue2779 x + ((2 : ℝ) * Sparse.eval nodeValue2782 x + 0)))))))))))))

noncomputable def reducedSource1851 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1827 x + ((2 : ℝ) * Sparse.eval nodeValue1831 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((1 : ℝ) * Sparse.eval nodeValue3118 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource1852 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue947 x + ((1 : ℝ) * Sparse.eval nodeValue1827 x + ((1 : ℝ) * Sparse.eval nodeValue1975 x + ((2 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1853 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4239 x + ((2 : ℝ) * Sparse.eval nodeValue4242 x + ((1 : ℝ) * Sparse.eval nodeValue4279 x + ((2 : ℝ) * Sparse.eval nodeValue4689 x + ((2 : ℝ) * Sparse.eval nodeValue4692 x + ((2 : ℝ) * Sparse.eval nodeValue4725 x + ((4 : ℝ) * Sparse.eval nodeValue4726 x + ((2 : ℝ) * Sparse.eval nodeValue4750 x + ((4 : ℝ) * Sparse.eval nodeValue4866 x + ((2 : ℝ) * Sparse.eval nodeValue4868 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue5390 x + ((2 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + 0)))))))))))))

noncomputable def reducedSource1854 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue739 x + ((2 : ℝ) * Sparse.eval nodeValue742 x + ((1 : ℝ) * Sparse.eval nodeValue831 x + ((2 : ℝ) * Sparse.eval nodeValue1815 x + ((2 : ℝ) * Sparse.eval nodeValue1818 x + ((2 : ℝ) * Sparse.eval nodeValue1879 x + ((4 : ℝ) * Sparse.eval nodeValue1880 x + ((2 : ℝ) * Sparse.eval nodeValue1929 x + ((4 : ℝ) * Sparse.eval nodeValue2107 x + ((2 : ℝ) * Sparse.eval nodeValue2109 x + ((2 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue3741 x + ((2 : ℝ) * Sparse.eval nodeValue3790 x + ((2 : ℝ) * Sparse.eval nodeValue3888 x + 0)))))))))))))

noncomputable def reducedSource1855 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4487 x + ((2 : ℝ) * Sparse.eval nodeValue4491 x + ((1 : ℝ) * Sparse.eval nodeValue4506 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4825 x + ((4 : ℝ) * Sparse.eval nodeValue4828 x + ((2 : ℝ) * Sparse.eval nodeValue4842 x + ((2 : ℝ) * Sparse.eval nodeValue4846 x + ((4 : ℝ) * Sparse.eval nodeValue4856 x + ((2 : ℝ) * Sparse.eval nodeValue4874 x + ((2 : ℝ) * Sparse.eval nodeValue4884 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5189 x + ((2 : ℝ) * Sparse.eval nodeValue5207 x + 0)))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1856 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1641 x + ((2 : ℝ) * Sparse.eval nodeValue1653 x + ((1 : ℝ) * Sparse.eval nodeValue1661 x + ((2 : ℝ) * Sparse.eval nodeValue2029 x + ((2 : ℝ) * Sparse.eval nodeValue2066 x + ((2 : ℝ) * Sparse.eval nodeValue2073 x + ((4 : ℝ) * Sparse.eval nodeValue2082 x + ((4 : ℝ) * Sparse.eval nodeValue2094 x + ((2 : ℝ) * Sparse.eval nodeValue2115 x + ((2 : ℝ) * Sparse.eval nodeValue2123 x + ((2 : ℝ) * Sparse.eval nodeValue2138 x + ((1 : ℝ) * Sparse.eval nodeValue2605 x + ((2 : ℝ) * Sparse.eval nodeValue2621 x + ((2 : ℝ) * Sparse.eval nodeValue2644 x + 0)))))))))))))

noncomputable def reducedSource1857 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1876 x + ((1 : ℝ) * Sparse.eval nodeValue1880 x + ((1 : ℝ) * Sparse.eval nodeValue1881 x + ((1 : ℝ) * Sparse.eval nodeValue1918 x + ((1 : ℝ) * Sparse.eval nodeValue2082 x + ((1 : ℝ) * Sparse.eval nodeValue3448 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1858 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4328 x + ((1 : ℝ) * Sparse.eval nodeValue4334 x + ((1 : ℝ) * Sparse.eval nodeValue4336 x + ((1 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4665 x + ((1 : ℝ) * Sparse.eval nodeValue4667 x + ((1 : ℝ) * Sparse.eval nodeValue4669 x + ((1 : ℝ) * Sparse.eval nodeValue4671 x + ((1 : ℝ) * Sparse.eval nodeValue4687 x + ((1 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4756 x + ((1 : ℝ) * Sparse.eval nodeValue4766 x + ((1 : ℝ) * Sparse.eval nodeValue4773 x + ((1 : ℝ) * Sparse.eval nodeValue4776 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((1 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4808 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((1 : ℝ) * Sparse.eval nodeValue5243 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1859 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1330 x + ((1 : ℝ) * Sparse.eval nodeValue1332 x + ((1 : ℝ) * Sparse.eval nodeValue1334 x + ((1 : ℝ) * Sparse.eval nodeValue1343 x + ((1 : ℝ) * Sparse.eval nodeValue1419 x + ((1 : ℝ) * Sparse.eval nodeValue1793 x + ((1 : ℝ) * Sparse.eval nodeValue1797 x + ((1 : ℝ) * Sparse.eval nodeValue1813 x + ((1 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2800 x + ((1 : ℝ) * Sparse.eval nodeValue2803 x + ((1 : ℝ) * Sparse.eval nodeValue2816 x + ((1 : ℝ) * Sparse.eval nodeValue2941 x + ((1 : ℝ) * Sparse.eval nodeValue3030 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3045 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3134 x + ((1 : ℝ) * Sparse.eval nodeValue3141 x + ((1 : ℝ) * Sparse.eval nodeValue3163 x + ((1 : ℝ) * Sparse.eval nodeValue3187 x + ((1 : ℝ) * Sparse.eval nodeValue3190 x + ((1 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3205 x + ((1 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3210 x + ((1 : ℝ) * Sparse.eval nodeValue3214 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1860 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1667 x + ((1 : ℝ) * Sparse.eval nodeValue1679 x + ((1 : ℝ) * Sparse.eval nodeValue1681 x + ((1 : ℝ) * Sparse.eval nodeValue1685 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue2144 x + ((1 : ℝ) * Sparse.eval nodeValue2155 x + ((1 : ℝ) * Sparse.eval nodeValue2157 x + ((1 : ℝ) * Sparse.eval nodeValue2160 x + ((1 : ℝ) * Sparse.eval nodeValue2161 x + ((1 : ℝ) * Sparse.eval nodeValue2162 x + ((1 : ℝ) * Sparse.eval nodeValue2176 x + ((1 : ℝ) * Sparse.eval nodeValue2177 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2194 x + ((1 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2212 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1861 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1791 x + ((1 : ℝ) * Sparse.eval nodeValue1795 x + ((1 : ℝ) * Sparse.eval nodeValue1797 x + ((1 : ℝ) * Sparse.eval nodeValue1814 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1862 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue932 x + ((1 : ℝ) * Sparse.eval nodeValue1814 x + ((1 : ℝ) * Sparse.eval nodeValue1966 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue2053 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1863 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue906 x + ((1 : ℝ) * Sparse.eval nodeValue1791 x + ((1 : ℝ) * Sparse.eval nodeValue1974 x + ((1 : ℝ) * Sparse.eval nodeValue2019 x + ((1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1864 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4200 x + ((1 : ℝ) * Sparse.eval nodeValue4203 x + ((1 : ℝ) * Sparse.eval nodeValue4205 x + ((1 : ℝ) * Sparse.eval nodeValue4223 x + ((1 : ℝ) * Sparse.eval nodeValue4255 x + ((1 : ℝ) * Sparse.eval nodeValue4634 x + ((1 : ℝ) * Sparse.eval nodeValue4636 x + ((1 : ℝ) * Sparse.eval nodeValue4638 x + ((1 : ℝ) * Sparse.eval nodeValue4653 x + ((1 : ℝ) * Sparse.eval nodeValue4658 x + ((1 : ℝ) * Sparse.eval nodeValue4678 x + ((1 : ℝ) * Sparse.eval nodeValue4707 x + ((1 : ℝ) * Sparse.eval nodeValue4716 x + ((1 : ℝ) * Sparse.eval nodeValue4731 x + ((1 : ℝ) * Sparse.eval nodeValue4766 x + ((1 : ℝ) * Sparse.eval nodeValue4770 x + ((1 : ℝ) * Sparse.eval nodeValue4798 x + ((1 : ℝ) * Sparse.eval nodeValue4800 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4828 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1865 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4329 x + ((2 : ℝ) * Sparse.eval nodeValue4335 x + ((1 : ℝ) * Sparse.eval nodeValue4355 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4666 x + ((2 : ℝ) * Sparse.eval nodeValue4670 x + ((1 : ℝ) * Sparse.eval nodeValue4689 x + ((2 : ℝ) * Sparse.eval nodeValue4757 x + ((1 : ℝ) * Sparse.eval nodeValue4767 x + ((1 : ℝ) * Sparse.eval nodeValue4774 x + ((2 : ℝ) * Sparse.eval nodeValue4777 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5236 x + ((1 : ℝ) * Sparse.eval nodeValue5246 x + ((1 : ℝ) * Sparse.eval nodeValue5269 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + 0))))))))))))))))))))

noncomputable def reducedSource1866 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1331 x + ((2 : ℝ) * Sparse.eval nodeValue1333 x + ((1 : ℝ) * Sparse.eval nodeValue1344 x + ((1 : ℝ) * Sparse.eval nodeValue1420 x + ((2 : ℝ) * Sparse.eval nodeValue2323 x + ((2 : ℝ) * Sparse.eval nodeValue2327 x + ((2 : ℝ) * Sparse.eval nodeValue2340 x + ((2 : ℝ) * Sparse.eval nodeValue2574 x + ((1 : ℝ) * Sparse.eval nodeValue3104 x + ((1 : ℝ) * Sparse.eval nodeValue3108 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3115 x + ((1 : ℝ) * Sparse.eval nodeValue3135 x + ((1 : ℝ) * Sparse.eval nodeValue3142 x + ((1 : ℝ) * Sparse.eval nodeValue3164 x + ((1 : ℝ) * Sparse.eval nodeValue3188 x + ((1 : ℝ) * Sparse.eval nodeValue3191 x + ((2 : ℝ) * Sparse.eval nodeValue3204 x + ((1 : ℝ) * Sparse.eval nodeValue3207 x + ((2 : ℝ) * Sparse.eval nodeValue3213 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0))))))))))))))))))))

noncomputable def reducedSource1867 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1671 x + ((2 : ℝ) * Sparse.eval nodeValue1689 x + ((1 : ℝ) * Sparse.eval nodeValue1691 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((1 : ℝ) * Sparse.eval nodeValue2148 x + ((2 : ℝ) * Sparse.eval nodeValue2164 x + ((1 : ℝ) * Sparse.eval nodeValue2166 x + ((2 : ℝ) * Sparse.eval nodeValue2181 x + ((1 : ℝ) * Sparse.eval nodeValue2183 x + ((1 : ℝ) * Sparse.eval nodeValue2199 x + ((2 : ℝ) * Sparse.eval nodeValue2202 x + ((2 : ℝ) * Sparse.eval nodeValue2223 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((2 : ℝ) * Sparse.eval nodeValue2227 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((2 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue2682 x + ((1 : ℝ) * Sparse.eval nodeValue2701 x + ((1 : ℝ) * Sparse.eval nodeValue2736 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + 0))))))))))))))))))))

noncomputable def reducedSource1868 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1792 x + ((2 : ℝ) * Sparse.eval nodeValue1796 x + ((1 : ℝ) * Sparse.eval nodeValue1815 x + ((1 : ℝ) * Sparse.eval nodeValue2029 x + ((1 : ℝ) * Sparse.eval nodeValue3380 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1869 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue933 x + ((1 : ℝ) * Sparse.eval nodeValue1815 x + ((1 : ℝ) * Sparse.eval nodeValue1967 x + ((1 : ℝ) * Sparse.eval nodeValue2029 x + ((2 : ℝ) * Sparse.eval nodeValue2057 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1870 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue907 x + ((1 : ℝ) * Sparse.eval nodeValue1792 x + ((1 : ℝ) * Sparse.eval nodeValue1975 x + ((2 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue2029 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1871 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4201 x + ((2 : ℝ) * Sparse.eval nodeValue4204 x + ((1 : ℝ) * Sparse.eval nodeValue4224 x + ((1 : ℝ) * Sparse.eval nodeValue4256 x + ((1 : ℝ) * Sparse.eval nodeValue4635 x + ((2 : ℝ) * Sparse.eval nodeValue4637 x + ((1 : ℝ) * Sparse.eval nodeValue4654 x + ((2 : ℝ) * Sparse.eval nodeValue4706 x + ((1 : ℝ) * Sparse.eval nodeValue4717 x + ((1 : ℝ) * Sparse.eval nodeValue4732 x + ((1 : ℝ) * Sparse.eval nodeValue4767 x + ((2 : ℝ) * Sparse.eval nodeValue4769 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1872 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4415 x + ((2 : ℝ) * Sparse.eval nodeValue4419 x + ((1 : ℝ) * Sparse.eval nodeValue4427 x + ((1 : ℝ) * Sparse.eval nodeValue4487 x + ((1 : ℝ) * Sparse.eval nodeValue4732 x + ((2 : ℝ) * Sparse.eval nodeValue4745 x + ((1 : ℝ) * Sparse.eval nodeValue4750 x + ((2 : ℝ) * Sparse.eval nodeValue4782 x + ((1 : ℝ) * Sparse.eval nodeValue4785 x + ((2 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4821 x + ((1 : ℝ) * Sparse.eval nodeValue4825 x + ((2 : ℝ) * Sparse.eval nodeValue4846 x + ((2 : ℝ) * Sparse.eval nodeValue4856 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5130 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + 0))))))))))))))))))))

noncomputable def reducedSource1873 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4348 x + ((1 : ℝ) * Sparse.eval nodeValue4359 x + ((1 : ℝ) * Sparse.eval nodeValue4362 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((2 : ℝ) * Sparse.eval nodeValue4678 x + ((2 : ℝ) * Sparse.eval nodeValue4683 x + ((1 : ℝ) * Sparse.eval nodeValue4691 x + ((1 : ℝ) * Sparse.eval nodeValue4694 x + ((2 : ℝ) * Sparse.eval nodeValue4702 x + ((2 : ℝ) * Sparse.eval nodeValue4762 x + ((2 : ℝ) * Sparse.eval nodeValue4832 x + ((2 : ℝ) * Sparse.eval nodeValue4836 x + ((1 : ℝ) * Sparse.eval nodeValue4837 x + ((1 : ℝ) * Sparse.eval nodeValue4844 x + ((2 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((2 : ℝ) * Sparse.eval nodeValue5222 x + ((1 : ℝ) * Sparse.eval nodeValue5235 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5268 x + 0))))))))))))))))))))

noncomputable def reducedSource1874 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1347 x + ((1 : ℝ) * Sparse.eval nodeValue1348 x + ((1 : ℝ) * Sparse.eval nodeValue1349 x + ((1 : ℝ) * Sparse.eval nodeValue1454 x + ((2 : ℝ) * Sparse.eval nodeValue1828 x + ((1 : ℝ) * Sparse.eval nodeValue1832 x + ((1 : ℝ) * Sparse.eval nodeValue2136 x + ((2 : ℝ) * Sparse.eval nodeValue2716 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((2 : ℝ) * Sparse.eval nodeValue3031 x + ((2 : ℝ) * Sparse.eval nodeValue3033 x + ((1 : ℝ) * Sparse.eval nodeValue3046 x + ((2 : ℝ) * Sparse.eval nodeValue3062 x + ((2 : ℝ) * Sparse.eval nodeValue3082 x + ((1 : ℝ) * Sparse.eval nodeValue3090 x + ((2 : ℝ) * Sparse.eval nodeValue3095 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((2 : ℝ) * Sparse.eval nodeValue3143 x + ((1 : ℝ) * Sparse.eval nodeValue3145 x + ((1 : ℝ) * Sparse.eval nodeValue3215 x + 0))))))))))))))))))))

noncomputable def reducedSource1875 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1669 x + ((1 : ℝ) * Sparse.eval nodeValue1683 x + ((1 : ℝ) * Sparse.eval nodeValue1687 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((2 : ℝ) * Sparse.eval nodeValue2143 x + ((2 : ℝ) * Sparse.eval nodeValue2146 x + ((1 : ℝ) * Sparse.eval nodeValue2159 x + ((1 : ℝ) * Sparse.eval nodeValue2163 x + ((2 : ℝ) * Sparse.eval nodeValue2171 x + ((2 : ℝ) * Sparse.eval nodeValue2180 x + ((2 : ℝ) * Sparse.eval nodeValue2193 x + ((2 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue2208 x + ((2 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2222 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((2 : ℝ) * Sparse.eval nodeValue2664 x + ((1 : ℝ) * Sparse.eval nodeValue2680 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + 0))))))))))))))))))))

noncomputable def reducedSource1876 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1809 x + ((1 : ℝ) * Sparse.eval nodeValue1817 x + ((1 : ℝ) * Sparse.eval nodeValue1820 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((1 : ℝ) * Sparse.eval nodeValue3396 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

noncomputable def reducedSource1877 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4349 x + ((1 : ℝ) * Sparse.eval nodeValue4360 x + ((1 : ℝ) * Sparse.eval nodeValue4361 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((2 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4692 x + ((1 : ℝ) * Sparse.eval nodeValue4693 x + ((2 : ℝ) * Sparse.eval nodeValue4763 x + ((2 : ℝ) * Sparse.eval nodeValue4769 x + ((2 : ℝ) * Sparse.eval nodeValue4770 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((2 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5248 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + 0))))))))))))))))))))

noncomputable def reducedSource1878 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1675 x + ((1 : ℝ) * Sparse.eval nodeValue1693 x + ((1 : ℝ) * Sparse.eval nodeValue1694 x + ((1 : ℝ) * Sparse.eval nodeValue1755 x + ((2 : ℝ) * Sparse.eval nodeValue2152 x + ((1 : ℝ) * Sparse.eval nodeValue2168 x + ((1 : ℝ) * Sparse.eval nodeValue2169 x + ((2 : ℝ) * Sparse.eval nodeValue2174 x + ((2 : ℝ) * Sparse.eval nodeValue2185 x + ((2 : ℝ) * Sparse.eval nodeValue2186 x + ((2 : ℝ) * Sparse.eval nodeValue2205 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((2 : ℝ) * Sparse.eval nodeValue2229 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((2 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))))))))))))))))

noncomputable def reducedSource1879 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1810 x + ((1 : ℝ) * Sparse.eval nodeValue1818 x + ((1 : ℝ) * Sparse.eval nodeValue1819 x + ((1 : ℝ) * Sparse.eval nodeValue2066 x + ((1 : ℝ) * Sparse.eval nodeValue3397 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1880 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4288 x + ((1 : ℝ) * Sparse.eval nodeValue4295 x + ((1 : ℝ) * Sparse.eval nodeValue4296 x + ((1 : ℝ) * Sparse.eval nodeValue4311 x + ((1 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4632 x + ((1 : ℝ) * Sparse.eval nodeValue4637 x + ((1 : ℝ) * Sparse.eval nodeValue4638 x + ((1 : ℝ) * Sparse.eval nodeValue4652 x + ((1 : ℝ) * Sparse.eval nodeValue4706 x + ((1 : ℝ) * Sparse.eval nodeValue4707 x + ((1 : ℝ) * Sparse.eval nodeValue4715 x + ((1 : ℝ) * Sparse.eval nodeValue4722 x + ((1 : ℝ) * Sparse.eval nodeValue4726 x + ((1 : ℝ) * Sparse.eval nodeValue4727 x + ((1 : ℝ) * Sparse.eval nodeValue4736 x + ((1 : ℝ) * Sparse.eval nodeValue4737 x + ((1 : ℝ) * Sparse.eval nodeValue4741 x + ((1 : ℝ) * Sparse.eval nodeValue4742 x + ((1 : ℝ) * Sparse.eval nodeValue4752 x + ((1 : ℝ) * Sparse.eval nodeValue4782 x + ((1 : ℝ) * Sparse.eval nodeValue4828 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue5015 x + ((1 : ℝ) * Sparse.eval nodeValue5056 x + ((1 : ℝ) * Sparse.eval nodeValue5095 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1881 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4082 x + ((1 : ℝ) * Sparse.eval nodeValue4298 x + ((1 : ℝ) * Sparse.eval nodeValue4303 x + ((1 : ℝ) * Sparse.eval nodeValue4305 x + ((1 : ℝ) * Sparse.eval nodeValue4313 x + ((1 : ℝ) * Sparse.eval nodeValue4419 x + ((1 : ℝ) * Sparse.eval nodeValue4640 x + ((1 : ℝ) * Sparse.eval nodeValue4644 x + ((1 : ℝ) * Sparse.eval nodeValue4646 x + ((1 : ℝ) * Sparse.eval nodeValue4653 x + ((1 : ℝ) * Sparse.eval nodeValue4709 x + ((1 : ℝ) * Sparse.eval nodeValue4711 x + ((1 : ℝ) * Sparse.eval nodeValue4716 x + ((1 : ℝ) * Sparse.eval nodeValue4731 x + ((1 : ℝ) * Sparse.eval nodeValue4732 x + ((1 : ℝ) * Sparse.eval nodeValue4744 x + ((2 : ℝ) * Sparse.eval nodeValue4745 x + ((1 : ℝ) * Sparse.eval nodeValue4749 x + ((1 : ℝ) * Sparse.eval nodeValue4750 x + ((1 : ℝ) * Sparse.eval nodeValue4753 x + ((1 : ℝ) * Sparse.eval nodeValue4782 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue5003 x + ((1 : ℝ) * Sparse.eval nodeValue5050 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1882 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4065 x + ((2 : ℝ) * Sparse.eval nodeValue4067 x + ((1 : ℝ) * Sparse.eval nodeValue4071 x + ((4 : ℝ) * Sparse.eval nodeValue4074 x + ((2 : ℝ) * Sparse.eval nodeValue4075 x + ((2 : ℝ) * Sparse.eval nodeValue4076 x + ((2 : ℝ) * Sparse.eval nodeValue4078 x + ((4 : ℝ) * Sparse.eval nodeValue4080 x + ((2 : ℝ) * Sparse.eval nodeValue4081 x + ((2 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4088 x + ((1 : ℝ) * Sparse.eval nodeValue4089 x + ((2 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))))))))))

noncomputable def reducedSource1883 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue923 x + ((1 : ℝ) * Sparse.eval nodeValue1806 x + ((1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2051 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1884 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2440 x + ((1 : ℝ) * Sparse.eval nodeValue3062 x + ((1 : ℝ) * Sparse.eval nodeValue3189 x + ((2 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3789 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1885 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue920 x + ((1 : ℝ) * Sparse.eval nodeValue1803 x + ((1 : ℝ) * Sparse.eval nodeValue2033 x + ((1 : ℝ) * Sparse.eval nodeValue2051 x + ((2 : ℝ) * Sparse.eval nodeValue2054 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1886 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2895 x + ((2 : ℝ) * Sparse.eval nodeValue3164 x + ((1 : ℝ) * Sparse.eval nodeValue3172 x + ((1 : ℝ) * Sparse.eval nodeValue3197 x + ((1 : ℝ) * Sparse.eval nodeValue3964 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1887 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2430 x + ((1 : ℝ) * Sparse.eval nodeValue3162 x + ((1 : ℝ) * Sparse.eval nodeValue3163 x + ((1 : ℝ) * Sparse.eval nodeValue3170 x + ((1 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1888 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2443 x + ((1 : ℝ) * Sparse.eval nodeValue3033 x + ((1 : ℝ) * Sparse.eval nodeValue3136 x + ((1 : ℝ) * Sparse.eval nodeValue3138 x + ((1 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1889 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue942 x + ((1 : ℝ) * Sparse.eval nodeValue1822 x + ((1 : ℝ) * Sparse.eval nodeValue2088 x + ((1 : ℝ) * Sparse.eval nodeValue2105 x + ((2 : ℝ) * Sparse.eval nodeValue2107 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1890 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2890 x + ((2 : ℝ) * Sparse.eval nodeValue3135 x + ((1 : ℝ) * Sparse.eval nodeValue3137 x + ((1 : ℝ) * Sparse.eval nodeValue3172 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1891 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue944 x + ((1 : ℝ) * Sparse.eval nodeValue1824 x + ((2 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2105 x + ((1 : ℝ) * Sparse.eval nodeValue2110 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1892 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2423 x + ((1 : ℝ) * Sparse.eval nodeValue3133 x + ((1 : ℝ) * Sparse.eval nodeValue3134 x + ((1 : ℝ) * Sparse.eval nodeValue3136 x + ((1 : ℝ) * Sparse.eval nodeValue3170 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1893 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2899 x + ((1 : ℝ) * Sparse.eval nodeValue3128 x + ((2 : ℝ) * Sparse.eval nodeValue3132 x + ((1 : ℝ) * Sparse.eval nodeValue3158 x + ((1 : ℝ) * Sparse.eval nodeValue3394 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1894 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2435 x + ((1 : ℝ) * Sparse.eval nodeValue3127 x + ((1 : ℝ) * Sparse.eval nodeValue3129 x + ((1 : ℝ) * Sparse.eval nodeValue3131 x + ((1 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3391 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1895 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1130 x + ((1 : ℝ) * Sparse.eval nodeValue2333 x + ((1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1896 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2437 x + ((1 : ℝ) * Sparse.eval nodeValue2900 x + ((1 : ℝ) * Sparse.eval nodeValue2902 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue3787 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1897 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1127 x + ((1 : ℝ) * Sparse.eval nodeValue2331 x + ((1 : ℝ) * Sparse.eval nodeValue2493 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((2 : ℝ) * Sparse.eval nodeValue2512 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1898 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2847 x + ((2 : ℝ) * Sparse.eval nodeValue2849 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((1 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue3945 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1899 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2426 x + ((1 : ℝ) * Sparse.eval nodeValue2846 x + ((1 : ℝ) * Sparse.eval nodeValue2848 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue3781 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1900 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1960 x + ((2 : ℝ) * Sparse.eval nodeValue2427 x + ((1 : ℝ) * Sparse.eval nodeValue2509 x + ((1 : ℝ) * Sparse.eval nodeValue2552 x + ((1 : ℝ) * Sparse.eval nodeValue3493 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1901 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2426 x + ((1 : ℝ) * Sparse.eval nodeValue2428 x + ((1 : ℝ) * Sparse.eval nodeValue2433 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2554 x + ((1 : ℝ) * Sparse.eval nodeValue3781 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1902 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2430 x + ((1 : ℝ) * Sparse.eval nodeValue2431 x + ((1 : ℝ) * Sparse.eval nodeValue2433 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((1 : ℝ) * Sparse.eval nodeValue2557 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1903 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1335 x + ((1 : ℝ) * Sparse.eval nodeValue2826 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1904 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4550 x + ((1 : ℝ) * Sparse.eval nodeValue4551 x + ((2 : ℝ) * Sparse.eval nodeValue4553 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4967 x + ((1 : ℝ) * Sparse.eval nodeValue4970 x + ((2 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue5113 x + ((2 : ℝ) * Sparse.eval nodeValue5114 x + ((1 : ℝ) * Sparse.eval nodeValue5166 x + ((3 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((2 : ℝ) * Sparse.eval nodeValue5171 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((2 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5415 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5441 x + 0)))))))))))))))))))

noncomputable def reducedSource1905 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1135 x + ((1 : ℝ) * Sparse.eval nodeValue1136 x + ((2 : ℝ) * Sparse.eval nodeValue1138 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + ((1 : ℝ) * Sparse.eval nodeValue2814 x + ((1 : ℝ) * Sparse.eval nodeValue2815 x + ((2 : ℝ) * Sparse.eval nodeValue2817 x + ((1 : ℝ) * Sparse.eval nodeValue2894 x + ((2 : ℝ) * Sparse.eval nodeValue2896 x + ((1 : ℝ) * Sparse.eval nodeValue2953 x + ((2 : ℝ) * Sparse.eval nodeValue2954 x + ((3 : ℝ) * Sparse.eval nodeValue2963 x + ((2 : ℝ) * Sparse.eval nodeValue2965 x + ((2 : ℝ) * Sparse.eval nodeValue2968 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + ((2 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3739 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + ((1 : ℝ) * Sparse.eval nodeValue4031 x + ((2 : ℝ) * Sparse.eval nodeValue4037 x + 0)))))))))))))))))))

noncomputable def reducedSource1906 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4343 x + ((2 : ℝ) * Sparse.eval nodeValue4349 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((1 : ℝ) * Sparse.eval nodeValue4760 x + ((1 : ℝ) * Sparse.eval nodeValue4769 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4939 x + ((2 : ℝ) * Sparse.eval nodeValue4946 x + ((2 : ℝ) * Sparse.eval nodeValue5036 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((2 : ℝ) * Sparse.eval nodeValue5134 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))

noncomputable def reducedSource1907 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue919 x + ((1 : ℝ) * Sparse.eval nodeValue921 x + ((2 : ℝ) * Sparse.eval nodeValue927 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((1 : ℝ) * Sparse.eval nodeValue1960 x + ((1 : ℝ) * Sparse.eval nodeValue1969 x + ((2 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2330 x + ((2 : ℝ) * Sparse.eval nodeValue2337 x + ((2 : ℝ) * Sparse.eval nodeValue2428 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((2 : ℝ) * Sparse.eval nodeValue2553 x + ((2 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2593 x + ((2 : ℝ) * Sparse.eval nodeValue2595 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue3821 x + ((1 : ℝ) * Sparse.eval nodeValue3824 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3999 x + 0))))))))))))))))))))

noncomputable def reducedSource1908 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4544 x + ((1 : ℝ) * Sparse.eval nodeValue4546 x + ((1 : ℝ) * Sparse.eval nodeValue4549 x + ((1 : ℝ) * Sparse.eval nodeValue4554 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue4968 x + ((1 : ℝ) * Sparse.eval nodeValue4972 x + ((1 : ℝ) * Sparse.eval nodeValue4974 x + ((1 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue5037 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5115 x + ((1 : ℝ) * Sparse.eval nodeValue5117 x + ((1 : ℝ) * Sparse.eval nodeValue5148 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((3 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource1909 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1129 x + ((1 : ℝ) * Sparse.eval nodeValue1131 x + ((1 : ℝ) * Sparse.eval nodeValue1134 x + ((1 : ℝ) * Sparse.eval nodeValue1139 x + ((1 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue2429 x + ((1 : ℝ) * Sparse.eval nodeValue2434 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2601 x + ((1 : ℝ) * Sparse.eval nodeValue2809 x + ((1 : ℝ) * Sparse.eval nodeValue2813 x + ((1 : ℝ) * Sparse.eval nodeValue2818 x + ((1 : ℝ) * Sparse.eval nodeValue2893 x + ((1 : ℝ) * Sparse.eval nodeValue2897 x + ((1 : ℝ) * Sparse.eval nodeValue2927 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2958 x + ((1 : ℝ) * Sparse.eval nodeValue2959 x + ((3 : ℝ) * Sparse.eval nodeValue2960 x + ((1 : ℝ) * Sparse.eval nodeValue2969 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3122 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((1 : ℝ) * Sparse.eval nodeValue3737 x + ((1 : ℝ) * Sparse.eval nodeValue3967 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource1910 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4349 x + ((1 : ℝ) * Sparse.eval nodeValue4355 x + ((1 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4941 x + ((1 : ℝ) * Sparse.eval nodeValue4943 x + ((1 : ℝ) * Sparse.eval nodeValue4946 x + ((1 : ℝ) * Sparse.eval nodeValue4950 x + ((1 : ℝ) * Sparse.eval nodeValue5033 x + ((1 : ℝ) * Sparse.eval nodeValue5036 x + ((1 : ℝ) * Sparse.eval nodeValue5039 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5465 x + ((1 : ℝ) * Sparse.eval nodeValue5476 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1911 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue922 x + ((1 : ℝ) * Sparse.eval nodeValue924 x + ((1 : ℝ) * Sparse.eval nodeValue927 x + ((1 : ℝ) * Sparse.eval nodeValue933 x + ((1 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue2332 x + ((1 : ℝ) * Sparse.eval nodeValue2334 x + ((1 : ℝ) * Sparse.eval nodeValue2337 x + ((1 : ℝ) * Sparse.eval nodeValue2342 x + ((1 : ℝ) * Sparse.eval nodeValue2425 x + ((1 : ℝ) * Sparse.eval nodeValue2428 x + ((1 : ℝ) * Sparse.eval nodeValue2432 x + ((1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2593 x + ((1 : ℝ) * Sparse.eval nodeValue2594 x + ((2 : ℝ) * Sparse.eval nodeValue2595 x + ((1 : ℝ) * Sparse.eval nodeValue2598 x + ((1 : ℝ) * Sparse.eval nodeValue2605 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue3931 x + ((1 : ℝ) * Sparse.eval nodeValue3965 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3999 x + ((1 : ℝ) * Sparse.eval nodeValue4000 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1912 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4345 x + ((1 : ℝ) * Sparse.eval nodeValue4347 x + ((1 : ℝ) * Sparse.eval nodeValue4348 x + ((1 : ℝ) * Sparse.eval nodeValue4357 x + ((1 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4942 x + ((1 : ℝ) * Sparse.eval nodeValue4944 x + ((1 : ℝ) * Sparse.eval nodeValue4945 x + ((1 : ℝ) * Sparse.eval nodeValue4951 x + ((1 : ℝ) * Sparse.eval nodeValue5034 x + ((1 : ℝ) * Sparse.eval nodeValue5035 x + ((1 : ℝ) * Sparse.eval nodeValue5040 x + ((1 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5140 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5484 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1913 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1668 x + ((1 : ℝ) * Sparse.eval nodeValue1669 x + ((1 : ℝ) * Sparse.eval nodeValue1676 x + ((1 : ℝ) * Sparse.eval nodeValue1682 x + ((1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue2652 x + ((1 : ℝ) * Sparse.eval nodeValue2658 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue3407 x + ((1 : ℝ) * Sparse.eval nodeValue3413 x + ((1 : ℝ) * Sparse.eval nodeValue3418 x + ((1 : ℝ) * Sparse.eval nodeValue3451 x + ((1 : ℝ) * Sparse.eval nodeValue3454 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1914 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4541 x + ((1 : ℝ) * Sparse.eval nodeValue4543 x + ((2 : ℝ) * Sparse.eval nodeValue4549 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4764 x + ((1 : ℝ) * Sparse.eval nodeValue4770 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4971 x + ((2 : ℝ) * Sparse.eval nodeValue4977 x + ((2 : ℝ) * Sparse.eval nodeValue5117 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5417 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + 0))))))))))))))))))))

noncomputable def reducedSource1915 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1126 x + ((1 : ℝ) * Sparse.eval nodeValue1128 x + ((2 : ℝ) * Sparse.eval nodeValue1134 x + ((1 : ℝ) * Sparse.eval nodeValue1300 x + ((1 : ℝ) * Sparse.eval nodeValue1964 x + ((1 : ℝ) * Sparse.eval nodeValue1970 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2807 x + ((2 : ℝ) * Sparse.eval nodeValue2813 x + ((2 : ℝ) * Sparse.eval nodeValue2893 x + ((2 : ℝ) * Sparse.eval nodeValue2924 x + ((2 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2958 x + ((1 : ℝ) * Sparse.eval nodeValue2959 x + ((2 : ℝ) * Sparse.eval nodeValue2960 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3122 x + ((1 : ℝ) * Sparse.eval nodeValue3736 x + ((1 : ℝ) * Sparse.eval nodeValue3823 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + 0))))))))))))))))))))

noncomputable def reducedSource1916 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4351 x + ((1 : ℝ) * Sparse.eval nodeValue4352 x + ((2 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4947 x + ((1 : ℝ) * Sparse.eval nodeValue4948 x + ((2 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue5037 x + ((2 : ℝ) * Sparse.eval nodeValue5038 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5174 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))

noncomputable def reducedSource1917 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue929 x + ((1 : ℝ) * Sparse.eval nodeValue930 x + ((2 : ℝ) * Sparse.eval nodeValue932 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue2338 x + ((1 : ℝ) * Sparse.eval nodeValue2339 x + ((2 : ℝ) * Sparse.eval nodeValue2341 x + ((1 : ℝ) * Sparse.eval nodeValue2429 x + ((2 : ℝ) * Sparse.eval nodeValue2431 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((1 : ℝ) * Sparse.eval nodeValue2589 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((2 : ℝ) * Sparse.eval nodeValue2599 x + ((2 : ℝ) * Sparse.eval nodeValue2601 x + ((2 : ℝ) * Sparse.eval nodeValue2604 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue3933 x + ((1 : ℝ) * Sparse.eval nodeValue3967 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((2 : ℝ) * Sparse.eval nodeValue4001 x + 0))))))))))))))))))))

noncomputable def reducedSource1918 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5099 x + ((2 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((2 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((2 : ℝ) * Sparse.eval nodeValue5138 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((2 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5205 x + 0))))))))))))))))))))

noncomputable def reducedSource1919 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1156 x + ((1 : ℝ) * Sparse.eval nodeValue2353 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2590 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource192 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2513 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource193 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1238 x + ((1 : ℝ) * Sparse.eval nodeValue2133 x + ((1 : ℝ) * Sparse.eval nodeValue2513 x + ((1 : ℝ) * Sparse.eval nodeValue2555 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource194 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2555 x + ((1 : ℝ) * Sparse.eval nodeValue2559 x + ((1 : ℝ) * Sparse.eval nodeValue2560 x + ((1 : ℝ) * Sparse.eval nodeValue2592 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource195 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1245 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((2 : ℝ) * Sparse.eval nodeValue2560 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource196 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2133 x + ((1 : ℝ) * Sparse.eval nodeValue2136 x + ((1 : ℝ) * Sparse.eval nodeValue2138 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource197 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1244 x + ((1 : ℝ) * Sparse.eval nodeValue2136 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((2 : ℝ) * Sparse.eval nodeValue2559 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource200 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1920 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2895 x + ((1 : ℝ) * Sparse.eval nodeValue2896 x + ((1 : ℝ) * Sparse.eval nodeValue2898 x + ((2 : ℝ) * Sparse.eval nodeValue2928 x + ((1 : ℝ) * Sparse.eval nodeValue3964 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1921 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1158 x + ((1 : ℝ) * Sparse.eval nodeValue2354 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((2 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2589 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1922 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2847 x + ((1 : ℝ) * Sparse.eval nodeValue2893 x + ((1 : ℝ) * Sparse.eval nodeValue2898 x + ((2 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue3945 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1923 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2922 x + ((1 : ℝ) * Sparse.eval nodeValue3748 x + ((1 : ℝ) * Sparse.eval nodeValue3751 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3973 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0))))))

noncomputable def reducedSource1924 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4327 x + ((1 : ℝ) * Sparse.eval nodeValue4328 x + ((1 : ℝ) * Sparse.eval nodeValue4332 x + ((1 : ℝ) * Sparse.eval nodeValue4345 x + ((1 : ℝ) * Sparse.eval nodeValue4439 x + ((1 : ℝ) * Sparse.eval nodeValue4930 x + ((1 : ℝ) * Sparse.eval nodeValue4931 x + ((1 : ℝ) * Sparse.eval nodeValue4933 x + ((1 : ℝ) * Sparse.eval nodeValue4942 x + ((1 : ℝ) * Sparse.eval nodeValue5037 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5114 x + ((1 : ℝ) * Sparse.eval nodeValue5117 x + ((1 : ℝ) * Sparse.eval nodeValue5128 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1925 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue905 x + ((1 : ℝ) * Sparse.eval nodeValue906 x + ((1 : ℝ) * Sparse.eval nodeValue910 x + ((1 : ℝ) * Sparse.eval nodeValue923 x + ((1 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue2320 x + ((1 : ℝ) * Sparse.eval nodeValue2321 x + ((1 : ℝ) * Sparse.eval nodeValue2324 x + ((1 : ℝ) * Sparse.eval nodeValue2333 x + ((1 : ℝ) * Sparse.eval nodeValue2526 x + ((1 : ℝ) * Sparse.eval nodeValue2527 x + ((1 : ℝ) * Sparse.eval nodeValue2530 x + ((1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue2557 x + ((1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2570 x + ((1 : ℝ) * Sparse.eval nodeValue2572 x + ((1 : ℝ) * Sparse.eval nodeValue2576 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2596 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue3925 x + ((1 : ℝ) * Sparse.eval nodeValue3988 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3996 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1926 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1667 x + ((1 : ℝ) * Sparse.eval nodeValue1668 x + ((1 : ℝ) * Sparse.eval nodeValue1670 x + ((1 : ℝ) * Sparse.eval nodeValue1678 x + ((1 : ℝ) * Sparse.eval nodeValue1713 x + ((1 : ℝ) * Sparse.eval nodeValue3406 x + ((1 : ℝ) * Sparse.eval nodeValue3407 x + ((1 : ℝ) * Sparse.eval nodeValue3408 x + ((1 : ℝ) * Sparse.eval nodeValue3414 x + ((1 : ℝ) * Sparse.eval nodeValue3455 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3597 x + ((1 : ℝ) * Sparse.eval nodeValue3599 x + ((1 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3797 x + ((1 : ℝ) * Sparse.eval nodeValue3798 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1927 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2422 x + ((1 : ℝ) * Sparse.eval nodeValue2822 x + ((1 : ℝ) * Sparse.eval nodeValue2824 x + ((1 : ℝ) * Sparse.eval nodeValue2826 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue3779 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1928 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1169 x + ((1 : ℝ) * Sparse.eval nodeValue2361 x + ((3 : ℝ) * Sparse.eval nodeValue2573 x + ((1 : ℝ) * Sparse.eval nodeValue2589 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource1929 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1964 x + ((2 : ℝ) * Sparse.eval nodeValue2892 x + ((2 : ℝ) * Sparse.eval nodeValue2923 x + ((1 : ℝ) * Sparse.eval nodeValue3496 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource1930 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2800 x + ((2 : ℝ) * Sparse.eval nodeValue2801 x + ((1 : ℝ) * Sparse.eval nodeValue2814 x + ((1 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1931 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2797 x + ((1 : ℝ) * Sparse.eval nodeValue2799 x + ((1 : ℝ) * Sparse.eval nodeValue2801 x + ((1 : ℝ) * Sparse.eval nodeValue2809 x + ((1 : ℝ) * Sparse.eval nodeValue2862 x + ((1 : ℝ) * Sparse.eval nodeValue3690 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource1932 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2524 x + ((2 : ℝ) * Sparse.eval nodeValue2798 x + ((1 : ℝ) * Sparse.eval nodeValue2807 x + ((1 : ℝ) * Sparse.eval nodeValue2861 x + ((1 : ℝ) * Sparse.eval nodeValue3689 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource1933 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2031 x + ((1 : ℝ) * Sparse.eval nodeValue2036 x + ((1 : ℝ) * Sparse.eval nodeValue2046 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

noncomputable def reducedSource1934 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2810 x + ((1 : ℝ) * Sparse.eval nodeValue2816 x + ((1 : ℝ) * Sparse.eval nodeValue2817 x + ((1 : ℝ) * Sparse.eval nodeValue2819 x + ((1 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1935 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4364 x + ((1 : ℝ) * Sparse.eval nodeValue4365 x + ((2 : ℝ) * Sparse.eval nodeValue4369 x + ((1 : ℝ) * Sparse.eval nodeValue4474 x + ((1 : ℝ) * Sparse.eval nodeValue4968 x + ((1 : ℝ) * Sparse.eval nodeValue4970 x + ((2 : ℝ) * Sparse.eval nodeValue4974 x + ((1 : ℝ) * Sparse.eval nodeValue5041 x + ((2 : ℝ) * Sparse.eval nodeValue5043 x + ((1 : ℝ) * Sparse.eval nodeValue5085 x + ((2 : ℝ) * Sparse.eval nodeValue5147 x + ((2 : ℝ) * Sparse.eval nodeValue5185 x + ((2 : ℝ) * Sparse.eval nodeValue5189 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((2 : ℝ) * Sparse.eval nodeValue5203 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + 0))))))))))))))))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1936 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1703 x + ((1 : ℝ) * Sparse.eval nodeValue1704 x + ((1 : ℝ) * Sparse.eval nodeValue1709 x + ((2 : ℝ) * Sparse.eval nodeValue1721 x + ((1 : ℝ) * Sparse.eval nodeValue3458 x + ((1 : ℝ) * Sparse.eval nodeValue3461 x + ((2 : ℝ) * Sparse.eval nodeValue3465 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((2 : ℝ) * Sparse.eval nodeValue3530 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((2 : ℝ) * Sparse.eval nodeValue3542 x + ((1 : ℝ) * Sparse.eval nodeValue3587 x + ((1 : ℝ) * Sparse.eval nodeValue3588 x + ((2 : ℝ) * Sparse.eval nodeValue3592 x + ((1 : ℝ) * Sparse.eval nodeValue3617 x + ((1 : ℝ) * Sparse.eval nodeValue3619 x + ((2 : ℝ) * Sparse.eval nodeValue3621 x + ((1 : ℝ) * Sparse.eval nodeValue3774 x + ((1 : ℝ) * Sparse.eval nodeValue3952 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3962 x + 0))))))))))))))))))))

noncomputable def reducedSource1937 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4366 x + ((1 : ℝ) * Sparse.eval nodeValue4367 x + ((1 : ℝ) * Sparse.eval nodeValue4368 x + ((1 : ℝ) * Sparse.eval nodeValue4372 x + ((1 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4971 x + ((1 : ℝ) * Sparse.eval nodeValue4972 x + ((1 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue5034 x + ((1 : ℝ) * Sparse.eval nodeValue5042 x + ((1 : ℝ) * Sparse.eval nodeValue5044 x + ((1 : ℝ) * Sparse.eval nodeValue5086 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5197 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1938 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1711 x + ((1 : ℝ) * Sparse.eval nodeValue1712 x + ((1 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1720 x + ((1 : ℝ) * Sparse.eval nodeValue1734 x + ((1 : ℝ) * Sparse.eval nodeValue3451 x + ((1 : ℝ) * Sparse.eval nodeValue3457 x + ((1 : ℝ) * Sparse.eval nodeValue3462 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3474 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3590 x + ((1 : ℝ) * Sparse.eval nodeValue3591 x + ((1 : ℝ) * Sparse.eval nodeValue3595 x + ((1 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1939 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1970 x + ((1 : ℝ) * Sparse.eval nodeValue2806 x + ((2 : ℝ) * Sparse.eval nodeValue2812 x + ((1 : ℝ) * Sparse.eval nodeValue2879 x + ((1 : ℝ) * Sparse.eval nodeValue3498 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1940 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2607 x + ((1 : ℝ) * Sparse.eval nodeValue3067 x + ((1 : ℝ) * Sparse.eval nodeValue3751 x + ((2 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3867 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0)))))

noncomputable def reducedSource1941 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4545 x + ((1 : ℝ) * Sparse.eval nodeValue4547 x + ((1 : ℝ) * Sparse.eval nodeValue4548 x + ((1 : ℝ) * Sparse.eval nodeValue4556 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4963 x + ((1 : ℝ) * Sparse.eval nodeValue4965 x + ((1 : ℝ) * Sparse.eval nodeValue4966 x + ((1 : ℝ) * Sparse.eval nodeValue4976 x + ((1 : ℝ) * Sparse.eval nodeValue5041 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5112 x + ((1 : ℝ) * Sparse.eval nodeValue5116 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5151 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1942 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2655 x + ((1 : ℝ) * Sparse.eval nodeValue2657 x + ((1 : ℝ) * Sparse.eval nodeValue2659 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue3259 x + ((1 : ℝ) * Sparse.eval nodeValue3266 x + ((1 : ℝ) * Sparse.eval nodeValue3271 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3458 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3475 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3553 x + ((1 : ℝ) * Sparse.eval nodeValue3555 x + ((1 : ℝ) * Sparse.eval nodeValue3556 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1943 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2353 x + ((1 : ℝ) * Sparse.eval nodeValue2355 x + ((1 : ℝ) * Sparse.eval nodeValue2356 x + ((1 : ℝ) * Sparse.eval nodeValue2362 x + ((1 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource1944 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4337 x + ((1 : ℝ) * Sparse.eval nodeValue4338 x + ((1 : ℝ) * Sparse.eval nodeValue4339 x + ((1 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4721 x + ((1 : ℝ) * Sparse.eval nodeValue4726 x + ((1 : ℝ) * Sparse.eval nodeValue4744 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4936 x + ((1 : ℝ) * Sparse.eval nodeValue4937 x + ((1 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue5032 x + ((1 : ℝ) * Sparse.eval nodeValue5038 x + ((1 : ℝ) * Sparse.eval nodeValue5070 x + ((1 : ℝ) * Sparse.eval nodeValue5123 x + ((1 : ℝ) * Sparse.eval nodeValue5125 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1945 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4527 x + ((2 : ℝ) * Sparse.eval nodeValue4530 x + ((1 : ℝ) * Sparse.eval nodeValue4542 x + ((1 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4956 x + ((2 : ℝ) * Sparse.eval nodeValue4958 x + ((1 : ℝ) * Sparse.eval nodeValue4964 x + ((1 : ℝ) * Sparse.eval nodeValue5037 x + ((2 : ℝ) * Sparse.eval nodeValue5039 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((2 : ℝ) * Sparse.eval nodeValue5128 x + ((2 : ℝ) * Sparse.eval nodeValue5130 x + ((2 : ℝ) * Sparse.eval nodeValue5137 x + ((2 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + 0))))))))))))))))))))

noncomputable def reducedSource1946 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3255 x + ((1 : ℝ) * Sparse.eval nodeValue3257 x + ((2 : ℝ) * Sparse.eval nodeValue3261 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3455 x + ((2 : ℝ) * Sparse.eval nodeValue3456 x + ((1 : ℝ) * Sparse.eval nodeValue3483 x + ((1 : ℝ) * Sparse.eval nodeValue3510 x + ((2 : ℝ) * Sparse.eval nodeValue3511 x + ((2 : ℝ) * Sparse.eval nodeValue3519 x + ((2 : ℝ) * Sparse.eval nodeValue3520 x + ((2 : ℝ) * Sparse.eval nodeValue3521 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((1 : ℝ) * Sparse.eval nodeValue3554 x + ((2 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3563 x + ((1 : ℝ) * Sparse.eval nodeValue3798 x + ((1 : ℝ) * Sparse.eval nodeValue3836 x + ((2 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3844 x + 0))))))))))))))))))))

noncomputable def reducedSource1947 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2349 x + ((2 : ℝ) * Sparse.eval nodeValue2351 x + ((1 : ℝ) * Sparse.eval nodeValue2354 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource1948 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4322 x + ((2 : ℝ) * Sparse.eval nodeValue4323 x + ((1 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4399 x + ((1 : ℝ) * Sparse.eval nodeValue4927 x + ((2 : ℝ) * Sparse.eval nodeValue4928 x + ((1 : ℝ) * Sparse.eval nodeValue4941 x + ((1 : ℝ) * Sparse.eval nodeValue4986 x + ((2 : ℝ) * Sparse.eval nodeValue4987 x + ((1 : ℝ) * Sparse.eval nodeValue4998 x + ((2 : ℝ) * Sparse.eval nodeValue5075 x + ((2 : ℝ) * Sparse.eval nodeValue5134 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5460 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + 0))))))))))))))))))))

noncomputable def reducedSource1949 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4528 x + ((1 : ℝ) * Sparse.eval nodeValue4529 x + ((1 : ℝ) * Sparse.eval nodeValue4533 x + ((1 : ℝ) * Sparse.eval nodeValue4545 x + ((1 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4954 x + ((1 : ℝ) * Sparse.eval nodeValue4955 x + ((1 : ℝ) * Sparse.eval nodeValue4957 x + ((1 : ℝ) * Sparse.eval nodeValue4963 x + ((1 : ℝ) * Sparse.eval nodeValue5033 x + ((1 : ℝ) * Sparse.eval nodeValue5036 x + ((1 : ℝ) * Sparse.eval nodeValue5038 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5127 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5135 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1950 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3258 x + ((1 : ℝ) * Sparse.eval nodeValue3259 x + ((1 : ℝ) * Sparse.eval nodeValue3260 x + ((1 : ℝ) * Sparse.eval nodeValue3267 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3449 x + ((1 : ℝ) * Sparse.eval nodeValue3450 x + ((1 : ℝ) * Sparse.eval nodeValue3452 x + ((1 : ℝ) * Sparse.eval nodeValue3453 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3470 x + ((1 : ℝ) * Sparse.eval nodeValue3508 x + ((1 : ℝ) * Sparse.eval nodeValue3509 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3553 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3793 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1951 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2347 x + ((1 : ℝ) * Sparse.eval nodeValue2348 x + ((1 : ℝ) * Sparse.eval nodeValue2350 x + ((1 : ℝ) * Sparse.eval nodeValue2353 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1952 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4320 x + ((1 : ℝ) * Sparse.eval nodeValue4321 x + ((1 : ℝ) * Sparse.eval nodeValue4323 x + ((1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4396 x + ((1 : ℝ) * Sparse.eval nodeValue4706 x + ((1 : ℝ) * Sparse.eval nodeValue4709 x + ((1 : ℝ) * Sparse.eval nodeValue4728 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4926 x + ((1 : ℝ) * Sparse.eval nodeValue4928 x + ((1 : ℝ) * Sparse.eval nodeValue4939 x + ((1 : ℝ) * Sparse.eval nodeValue4985 x + ((1 : ℝ) * Sparse.eval nodeValue4987 x + ((1 : ℝ) * Sparse.eval nodeValue4996 x + ((1 : ℝ) * Sparse.eval nodeValue5126 x + ((2 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1953 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4528 x + ((1 : ℝ) * Sparse.eval nodeValue4530 x + ((1 : ℝ) * Sparse.eval nodeValue4533 x + ((1 : ℝ) * Sparse.eval nodeValue4544 x + ((1 : ℝ) * Sparse.eval nodeValue4590 x + ((1 : ℝ) * Sparse.eval nodeValue4930 x + ((1 : ℝ) * Sparse.eval nodeValue4932 x + ((1 : ℝ) * Sparse.eval nodeValue4933 x + ((1 : ℝ) * Sparse.eval nodeValue4941 x + ((1 : ℝ) * Sparse.eval nodeValue5034 x + ((1 : ℝ) * Sparse.eval nodeValue5043 x + ((1 : ℝ) * Sparse.eval nodeValue5044 x + ((1 : ℝ) * Sparse.eval nodeValue5065 x + ((1 : ℝ) * Sparse.eval nodeValue5067 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5100 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((1 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1954 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3260 x + ((1 : ℝ) * Sparse.eval nodeValue3261 x + ((1 : ℝ) * Sparse.eval nodeValue3263 x + ((1 : ℝ) * Sparse.eval nodeValue3267 x + ((1 : ℝ) * Sparse.eval nodeValue3290 x + ((1 : ℝ) * Sparse.eval nodeValue3408 x + ((1 : ℝ) * Sparse.eval nodeValue3409 x + ((1 : ℝ) * Sparse.eval nodeValue3410 x + ((1 : ℝ) * Sparse.eval nodeValue3414 x + ((1 : ℝ) * Sparse.eval nodeValue3451 x + ((1 : ℝ) * Sparse.eval nodeValue3465 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((2 : ℝ) * Sparse.eval nodeValue3467 x + ((1 : ℝ) * Sparse.eval nodeValue3469 x + ((1 : ℝ) * Sparse.eval nodeValue3474 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((1 : ℝ) * Sparse.eval nodeValue3477 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3483 x + ((1 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1955 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1875 x + ((1 : ℝ) * Sparse.eval nodeValue1876 x + ((1 : ℝ) * Sparse.eval nodeValue1878 x + ((1 : ℝ) * Sparse.eval nodeValue1908 x + ((1 : ℝ) * Sparse.eval nodeValue2075 x + ((1 : ℝ) * Sparse.eval nodeValue3444 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

noncomputable def reducedSource1956 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4527 x + ((2 : ℝ) * Sparse.eval nodeValue4529 x + ((1 : ℝ) * Sparse.eval nodeValue4541 x + ((1 : ℝ) * Sparse.eval nodeValue4589 x + ((1 : ℝ) * Sparse.eval nodeValue4929 x + ((2 : ℝ) * Sparse.eval nodeValue4931 x + ((1 : ℝ) * Sparse.eval nodeValue4939 x + ((1 : ℝ) * Sparse.eval nodeValue5041 x + ((2 : ℝ) * Sparse.eval nodeValue5042 x + ((2 : ℝ) * Sparse.eval nodeValue5074 x + ((2 : ℝ) * Sparse.eval nodeValue5075 x + ((2 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((2 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5184 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5409 x + 0))))))))))))))))))))

noncomputable def reducedSource1957 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3255 x + ((1 : ℝ) * Sparse.eval nodeValue3256 x + ((2 : ℝ) * Sparse.eval nodeValue3258 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((1 : ℝ) * Sparse.eval nodeValue3403 x + ((1 : ℝ) * Sparse.eval nodeValue3404 x + ((2 : ℝ) * Sparse.eval nodeValue3406 x + ((1 : ℝ) * Sparse.eval nodeValue3458 x + ((1 : ℝ) * Sparse.eval nodeValue3460 x + ((2 : ℝ) * Sparse.eval nodeValue3462 x + ((2 : ℝ) * Sparse.eval nodeValue3463 x + ((2 : ℝ) * Sparse.eval nodeValue3468 x + ((2 : ℝ) * Sparse.eval nodeValue3470 x + ((2 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((2 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3807 x + 0))))))))))))))))))))

noncomputable def reducedSource1958 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4540 x + ((1 : ℝ) * Sparse.eval nodeValue4543 x + ((2 : ℝ) * Sparse.eval nodeValue4548 x + ((1 : ℝ) * Sparse.eval nodeValue4600 x + ((1 : ℝ) * Sparse.eval nodeValue4760 x + ((1 : ℝ) * Sparse.eval nodeValue4769 x + ((2 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4938 x + ((2 : ℝ) * Sparse.eval nodeValue4945 x + ((2 : ℝ) * Sparse.eval nodeValue5035 x + ((1 : ℝ) * Sparse.eval nodeValue5097 x + ((2 : ℝ) * Sparse.eval nodeValue5099 x + ((2 : ℝ) * Sparse.eval nodeValue5103 x + ((2 : ℝ) * Sparse.eval nodeValue5110 x + ((1 : ℝ) * Sparse.eval nodeValue5133 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5248 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((2 : ℝ) * Sparse.eval nodeValue5272 x + ((2 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + 0))))))))))))))))))))

noncomputable def reducedSource1959 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2173 x + ((1 : ℝ) * Sparse.eval nodeValue2184 x + ((1 : ℝ) * Sparse.eval nodeValue2185 x + ((2 : ℝ) * Sparse.eval nodeValue2228 x + ((2 : ℝ) * Sparse.eval nodeValue2652 x + ((2 : ℝ) * Sparse.eval nodeValue2657 x + ((2 : ℝ) * Sparse.eval nodeValue2658 x + ((2 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue2688 x + ((1 : ℝ) * Sparse.eval nodeValue2689 x + ((1 : ℝ) * Sparse.eval nodeValue2693 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2702 x + ((2 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((2 : ℝ) * Sparse.eval nodeValue2740 x + ((2 : ℝ) * Sparse.eval nodeValue2742 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3058 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + 0))))))))))))))))))))

noncomputable def reducedSource1960 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4366 x + ((1 : ℝ) * Sparse.eval nodeValue4371 x + ((2 : ℝ) * Sparse.eval nodeValue4372 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4698 x + ((1 : ℝ) * Sparse.eval nodeValue4702 x + ((2 : ℝ) * Sparse.eval nodeValue4703 x + ((1 : ℝ) * Sparse.eval nodeValue4765 x + ((2 : ℝ) * Sparse.eval nodeValue4775 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((2 : ℝ) * Sparse.eval nodeValue4808 x + ((2 : ℝ) * Sparse.eval nodeValue4852 x + ((2 : ℝ) * Sparse.eval nodeValue4856 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4893 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((1 : ℝ) * Sparse.eval nodeValue5279 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + 0))))))))))))))))))))

noncomputable def reducedSource1961 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1711 x + ((2 : ℝ) * Sparse.eval nodeValue1734 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue1742 x + ((1 : ℝ) * Sparse.eval nodeValue2179 x + ((1 : ℝ) * Sparse.eval nodeValue2180 x + ((2 : ℝ) * Sparse.eval nodeValue2211 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((2 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((1 : ℝ) * Sparse.eval nodeValue2248 x + ((2 : ℝ) * Sparse.eval nodeValue2250 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((2 : ℝ) * Sparse.eval nodeValue2272 x + ((2 : ℝ) * Sparse.eval nodeValue2274 x + ((2 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((1 : ℝ) * Sparse.eval nodeValue2748 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + 0))))))))))))))))))))

noncomputable def reducedSource1962 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1824 x + ((1 : ℝ) * Sparse.eval nodeValue1828 x + ((2 : ℝ) * Sparse.eval nodeValue1829 x + ((1 : ℝ) * Sparse.eval nodeValue2110 x + ((1 : ℝ) * Sparse.eval nodeValue3079 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1963 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4236 x + ((1 : ℝ) * Sparse.eval nodeValue4237 x + ((2 : ℝ) * Sparse.eval nodeValue4238 x + ((1 : ℝ) * Sparse.eval nodeValue4275 x + ((1 : ℝ) * Sparse.eval nodeValue4685 x + ((1 : ℝ) * Sparse.eval nodeValue4686 x + ((2 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4723 x + ((2 : ℝ) * Sparse.eval nodeValue4724 x + ((1 : ℝ) * Sparse.eval nodeValue4746 x + ((1 : ℝ) * Sparse.eval nodeValue4859 x + ((2 : ℝ) * Sparse.eval nodeValue4860 x + ((3 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue4871 x + ((2 : ℝ) * Sparse.eval nodeValue4874 x + ((2 : ℝ) * Sparse.eval nodeValue4898 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5403 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + 0)))))))))))))))))))

noncomputable def reducedSource1964 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue736 x + ((1 : ℝ) * Sparse.eval nodeValue737 x + ((2 : ℝ) * Sparse.eval nodeValue738 x + ((1 : ℝ) * Sparse.eval nodeValue827 x + ((1 : ℝ) * Sparse.eval nodeValue1811 x + ((1 : ℝ) * Sparse.eval nodeValue1812 x + ((2 : ℝ) * Sparse.eval nodeValue1814 x + ((1 : ℝ) * Sparse.eval nodeValue1877 x + ((2 : ℝ) * Sparse.eval nodeValue1878 x + ((1 : ℝ) * Sparse.eval nodeValue1925 x + ((1 : ℝ) * Sparse.eval nodeValue2100 x + ((2 : ℝ) * Sparse.eval nodeValue2101 x + ((2 : ℝ) * Sparse.eval nodeValue2110 x + ((2 : ℝ) * Sparse.eval nodeValue2112 x + ((2 : ℝ) * Sparse.eval nodeValue2115 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((2 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue3739 x + ((1 : ℝ) * Sparse.eval nodeValue3789 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((2 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

noncomputable def reducedSource1965 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4364 x + ((1 : ℝ) * Sparse.eval nodeValue4367 x + ((1 : ℝ) * Sparse.eval nodeValue4369 x + ((1 : ℝ) * Sparse.eval nodeValue4372 x + ((1 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4696 x + ((1 : ℝ) * Sparse.eval nodeValue4699 x + ((1 : ℝ) * Sparse.eval nodeValue4701 x + ((1 : ℝ) * Sparse.eval nodeValue4703 x + ((1 : ℝ) * Sparse.eval nodeValue4772 x + ((1 : ℝ) * Sparse.eval nodeValue4774 x + ((1 : ℝ) * Sparse.eval nodeValue4775 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4851 x + ((1 : ℝ) * Sparse.eval nodeValue4853 x + ((1 : ℝ) * Sparse.eval nodeValue4856 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4893 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5288 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1966 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1703 x + ((1 : ℝ) * Sparse.eval nodeValue1720 x + ((1 : ℝ) * Sparse.eval nodeValue1721 x + ((1 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1734 x + ((1 : ℝ) * Sparse.eval nodeValue2198 x + ((1 : ℝ) * Sparse.eval nodeValue2199 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2211 x + ((1 : ℝ) * Sparse.eval nodeValue2238 x + ((1 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((1 : ℝ) * Sparse.eval nodeValue2256 x + ((1 : ℝ) * Sparse.eval nodeValue2257 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((1 : ℝ) * Sparse.eval nodeValue2272 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2760 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1967 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1822 x + ((1 : ℝ) * Sparse.eval nodeValue1825 x + ((1 : ℝ) * Sparse.eval nodeValue1827 x + ((1 : ℝ) * Sparse.eval nodeValue1829 x + ((1 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue3096 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1968 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4232 x + ((1 : ℝ) * Sparse.eval nodeValue4233 x + ((1 : ℝ) * Sparse.eval nodeValue4234 x + ((1 : ℝ) * Sparse.eval nodeValue4239 x + ((1 : ℝ) * Sparse.eval nodeValue4268 x + ((1 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4689 x + ((1 : ℝ) * Sparse.eval nodeValue4721 x + ((1 : ℝ) * Sparse.eval nodeValue4722 x + ((1 : ℝ) * Sparse.eval nodeValue4725 x + ((1 : ℝ) * Sparse.eval nodeValue4740 x + ((1 : ℝ) * Sparse.eval nodeValue4826 x + ((1 : ℝ) * Sparse.eval nodeValue4827 x + ((1 : ℝ) * Sparse.eval nodeValue4828 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1969 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue732 x + ((1 : ℝ) * Sparse.eval nodeValue733 x + ((1 : ℝ) * Sparse.eval nodeValue734 x + ((1 : ℝ) * Sparse.eval nodeValue739 x + ((1 : ℝ) * Sparse.eval nodeValue824 x + ((1 : ℝ) * Sparse.eval nodeValue1805 x + ((1 : ℝ) * Sparse.eval nodeValue1807 x + ((1 : ℝ) * Sparse.eval nodeValue1810 x + ((1 : ℝ) * Sparse.eval nodeValue1815 x + ((1 : ℝ) * Sparse.eval nodeValue1875 x + ((1 : ℝ) * Sparse.eval nodeValue1876 x + ((1 : ℝ) * Sparse.eval nodeValue1879 x + ((1 : ℝ) * Sparse.eval nodeValue1922 x + ((1 : ℝ) * Sparse.eval nodeValue2077 x + ((1 : ℝ) * Sparse.eval nodeValue2079 x + ((1 : ℝ) * Sparse.eval nodeValue2082 x + ((1 : ℝ) * Sparse.eval nodeValue2105 x + ((1 : ℝ) * Sparse.eval nodeValue2106 x + ((2 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue3737 x + ((1 : ℝ) * Sparse.eval nodeValue3787 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1970 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4449 x + ((1 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4453 x + ((1 : ℝ) * Sparse.eval nodeValue4462 x + ((1 : ℝ) * Sparse.eval nodeValue4489 x + ((1 : ℝ) * Sparse.eval nodeValue4798 x + ((1 : ℝ) * Sparse.eval nodeValue4799 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4806 x + ((1 : ℝ) * Sparse.eval nodeValue4826 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4849 x + ((1 : ℝ) * Sparse.eval nodeValue4851 x + ((1 : ℝ) * Sparse.eval nodeValue4852 x + ((1 : ℝ) * Sparse.eval nodeValue4860 x + ((1 : ℝ) * Sparse.eval nodeValue4861 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((1 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue4870 x + ((1 : ℝ) * Sparse.eval nodeValue4879 x + ((1 : ℝ) * Sparse.eval nodeValue4880 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5203 x + ((1 : ℝ) * Sparse.eval nodeValue5204 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1974 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1821 x + ((1 : ℝ) * Sparse.eval nodeValue1823 x + ((2 : ℝ) * Sparse.eval nodeValue1826 x + ((1 : ℝ) * Sparse.eval nodeValue2106 x + ((1 : ℝ) * Sparse.eval nodeValue3050 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource1975 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue941 x + ((1 : ℝ) * Sparse.eval nodeValue1821 x + ((1 : ℝ) * Sparse.eval nodeValue2104 x + ((3 : ℝ) * Sparse.eval nodeValue2106 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource2112 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1534 x + ((2 : ℝ) * Sparse.eval nodeValue1541 x + ((-1 : ℝ) * Sparse.eval nodeValue4062 x + 0))

end MUB6.Certificate.MixedSourceBridge

end OAI
end


