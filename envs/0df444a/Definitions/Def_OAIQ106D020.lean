-- Prove2me | Definitions.Def_OAIQ106D020
-- name    : OAIQ106D020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:07:24.870164+00:00
-- url     : https://prove2.me/theorems/d092295a-5579-440c-b15a-feec49705101
-- title:
--   Definitions bundle OAIQ106D020 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7610 declarations of OpenAI's Lean: 7610 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw22672Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22672step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22672step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22672step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22672step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22672step2`, `OAI.MUB6.Certificate.MixedSemantics.raw22672step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22673`, `OAI.MUB6.Certificate.MixedSemantics.raw22673Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22673step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22673step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22673step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22673step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22673step2`, `OAI.MUB6.Certificate.MixedSemantics.raw22673step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22673step3`, `OAI.MUB6.Certificate.MixedSemantics.raw22673step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22674`, `OAI.MUB6.Certificate.MixedSemantics.raw22674Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22674step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22674step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22674step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22674step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22674step2`, `OAI.MUB6.Certificate.MixedSemantics.raw22674step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22675`, `OAI.MUB6.Certificate.MixedSemantics.raw22675Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22675step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22675step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22675step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22675step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22675step2`, `OAI.MUB6.Certificate.MixedSemantics.raw22675step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22676`, `OAI.MUB6.Certificate.MixedSemantics.raw22676Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22676step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22676step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22676step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22676step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22677` and 7570 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical1`, `MutuallyUnbiased_MixedSemantics_Canonical17`, `MutuallyUnbiased_MixedSemantics_Canonical177`, `MutuallyUnbiased_MixedSemantics_Canonical178`, `MutuallyUnbiased_MixedSemantics_Canonical179`, `MutuallyUnbiased_MixedSemantics_Canonical18`, `MutuallyUnbiased_MixedSemantics_Canonical180`, `MutuallyUnbiased_MixedSemantics_Canonical181`, `MutuallyUnbiased_MixedSemantics_Canonical182`, `MutuallyUnbiased_MixedSemantics_Canonical183`, `MutuallyUnbiased_MixedSemantics_Canonical184`, `MutuallyUnbiased_MixedSemantics_Canonical185`, `MutuallyUnbiased_MixedSemantics_Canonical186`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound2576`, `OAI.MUB6.Certificate.MixedSemantics.sound2593`, `OAI.MUB6.Certificate.MixedSemantics.sound2594`, `OAI.MUB6.Certificate.MixedSemantics.sound2595`, `OAI.MUB6.Certificate.MixedSemantics.sound2596`, `OAI.MUB6.Certificate.MixedSemantics.sound2598`, `OAI.MUB6.Certificate.MixedSemantics.sound5292`, `OAI.MUB6.Certificate.MixedSemantics.sound5293`, `OAI.MUB6.Certificate.MixedSemantics.sound5294`, `OAI.MUB6.Certificate.MixedSemantics.sound5296`, `OAI.MUB6.Certificate.MixedSemantics.sound5306`, `OAI.MUB6.Certificate.MixedSemantics.sound5310`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound22`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero733`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero863`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1123`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound129`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1422`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1490`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1561`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1657`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound18`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1817`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1848`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2045`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound426`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound503`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound520`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound536`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound620`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound632`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound642`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound660`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound693`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound708`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound721`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound728`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound745`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound791`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound901`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound934`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound943`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound946`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound957`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound961`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1852`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1853` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1882`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw226Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw226step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw227 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw227Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw227step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw230 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw230Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw230step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw231 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw231Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw231step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw232 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw232Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw232step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw233 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw233Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw233step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw234 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw234Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw234step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw235 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw235Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw235step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw236 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw236Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw236step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw236step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw237 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw237Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw237step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw238 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 3, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2267Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw2267step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2267step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2268 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2268step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2269 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2270 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2270Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2270step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2270step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2270step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2271 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2271step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2272 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2273 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2273Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw2273step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2274 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2274step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2275 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2276 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2276Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2276step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2276step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2277 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2]]
def raw2277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2277step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2277step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2278 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2]]
def raw2278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2278step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2279 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2]]
def raw2279Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2279step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw2279step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw2279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2280 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2280step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2281 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2282 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2282Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2282step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2283 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3]]
def raw2283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2283step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2283step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2284 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3]]
def raw2284Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2284step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2284step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2285 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3]]
def raw2285Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2285step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2285step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2285step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2286 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2286step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2286step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2287 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2287Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2287step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2288 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2288Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2288step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw2288step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2288step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2288step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2289 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2289step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2290 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2290Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2290step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2291 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2291Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw2291step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw2291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw2291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2292 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2292step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2293 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2293Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2293step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2294 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2294Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2295 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2295step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2295step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2296 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2296Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2296step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2297 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2297Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2297step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw2297step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2298 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2298step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2299 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2300 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2300Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2301 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2301step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2301step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2302 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2302step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2302step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2303 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2303Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2303step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw2303step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2303step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw22672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22673step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22673step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22675step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22677step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw22677step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22681step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22686step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22689step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22689step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22690step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22693step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw22693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22694step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw22694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22695step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22698step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw22698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22699Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22699step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22699step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw22699step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22699step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22699step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22699step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22700step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw22700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22700step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22700step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22700step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw22701step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22701step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw22702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw22702step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22702step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw22702step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw22703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22703step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22703step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22703step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw22704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22704step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw22705step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22705step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw22706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw22706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22706step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw22706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw22707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22708step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw22708step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22708step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22708step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22708step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw22709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22709step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22709step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22709step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw22710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22711step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw22711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22711step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22711step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22711step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22712step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw22712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22712step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22712step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22712step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw22713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22713step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22713step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw22714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22715step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw22715step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22715step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw22715step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22715step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw22715step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22716step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22716step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22716step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22716step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22716step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22716step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22717step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22717step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22717step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw22717step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22717step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22717step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22717step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22717step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw22718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw22719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22719step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22720step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw22720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22720step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw22720step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22720step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw22720step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22721Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22721step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22722step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22723step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22737step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22737step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22738step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22739step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22739step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22740step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22740step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22741step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22741step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22742step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22743step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22743step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22744step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22745step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22745step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22745step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22746step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22746step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22747step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22747step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22748step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22748step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22749step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22749step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22750step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22750step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22751step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw22752step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22752step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw22752step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw22753step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22753step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw22753step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22754step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22756Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22756step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22757step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22758step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22760step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22761Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22761step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22762Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22762step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22762step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22763Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22763step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22764Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22764step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22765Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22765step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22765step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22766step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22766step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22767step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22768step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22769step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22769step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw22769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22770step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22770step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22770step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw22770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22775 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22775step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22779 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22779step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22783 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22783step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22783step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22783step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22783step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22788 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22788step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22788step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22788step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22788step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22796 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22796step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22818 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22818step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22821step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22821step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22828 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22828Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22828step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22828step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22828step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-1, -1, 2]]
def raw22828step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22828step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw22828step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22828step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw22828step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22831 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22831Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22831step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22831step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22831step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, -1, 2], ![-1, -1, 2]]
def raw22831step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22831step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw22831step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22831step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw22831step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22846step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22846step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw22847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw22847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw22847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw22848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw22848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw22848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw22848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22849 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-2, 2], ![3, -3], ![1, -1]]
def raw22849Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22849step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![3, -3], ![1, -1]]
def raw22849step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22849step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![3, -3], ![1, -1]]
def raw22849step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22849step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw22849step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22849step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw22849step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw22853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw22856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw22856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw22856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22856step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw22856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw22857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw22857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw22857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw22868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw22868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw22869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw22869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22870 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3], ![1, -1]]
def raw22870Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22870step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![3, -3], ![1, -1]]
def raw22870step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22870step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw22870step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22870step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw22870step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw22874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw22874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw22874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw22877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw22877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw22877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw22878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw22878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, 0, -2], ![2, -3, 1]]
def raw22884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22884step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw22884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, 0, -2], ![2, -3, 1]]
def raw22885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22885step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def raw22885step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw22886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw22887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw22888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, 0, -2], ![1, -2, 1]]
def raw22889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22890 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![2, -2], ![-1, 1]]
def raw22890Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22890step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![2, -2], ![-1, 1]]
def raw22890step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22890step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![2, -2], ![-1, 1]]
def raw22890step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22890step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw22890step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22892step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw22895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw22895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw22896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw22896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22897 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![2, -2], ![0, 0]]
def raw22897Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22897step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![2, -2]]
def raw22897step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22897step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![2, -2]]
def raw22897step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22897step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw22897step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw22899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw22900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw22901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw22901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw22906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw22907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw22907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22908 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![2, -2], ![-1, 1]]
def raw22908Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22908step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![2, -2], ![-1, 1]]
def raw22908step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22908step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw22908step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw22913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw22914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22915 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![2, -2], ![0, 0]]
def raw22915Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22915step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![2, -2]]
def raw22915step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22915step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw22915step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw22919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 1, -3], ![2, -3, 1]]
def raw22920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw22920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 1, -3], ![2, -3, 1]]
def raw22921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def raw22921step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw22922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw22923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw22924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw22924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw22924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw22925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw22925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 1, -3], ![1, -2, 1]]
def raw22925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw22925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22926 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![3, -3], ![-1, 1]]
def raw22926Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22926step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![3, -3], ![-1, 1]]
def raw22926step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22926step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![3, -3], ![-1, 1]]
def raw22926step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22926step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw22926step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22927step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22927step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22932step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw22947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22947step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw22948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22948step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22949step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22950step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw22951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw22951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw22951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22954step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22955step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw22956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22957step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22960step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw22960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22960step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw22960step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22961step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw22961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22962step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22965step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw22965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22966step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22973step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw22977step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw22978step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22978step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw22978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22980step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw22981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw22981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw22981step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw22981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22982step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22983step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22983step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw22983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22984step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22985step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw22986step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw22986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22987step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw22987step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22987step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22987step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22987step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22987step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22988step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22988step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22988step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22989step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22989step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22990step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw22990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22990step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw22990step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22990step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw22990step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22991step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22991step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw22991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22991step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22991step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22991step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22991step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22992step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw22992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22992step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22992step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22992step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw22993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22993step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw22994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22995step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22995step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw22995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22995step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22995step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22995step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22995step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22996step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw22996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22996step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22996step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22996step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22996step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22997step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22997step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw22998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22998step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22999step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22999step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw23000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23000step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23001step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23001step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw23002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw23002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23002step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw23002step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw23003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw23003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw23003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw23004step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw23004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23004step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw23004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23005step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw23005step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23005step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23005step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23005step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23007step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw23007step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw23007step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23007step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23007step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23007step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23007step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23008step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw23008step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23008step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw23008step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23008step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw23008step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23008step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw23008step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw23009step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23009step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23009step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw23010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23010step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw23011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw23011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw23011step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw23011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23011step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw23011step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23011step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw23011step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw23012step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw23012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23012step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23012step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23012step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23012step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw23013step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-2, 0, 2]]
def raw23013step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23013step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw23013step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23013step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw23013step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw23014step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23014step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw23015step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23015step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23015step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23015step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw23016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw23016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw23016step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw23016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw23016step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23016step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw23016step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23018step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw23021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw23021step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw23022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23023 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2], ![0, 0]]
def raw23023Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23023step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]
def raw23023step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23023step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2]]
def raw23023step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23023step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw23023step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw23027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw23031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23031step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw23031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw23032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23036step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23037step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23038step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23038step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23039step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2304 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2304step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2304step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2305 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2305step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2306 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2306Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2306step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw2306step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2306step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2307 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 3, -1]]
def raw2307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2307step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw2307step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2307step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw2307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2308 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 3, -1]]
def raw2308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2308step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw2308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2309 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 3, -1]]
def raw2309Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2309step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]
def raw2309step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2309step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]
def raw2309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2310 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2310step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2311 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2312 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2312Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2312step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2313 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw2313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2313step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2313step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2314 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw2314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2314step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw2314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2315 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw2315Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2315step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw2315step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw2315step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw2315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2316 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2316step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2316step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2317 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2317step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2318 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2318Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2318step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2318step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2319 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]
def raw2319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2319step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2319step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2319step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2319step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2320 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]
def raw2320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2320step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2321 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]
def raw2321Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2321step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2321step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2322 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2322step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2322step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2323 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2323step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2324 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2324Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2324step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw2324step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2324step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2325 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 2, 0]]
def raw2325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2325step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2325step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2325step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2326 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 2, 0]]
def raw2326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2326step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2327 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 2, 0]]
def raw2327Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2327step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-2, 1, 1]]
def raw2327step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2327step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw2327step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2327step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw2327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2355 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2355step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2356 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2357 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2357Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2357step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2357step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2357step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2358 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2358step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2358step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2359 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2360 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2360Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw2360step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2360step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2364 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2364step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2365 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2366 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2366Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2366step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2370 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2370step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2370step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2371 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2372 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2372Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2372step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2373 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2373step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2373step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2374 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2375 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2375Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw2375step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2375step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2375step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2376 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2376step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2376step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2377 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2378 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2378Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2378step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2378step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2378step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2379 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2379step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2380 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2381 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2381Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2381step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2382step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2382step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2383 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2384 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2384Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2384step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2385 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2385step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2385step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2386 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2387 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2387Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2387step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2387step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2387step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2388 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23040step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw23041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23041step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23041step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23041step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23042step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23042step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23043step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23043step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23044step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23044step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23045step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23045step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23046step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23047step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23047step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23048step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw23049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23049step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23049step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23049step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw23050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23050step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23050step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23050step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23050step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23051step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23051step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23052step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23052step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw23053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw23053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![3, -3, 0], ![1, 1, -2]]
def raw23053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw23053step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw23053step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw23054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw23054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw23054step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23054step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23054step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23054step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23054step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23055step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23055step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23058step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23058step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw23061step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23061step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23061step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23062step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw23069step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23070step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw23070step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23070step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23071step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23072step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw23073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw23073step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![3, -3, 0], ![1, 1, -2]]
def raw23073step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw23073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw23074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw23074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw23074step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23077 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23077step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23077step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23077step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23077step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23077step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23077step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23077step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23080 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23080step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23080step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23080step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23080step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23082 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23082step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23082step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23083step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23083step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23083step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23085 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23085step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23087 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23087step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23088 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23088step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23088step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23090 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23090step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23092 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23092step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23092step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -3, 2], ![-2, 0, 2]]
def raw23093step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw23093step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23093step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw23093step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23097 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23097step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23097step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23097step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23098step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23098step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23098step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23104 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23104step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23109 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23121 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23121step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23121step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23122 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23124 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23124step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23124step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23124step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23124step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23124step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23129 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23129Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23129step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23129step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw23129step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw23129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23134 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23134step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23134step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23134step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23139 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23139Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23139step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23139step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23139step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23146 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23146step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23146step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23146step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23146step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23146step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23147 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23147Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23147step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23147step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23161step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23161step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23162step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23162step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23162step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23164step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw23165step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23165step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23166step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw23166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23169step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw23169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23170step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23173step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23179step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23180step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23182step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw23182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23183step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw23183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw23184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw23185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw23186step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw23186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw23187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw23187step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23187step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw23187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23188step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23188step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23188step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23188step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23188step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23188step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23188step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23190step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23191step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23191step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23191step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23191step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23191step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23191step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23191step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23191step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23192step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23192step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23192step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23193step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw23193step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23193step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw23193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23194step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23195step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23195step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23196step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23196step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23196step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23196step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw23197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23197step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw23197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23198step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23199step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23199step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23199step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23200step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw23200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23200step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23200step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23200step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23200step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23201step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw23201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23201step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw23201step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23201step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw23201step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw23202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw23203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23203step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23203step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw23204step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23204step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw23204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23204step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw23204step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23204step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw23204step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23209step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23211step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23212step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23215step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23219step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23219step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23220step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23220step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw23221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw23221step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw23221step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23222step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23222step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23222step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23223step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23224step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23224step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw23225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23225step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23225step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23225step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23226step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23226step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23226step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23227step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23227step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23228step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23229step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23230step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23231step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23231step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23232step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23232step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23233step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23233step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw23234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23234step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23234step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw23235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23235step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23235step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23235step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23236step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23236step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23237step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![3, -2, -1], ![1, 0, -1]]
def raw23238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23238step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23238step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23238step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23238step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23239step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23239step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23239step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23241step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23242step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw23242step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw23242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23248step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw23256step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23256step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23260 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23260step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23260step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23260step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23261 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23261step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23262step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23263 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23263step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23263step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23264 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23264step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23265 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23265step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23266 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23266step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23266step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23267 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23267step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23268 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23268step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23269 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23269step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23269step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23270 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23270step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23270step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23270step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23270step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23271 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23271step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23271step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23271step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23272 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23272step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23272step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23273 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23273step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23274 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23274step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23274step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23274step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23274step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23275 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23276 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23276step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23277 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23277step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23278 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23279 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23280 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23280step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23281 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23281step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23281step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23282 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23282step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23283 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23284 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23284step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23284step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23284step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23285 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23285step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23285step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23285step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23286 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23286step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23287 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23288 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23288step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23289 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23289step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23289step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23289step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23289step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23289step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23290 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23290step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23290step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23290step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw23290step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23290step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw23290step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23291 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23292 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23292step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23293 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23293step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23293step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw23293step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23293step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw23293step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23294 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23294step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23295 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23295step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23295step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23295step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23295step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23295step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23296 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23297 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23297step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23298 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23298step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23299 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23299step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23299step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23299step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23299step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23299step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23300 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23301 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23301step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23302step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23302step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23302step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23303 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23303step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23303step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23303step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23303step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23303step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23303step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23304 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23304step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23304step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23304step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -1, 2], ![0, -2, 2]]
def raw23304step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23304step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23304step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23304step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23304step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23305 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23305step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23305step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23306 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23306step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23307 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw23307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw23307step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw23307step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23307step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23307step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23307step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23307step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw23312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw23312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw23312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw23313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw23313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw23313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23314 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![3, -3], ![0, 0]]
def raw23314Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23314step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![3, -3]]
def raw23314step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23314step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw23314step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23314step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw23314step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw23318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw23318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw23324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw23324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw23325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw23325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23326 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23327 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23328 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23329step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23330 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw23330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23331 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw23331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23333step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23334step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23335step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23335step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23336step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 1, -3], ![1, -1, 0]]
def raw23336step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw23336step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23336step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw23336step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23336step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw23336step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23337step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23339step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23340step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23341step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23342step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23342step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23342step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23343step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23345step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23346step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23346step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23347step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23347step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23348step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23351step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23351step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23351step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23351step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, 0, -3], ![2, -2, 0]]
def raw23352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw23352step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23353step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23353step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23354step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23355step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23356step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, 0, -3], ![1, -1, 0]]
def raw23356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw23356step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23357step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23357step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw23357step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23358step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23361step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw23361step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23362step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw23362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23363step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23363step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw23363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23364step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23364step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 1, -3], ![1, -1, 0]]
def raw23364step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23364step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw23364step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23365step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23365step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23368step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23368step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23369step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23369step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23369step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23370step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23370step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23373step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23373step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23374step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23378step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23378step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23378step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23379step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23380step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23380step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, 0, -3], ![2, -2, 0]]
def raw23380step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23380step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw23380step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23381step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23381step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23381step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw23381step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23382step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23382step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw23382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23383step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23383step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw23383step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23384step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23384step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, 0, -3], ![1, -1, 0]]
def raw23384step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23384step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def raw23384step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23385step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23385step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw23385step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23385step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw23385step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23386step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw23386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23387step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw23387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23388step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw23388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23389Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23389step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23389step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw23389step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23389step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23389step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23389step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23389step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23390Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23390step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23390step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw23390step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23390step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23390step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23390step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23390step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23391Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23391step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23391step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23391step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw23391step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23391step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23391step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23391step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23391step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23392step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23392step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23392step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw23392step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23392step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw23392step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23392step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw23392step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23392step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw23392step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23393Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23393step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23393step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23393step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 1, -3], ![1, -1, 0]]
def raw23393step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23393step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw23393step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23393step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw23393step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23393step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw23393step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23394Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23394step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23394step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23394step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23394step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23394step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23394step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23394step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23395Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23395step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23395step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23395step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23395step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23395step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23396Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23396step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23396step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23396step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23396step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23396step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23397Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23397step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23397step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw23397step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23397step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23397step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23397step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23397step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23398Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23398step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23398step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23398step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23398step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23398step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23398step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23398step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23398step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23399Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23399step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23399step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23399step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23399step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23399step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23399step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23399step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23400Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23400step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23400step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23400step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23400step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23401Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23401step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23401step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23401step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23401step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23402step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23402step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23402step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw23402step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23402step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23402step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23402step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23402step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23403step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23403step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23403step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23403step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23403step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23403step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23403step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23403step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23404step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23404step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23404step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23404step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23404step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23405step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23405step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23405step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23405step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23406step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23406step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23406step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23407step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23407step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23407step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw23407step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23407step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23407step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23407step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23407step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23408step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23408step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23408step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23408step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23408step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23408step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23408step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23408step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23409step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23409step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23409step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, 0, -3], ![2, -2, 0]]
def raw23409step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23409step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-3, 0, 3]]
def raw23409step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23409step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw23409step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23409step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw23409step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23410step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23410step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw23410step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23410step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23410step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23410step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23410step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23411step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23411step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw23411step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23411step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23411step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23411step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23411step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23412step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23412step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23412step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw23412step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23412step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23412step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23412step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23412step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23413step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23413step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23413step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, 0, -3], ![1, -1, 0]]
def raw23413step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23413step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw23413step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23413step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw23413step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23413step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw23413step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23414step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23414step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23414step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw23414step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23414step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-3, 1, 2]]
def raw23414step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23414step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw23414step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23414step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw23414step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23415step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23415step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw23415step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23415step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23415step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23415step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23415step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23416step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23416step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw23416step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23416step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23416step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23416step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23416step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23417Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23417step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23417step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw23417step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23417step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23417step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23417step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw23418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw23418step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw23418step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23418step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw23418step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23418step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-3, 2, 1]]
def raw23418step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23418step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw23418step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23418step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw23418step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, 0, -3], ![2, -2, 0]]
def raw23422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw23422step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical183
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23477step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -3, 2], ![-1, -1, 2]]
def raw23477step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23477step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -1, 2], ![-3, 1, 2]]
def raw23477step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23477step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw23477step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23477step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw23477step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23478 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23478step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23478step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23478step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23479 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23479step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23479step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23479step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23518step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23521step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23525step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23526step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23526step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, -1, -2], ![2, -1, -1]]
def raw23530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw23530step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23531step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23532step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23533step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23533step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, -1, -2], ![1, 0, -1]]
def raw23534step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw23534step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23535Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23535step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23535step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23535step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23535step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23535step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23535step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23535step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23536step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23536step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23536step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23536step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23536step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23536step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23536step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23537Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23537step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23537step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23537step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23537step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23537step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23537step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23537step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23538step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23538step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23538step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 0, -2], ![1, 0, -1]]
def raw23538step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23538step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw23538step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23538step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw23538step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23539Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23539step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23539step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23539step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23539step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23539step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23539step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23539step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23539step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23540step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23540step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23540step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23541Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23541step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23541step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23541step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23541step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23542step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23542step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23542step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23542step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23542step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23542step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23542step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23543step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23543step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23543step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23543step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23543step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23543step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23543step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23544step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23544step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23544step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23544step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23544step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23545step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23545step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23545step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23545step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23545step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23546step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23546step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23546step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23546step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23546step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23546step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23546step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23547Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23547step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23547step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23547step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23547step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23547step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23547step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23547step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23548Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23548step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23548step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23548step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23548step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23548step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23548step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23549Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23549step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23549step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23549step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23549step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23549step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23549step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23550Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23550step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23550step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23550step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23550step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23550step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23550step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23551Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23551step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23551step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23551step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, -1, -2], ![2, -1, -1]]
def raw23551step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23551step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -1, 2], ![-2, -1, 3]]
def raw23551step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23551step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw23551step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23551step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw23551step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23552step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23552step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw23552step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23552step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23552step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23552step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23552step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23553step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23553step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw23553step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23553step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23553step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23553step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23553step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23554step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23554step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw23554step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23554step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23554step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23554step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23554step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23555step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23555step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23555step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, -1, -2], ![1, 0, -1]]
def raw23555step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23555step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw23555step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23555step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw23555step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23555step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw23555step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23556step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23556step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23556step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw23556step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23556step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]
def raw23556step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23556step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw23556step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23556step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw23556step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw23557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw23557step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23559step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23560step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23560step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23561step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, -1, -2], ![2, -1, -1]]
def raw23561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw23561step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23562step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw23562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23563 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23563step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23563step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23563step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23564 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23564step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23565 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23565step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23565step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23565step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23566 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23566step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23566step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23567 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23567step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23567step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![0, -2, 2], ![0, -2, 2]]
def raw23568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-2, 2], ![-2, 2]]
def raw23568step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw23568step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw23568step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw23568step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw23568step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23569 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23569step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23570step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23570step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23570step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23570step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw23574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw23574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw23574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw23574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23581step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw23581step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw23581step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw23581step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw23582step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23582step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23582step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23582step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23582step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw23583step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23583step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23583step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23583step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23588step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23598step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23599step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23602step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw23603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw23603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw23603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23646 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw23646step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23646step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23646step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23646step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23662step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, 0, -2], ![2, -2, 0]]
def raw23662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23664Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23664step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23665Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![2, 0, -2], ![1, -1, 0]]
def raw23665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23667step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23668Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23668step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23669step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![2, -1, -1], ![1, 0, -1]]
def raw23669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw23669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23674Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23674step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23674step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23675step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23676step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw23677step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical185
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23680step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw23681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23682step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23683step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23683step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23684 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23684step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23684step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23685 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw23685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23685step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23686step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23694step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23694step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23694step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23694step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23695step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23695step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23695step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23696step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23696step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23696step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23696step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23697step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23697step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23697step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23697step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23697step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23698step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23698step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23698step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23698step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23703step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw23703step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw23703step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23703step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw23703step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23703step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23714step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23715step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23717step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![3, -1, -2], ![1, 0, -1]]
def raw23718step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23718step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw23718step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw23723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23724step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23724step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23724step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23724step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23724step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23725step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23725step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23726step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23727step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23727step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23727step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23728step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23728step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23728step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23728step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23729step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23729step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23729step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23729step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23729step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23731step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23731step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23731step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23732step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23732step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23732step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23732step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23732step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23732step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23733step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23733step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw23733step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23733step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23733step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23737step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23737step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23739step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23740step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23740step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23740step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23741step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23741step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23743step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23743step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23743step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23744step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23744step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw23744step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23744step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23744step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23744step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23744step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23745step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw23745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23745step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23745step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23745step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23745step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw23746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23746step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23746step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23746step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw23747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![3, -1, -2], ![1, 0, -1]]
def raw23748step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw23748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw23748step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23748step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw23748step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23749step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw23749step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23749step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23749step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23749step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23750step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23750step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw23750step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23750step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw23750step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23750step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw23750step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw23751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23751step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23751step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23751step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw23752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23752step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23752step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23752step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw23753step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw23753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23753step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw23753step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23753step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw23753step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23765step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23765step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23765step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23765step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23766 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23766step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23766step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23766step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23767 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23767step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23767step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23768step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23768step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23768step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23768step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23769 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23769step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23769step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23769step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23770step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23770step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23770step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23770step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23771 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23771step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23771step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23771step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23771step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23772step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23772step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw23772step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23772step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23772step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23772step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23772step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23773 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw23773step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23773step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23773step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23773step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23774 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw23774step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23774step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23774step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23774step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw23775step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23775step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23775step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23775step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23775step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23776 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw23776step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23776step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23776step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23776step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23777step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23777step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def raw23777step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23778step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![2, -2], ![2, -2]]
def raw23778step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23778step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23778step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23779step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![2, -2], ![2, -2]]
def raw23779step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23779step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23779step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23780step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23780step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw23780step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23780step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23780step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23781step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23781step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def raw23781step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23782step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23782step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23783step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![2, -2], ![2, -2]]
def raw23783step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23783step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23783step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23784step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23784step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw23784step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23784step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23784step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23785step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23785step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def raw23785step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23786step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23786step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23787step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23787step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23788step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23788step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23788step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23788step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![3, -3], ![2, -2]]
def raw23788step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23788step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]
def raw23788step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23789step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23789step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![3, -3], ![2, -2]]
def raw23789step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23789step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw23789step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23790step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23790step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![3, -3], ![2, -2]]
def raw23790step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23790step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw23790step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23791step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23791step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23791step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![3, -3], ![2, -2]]
def raw23791step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23791step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw23791step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw23792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw23792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw23792step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23792step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![3, -3, 0], ![1, -1, 0]]
def raw23792step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23792step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![3, -3], ![1, -1]]
def raw23792step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23792step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw23792step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23793step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw23793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23793step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23793step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23794 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23795 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23796 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23796step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def raw23796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23797Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23797step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23798 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw23798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw23798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw23798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23798step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw23798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23799 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw23799Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23799step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw23799step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23799step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw23799step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23799step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23799step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw23800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23801 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw23801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw23802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw23802step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23803step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw23808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw23808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw23809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw23809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23810 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]
def raw23810Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23810step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]
def raw23810step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23810step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw23810step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23810step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw23810step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23814step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw23816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw23816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw23816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23817 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw23817Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23817step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw23817step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23817step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw23817step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23817step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw23817step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23818 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23819 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23819step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23820 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23820step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw23821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw23821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23822 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23823 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23824 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23825 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw23825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw23825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23826 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw23826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23827 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw23827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw23827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23828 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23829 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23829step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23830 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23831 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw23836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23836step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23838 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]
def raw23838Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23838step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![0, 0], ![1, -1]]
def raw23838step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23838step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]
def raw23838step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23838step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw23838step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23838step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw23838step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23845 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23846 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23847 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23848 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23849 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23849step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23850 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23851 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw23851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw23851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23852 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23853 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23854 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23855 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23856 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23857 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw23857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw23857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw23865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23866 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]
def raw23866Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23866step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]
def raw23866step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23866step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw23866step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23866step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw23866step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23867 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23868 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23868step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23869 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23870 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23870step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23871 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23872 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw23882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw23882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23884 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


