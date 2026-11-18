-- Prove2me | Definitions.Def_PrimorialCertData_11
-- name    : PrimorialCertData_11
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:39.639197+00:00
-- url     : https://prove2.me/theorems/454aeaba-7d14-45d9-bf65-744bb73ba45b
-- title:
--   Primorial certificate data, block 11 of 75
-- statement:
--   Certificate data, block 11 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[10\,092\,547,\,11\,010\,051)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_11` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData11.s0 : Seg := ⟨186095470539918573924399197, 186095470539918577453405646, 10092547, 65536, [], 188498712590508733619659231, 188498712590508737194232504⟩
def PrimData11.s1 : Seg := ⟨188498712590508733619659231, 188498712590508737194232504, 10223619, 65536, [], 190917267665010052076437175, 190917267665010055696883783⟩
def PrimData11.s2 : Seg := ⟨190917267665010052076437175, 190917267665010055696883783, 10354691, 65536, [], 193352327785444209573839498, 193352327785444213240456887⟩
def PrimData11.s3 : Seg := ⟨193352327785444209573839498, 193352327785444213240456887, 10485763, 65536, [], 195771670431246400653466808, 195771670431246404365963840⟩
def PrimData11.s4 : Seg := ⟨195771670431246400653466808, 195771670431246404365963840, 10616835, 65536, [], 198204802176393046902501796, 198204802176393050661143475⟩
def PrimData11.s5 : Seg := ⟨198204802176393046902501796, 198204802176393050661143475, 10747907, 65536, [], 200612583163308556561675602, 200612583163308560365973194⟩
def PrimData11.s6 : Seg := ⟨200612583163308556561675602, 200612583163308560365973194, 10878979, 65536, [], 203032315976804453386836300, 203032315976804457237019916⟩

def PrimData11.segs : List Seg := [PrimData11.s0, PrimData11.s1, PrimData11.s2, PrimData11.s3, PrimData11.s4, PrimData11.s5, PrimData11.s6]

end ThetaSieve


