-- Prove2me | Definitions.Def_PrimorialCertData_7
-- name    : PrimorialCertData_7
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:31.79258+00:00
-- url     : https://prove2.me/theorems/86128b0d-b3eb-4944-a4bd-9dd50d3e337b
-- title:
--   Primorial certificate data, block 7 of 75
-- statement:
--   Certificate data, block 7 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[6\,422\,531,\,7\,340\,035)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_7` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData7.s0 : Seg := ⟨118412439619807149468598397, 118412439619807151714097600, 6422531, 65536, [], 120826452434641554040032508, 120826452434641556331312073⟩
def PrimData7.s1 : Seg := ⟨120826452434641554040032508, 120826452434641556331312073, 6553603, 65536, [], 123241505414815725288022745, 123241505414815727625092666⟩
def PrimData7.s2 : Seg := ⟨123241505414815725288022745, 123241505414815727625092666, 6684675, 65536, [], 125667409074356355135699740, 125667409074356357518775519⟩
def PrimData7.s3 : Seg := ⟨125667409074356355135699740, 125667409074356357518775519, 6815747, 65536, [], 128097441488274497983725029, 128097441488274500412887617⟩
def PrimData7.s4 : Seg := ⟨128097441488274497983725029, 128097441488274500412887617, 6946819, 65536, [], 130530387950041754343014340, 130530387950041756818309884⟩
def PrimData7.s5 : Seg := ⟨130530387950041754343014340, 130530387950041756818309884, 7077891, 65536, [], 132938537417078736970844395, 132938537417078739491805799⟩
def PrimData7.s6 : Seg := ⟨132938537417078736970844395, 132938537417078739491805799, 7208963, 65536, [], 135354997734773423294873595, 135354997734773425861660085⟩

def PrimData7.segs : List Seg := [PrimData7.s0, PrimData7.s1, PrimData7.s2, PrimData7.s3, PrimData7.s4, PrimData7.s5, PrimData7.s6]

end ThetaSieve


