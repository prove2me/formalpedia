-- Prove2me | Definitions.Def_PrimorialCertData_14
-- name    : PrimorialCertData_14
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:45.4662+00:00
-- url     : https://prove2.me/theorems/eb9e1cd5-8c46-4b36-9abe-b67294ece1a2
-- title:
--   Primorial certificate data, block 14 of 75
-- statement:
--   Certificate data, block 14 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[12\,845\,059,\,13\,762\,563)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_14` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData14.s0 : Seg := ⟨236910301832165443549579431, 236910301832165448042213863, 12845059, 65536, [], 239312716629432030222531846, 239312716629432034760722903⟩
def PrimData14.s1 : Seg := ⟨239312716629432030222531846, 239312716629432034760722903, 12976131, 65536, [], 241710267446006960569313133, 241710267446006965152972898⟩
def PrimData14.s2 : Seg := ⟨241710267446006960569313133, 241710267446006965152972898, 13107203, 65536, [], 244130755095105200998707347, 244130755095105205628253931⟩
def PrimData14.s3 : Seg := ⟨244130755095105200998707347, 244130755095105205628253931, 13238275, 65536, [], 246551193335702619516260590, 246551193335702624191713857⟩
def PrimData14.s4 : Seg := ⟨246551193335702619516260590, 246551193335702624191713857, 13369347, 65536, [], 248951275694715984081758056, 248951275694715988802734188⟩
def PrimData14.s5 : Seg := ⟨248951275694715984081758056, 248951275694715988802734188, 13500419, 65536, [], 251369139466159190563625856, 251369139466159195330444290⟩
def PrimData14.s6 : Seg := ⟨251369139466159190563625856, 251369139466159195330444290, 13631491, 65536, [], 253792657888517438611597777, 253792657888517443424373437⟩

def PrimData14.segs : List Seg := [PrimData14.s0, PrimData14.s1, PrimData14.s2, PrimData14.s3, PrimData14.s4, PrimData14.s5, PrimData14.s6]

end ThetaSieve


