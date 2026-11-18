-- Prove2me | Definitions.Def_PrimorialCertData_2
-- name    : PrimorialCertData_2
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:22.343087+00:00
-- url     : https://prove2.me/theorems/fc6703d4-a5c0-40ee-9c4a-341e9e259640
-- title:
--   Primorial certificate data, block 2 of 75
-- statement:
--   Certificate data, block 2 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[1\,835\,011,\,2\,752\,515)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_2` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData2.s0 : Seg := ⟨33822898766633561946684472, 33822898766633562588072272, 1835011, 65536, [], 36244736439612024432094106, 36244736439612025119404726⟩
def PrimData2.s1 : Seg := ⟨36244736439612024432094106, 36244736439612025119404726, 1966083, 65536, [], 38657649809743840824688834, 38657649809743841557732323⟩
def PrimData2.s2 : Seg := ⟨38657649809743840824688834, 38657649809743841557732323, 2097155, 65536, [], 41075832242750600004543720, 41075832242750600783469637⟩
def PrimData2.s3 : Seg := ⟨41075832242750600004543720, 41075832242750600783469637, 2228227, 65536, [], 43484589193291898634853182, 43484589193291899459455329⟩
def PrimData2.s4 : Seg := ⟨43484589193291898634853182, 43484589193291899459455329, 2359299, 65536, [], 45899786807720768217807465, 45899786807720769088206278⟩
def PrimData2.s5 : Seg := ⟨45899786807720768217807465, 45899786807720769088206278, 2490371, 65536, [], 48318737117885074966074576, 48318737117885075882345363⟩
def PrimData2.s6 : Seg := ⟨48318737117885074966074576, 48318737117885075882345363, 2621443, 65536, [], 50738232456578986518095520, 50738232456578987480247599⟩

def PrimData2.segs : List Seg := [PrimData2.s0, PrimData2.s1, PrimData2.s2, PrimData2.s3, PrimData2.s4, PrimData2.s5, PrimData2.s6]

end ThetaSieve


