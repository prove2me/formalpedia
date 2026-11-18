-- Prove2me | Definitions.Def_PrimorialCertData_15
-- name    : PrimorialCertData_15
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:47.798601+00:00
-- url     : https://prove2.me/theorems/6c92dcdc-9079-4c71-8723-372f538a5425
-- title:
--   Primorial certificate data, block 15 of 75
-- statement:
--   Certificate data, block 15 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[13\,762\,563,\,14\,680\,067)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_15` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData15.s0 : Seg := ⟨253792657888517438611597777, 253792657888517443424373437, 13762563, 65536, [], 256222132547694801117888667, 256222132547694805976741875⟩
def PrimData15.s1 : Seg := ⟨256222132547694801117888667, 256222132547694805976741875, 13893635, 65536, [], 258626898684251602065807599, 258626898684251606970254679⟩
def PrimData15.s2 : Seg := ⟨258626898684251602065807599, 258626898684251606970254679, 14024707, 65536, [], 261050343241663287890948370, 261050343241663292841358921⟩
def PrimData15.s3 : Seg := ⟨261050343241663287890948370, 261050343241663292841358921, 14155779, 65536, [], 263463608930514876366168616, 263463608930514881362341286⟩
def PrimData15.s4 : Seg := ⟨263463608930514876366168616, 263463608930514881362341286, 14286851, 65536, [], 265900406756592353358761652, 265900406756592358401142955⟩
def PrimData15.s5 : Seg := ⟨265900406756592353358761652, 265900406756592358401142955, 14417923, 65536, [], 268304786602973146261293720, 268304786602973151349265305⟩
def PrimData15.s6 : Seg := ⟨268304786602973146261293720, 268304786602973151349265305, 14548995, 65536, [], 270719303875204127302884649, 270719303875204132436649856⟩

def PrimData15.segs : List Seg := [PrimData15.s0, PrimData15.s1, PrimData15.s2, PrimData15.s3, PrimData15.s4, PrimData15.s5, PrimData15.s6]

end ThetaSieve


