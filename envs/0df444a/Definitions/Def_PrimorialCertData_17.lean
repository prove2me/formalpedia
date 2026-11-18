-- Prove2me | Definitions.Def_PrimorialCertData_17
-- name    : PrimorialCertData_17
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:51.789208+00:00
-- url     : https://prove2.me/theorems/e1c1500a-d130-4a23-bb5f-e061925fa7e8
-- title:
--   Primorial certificate data, block 17 of 75
-- statement:
--   Certificate data, block 17 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 2 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[15\,597\,571,\,15\,859\,715)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_17` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData17.s0 : Seg := ⟨287641951201008012394754886, 287641951201008017849453624, 15597571, 65536, [], 290054082194843772565053050, 290054082194843778065524075⟩
def PrimData17.s1 : Seg := ⟨290054082194843772565053050, 290054082194843778065524075, 15728643, 65536, [], 292478131132665993223673120, 292478131132665998770138892⟩

def PrimData17.segs : List Seg := [PrimData17.s0, PrimData17.s1]

end ThetaSieve


