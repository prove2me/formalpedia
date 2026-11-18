-- Prove2me | Definitions.Def_PrimorialCertData_6
-- name    : PrimorialCertData_6
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:30.77354+00:00
-- url     : https://prove2.me/theorems/817013b5-ee64-4c2b-8115-7a2125b1e2f3
-- title:
--   Primorial certificate data, block 6 of 75
-- statement:
--   Certificate data, block 6 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[5\,505\,027,\,6\,422\,531)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_6` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData6.s0 : Seg := ⟨101512749294931043246950046, 101512749294931045171972978, 5505027, 65536, [], 103919629605615013315204983, 103919629605615015285868141⟩
def PrimData6.s1 : Seg := ⟨103919629605615013315204983, 103919629605615015285868141, 5636099, 65536, [], 106328391098867353953433708, 106328391098867355969781740⟩
def PrimData6.s2 : Seg := ⟨106328391098867353953433708, 106328391098867355969781740, 5767171, 65536, [], 108744700358953986479134209, 108744700358953988541285792⟩
def PrimData6.s3 : Seg := ⟨108744700358953986479134209, 108744700358953988541285792, 5898243, 65536, [], 111178262321727320329815162, 111178262321727322438137925⟩
def PrimData6.s4 : Seg := ⟨111178262321727320329815162, 111178262321727322438137925, 6029315, 65536, [], 113584100717406891517601964, 113584100717406893671536908⟩
def PrimData6.s5 : Seg := ⟨113584100717406891517601964, 113584100717406893671536908, 6160387, 65536, [], 116003312656943163476025464, 116003312656943165675838242⟩
def PrimData6.s6 : Seg := ⟨116003312656943163476025464, 116003312656943165675838242, 6291459, 65536, [], 118412439619807149468598397, 118412439619807151714097600⟩

def PrimData6.segs : List Seg := [PrimData6.s0, PrimData6.s1, PrimData6.s2, PrimData6.s3, PrimData6.s4, PrimData6.s5, PrimData6.s6]

end ThetaSieve


