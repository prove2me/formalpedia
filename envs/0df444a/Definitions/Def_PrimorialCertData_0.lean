-- Prove2me | Definitions.Def_PrimorialCertData_0
-- name    : PrimorialCertData_0
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:12:01.360504+00:00
-- url     : https://prove2.me/theorems/d6c7e64b-a233-4384-b729-1e2941f1d46b
-- title:
--   Primorial certificate data, block 0 of 75
-- statement:
--   Certificate data, block 0 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[3,\,917\,507)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_0` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData0.s0 : Seg := ⟨12786308645202655427, 12786308645202655670, 3, 65536, [], 2410511247392363703085771, 2410511247392363748796110⟩
def PrimData0.s1 : Seg := ⟨2410511247392363703085771, 2410511247392363748796110, 131075, 65536, [], 4822904977794544141515358, 4822904977794544232967787⟩
def PrimData0.s2 : Seg := ⟨4822904977794544141515358, 4822904977794544232967787, 262147, 65536, [], 7242583340656157963798969, 7242583340656158101140588⟩
def PrimData0.s3 : Seg := ⟨7242583340656157963798969, 7242583340656158101140588, 393219, 65536, [], 9659920023984658427163564, 9659920023984658610339780⟩
def PrimData0.s4 : Seg := ⟨9659920023984658427163564, 9659920023984658610339780, 524291, 65536, [], 12070909330197340498338073, 12070909330197340727238298⟩
def PrimData0.s5 : Seg := ⟨12070909330197340498338073, 12070909330197340727238298, 655363, 65536, [], 14488863649274660610409540, 14488863649274660885163672⟩
def PrimData0.s6 : Seg := ⟨14488863649274660610409540, 14488863649274660885163672, 786435, 65536, [], 16906844048882945717223248, 16906844048882946037829117⟩

def PrimData0.segs : List Seg := [PrimData0.s0, PrimData0.s1, PrimData0.s2, PrimData0.s3, PrimData0.s4, PrimData0.s5, PrimData0.s6]

end ThetaSieve


