-- Prove2me | Definitions.Def_PrimorialCertData_13
-- name    : PrimorialCertData_13
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:45.162688+00:00
-- url     : https://prove2.me/theorems/b5e069c3-8be6-48e9-800b-2c6adcdb3f46
-- title:
--   Primorial certificate data, block 13 of 75
-- statement:
--   Certificate data, block 13 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[11\,927\,555,\,12\,845\,059)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_13` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData13.s0 : Seg := ⟨219970796465872430687379675, 219970796465872434858773145, 11927555, 65536, [], 222386451081856408329755221, 222386451081856412546983020⟩
def PrimData13.s1 : Seg := ⟨222386451081856408329755221, 222386451081856412546983020, 12058627, 65536, [], 224795291833984484707633993, 224795291833984488970533957⟩
def PrimData13.s2 : Seg := ⟨224795291833984484707633993, 224795291833984488970533957, 12189699, 65536, [], 227228003362938141862661704, 227228003362938146171681165⟩
def PrimData13.s3 : Seg := ⟨227228003362938141862661704, 227228003362938146171681165, 12320771, 65536, [], 229651151250197576595100676, 229651151250197580950068508⟩
def PrimData13.s4 : Seg := ⟨229651151250197576595100676, 229651151250197580950068508, 12451843, 65536, [], 232053248961356556899444229, 232053248961356561299970405⟩
def PrimData13.s5 : Seg := ⟨232053248961356556899444229, 232053248961356561299970405, 12582915, 65536, [], 234477691864511484719940132, 234477691864511489166441349⟩
def PrimData13.s6 : Seg := ⟨234477691864511484719940132, 234477691864511489166441349, 12713987, 65536, [], 236910301832165443549579431, 236910301832165448042213863⟩

def PrimData13.segs : List Seg := [PrimData13.s0, PrimData13.s1, PrimData13.s2, PrimData13.s3, PrimData13.s4, PrimData13.s5, PrimData13.s6]

end ThetaSieve


