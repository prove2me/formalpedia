-- Prove2me | Definitions.Def_PrimorialCertData_5
-- name    : PrimorialCertData_5
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:28.686934+00:00
-- url     : https://prove2.me/theorems/f0f7c60e-2c20-493c-9011-7d45a43e2367
-- title:
--   Primorial certificate data, block 5 of 75
-- statement:
--   Certificate data, block 5 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[4\,587\,523,\,5\,505\,027)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_5` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData5.s0 : Seg := ⟨84580223118700218988344251, 84580223118700220592247921, 4587523, 65536, [], 86999713916019588196637348, 86999713916019589846429961⟩
def PrimData5.s1 : Seg := ⟨86999713916019588196637348, 86999713916019589846429961, 4718595, 65536, [], 89411381445387458623753359, 89411381445387460319283178⟩
def PrimData5.s2 : Seg := ⟨89411381445387458623753359, 89411381445387460319283178, 4849667, 65536, [], 91850593137441723421606632, 91850593137441725163394587⟩
def PrimData5.s3 : Seg := ⟨91850593137441723421606632, 91850593137441725163394587, 4980739, 65536, [], 94259518150970532083966902, 94259518150970533871437550⟩
def PrimData5.s4 : Seg := ⟨94259518150970532083966902, 94259518150970533871437550, 5111811, 65536, [], 96676439549777769961827976, 96676439549777771795135720⟩
def PrimData5.s5 : Seg := ⟨96676439549777769961827976, 96676439549777771795135720, 5242883, 65536, [], 99095263268148018839641850, 99095263268148020718821991⟩
def PrimData5.s6 : Seg := ⟨99095263268148018839641850, 99095263268148020718821991, 5373955, 65536, [], 101512749294931043246950046, 101512749294931045171972978⟩

def PrimData5.segs : List Seg := [PrimData5.s0, PrimData5.s1, PrimData5.s2, PrimData5.s3, PrimData5.s4, PrimData5.s5, PrimData5.s6]

end ThetaSieve


