-- Prove2me | Definitions.Def_PrimorialCertData_1
-- name    : PrimorialCertData_1
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:20.023674+00:00
-- url     : https://prove2.me/theorems/64bd3c9e-c1f6-4010-9d65-cf58f48be249
-- title:
--   Primorial certificate data, block 1 of 75
-- statement:
--   Certificate data, block 1 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[917\,507,\,1\,835\,011)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_1` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData1.s0 : Seg := ⟨16906844048882945717223248, 16906844048882946037829117, 917507, 65536, [], 19319182800820645148719502, 19319182800820645515060685⟩
def PrimData1.s1 : Seg := ⟨19319182800820645148719502, 19319182800820645515060685, 1048579, 65536, [], 21743976388148939469412628, 21743976388148939881747051⟩
def PrimData1.s2 : Seg := ⟨21743976388148939469412628, 21743976388148939881747051, 1179651, 65536, [], 24156800680800159128796984, 24156800680800159586884419⟩
def PrimData1.s3 : Seg := ⟨24156800680800159128796984, 24156800680800159586884419, 1310723, 65536, [], 26573830403824655916006596, 26573830403824656419930748⟩
def PrimData1.s4 : Seg := ⟨26573830403824655916006596, 26573830403824656419930748, 1441795, 65536, [], 28991178078555431486694189, 28991178078555432036458855⟩
def PrimData1.s5 : Seg := ⟨28991178078555431486694189, 28991178078555432036458855, 1572867, 65536, [], 31405049667962231732432131, 31405049667962232327965867⟩
def PrimData1.s6 : Seg := ⟨31405049667962231732432131, 31405049667962232327965867, 1703939, 65536, [], 33822898766633561946684472, 33822898766633562588072272⟩

def PrimData1.segs : List Seg := [PrimData1.s0, PrimData1.s1, PrimData1.s2, PrimData1.s3, PrimData1.s4, PrimData1.s5, PrimData1.s6]

end ThetaSieve


