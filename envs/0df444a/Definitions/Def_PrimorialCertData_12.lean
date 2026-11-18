-- Prove2me | Definitions.Def_PrimorialCertData_12
-- name    : PrimorialCertData_12
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:44.401877+00:00
-- url     : https://prove2.me/theorems/e889c6ba-3838-490c-85f2-d1b0989b4a5e
-- title:
--   Primorial certificate data, block 12 of 75
-- statement:
--   Certificate data, block 12 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[11\,010\,051,\,11\,927\,555)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_12` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData12.s0 : Seg := ⟨203032315976804453386836300, 203032315976804457237019916, 11010051, 65536, [], 205448440103465702187313960, 205448440103465706083318134⟩
def PrimData12.s1 : Seg := ⟨205448440103465702187313960, 205448440103465706083318134, 11141123, 65536, [], 207869308170523395798070436, 207869308170523399739972907⟩
def PrimData12.s2 : Seg := ⟨207869308170523395798070436, 207869308170523399739972907, 11272195, 65536, [], 210279929765540840726699684, 210279929765540844714319291⟩
def PrimData12.s3 : Seg := ⟨210279929765540840726699684, 210279929765540844714319291, 11403267, 65536, [], 212699155407097362506425241, 212699155407097366539934748⟩
def PrimData12.s4 : Seg := ⟨212699155407097362506425241, 212699155407097366539934748, 11534339, 65536, [], 215133571593409791258263660, 215133571593409795337934868⟩
def PrimData12.s5 : Seg := ⟨215133571593409791258263660, 215133571593409795337934868, 11665411, 65536, [], 217546251890993418985295791, 217546251890993423110689523⟩
def PrimData12.s6 : Seg := ⟨217546251890993418985295791, 217546251890993423110689523, 11796483, 65536, [], 219970796465872430687379675, 219970796465872434858773145⟩

def PrimData12.segs : List Seg := [PrimData12.s0, PrimData12.s1, PrimData12.s2, PrimData12.s3, PrimData12.s4, PrimData12.s5, PrimData12.s6]

end ThetaSieve


