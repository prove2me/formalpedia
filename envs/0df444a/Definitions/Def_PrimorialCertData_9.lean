-- Prove2me | Definitions.Def_PrimorialCertData_9
-- name    : PrimorialCertData_9
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:36.563772+00:00
-- url     : https://prove2.me/theorems/958eb11b-26bc-4d6b-a4c6-26a222710c23
-- title:
--   Primorial certificate data, block 9 of 75
-- statement:
--   Certificate data, block 9 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[8\,257\,539,\,9\,175\,043)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_9` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData9.s0 : Seg := ⟨152264165381893857302247230, 152264165381893860189653591, 8257539, 65536, [], 154680647531886150714662185, 154680647531886153647827089⟩
def PrimData9.s1 : Seg := ⟨154680647531886150714662185, 154680647531886153647827089, 8388611, 65536, [], 157094207329463570263616654, 157094207329463573242645533⟩
def PrimData9.s2 : Seg := ⟨157094207329463570263616654, 157094207329463573242645533, 8519683, 65536, [], 159525107241979406761091686, 159525107241979409786269579⟩
def PrimData9.s3 : Seg := ⟨159525107241979406761091686, 159525107241979409786269579, 8650755, 65536, [], 161956254715816744517052849, 161956254715816747588340678⟩
def PrimData9.s4 : Seg := ⟨161956254715816744517052849, 161956254715816747588340678, 8781827, 65536, [], 164360756294591755717098291, 164360756294591758833956293⟩
def PrimData9.s5 : Seg := ⟨164360756294591755717098291, 164360756294591758833956293, 8912899, 65536, [], 166768939607633126526734063, 166768939607633129689227944⟩
def PrimData9.s6 : Seg := ⟨166768939607633126526734063, 166768939607633129689227944, 9043971, 65536, [], 169182264143941766940464450, 169182264143941770148717453⟩

def PrimData9.segs : List Seg := [PrimData9.s0, PrimData9.s1, PrimData9.s2, PrimData9.s3, PrimData9.s4, PrimData9.s5, PrimData9.s6]

end ThetaSieve


