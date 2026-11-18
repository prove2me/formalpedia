-- Prove2me | Definitions.Def_PrimorialCertData_8
-- name    : PrimorialCertData_8
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:33.552567+00:00
-- url     : https://prove2.me/theorems/a98814a4-014a-41e2-b538-b558872bcdcf
-- title:
--   Primorial certificate data, block 8 of 75
-- statement:
--   Certificate data, block 8 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[7\,340\,035,\,8\,257\,539)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_8` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData8.s0 : Seg := ⟨135354997734773423294873595, 135354997734773425861660085, 7340035, 65536, [], 137765435308109419192158125, 137765435308109421804650744⟩
def PrimData8.s1 : Seg := ⟨137765435308109419192158125, 137765435308109421804650744, 7471107, 65536, [], 140180011878570369917233443, 140180011878570372575510767⟩
def PrimData8.s2 : Seg := ⟨140180011878570369917233443, 140180011878570372575510767, 7602179, 65536, [], 142602183797691891829721139, 142602183797691894533934412⟩
def PrimData8.s3 : Seg := ⟨142602183797691891829721139, 142602183797691894533934412, 7733251, 65536, [], 145021394867239667344782493, 145021394867239670094898608⟩
def PrimData8.s4 : Seg := ⟨145021394867239667344782493, 145021394867239670094898608, 7864323, 65536, [], 147436398244268763413228786, 147436398244268766209164068⟩
def PrimData8.s5 : Seg := ⟨147436398244268763413228786, 147436398244268766209164068, 7995395, 65536, [], 149847444523602074207330966, 149847444523602077048970819⟩
def PrimData8.s6 : Seg := ⟨149847444523602074207330966, 149847444523602077048970819, 8126467, 65536, [], 152264165381893857302247230, 152264165381893860189653591⟩

def PrimData8.segs : List Seg := [PrimData8.s0, PrimData8.s1, PrimData8.s2, PrimData8.s3, PrimData8.s4, PrimData8.s5, PrimData8.s6]

end ThetaSieve


