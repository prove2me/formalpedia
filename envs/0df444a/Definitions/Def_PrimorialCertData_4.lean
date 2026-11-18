-- Prove2me | Definitions.Def_PrimorialCertData_4
-- name    : PrimorialCertData_4
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:25.755265+00:00
-- url     : https://prove2.me/theorems/43957524-b960-456d-8056-3dc75db03cbf
-- title:
--   Primorial certificate data, block 4 of 75
-- statement:
--   Certificate data, block 4 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[3\,670\,019,\,4\,587\,523)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_4` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData4.s0 : Seg := ⟨67650450518408628219751483, 67650450518408629502617226, 3670019, 65536, [], 70072713753455044422230921, 70072713753455045751027845⟩
def PrimData4.s1 : Seg := ⟨70072713753455044422230921, 70072713753455045751027845, 3801091, 65536, [], 72501911950632555133565699, 72501911950632556508439696⟩
def PrimData4.s2 : Seg := ⟨72501911950632555133565699, 72501911950632556508439696, 3932163, 65536, [], 74915991793164034759567744, 74915991793164036180228738⟩
def PrimData4.s3 : Seg := ⟨74915991793164034759567744, 74915991793164036180228738, 4063235, 65536, [], 77332941354418201366188085, 77332941354418202832618782⟩
def PrimData4.s4 : Seg := ⟨77332941354418201366188085, 77332941354418202832618782, 4194307, 65536, [], 79733719058465780259125963, 79733719058465781771154064⟩
def PrimData4.s5 : Seg := ⟨79733719058465780259125963, 79733719058465781771154064, 4325379, 65536, [], 82163544925193353376923805, 82163544925193354935014378⟩
def PrimData4.s6 : Seg := ⟨82163544925193353376923805, 82163544925193354935014378, 4456451, 65536, [], 84580223118700218988344251, 84580223118700220592247921⟩

def PrimData4.segs : List Seg := [PrimData4.s0, PrimData4.s1, PrimData4.s2, PrimData4.s3, PrimData4.s4, PrimData4.s5, PrimData4.s6]

end ThetaSieve


