-- Prove2me | Definitions.Def_PrimorialCertData_10
-- name    : PrimorialCertData_10
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:37.368551+00:00
-- url     : https://prove2.me/theorems/6fc6b2b0-e286-4a68-a3e7-e99a600daa5b
-- title:
--   Primorial certificate data, block 10 of 75
-- statement:
--   Certificate data, block 10 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[9\,175\,043,\,10\,092\,547)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_10` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData10.s0 : Seg := ⟨169182264143941766940464450, 169182264143941770148717453, 9175043, 65536, [], 171615786220914218834980278, 171615786220914222089392538⟩
def PrimData10.s1 : Seg := ⟨171615786220914218834980278, 171615786220914222089392538, 9306115, 65536, [], 174022424540493076441276828, 174022424540493079741334871⟩
def PrimData10.s2 : Seg := ⟨174022424540493076441276828, 174022424540493079741334871, 9437187, 65536, [], 176433221601052817754443581, 176433221601052821100222165⟩
def PrimData10.s3 : Seg := ⟨176433221601052817754443581, 176433221601052821100222165, 9568259, 65536, [], 178861196218641360375191030, 178861196218641363767012557⟩
def PrimData10.s4 : Seg := ⟨178861196218641360375191030, 178861196218641363767012557, 9699331, 65536, [], 181285282335047259891820462, 181285282335047263329611966⟩
def PrimData10.s5 : Seg := ⟨181285282335047259891820462, 181285282335047263329611966, 9830403, 65536, [], 183678989964445108978597099, 183678989964445112461770436⟩
def PrimData10.s6 : Seg := ⟨183678989964445108978597099, 183678989964445112461770436, 9961475, 65536, [], 186095470539918573924399197, 186095470539918577453405646⟩

def PrimData10.segs : List Seg := [PrimData10.s0, PrimData10.s1, PrimData10.s2, PrimData10.s3, PrimData10.s4, PrimData10.s5, PrimData10.s6]

end ThetaSieve


