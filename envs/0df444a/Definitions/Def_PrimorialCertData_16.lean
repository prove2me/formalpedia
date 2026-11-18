-- Prove2me | Definitions.Def_PrimorialCertData_16
-- name    : PrimorialCertData_16
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:50.344898+00:00
-- url     : https://prove2.me/theorems/15d6fe5e-74f7-45f3-8183-e242803aa454
-- title:
--   Primorial certificate data, block 16 of 75
-- statement:
--   Certificate data, block 16 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[14\,680\,067,\,15\,597\,571)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_16` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData16.s0 : Seg := ⟨270719303875204127302884649, 270719303875204132436649856, 14680067, 65536, [], 273149745272316352743617984, 273149745272316357923474196⟩
def PrimData16.s1 : Seg := ⟨273149745272316352743617984, 273149745272316357923474196, 14811139, 65536, [], 275555898163550332730296315, 275555898163550337955772831⟩
def PrimData16.s2 : Seg := ⟨275555898163550332730296315, 275555898163550337955772831, 14942211, 65536, [], 277963329698894156704629001, 277963329698894161975758862⟩
def PrimData16.s3 : Seg := ⟨277963329698894156704629001, 277963329698894161975758862, 15073283, 65536, [], 280372635926705336518321671, 280372635926705341835135715⟩
def PrimData16.s4 : Seg := ⟨280372635926705336518321671, 280372635926705341835135715, 15204355, 65536, [], 282799981340096071390590375, 282799981340096076753432663⟩
def PrimData16.s5 : Seg := ⟨282799981340096071390590375, 282799981340096076753432663, 15335427, 65536, [], 285198359281014543449573717, 285198359281014548857910660⟩
def PrimData16.s6 : Seg := ⟨285198359281014543449573717, 285198359281014548857910660, 15466499, 65536, [], 287641951201008012394754886, 287641951201008017849453624⟩

def PrimData16.segs : List Seg := [PrimData16.s0, PrimData16.s1, PrimData16.s2, PrimData16.s3, PrimData16.s4, PrimData16.s5, PrimData16.s6]

end ThetaSieve


