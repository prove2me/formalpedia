-- Prove2me | Definitions.Def_PrimorialCertData_3
-- name    : PrimorialCertData_3
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:18:23.35407+00:00
-- url     : https://prove2.me/theorems/ed13cdef-3a0c-45c5-804a-e6ff19573be5
-- title:
--   Primorial certificate data, block 3 of 75
-- statement:
--   Certificate data, block 3 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 7 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[2\,752\,515,\,3\,670\,019)$ in consecutive segments of length $2W=131\,072$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_3` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData3.s0 : Seg := ⟨50738232456578986518095520, 50738232456578987480247599, 2752515, 65536, [], 53161684059256615497480866, 53161684059256616505593446⟩
def PrimData3.s1 : Seg := ⟨53161684059256615497480866, 53161684059256616505593446, 2883587, 65536, [], 55578008038011208461481239, 55578008038011209515416353⟩
def PrimData3.s2 : Seg := ⟨55578008038011208461481239, 55578008038011209515416353, 3014659, 65536, [], 57987332130655336215833865, 57987332130655337315452819⟩
def PrimData3.s3 : Seg := ⟨57987332130655336215833865, 57987332130655337315452819, 3145731, 65536, [], 60425194394908542390021863, 60425194394908543535871891⟩
def PrimData3.s4 : Seg := ⟨60425194394908542390021863, 60425194394908543535871891, 3276803, 65536, [], 62835771753263751908213555, 62835771753263753099774316⟩
def PrimData3.s5 : Seg := ⟨62835771753263751908213555, 62835771753263753099774316, 3407875, 65536, [], 65229992208343803034378498, 65229992208343804271342794⟩
def PrimData3.s6 : Seg := ⟨65229992208343803034378498, 65229992208343804271342794, 3538947, 65536, [], 67650450518408628219751483, 67650450518408629502617226⟩

def PrimData3.segs : List Seg := [PrimData3.s0, PrimData3.s1, PrimData3.s2, PrimData3.s3, PrimData3.s4, PrimData3.s5, PrimData3.s6]

end ThetaSieve


