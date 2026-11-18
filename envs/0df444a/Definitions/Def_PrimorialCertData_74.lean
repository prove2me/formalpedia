-- Prove2me | Definitions.Def_PrimorialCertData_74
-- name    : PrimorialCertData_74
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:20:44.265578+00:00
-- url     : https://prove2.me/theorems/b6a8a5fb-477c-4368-bcf8-303b349d96f3
-- title:
--   Primorial certificate data, block 74 of 75
-- statement:
--   Certificate data, block 74 of 75, for the primorial bound $\prod_{p\le n}p\cdot 25^n<68^n$ on $16\,000\,000<n\le 32\,000\,000$.
--
--   The block is a list of 11 records of the structure `Seg` from the definition `ThetaCertCore`. Together they cover the integers in $[31\,916\,035,\,32\,006\,147)$ in consecutive segments of length $2W=8\,192$. A record with fields $lo, hi, L, W, lo', hi'$ encodes the claim
--
--   $$
--   lo\le Q\,\theta(L-1)\le hi\ \Longrightarrow\ lo'\le Q\,\theta(L+2W-1)\le hi',
--   $$
--
--   where $\theta(x)=\sum_{p\le x}\log p$ is the Chebyshev function, the sum running over primes, and $Q=2^{64}$.
--
--   The records were produced by a program and are not trusted. The problem `PrimorialCert.block_74` states that every record passes the kernel-evaluated checker `Seg.bok`, that consecutive records connect, and that each record reaching past $16\,000\,001$ satisfies the inequality needed for the bound. The 75 blocks together form one chain from $L=3$ to $32\,006\,147$.
--
--   **Formalization Note** The field `ws` of every record is the empty list. The data are plain natural-number literals, so the definition needs nothing beyond `ThetaCertCore`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_ThetaCertCore

namespace ThetaSieve
set_option maxRecDepth 100000

def PrimData74.s0 : Seg := ⟨588650822501545982291308738, 588650822501545993454285301, 31916035, 4096, [], 588808915892863270210610037, 588808915892863281376585336⟩
def PrimData74.s1 : Seg := ⟨588808915892863270210610037, 588808915892863281376585336, 31924227, 4096, [], 588950437066798574147706504, 588950437066798585316364639⟩
def PrimData74.s2 : Seg := ⟨588950437066798574147706504, 588950437066798585316364639, 31932419, 4096, [], 589104072706579258253880021, 589104072706579269425451625⟩
def PrimData74.s3 : Seg := ⟨589104072706579258253880021, 589104072706579269425451625, 31940611, 4096, [], 589253248105701470293616492, 589253248105701481468016732⟩
def PrimData74.s4 : Seg := ⟨589253248105701470293616492, 589253248105701481468016732, 31948803, 4096, [], 589405931984106661904097662, 589405931984106673081393152⟩
def PrimData74.s5 : Seg := ⟨589405931984106661904097662, 589405931984106673081393152, 31956995, 4096, [], 589560849507196319503301138, 589560849507196330683534614⟩
def PrimData74.s6 : Seg := ⟨589560849507196319503301138, 589560849507196330683534614, 31965187, 4096, [], 589711306625830136457413525, 589711306625830147640499941⟩
def PrimData74.s7 : Seg := ⟨589711306625830136457413525, 589711306625830147640499941, 31973379, 4096, [], 589862403438163080081098099, 589862403438163091267049601⟩
def PrimData74.s8 : Seg := ⟨589862403438163080081098099, 589862403438163091267049601, 31981571, 4096, [], 590009996037381518942999867, 590009996037381530131749630⟩
def PrimData74.s9 : Seg := ⟨590009996037381518942999867, 590009996037381530131749630, 31989763, 4096, [], 590161097331805356967569302, 590161097331805368159184151⟩
def PrimData74.s10 : Seg := ⟨590161097331805356967569302, 590161097331805368159184151, 31997955, 4096, [], 590315707487913136229663588, 590315707487913147424210348⟩

def PrimData74.segs : List Seg := [PrimData74.s0, PrimData74.s1, PrimData74.s2, PrimData74.s3, PrimData74.s4, PrimData74.s5, PrimData74.s6, PrimData74.s7, PrimData74.s8, PrimData74.s9, PrimData74.s10]

end ThetaSieve


