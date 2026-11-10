-- Prove2me | Definitions.Def_PPSLattice_PPS_Correct
-- name    : PPSLattice_PPS_Correct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:23.385295+00:00
-- url     : https://prove2.me/theorems/47eb2c46-f8e0-4467-b637-699176ac7f1b
-- title:
--   Perfect correctness of a PPS scheme
-- statement:
--   A PPS scheme is **correct** if for every $\lambda\in\mathbb N$ (a positive integer, as in §3), every $N\le2^\lambda$, every $S\subseteq[N]$, every $i\in S$ and every $\mu\in\{0,1\}^\lambda$,
--   $$\Pr\bigl[\mu=\mathrm{Decode}(S,\mathrm{sk}_S,i,\mathrm{ct})\bigr]=1,$$
--   over $\mathrm{crs}\leftarrow\mathrm{GSetup}(1^\lambda,N)$, $\mathrm{msk}\leftarrow\mathrm{MSKGen}(\mathrm{crs})$, $\mathrm{ct}\leftarrow\mathrm{skEnc}(\mathrm{msk},i,\mu)$, $\mathrm{sk}_S\leftarrow\mathrm{KGen}(\mathrm{msk},S)$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, Correctness, p.18

import Mathlib
import Definitions.Def_PPSLattice_PPS
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- **Perfect correctness** of a PPS scheme: for every `λ ≥ 1`, every `N ≤ 2^λ`, every set
`S ⊆ [N]`, every `i ∈ S` and every message `µ ∈ {0,1}^λ`,
`Pr[µ = Decode(S, sk_S, i, ct)] = 1` over `crs ← GSetup(1^λ, N)`, `msk ← MSKGen(crs)`,
`ct ← skEnc(msk, i, µ)` and `sk_S ← KGen(msk, S)`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, Correctness, p.18.

**Formalization Note.** `[N] = Finset.Icc 1 N`; `i ∈ S ⊆ [N]` forces `N ≥ 1`. `λ ∈ N` ranges over the positive integers (§3, p.15: "We denote … the set of positive integers by N"). -/
def PPS.Correct (E : PPS) : Prop :=
  ∀ lam N : ℕ, 1 ≤ lam → N ≤ 2 ^ lam → ∀ S ⊆ Finset.Icc 1 N, ∀ i ∈ S, ∀ mu : Str, mu.length = lam →
    ((E.gsetup lam N).bind fun crs => (E.mskgen lam N crs).bind fun msk =>
      (E.skEnc lam N crs msk i mu).bind fun ct => (E.kgen lam N crs msk S).map fun sk =>
        decide (E.decode lam N crs S sk i ct = some mu)) true = 1

end PPSLattice


