-- Prove2me | Definitions.Def_PPSLattice_PPS_FullyCompact
-- name    : PPSLattice_PPS_FullyCompact
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:31.878731+00:00
-- url     : https://prove2.me/theorems/4084a342-c64d-49c4-926d-f54789001e03
-- title:
--   Full compactness of a PPS scheme
-- statement:
--   A PPS scheme is **fully compact** if one polynomial in $(\lambda,\lceil\log N\rceil)$ bounds the length of every output of its algorithms: there is $c$ such that for all $\lambda\ge1$ and $1\le N\le2^\lambda$, every $\mathrm{crs}$ output by $\mathrm{GSetup}(1^\lambda,N)$, every $\mathrm{msk}$ output by $\mathrm{MSKGen}(\mathrm{crs})$, every ciphertext output by $\mathrm{pkEnc}(i)$ or $\mathrm{skEnc}(\mathrm{msk},i,\mu)$ ($i\in[N]$, $\mu\in\{0,1\}^\lambda$) and every key output by $\mathrm{KGen}(\mathrm{msk},S)$ ($S\subseteq[N]$) has length at most
--   $$(\lambda+\lceil\log_2N\rceil+2)^c.$$
--
--   **Formalization Note** "$|\mathrm{crs}|=\mathrm{poly}_{\mathrm{crs}}(\lambda,\log N)$" is read as an upper bound by a fixed polynomial; one exponent for the four objects is equivalent to four polynomials. Lengths are bounded on the whole support, not with high probability.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, Full Compactness, p.18

import Mathlib
import Definitions.Def_PPSLattice_PPS
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- **Full compactness** of a PPS scheme: one polynomial in `(λ, ⌈log N⌉)` bounds, for all `λ ≥ 1` and
`1 ≤ N ≤ 2^λ`, the length of every possible output: every crs of `GSetup(1^λ, N)`, every msk of
`MSKGen(crs)`, every ciphertext of `pkEnc(i)` and of `skEnc(msk, i, µ)` (`i ∈ [N]`, `µ ∈ {0,1}^λ`) and
every key of `KGen(msk, S)` (`S ⊆ [N]`): the bound is `(λ + ⌈log₂ N⌉ + 2)^c` for one constant `c`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, Full Compactness, p.18 ("There exist polynomials poly_crs, poly_msk, poly_ct,
poly_sk such that ∀λ, N ≤ 2^λ, S ⊆ [N], |crs| = poly_crs(λ, log N), …").

**Formalization Note.** `λ` and `N` are positive integers (§3, p.15: "We denote … the set of positive integers by N"). "= poly(λ, log N)" is read as an upper bound by a fixed polynomial (the
paper's own sizes, such as `nm⌈log N⌉⌈log q⌉`, are not polynomials in the real `log N`). One
exponent `c` for all four objects is equivalent to four polynomials. `⌈log₂ N⌉ = Nat.clog 2 N`.
Lengths are bounded on the whole support of each algorithm, not with high probability. -/
def PPS.FullyCompact (E : PPS) : Prop :=
  ∃ c : ℕ, ∀ lam N : ℕ, 1 ≤ lam → 1 ≤ N → N ≤ 2 ^ lam →
    ∀ crs ∈ (E.gsetup lam N).support, crs.length ≤ (lam + Nat.clog 2 N + 2) ^ c ∧
      ∀ msk ∈ (E.mskgen lam N crs).support, msk.length ≤ (lam + Nat.clog 2 N + 2) ^ c ∧
        (∀ i ∈ Finset.Icc 1 N, ∀ ct ∈ (E.pkEnc lam N crs i).support,
          ct.length ≤ (lam + Nat.clog 2 N + 2) ^ c) ∧
        (∀ i ∈ Finset.Icc 1 N, ∀ mu : Str, mu.length = lam →
          ∀ ct ∈ (E.skEnc lam N crs msk i mu).support,
            ct.length ≤ (lam + Nat.clog 2 N + 2) ^ c) ∧
        (∀ S ⊆ Finset.Icc 1 N, ∀ sk ∈ (E.kgen lam N crs msk S).support,
          sk.length ≤ (lam + Nat.clog 2 N + 2) ^ c)

end PPSLattice


