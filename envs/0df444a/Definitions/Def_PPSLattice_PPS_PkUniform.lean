-- Prove2me | Definitions.Def_PPSLattice_PPS_PkUniform
-- name    : PPSLattice_PPS_PkUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:54.141827+00:00
-- url     : https://prove2.me/theorems/b0251487-8f38-4871-b7b4-70d8867186f4
-- title:
--   Public-key ciphertexts are uniformly random strings
-- statement:
--   There is a length $L(\lambda,N)$ such that for all $\lambda\ge1$, $N\ge1$, every $\mathrm{crs}$ output by $\mathrm{GSetup}(1^\lambda,N)$ and every $i\in[N]$, $\mathrm{pkEnc}(i)$ is uniformly distributed on $\{0,1\}^{L(\lambda,N)}$.
--
--   This is the "Moreover" clause of Theorem 1.1 and Remark 4.7; it gives a transparent setup in applications.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 1.1, p.4; Remark 4.7, p.22

import Mathlib
import Definitions.Def_PPSLattice_PPS
import Definitions.Def_AvgPHETH_uniformDist
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- **Public-key ciphertexts are uniformly random strings**: there is a length `L(λ, N)` such that,
for every `λ ≥ 1`, every `N ≥ 1`, every crs that `GSetup(1^λ, N)` can output and every `i ∈ [N]`, the law of
`pkEnc(i)` is the uniform law on `{0,1}^{L(λ,N)}`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 1.1, p.4 ("Moreover, public-key ciphertexts are uniformly random strings"); Remark 4.7,
p.22 ("pkEnc in Construction 4.6 outputs uniformly random strings of appropriate length"). -/
def PPS.PkUniform (E : PPS) : Prop :=
  ∃ L : ℕ → ℕ → ℕ, ∀ lam N : ℕ, 1 ≤ lam → 1 ≤ N → ∀ crs ∈ (E.gsetup lam N).support,
    ∀ i ∈ Finset.Icc 1 N, E.pkEnc lam N crs i = AvgPHETH.uniformDist (L lam N)

end PPSLattice


