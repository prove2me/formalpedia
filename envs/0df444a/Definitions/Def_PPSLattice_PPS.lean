-- Prove2me | Definitions.Def_PPSLattice_PPS
-- name    : PPSLattice_PPS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:29.944838+00:00
-- url     : https://prove2.me/theorems/9b46e8ef-986c-406b-94e8-6b33370b1b8a
-- title:
--   Programmable pseudorandom set sampler (PPS) scheme: syntax
-- statement:
--   A **PPS scheme** for the message space $\mathcal M_\lambda=\{0,1\}^\lambda$ consists of six algorithms:
--
--   1. $\mathrm{GSetup}(1^\lambda,N)\to\mathrm{crs}$, with $N$ in binary;
--   2. $\mathrm{MSKGen}\to\mathrm{msk}$;
--   3. $\mathrm{pkEnc}(i)\to\mathrm{ct}$ for $i\in[N]$;
--   4. $\mathrm{KGen}(\mathrm{msk},S)\to\mathrm{sk}_S$ for $S\subseteq[N]$;
--   5. $\mathrm{skEnc}(\mathrm{msk},i,\mu)\to\mathrm{ct}$ for $\mu\in\mathcal M_\lambda$;
--   6. the deterministic $\mathrm{Decode}(S,\mathrm{sk}_S,i,\mathrm{ct})\to\mu'\in\mathcal M_\lambda\cup\{\perp\}$.
--
--   All algorithms after GSetup take $\mathrm{crs}$ implicitly.
--
--   **Formalization Note** The randomized algorithms are given by their output laws (`PMF`), Decode by a function; every algorithm receives $\lambda$, $N$ and $\mathrm{crs}$ explicitly. crs, keys, ciphertexts and messages are bit strings; $[N]=\{1,\dots,N\}$; $\perp$ is `none`. The message length $\lambda$ is imposed by the properties, not by the type.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.1, Syntax, p.17; Construction 4.6, p.21

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- A **programmable pseudorandom set sampler (PPS) scheme** for the message space
`M_λ = {0,1}^λ`, given by the laws of its algorithms (every algorithm also receives `λ` and `N`):
1. `gsetup λ N`: `GSetup(1^λ, N) → crs`;
2. `mskgen λ N crs`: `MSKGen → msk`;
3. `pkEnc λ N crs i`: `pkEnc(i) → ct` for an index `i ∈ [N]`;
4. `kgen λ N crs msk S`: `KGen(msk, S) → sk_S` for a set `S ⊆ [N]`;
5. `skEnc λ N crs msk i µ`: `skEnc(msk, i, µ) → ct` for `µ ∈ M_λ`;
6. `decode λ N crs S sk i ct`: the deterministic `Decode(S, sk_S, i, ct) → µ′ ∈ M_λ ∪ {⊥}`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.1, Syntax, p.17; message space `M_λ = {0,1}^λ` from Construction 4.6, p.21.

**Formalization Note.** crs, keys, ciphertexts and messages are bit strings; `[N] = {1, …, N}`;
sets are `Finset ℕ`; `⊥` is `none`. "The following algorithms takes crs implicitly" is encoded by
passing `crs`, `λ` and `N` to every algorithm. Messages of length `λ` are fixed by the properties
(`PPS.Correct`, the games), not by the type. -/
structure PPS where
  gsetup : ℕ → ℕ → PMF Str
  mskgen : ℕ → ℕ → Str → PMF Str
  pkEnc : ℕ → ℕ → Str → ℕ → PMF Str
  kgen : ℕ → ℕ → Str → Str → Finset ℕ → PMF Str
  skEnc : ℕ → ℕ → Str → Str → ℕ → Str → PMF Str
  decode : ℕ → ℕ → Str → Finset ℕ → Str → ℕ → Str → Option Str

end PPSLattice


