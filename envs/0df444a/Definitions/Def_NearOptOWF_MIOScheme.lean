-- Prove2me | Definitions.Def_NearOptOWF_MIOScheme
-- name    : NearOptOWF_MIOScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:20.818792+00:00
-- url     : https://prove2.me/theorems/dcc12ead-1e05-4978-a5b2-50a75b7ff2f9
-- title:
--   Obfuscator for multi-output circuits (syntax)
-- statement:
--   An **obfuscator** takes a security parameter $\lambda$, a circuit $C$ with $n$ inputs and $\mathrm{coins}(\lambda, n, |C|)$ uniform coins $\rho$, and returns a circuit $i\mathcal O(1^\lambda, C; \rho)$ with the same $n$ inputs.
--
--   The construction of the paper obfuscates circuits $\{0,1\}^n \to \{0,1\}^m$ with many output bits, so circuits are the published multi-output circuits.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.4, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF

open LaconicBarrier

/-- The syntax of an **obfuscator for (multi-output) circuits** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.4, p.9
(PDF p.11): "A PPT algorithm iO is an indistinguishability obfuscator for circuits"): on security
parameter `λ`, a circuit `C` with `n` inputs and coins `ρ ∈ {0,1}^{coins(λ, n, |C|)}`, it returns the
circuit `obf λ n C ρ = iO(1^λ, C; ρ)` with the same `n` inputs.

**Formalization Note** Circuits are the published multi-output circuits `LaconicBarrier.MCircuit`,
because the construction obfuscates circuits `{0,1}ⁿ → {0,1}ᵐ` (Eq. (1), p.11). The number of coins
depends on `λ`, `n` and the size of `C`. -/
structure MIOScheme where
  /-- the number of coins at `(λ, n, |C|)` -/
  coins : ℕ → ℕ → ℕ → ℕ
  /-- the obfuscator `iO(1^λ, C; ρ)` -/
  obf : (lam n : ℕ) → (C : MCircuit n) → (Fin (coins lam n C.size) → Bool) → MCircuit n

end NearOptOWF


