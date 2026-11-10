-- Prove2me | Definitions.Def_NearOptOWF_KeyedFam
-- name    : NearOptOWF_KeyedFam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:46.875214+00:00
-- url     : https://prove2.me/theorems/c8a56ae5-ef8f-47f9-8e25-dea022cbaa71
-- title:
--   Keyed family of functions $\{f_k : \{0,1\}^n \to \{0,1\}^m\}$
-- statement:
--   A **keyed family of functions** with security parameter $\lambda$, input length $n$ and output length $m$: a key $k$ is a uniform string of $\ell(\lambda, n, m)$ bits, and $f_k$ is given by a circuit with $n$ inputs.
--
--   The input and output lengths are explicit, because the construction uses pseudorandom functions $\{0,1\}^n \to \{0,1\}^{10n}$ and $\{0,1\}^{10n} \to \{0,1\}^m$ at the same security parameter.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 4.10, p.17 (PDF p.19); Lemma 3.5, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF

open LaconicBarrier

/-- A **keyed family of functions** `{f_k : {0,1}ⁿ → {0,1}ᵐ}` with security parameter `λ` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…),
Lemma 4.10, p.17 (PDF p.19): "`H = {f : {0,1}ⁿ → {0,1}ᵐ}` is a sub-exponentially secure PRF";
Lemma 3.5, p.9 (PDF p.11)): a key is a uniform string of `keyLen λ n m` bits, and `circ λ n m k` is a
circuit with `n` inputs computing `f_k`.

**Formalization Note** The input length `n` and output length `m` are explicit parameters, because
the construction uses PRFs `{0,1}ⁿ → {0,1}^{10n}` and `{0,1}^{10n} → {0,1}ᵐ` at the same `λ` (p.14). -/
structure KeyedFam where
  /-- the key length at `(λ, n, m)` -/
  keyLen : ℕ → ℕ → ℕ → ℕ
  /-- the circuit computing `f_k` -/
  circ : (lam n m : ℕ) → (Fin (keyLen lam n m) → Bool) → MCircuit n

end NearOptOWF


