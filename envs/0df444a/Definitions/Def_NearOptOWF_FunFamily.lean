-- Prove2me | Definitions.Def_NearOptOWF_FunFamily
-- name    : NearOptOWF_FunFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:28.023313+00:00
-- url     : https://prove2.me/theorems/fa6177a9-fedf-4088-87e0-c38cf389eec7
-- title:
--   Sampleable family of functions $\{0,1\}^n \to \{0,1\}^{m(n)}$
-- statement:
--   A **sampleable family of functions**: for each input length $n$, a sampler turns $\mathrm{coins}(n)$ uniform bits $\rho$ into a circuit $f_\rho$ with $n$ inputs, the sampled function. The candidate one-way function family $\mathcal H = \{i\mathcal O(F)\}$ of Eq. (1) is such a family.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1 and Eq. (1), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF

open LaconicBarrier

/-- A **sampleable family of functions** `{f : {0,1}ⁿ → {0,1}^{m(n)}}` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1, p.11
(PDF p.13): "a family of … one-way functions", Eq. (1): "`H = {iO(F) : {0,1}ⁿ → {0,1}ᵐ}`"): for each
input length `n`, the sampler turns `coins n` uniform bits `ρ` into a circuit `samp n ρ` with `n`
inputs, the sampled function.

**Formalization Note** The output length `m(n)` is a parameter of the type; the requirement that the
sampled circuits have `m(n)` outputs is part of `FunFamily.IsEfficient`. -/
structure FunFamily (m : ℕ → ℕ) where
  /-- the number of sampling coins at input length `n` -/
  coins : ℕ → ℕ
  /-- the sampled function, as a circuit -/
  samp : (n : ℕ) → (Fin (coins n) → Bool) → MCircuit n

end NearOptOWF


