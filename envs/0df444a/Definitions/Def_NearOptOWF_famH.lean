-- Prove2me | Definitions.Def_NearOptOWF_famH
-- name    : NearOptOWF_famH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:50:20.176245+00:00
-- url     : https://prove2.me/theorems/1b05e06b-8fde-4473-b116-46c99d3cbd01
-- title:
--   Candidate family $\mathcal H = \{i\mathcal O(F)\}$
-- statement:
--   The candidate one-way function family of Eq. (1),
--   $$
--   \mathcal H = \{\, i\mathcal O(F) : \{0,1\}^n \to \{0,1\}^m \,\},
--   $$
--   padded as in the paper: at input length $n$, sample a key $k$ of the puncturable PRF $F$ at security parameter $\lambda(n)$ with input length $n$ and output length $m(n)$, and coins $\rho$ of $i\mathcal O$, and output $i\mathcal O(1^{\lambda(n)}, \mathrm{pad}_{S(n)}(F_k); \rho)$.
--
--   **Formalization Note** The security parameter $\lambda(n)$ ("a sufficiently large polynomial $\lambda = \mathrm{poly}(n, m)$") and the padded size $S(n)$ are parameters.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Eq. (1), p.11 (PDF p.13), with the padding on pp.11–12

import Mathlib
import Definitions.Def_NearOptOWF_FunFamily
import Definitions.Def_NearOptOWF_obfPad
import Definitions.Def_NearOptOWF_PPRF

namespace NearOptOWF

open LaconicBarrier

/-- The candidate family **`H = {iO(F) : {0,1}ⁿ → {0,1}ᵐ}`** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Eq. (1), p.11 (PDF p.13), with
the padding of pp.11–12): at input length `n`, sample a key `k` of the puncturable PRF `F` at
`(λ(n), n, m(n))` and coins `ρ` of `iO`, and output `iO(1^{λ(n)}, padTo S(n) F_k; ρ)`.

**Formalization Note** The security parameter `λ(n)` and the padded size `S(n)` are parameters of
the construction ("`λ = poly(n, m)`", "pad F with sufficiently many dummy gates"). -/
def famH (O : MIOScheme) (F : PPRF) (lam S m : ℕ → ℕ) : FunFamily m where
  coins n := F.keyLen (lam n) n (m n) + O.coins (lam n) n (S n)
  samp n ρ := obfPad O (lam n) n (S n)
    (F.circ (lam n) n (m n) (fun i => ρ (Fin.castAdd _ i))) (fun j => ρ (Fin.natAdd _ j))

end NearOptOWF


