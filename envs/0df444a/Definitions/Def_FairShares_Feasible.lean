-- Prove2me | Definitions.Def_FairShares_Feasible
-- name    : FairShares_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:12.183271+00:00
-- url     : https://prove2.me/theorems/49fdf829-c62e-4900-9a17-8d874396413e
-- title:
--   Feasible share for a class
-- statement:
--   A share $s$ is **feasible for the class $\mathcal C$** if for every number $m$ of goods and every number $n\ge 1$ of agents, every profile of $n$ valuations in $\mathcal C_m$ admits an allocation giving each agent $i$ a bundle of value at least $s_{m,n}(v_i)$ (see `FairShares.FeasibleAt`).
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, §3.1, p.10

import Mathlib
import Definitions.Def_FairShares_FeasibleAt

namespace FairShares

/-- **Feasible share for a class.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, §3.1, p.10 (see `FairShares.FeasibleAt`).

`Feasible C s`: for every number `m` of items and every number `n ≥ 1` of agents, every profile of
`n` valuations in `C m` admits an allocation giving each agent `i` a bundle of value at least
`s m n (vs i)`.

**Formalization Note.** Shares and classes as in `FairShares.IsShare`; `n ≥ 1`. -/
def Feasible (C : (m : ℕ) → Set (Finset (Fin m) → ℝ))
    (s : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ) : Prop :=
  ∀ m n : ℕ, 1 ≤ n → FeasibleAt n (C m) (s m n)

end FairShares


