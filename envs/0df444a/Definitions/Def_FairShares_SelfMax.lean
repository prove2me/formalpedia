-- Prove2me | Definitions.Def_FairShares_SelfMax
-- name    : FairShares_SelfMax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:39.356619+00:00
-- url     : https://prove2.me/theorems/91424300-3aab-4e13-acee-3c35a5abb11c
-- title:
--   Self-maximizing share for a class (Definition 3)
-- statement:
--   A share $s$ is **self-maximizing for the class $\mathcal C$** if for every number $m$ of goods and every number $n\ge1$ of agents, for all $v,v'\in\mathcal C_m$,
--   $$
--   \hat s(v,n)\ge \hat s_v(v')
--   $$
--   (see `FairShares.SelfMaxAt`).
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, Definition 3, p.12

import Mathlib
import Definitions.Def_FairShares_SelfMaxAt

namespace FairShares

/-- **Self-maximizing share for a class (Definition 3).**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, Definition 3, p.12: "for every set M of items and number of agents n, for every true
valuation v ∈ C and every report v′ ∈ C it holds that ŝ_v(v) = ŝ(v, n) ≥ ŝ_v(v′)".

`SelfMax C s`: `SelfMaxAt (C m) (s m n)` for every `m` and every `n ≥ 1`.

**Formalization Note.** Shares and classes as in `FairShares.IsShare`; `n ≥ 1`. -/
def SelfMax (C : (m : ℕ) → Set (Finset (Fin m) → ℝ))
    (s : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ) : Prop :=
  ∀ m n : ℕ, 1 ≤ n → SelfMaxAt (C m) (s m n)

end FairShares


