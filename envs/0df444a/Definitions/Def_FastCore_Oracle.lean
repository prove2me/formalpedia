-- Prove2me | Definitions.Def_FastCore_Oracle
-- name    : FastCore_Oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:45.144986+00:00
-- url     : https://prove2.me/theorems/b45ad691-8224-41cf-9aef-1e99c4552f5a
-- title:
--   Answer table of WIN-ORAC
-- statement:
--   An **oracle** on $n$ bidders is a map sending required truncations $\{\pi_i\}_{i\in N}$ to a pair: a real value and a subset of $N$.
--
--   **Formalization Note** The bids are not an input here: they are fixed inside the oracle, so the algorithm can reach them only through queries. This is what gives the oracle-call count its meaning. Whether an oracle is correct for given bids is `IsWinOrac`. The paper's "any set in $\mathcal W(\cdot)$" becomes a universal quantifier over oracles in the theorems.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 6, p.14

import Mathlib

namespace FastCore

/-- A black-box answer table for WIN-ORAC (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 6, p.14): it maps the required
truncations `π` to a value and a set of bidders.

**Formalization Note.** The bids are fixed inside `q`, so the algorithm sees them only through
queries; this is what makes the oracle count meaningful. "Any set in `W(·)`" (line 4 of Algorithm 1)
is the universal quantifier over `q` in the theorems. -/
abbrev Oracle (n : ℕ) : Type := (Fin n → ℝ) → ℝ × Finset (Fin n)

end FastCore


