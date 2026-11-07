-- Prove2me | Definitions.Def_LocalBreadth_bTop
-- name    : LocalBreadth_bTop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:56.939834+00:00
-- url     : https://prove2.me/theorems/7f0b093e-c9dc-41c9-81b5-0e4f04c723fb
-- title:
--   The topological value b_n^top
-- statement:
--   Let $\mathcal H_K$ be the set of histories beginning at $K$. The **topological value** is
--   $$b_n^{\mathrm{top}}(K)=\sup_{\substack{U\subseteq\mathcal H_K\text{ open}\\(K)\in U}}\ \inf_{H\in U}c_n(H),$$
--   the topological lower limit of $c_n$ at the one-language history $(K)$: the best lower bound on the score that holds throughout a finite-evidence neighborhood.
--
--   **Formalization Note** "Open" means open in the space of all histories, and $U$ is contained in $\mathcal H_K$. Since $\mathcal H_K$ is open and closed, this is the subspace statement.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), eq. (5), p.6; eq. (10), p.17

import Mathlib
import Definitions.Def_LocalBreadth_cScore
import Definitions.Def_LocalBreadth_historyTopology

open scoped Topology

namespace LocalBreadth

/-- `ℋ_K`, the histories beginning at `K` (p.6, p.27). -/
def historiesFrom (X : Set (Set ℤ)) (K : Set ℤ) : Set (History X) := {H | H.first = K}

/-- The topological value, eq. (5), p.6:
`b_n^top(K) = sup_{U ⊆ ℋ_K open, (K) ∈ U} inf_{H ∈ U} c_n(H)`.
Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…).

**Formalization Note.** `U ⊆ ℋ_K` open means open in `ℋ` and contained in `ℋ_K`; `ℋ_K` is open and
closed in `ℋ` (p.27), so this is the subspace statement. `(K) ∈ U` is written through the chain, which
needs no membership proof of `K ∈ X`. Every such `U` is nonempty, and `ℋ_K` itself is one. -/
noncomputable def bTop (X : Set (Set ℤ)) (n : ℕ) (K : Set ℤ) : ℝ :=
  ⨆ U : {U : Set (History X) // IsOpen[historyTopology X] U ∧ U ⊆ historiesFrom X K ∧
      ∃ H ∈ U, H.chain = [K]},
    ⨅ H : U.1, cScore n H.1.chain

end LocalBreadth


