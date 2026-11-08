-- Prove2me | Definitions.Def_CompDesignBFM_IsPriority
-- name    : CompDesignBFM_IsPriority
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:35.752201+00:00
-- url     : https://prove2.me/theorems/be04718d-6449-46c2-8bd2-e6bce68b9104
-- title:
--   Fixed priority on sets, with the empty set first
-- statement:
--   Ties among sets are resolved by a fixed priority order, independent of the bids, with $\emptyset$ first.
--
--   **Formalization Note** The order is an injective rank $r$ on $2^N$ with $r(\emptyset)\le r(S)$ for all $S$; a smaller rank has priority.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Remark 2.1, p.12 (PDF 14)

import Mathlib

namespace CompDesignBFM

/-- A fixed priority order on `2^N` with `∅` first (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Remark 2.1, p.12, PDF 14), encoded as an
injective rank; a smaller rank has priority. -/
def IsPriority {n : ℕ} (r : Finset (Fin n) → ℕ) : Prop :=
  Function.Injective r ∧ ∀ S, r ∅ ≤ r S

end CompDesignBFM


