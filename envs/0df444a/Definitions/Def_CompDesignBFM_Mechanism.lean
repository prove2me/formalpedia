-- Prove2me | Definitions.Def_CompDesignBFM_Mechanism
-- name    : CompDesignBFM_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:30.968903+00:00
-- url     : https://prove2.me/theorems/289f149a-0b0a-4de2-b40b-3500b0dbaec2
-- title:
--   Deterministic direct mechanism
-- statement:
--   A **deterministic direct mechanism** on the agents $N=\{1,\dots,n\}$ assigns to every bid vector $b$ a selected set $S(b)\subseteq N$ and payments $p_i(b)$. It reads only the bids, so it cannot depend on the private costs. This is the object all the properties of budget-feasible mechanism design are stated for.
--
--   **Formalization Note** Agents are `Fin n`, sets are `Finset (Fin n)`, bids are `Fin n → ℝ`; nonnegativity of bids is in the quantifiers of the properties.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1 (PDF 3)

import Mathlib

namespace CompDesignBFM

/-- A deterministic direct mechanism on the agents `Fin n` (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1, PDF 3):
an allocation `alloc b ⊆ N` and payments `pay b i`, both functions of the bid vector `b` only.
**Formalization Note.** Agents are `Fin n` and sets are `Finset (Fin n)`. Bids live in `Fin n → ℝ`; the
nonnegativity `b i ≥ 0` of the paper is in the quantifiers of the properties below. The costs are not an
argument, so a mechanism is cost-oblivious by type. -/
structure Mechanism (n : ℕ) where
  /-- The allocated set at a bid vector. -/
  alloc : (Fin n → ℝ) → Finset (Fin n)
  /-- The payment to an agent at a bid vector. -/
  pay : (Fin n → ℝ) → Fin n → ℝ

end CompDesignBFM


