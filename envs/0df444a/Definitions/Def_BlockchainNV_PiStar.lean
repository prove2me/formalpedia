-- Prove2me | Definitions.Def_BlockchainNV_PiStar
-- name    : BlockchainNV_PiStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:42:31.808094+00:00
-- url     : https://prove2.me/theorems/58d041f9-cbfc-4ae4-a8ae-c3e6e0b31863
-- title:
--   Blockchain retailer's conditional optimal expected profit $\Pi^*(x)$
-- statement:
--   For a realized freshness state $x$, the blockchain retailer's optimal expected profit conditional on $X = x$ is
--
--   $$
--   \Pi^*(x) = \sup_{q \in \mathbb R} G_x(q),
--   $$
--
--   where $G_x(q)$ is her expected profit from ordering $q$ given $X = x$. Theorem 1 evaluates its expectation $\mathbb E_X[\Pi^*(X)]$.
--
--   **Formalization Note** The supremum is Lean's `sSup` of the range of $q \mapsto G_x(q)$ in $\mathbb R$. That the supremum is finite and attained is a theorem (eq. (3)), not part of the definition.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, §2.1, eq. (3), p.8 (PDF p.8)

import Mathlib
import Definitions.Def_BlockchainNV_condExpProfit

open MeasureTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor*, Management Science (2024),
doi:10.1287/mnsc.2021.02949, §2.1, eq. (3), p.8 (PDF p.8): `Π*(x)`, the blockchain retailer's
optimal expected profit conditional on `X = x`: the supremum over all order quantities `q ∈ ℝ` of
her expected profit `condExpProfit θ P ε x q`.

**Formalization Note.** Defined as `sSup` of the range in `ℝ`. That the supremum is a finite
maximum (so that the `sSup` is not Lean's junk value `0` of an unbounded set) is part of the
theorem `conditional_optimal_profit`, not of the definition. -/
noncomputable def PiStar (θ : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ε : Ω → ℝ) (x : ℝ) : ℝ :=
  sSup (Set.range (condExpProfit θ P ε x))

end BlockchainNV


