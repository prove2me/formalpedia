-- Prove2me | Definitions.Def_BlockchainNV_PiStarO
-- name    : BlockchainNV_PiStarO
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:42:28.165927+00:00
-- url     : https://prove2.me/theorems/9c99fb3a-e6de-4287-abf2-3ab5be73c80e
-- title:
--   Traditional retailer's optimal expected profit $\Pi^*_o$
-- statement:
--   The traditional retailer's optimal expected profit is
--
--   $$
--   \Pi^*_o = \sup_{q \in \mathbb R} G(q),
--   $$
--
--   where $G(q)$ is her expected profit from ordering $q$ against the compound demand $D = \lambda + \beta X + \varepsilon$. Theorem 1 compares it with the blockchain retailer's $\mathbb E_X[\Pi^*(X)]$.
--
--   **Formalization Note** The supremum is Lean's `sSup` of the range of $G$ in $\mathbb R$. That it is finite and attained is a theorem, not part of the definition.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, §2.1 and Theorem 1, p.8 (PDF p.8)

import Mathlib
import Definitions.Def_BlockchainNV_tradExpProfit

open MeasureTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor*, Management Science (2024),
doi:10.1287/mnsc.2021.02949, §2.1 and Theorem 1, p.8 (PDF p.8): `Π*_o`, the traditional
retailer's optimal expected profit: the supremum over all order quantities `q ∈ ℝ` of her
expected profit `tradExpProfit θ P X ε q` against the compound demand `D = λ + βX + ε`.

**Formalization Note.** Defined as `sSup` of the range in `ℝ`. That the supremum is a finite
maximum is part of the theorem `traditional_optimal_profit`, not of the definition. -/
noncomputable def PiStarO (θ : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X ε : Ω → ℝ) : ℝ :=
  sSup (Set.range (tradExpProfit θ P X ε))

end BlockchainNV


