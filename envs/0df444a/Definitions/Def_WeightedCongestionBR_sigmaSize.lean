-- Prove2me | Definitions.Def_WeightedCongestionBR_sigmaSize
-- name    : WeightedCongestionBR_sigmaSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:20.657842+00:00
-- url     : https://prove2.me/theorems/4bad12da-9e83-4ac3-b5bc-cbde977cad87
-- title:
--   Input size $\sigma(\Gamma)$
-- statement:
--   The size of a rational instance with $n$ players and $|E|$ resources:
--
--   $$
--   \sigma(\Gamma)=n+|E|+\sum_{u}\ell(w_u)+\sum_{e}\sum_{\nu=0}^d\ell(a_{e,\nu}).
--   $$
--
--   **Formalization Note** The strategy sets and the initial state are not counted. The paper wants the bound even for succinctly represented games (p.4), with best responses from an oracle (footnote 15), so leaving them out only strengthens a polynomial bound.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Theorem 4, p.18

import Mathlib
import Definitions.Def_WeightedCongestionBR_RatData
import Definitions.Def_WeightedCongestionBR_bitLen
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- The **input size** of a rational instance (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Theorem 4, p.18):
`σ(Γ) := n + |E| + ∑_u ℓ(w_u) + ∑_{e, ν ≤ d} ℓ(a_{e,ν})`.

**Formalization Note** The strategy sets and `s_init` are not counted: the bound must hold even for
succinctly represented games (p.4), with best responses supplied by an oracle (footnote 15,
p.15). Counting them would only weaken the claim. -/
def sigmaSize {n r d : ℕ} (D : RatData n r d) : ℕ :=
  n + r + ∑ u, bitLen (D.w u) + ∑ e, ∑ ν, bitLen (D.a e ν)

end WeightedCongestionBR


