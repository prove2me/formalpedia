-- Prove2me | Definitions.Def_AuctionMatroidInt_roundUp
-- name    : AuctionMatroidInt_roundUp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:22.240175+00:00
-- url     : https://prove2.me/theorems/62980579-46f9-4419-8e89-2fdf997c4af5
-- title:
--   Rounding up to a power of $1+\varepsilon$ and the value set $\Lambda$
-- statement:
--   Fix $\varepsilon>0$. For $u\in\mathbb R$ define
--
--   $$
--   \lceil u\rceil_{1+\varepsilon}=\begin{cases}(1+\varepsilon)^{\lceil\log_{1+\varepsilon}u\rceil}&u>0,\\ 0&u\le 0,\end{cases}
--   $$
--
--   which rounds $u>0$ up to the nearest (integer, possibly negative) power of $1+\varepsilon$. Let $\Lambda=\{0\}\cup\{(1+\varepsilon)^k : k\in\mathbb Z\}$, the set of values of the rounding.
--
--   Rounding the utilities to $\Lambda$ is what makes every decrease of a utility a decrease by at least a factor $1+\varepsilon$, which drives the round-by-round progress of the algorithm.
--
--   **Formalization Note** $\lceil\cdot\rceil$ is `Int.ceil`, $\log_{1+\varepsilon}$ is `Real.logb (1 + ε)`, the power is `zpow`. `InLambda ε x` states $x\in\Lambda$.
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), §5.1.1, p.20 (PDF p.22)

import Mathlib

namespace AuctionMatroidInt

/-- **Rounding up to a power of `1 + ε`, `⌈u⌉_{1+ε}`.**
Huang, Kobayashi, Terao (manuscript, sha256 2e12cb4a…), §5.1.1, p.20: "For u > 0, we define
⌈u⌉_{1+ε} := (1+ε)^{⌈log_{1+ε} u⌉}, which rounds u up to the nearest power of 1+ε, and
⌈u⌉_{1+ε} := 0 for u ≤ 0."

**Formalization Note.** `⌈·⌉` is `Int.ceil`, `log_{1+ε}` is `Real.logb (1 + ε)`, and the power
is the integer power `zpow`, so the exponent may be negative, as on p.20 ("k may be
negative"). -/
noncomputable def roundUp (ε u : ℝ) : ℝ :=
  if 0 < u then (1 + ε) ^ (⌈Real.logb (1 + ε) u⌉ : ℤ) else 0

/-- **The value set `Λ = {0} ∪ {(1 + ε)^k | k ∈ ℤ}`** (§5.1.1, p.20): `InLambda ε x` says
`x ∈ Λ`. -/
def InLambda (ε x : ℝ) : Prop :=
  x = 0 ∨ ∃ k : ℤ, x = (1 + ε) ^ k

end AuctionMatroidInt


