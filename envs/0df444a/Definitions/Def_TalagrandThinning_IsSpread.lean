-- Prove2me | Definitions.Def_TalagrandThinning_IsSpread
-- name    : TalagrandThinning_IsSpread
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:02.632807+00:00
-- url     : https://prove2.me/theorems/d1702831-be13-4d8c-851f-c8eaceae1b40
-- title:
--   $q$-spread law on the cube
-- statement:
--   A measure $\nu$ on $\{0,1\}^N$ is **$q$-spread** if a random set $J\sim\nu$ satisfies
--
--   $$\mathbb P(I\subseteq J)\le q^{|I|}\qquad\text{for every } I\subseteq[N].$$
--
--   This is the $R$-spread condition of the literature with $q=1/R$: a spread law cannot concentrate on sets containing any fixed $I$.
--
--   **Formalization Note** $I$ ranges over every finite subset, including $\emptyset$. The bound is `ENNReal.ofReal (q ^ |I|)`. The definition does not bundle "probability measure" or $0<q<1$; every theorem that uses it assumes both, as the paper does.
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), Definition 1.1, eq. (1.1), p.2

import Mathlib
import Definitions.Def_TalagrandThinning_Cube

set_option autoImplicit false

open MeasureTheory

namespace TalagrandThinning

/-- `q`-spreadness of a law on the cube, eq. (1.1): a random set `J ∼ ν` satisfies
`P(I ⊆ J) ≤ q^{|I|}` for every `I ⊆ [N]`
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, Definition 1.1, eq. (1.1), p.2).

**Formalization Note** `I` ranges over all `Finset (Fin N)`, including `I = ∅` (where the bound
is `1`). The bound is `ENNReal.ofReal (q ^ |I|)`, which is the real number `q^{|I|}` whenever
`q ≥ 0`. The definition does not require `ν` to be a probability measure, nor `0 < q < 1`; the
theorems that use it assume both, as the paper does. -/
def IsSpread {N : ℕ} (q : ℝ) (ν : Measure (Cube N)) : Prop :=
  ∀ I : Finset (Fin N), ν {J : Cube N | ∀ i ∈ I, J i = true} ≤ ENNReal.ofReal (q ^ I.card)

end TalagrandThinning


