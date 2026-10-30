-- Prove2me | Definitions.Def_NisanRonen_Rounding_IsDominant
-- name    : NisanRonen_Rounding_IsDominant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:21:14.450991+00:00
-- url     : https://prove2.me/theorems/ba7e5716-b326-4a5f-91ef-da539360c0d2
-- title:
--   Dominant strategy under the rounding mechanism
-- statement:
--   Fix an allocation algorithm $f$ on rounded instances, a grid step $\delta$ and $0 < a < b$. A strategy $\sigma$ is **dominant** for agent $i$ of type $t^i$ if $\sigma$ is admissible and, for every profile $s$ of strategies of the other agents whose declarations lie in $[a,b]^k$, and every admissible strategy $\sigma'$ of agent $i$,
--
--   $$
--   u^i(s^{-i}, \sigma') \le u^i(s^{-i}, \sigma),
--   $$
--
--   where $u^i$ is agent $i$'s utility under the rounding mechanism.
--
--   **Formalization Note** The other agents' executions are not constrained; agent $i$'s utility depends on them only through their declarations, so this is the same as quantifying over their admissible strategies.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Definition 3, p. 172 (PDF p. 7), first bullet: "for all possible strategies of the other agents a^{−i}, a^i maximizes agent i's utility"

import Mathlib
import Definitions.Def_NisanRonen_Rounding_utility
import Definitions.Def_NisanRonen_Rounding_IsValid

namespace NisanRonen.Rounding

/-- **Dominant strategy of agent `i` of type `t^i` under the rounding mechanism**
(Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), Definition 3, p. 172: "for all possible strategies of the other agents
a^{−i}, a^i maximizes agent i's utility, i.e., for every a′^i ∈ A^i … v^i(t^i, o) + p^i ≥
v^i(t^i, o′) + p′^i"), for the mechanism of Definition 34 run with allocation algorithm `f` and
grid `δ`, in the bounded problem with type space `[a, b]^k`.

`σ` is admissible for `i`, and for every profile `s` of the other agents whose declarations lie
in `[a, b]^k` and every admissible alternative `σ'`, agent `i`'s utility with `σ` is at least
its utility with `σ'`.

**Formalization Note** Profiles are `Fin n → Strategy n k`; agent `i`'s entry is replaced by
`Function.update`. The other agents' executions are quantified without constraint: agent `i`'s
utility depends on them only through the declarations (the bonus uses declared times for the
other agents' tasks), so this is equivalent to restricting them to admissible executions. -/
def IsDominant {n k : ℕ} [NeZero n] (f : List (Fin n → ℕ) → List (Fin n)) (δ a b : ℝ)
    (i : Fin n) (ti : Fin k → ℝ) (σ : Strategy n k) : Prop :=
  IsValid a b ti i σ ∧
    ∀ s : Fin n → Strategy n k,
      (∀ l, l ≠ i → ∀ j, a ≤ (s l).decl j ∧ (s l).decl j ≤ b) →
      ∀ σ' : Strategy n k, IsValid a b ti i σ' →
        utility f δ (Function.update s i σ') i ≤ utility f δ (Function.update s i σ) i

end NisanRonen.Rounding


