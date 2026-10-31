-- Prove2me | Definitions.Def_CongestionApproxPNE_IsApproxPNE
-- name    : CongestionApproxPNE_IsApproxPNE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:16:38.741103+00:00
-- url     : https://prove2.me/theorems/c33616e7-b5d4-49df-a527-62d7c0822e46
-- title:
--   $\alpha$-approximate pure Nash equilibrium ($\alpha$-PNE), (1)
-- statement:
--   In a weighted congestion game, a strategy profile $s$ is an **$\alpha$-approximate pure Nash equilibrium** ($\alpha$-PNE) if no player can lower her cost by more than a factor $\alpha$ through a unilateral change of strategy:
--
--   $$
--   C_i(s)\le \alpha\cdot C_i(s_i',s_{-i})\qquad\text{for all } i\in N \text{ and all } s_i'\in S_i. \tag{1}
--   $$
--
--   Here $(s_i',s_{-i})$ is the profile $s$ with player $i$'s strategy replaced by $s_i'$. For $\alpha=1$ this is an exact pure Nash equilibrium. The paper uses the notion for $\alpha\ge 1$.
--
--   **Formalization Note** $(s_i',s_{-i})$ is `Function.update s i t`. The requirement $\alpha\ge 1$ is not built into the predicate; every theorem that uses it assumes $1\le\alpha$.
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, §2, display (1), p.3 (PDF p.4)

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_CongestionApproxPNE_playerCost

set_option autoImplicit false
open scoped NNReal

namespace CongestionApproxPNE

open HarksKlimm.Consistency

/-- **α-approximate pure Nash equilibrium (α-PNE)**, display (1).
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, arXiv:2002.07466v3, §2, p.3: "An outcome
s will be called α-approximate (pure Nash) equilibrium (α-PNE), where α ≥ 1, if no player can
unilaterally improve her cost by more than a factor of α. Formally:
Ci(s) ≤ α · Ci(s′i, s−i) for all i ∈ N and all s′i ∈ Si. (1)"

**Formalization Note** `(s′ᵢ, s₋ᵢ)` is `Function.update s i t`. The paper's standing requirement
`α ≥ 1` is not part of this predicate; every theorem using it states `1 ≤ α` as a hypothesis. -/
def IsApproxPNE {n m : ℕ} (G : Game n m) (α : ℝ) (s : G.Profile) : Prop :=
  ∀ (i : Fin n) (t : G.Strategy i), playerCost G s i ≤ α * playerCost G (Function.update s i t) i

end CongestionApproxPNE


