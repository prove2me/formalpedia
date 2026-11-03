-- Prove2me | Definitions.Def_WeightedCongestionBR_PoASet
-- name    : WeightedCongestionBR_PoASet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:15.579369+00:00
-- url     : https://prove2.me/theorems/0fc0f227-6c92-4d2c-a110-bbbc921a3b30
-- title:
--   Ratios defining the $\rho$-PoA of degree $d$
-- statement:
--   The $\rho$-approximate Price of Anarchy of degree $d$ is
--
--   $$
--   \mathrm{PoA}_d(\rho)=\sup_\Gamma \max_{s\in\mathcal Q^\Gamma_\rho}\frac{C(s)}{C(s^*)},\qquad s^*\in\operatorname*{argmin}_s C(s),
--   $$
--
--   the supremum over all weighted polynomial congestion games $\Gamma$ of degree $d$. This definition is the set of ratios $C(s)/C(s^*)$ over all such games, all $\rho$-equilibria $s$ and all minimizers $s^*$ of the social cost; $\mathrm{PoA}_d(\rho)$ is its supremum.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load. Degree $d$ is `CongestionApproxPNE.IsPolyGame d`. Games whose optimal social cost is $0$ are left out, since their ratio $0/0$ is undefined. Statements take the supremum with `IsLUB` or bound every element.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, §2, pp.6–7

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_WeightedCongestionBR_groupCost
import Definitions.Def_WeightedCongestionBR_IsGroupEq
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- The set of ratios whose supremum is the **`ρ`-approximate Price of Anarchy of degree `d`**
(Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, §2, pp.6–7): `PoA_d(ρ) := sup_Γ max_{s ∈ Q_ρ^Γ} C(s)/C(s*)`, with `s* ∈ argmin_s C(s)`, over all
polynomial weighted congestion games `Γ` of degree `d`. An element is a ratio `C(s)/C(s*)` for a game
`Γ` of degree `d`, a `ρ`-equilibrium `s` of `Γ` and a minimizer `s*` of the social cost.

**Formalization Note** The supremum is taken through `IsLUB` in the statements. Games are
`HarksKlimm.Consistency.Game n r` for every `n r` (both positive, weights positive) with
`CongestionApproxPNE.IsPolyGame d`. Games with `C(s*) = 0` are left out: their ratio is `0/0`, which
the paper does not define. -/
def PoASet (d : ℕ) (ρ : ℝ) : Set ℝ :=
  {q | ∃ (n r : ℕ) (G : Game n r), CongestionApproxPNE.IsPolyGame d G ∧
    ∃ s sStar : G.Profile, IsGroupEq G ρ Finset.univ s ∧
      (∀ s' : G.Profile, groupCost G Finset.univ sStar ≤ groupCost G Finset.univ s') ∧
      0 < groupCost G Finset.univ sStar ∧
      q = groupCost G Finset.univ s / groupCost G Finset.univ sStar}

end WeightedCongestionBR


