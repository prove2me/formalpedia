-- Prove2me | Definitions.Def_WeightedCongestionBR_IsGroupEq
-- name    : WeightedCongestionBR_IsGroupEq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:04.756208+00:00
-- url     : https://prove2.me/theorems/73beb370-0ee9-4d85-b990-85f3230944f1
-- title:
--   $\rho$-approximate equilibrium for a group
-- statement:
--   For $\rho\ge1$ and a group of players $R\subseteq N$, a state $s$ is a **$\rho$-equilibrium for $R$** if no player of $R$ has a $\rho$-move:
--
--   $$
--   C_u(s)\le \rho\, C_u(s'_u,s_{-u})\qquad\text{for all }u\in R,\ s'_u\in S_u .
--   $$
--
--   For $R=N$ these are the $\rho$-equilibria of the game, the set $\mathcal Q^\Gamma_\rho$.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, §2, p.6

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- `s` is a **`ρ`-approximate equilibrium for the group `R`** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, §2, p.6): no player of `R` has
a `ρ`-move, i.e. `C_u(s) ≤ ρ · C_u(s'_u, s_{-u})` for all `u ∈ R` and `s'_u ∈ S_u`. For `R = N` this
is a `ρ`-equilibrium of the game, and the set of these is `Q_ρ^Γ`.

**Formalization Note** The whole player set is `Finset.univ`. -/
def IsGroupEq {n r : ℕ} (G : Game n r) (ρ : ℝ) (R : Finset (Fin n)) (s : G.Profile) : Prop :=
  ∀ u ∈ R, ∀ t : G.Strategy u, privateCost G s u ≤ ρ * privateCost G (Function.update s u t) u

end WeightedCongestionBR


