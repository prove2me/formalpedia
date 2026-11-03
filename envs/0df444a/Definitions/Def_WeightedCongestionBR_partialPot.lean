-- Prove2me | Definitions.Def_WeightedCongestionBR_partialPot
-- name    : WeightedCongestionBR_partialPot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:12.170142+00:00
-- url     : https://prove2.me/theorems/8c71fedf-1f0f-4b6c-bfe7-0962d050afaf
-- title:
--   Partial potential $\Phi_R(s)$, (8)
-- statement:
--   The partial potential of a group $R$ at state $s$ is
--
--   $$
--   \Phi_R(s)=\Phi(s)-\Phi^{N\setminus R}(s)=\sum_{e\in E}\Big[\phi_e(x_e(s))-\phi_e(x_{N\setminus R,e}(s))\Big].
--   $$
--
--   It measures the share of the potential due to the players of $R$; Lemma 5 shows it is within a factor $\alpha$ of $C_R(s)$.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load. The subscript $\Phi_R$ (partial) and the superscript $\Phi^R$ (subgame) are different objects.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, eq. (8), p.12

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_WeightedCongestionBR_subgamePot
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- The **partial potential** of a group `R` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, eq. (8), p.12):
`Φ_R(s) := Φ(s) − Φ^{N∖R}(s) = ∑_e [φ_e(x_e(s)) − φ_e(x_{N∖R,e}(s))]`.

**Formalization Note** Subscript `Φ_R` (partial) and superscript `Φ^R` (subgame, `subgamePot`) are
different objects; `Rᶜ` is the complement in `Fin n`. -/
noncomputable def partialPot {n r : ℕ} (G : Game n r) (R : Finset (Fin n)) (s : G.Profile) : ℝ :=
  subgamePot G Finset.univ s - subgamePot G Rᶜ s

end WeightedCongestionBR


