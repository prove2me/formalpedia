-- Prove2me | Definitions.Def_SlottingFees_Game
-- name    : SlottingFees_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:44.302684+00:00
-- url     : https://prove2.me/theorems/1666a88e-cb19-411c-850c-f55218c05c95
-- title:
--   Subgame-perfect equilibria of the slotting-fee game and the equilibrium assortment
-- statement:
--   The full three-stage game (Figure 1, p.9): in stage 1 the retailer announces its product variety $|A|\in\{1,2\}$ (a binding commitment) and a slotting fee $S$; in stage 2 the manufacturers decide whether to participate and set wholesale prices; in stage 3 the retailer chooses its assortment and retail prices.
--
--   A **subgame-perfect equilibrium** consists of an equilibrium of the $|A|=1$ subgame and an equilibrium of the $|A|=2$ subgame. The retailer chooses $|A|=2$ exactly when $\Pi^{|2|}_r>\Pi^{|1|}_r$, and $|A|=1$ on a tie. On the equilibrium path:
--
--   1. the **assortment** $A^*$ is $\{1,2\}$ under high variety and $\{i\}$ for the product carried in the $|A|=1$ subgame otherwise;
--   2. the **slotting fee** $S^*$ is the fee of the chosen subgame;
--   3. the **retailer's profit** $\Pi^*_r$ is the larger of the two subgame values.
--
--   The **main model** is this game. The **benchmark** of §5.2 is the same game in which the retailer sets the slotting fee to zero in the first stage. An assortment is an equilibrium assortment ($A^*$, resp. $\bar A$) when it is the path assortment of some subgame-perfect equilibrium of the main model (resp. benchmark). Propositions 3–5 are stated about these objects.
--
--   **Formalization Note** The tie rule for product variety is a reading, matching the closed boundaries $K\ge\dots$ of the low-variety regions in Propositions 4–5 and Corollary 2. The empty assortment (category not offered) can only occur off $\Omega$.
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, §3 Figure 1, p.9; §4 and §4.3, pp.10, 16; §5.2, p.20

import Mathlib
import Definitions.Def_SlottingFees_Subgame1
import Definitions.Def_SlottingFees_Subgame2

namespace SlottingFees

/-- A strategy profile of the three-stage game (Figure 1, p.9): a profile of the `|A| = 1`
subgame and one of the `|A| = 2` subgame. The retailer's product-variety choice is read off the
two subgame values (`Profile.assortment`). -/
structure Profile where
  low : Play1
  high : Play2

/-- `P` is a subgame-perfect equilibrium of the game (§4, p.10; §4.3, p.16): both subgame
profiles are subgame equilibria. `fees = true` is the main model; `fees = false` is the benchmark
of §5.2, p.20, "a special case of our main model in which the retailer sets the slotting fee to
zero in the first stage". -/
def IsSPE (fees : Bool) (ω : Params) (P : Profile) : Prop :=
  IsEq1 fees ω P.low ∧ IsEq2 fees ω P.high

/-- The assortment on the equilibrium path: `{1, 2}` if the retailer chooses `|A| = 2`;
otherwise `{i}` for the product carried in the `|A| = 1` subgame at the chosen fee (`∅` if the
category is not offered). Product 1 is `0`.

The retailer chooses `|A| = 2` exactly when `Π^{|2|}_r > Π^{|1|}_r` (§4.3, p.16).

**Formalization Note** On a tie `Π^{|2|}_r = Π^{|1|}_r` the retailer takes `|A| = 1`, the
convention behind the boundaries `K ≥ …` of the low-variety regions in Propositions 4–5 and
Corollary 2. -/
noncomputable def Profile.assortment (ω : Params) (P : Profile) : Finset (Fin 2) :=
  if P.low.value ω < P.high.value ω then Finset.univ
  else
    match P.low.outcome P.low.fee with
    | none => ∅
    | some (i, _) => {i}

/-- The retailer's slotting fee on the equilibrium path, `S*` (Proposition 3, (19)). -/
noncomputable def Profile.fee (ω : Params) (P : Profile) : ℝ :=
  if P.low.value ω < P.high.value ω then P.high.fee else P.low.fee

/-- The retailer's equilibrium profit `Π*_r` on the equilibrium path (Proposition 3, (20);
Proposition 4, (21)). -/
noncomputable def Profile.profit (ω : Params) (P : Profile) : ℝ :=
  if P.low.value ω < P.high.value ω then P.high.value ω else P.low.value ω

/-- `A` is an equilibrium assortment of the main model (`fees = true`, `A*`) or of the
benchmark (`fees = false`, `Ā`): it is the assortment on the path of some subgame-perfect
equilibrium. -/
def IsEqAssortment (fees : Bool) (ω : Params) (A : Finset (Fin 2)) : Prop :=
  ∃ P : Profile, IsSPE fees ω P ∧ P.assortment ω = A

end SlottingFees


