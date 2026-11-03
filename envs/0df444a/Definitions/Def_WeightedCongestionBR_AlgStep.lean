-- Prove2me | Definitions.Def_WeightedCongestionBR_AlgStep
-- name    : WeightedCongestionBR_AlgStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:09.696927+00:00
-- url     : https://prove2.me/theorems/165bf086-eb90-4ae6-8686-add29f728fc1
-- title:
--   Algorithm 1 as a step relation
-- statement:
--   Algorithm 1 is encoded as a nondeterministic step relation on configurations $(i,s,F)$, started at $(0,s_{\mathrm{init}},\emptyset)$:
--
--   1. **Line 6–7, move.** In phase $0$, a player $u$ with $C_u(s)\ge b_1$ that has an $(\alpha+1/p)$-move switches to a best response.
--   2. **Line 6, exit.** In phase $0$, if no player satisfies this guard, go to phase $1$.
--   3. **Line 9–10, move.** In phase $1\le i\le m-1$, a player $u\notin F$ with
--
--   $$
--   \big[C_u(s)\in[b_{i+1},b_i)\ \wedge\ u\text{ has an }(\alpha+1/p)\text{-move}\big]\ \vee\ \big[C_u(s)\ge b_i\ \wedge\ u\text{ has a }p\text{-move}\big]
--   $$
--
--   switches to a best response.
--   4. **Line 9 exit, Line 11.** In phase $1\le i\le m-1$, if no player outside $F$ satisfies this guard, add $\{u\notin F: C_u(s)\ge b_i\}$ to $F$ and go to phase $i+1$.
--
--   A configuration of phase $m$ has no successor: its state is the output. Line 12 only enlarges $N_{\mathrm{fixed}}$.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load. The existential choices of Lines 6 and 9 and the tie-break of $\mathcal{BR}_u$ are universally quantified: every selection is a step. The number $m$ of phases is a parameter; the statements require $m\ge1$ and $c_{\max}/c_{\min}\le g^m$ instead of $m=\log(c_{\max}/c_{\min})$.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Algorithm 1, Lines 4–12, p.14

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_WeightedCongestionBR_HasRhoMove
import Definitions.Def_WeightedCongestionBR_IsBestResponse
import Definitions.Def_WeightedCongestionBR_alphaC
import Definitions.Def_WeightedCongestionBR_pConst
import Definitions.Def_WeightedCongestionBR_bnd
import Definitions.Def_WeightedCongestionBR_Config
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

open Classical in
/-- One step of **Algorithm 1** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Algorithm 1, Lines 4–11, p.14), as a nondeterministic step
relation on configurations, started from `(0, s_init, ∅)`:

1. `move0` (Lines 6–7): in phase `0`, a player `u` with `C_u(s) ≥ b_1` that has an
   `(α + 1/p)`-move switches to a best response `t ∈ BR_u(s)`.
2. `end0` (Line 6 exits): in phase `0`, no player satisfies that guard; go to phase `1`.
3. `moveI` (Lines 9–10): in phase `1 ≤ i ≤ m − 1`, a player `u ∉ N_fixed` with
   `[C_u(s) ∈ [b_{i+1}, b_i) ∧ u has an (α + 1/p)-move] ∨ [C_u(s) ≥ b_i ∧ u has a p-move]`
   switches to a best response.
4. `endI` (Lines 9 exits, 11): in phase `1 ≤ i ≤ m − 1`, no player of `N ∖ N_fixed` satisfies the
   guard; add `{u ∈ N ∖ N_fixed : C_u(s) ≥ b_i}` to `N_fixed` and go to phase `i + 1`.

A configuration of phase `m` has no successor: the algorithm returns its state. Line 12 only
enlarges `N_fixed` and does not change the state.

**Formalization Note** The existential choices of Lines 6 and 9 and the tie-break of `BR_u` are
universally quantified: every selection gives a step. Here `m` is an arbitrary natural number,
which the statements constrain (`1 ≤ m`, `c_max/c_min ≤ g^m`) instead of fixing
`m = log(c_max/c_min)` as Line 1 does. -/
inductive AlgStep {n r : ℕ} (G : Game n r) (d m : ℕ) (sinit : G.Profile) :
    Config G → Config G → Prop
  | move0 (c : Config G) (u : Fin n) (t : G.Strategy u) :
      c.phase = 0 →
      bnd G d m sinit 1 ≤ privateCost G c.s u →
      HasRhoMove G (alphaC d + 1 / pConst d) c.s u →
      IsBestResponse G c.s u t →
      AlgStep G d m sinit c ⟨0, Function.update c.s u t, c.F⟩
  | end0 (c : Config G) :
      c.phase = 0 →
      (∀ u : Fin n, ¬ (bnd G d m sinit 1 ≤ privateCost G c.s u ∧
        HasRhoMove G (alphaC d + 1 / pConst d) c.s u)) →
      AlgStep G d m sinit c ⟨1, c.s, c.F⟩
  | moveI (c : Config G) (u : Fin n) (t : G.Strategy u) :
      1 ≤ c.phase → c.phase + 1 ≤ m → u ∉ c.F →
      ((bnd G d m sinit (c.phase + 1) ≤ privateCost G c.s u ∧
          privateCost G c.s u < bnd G d m sinit c.phase ∧
          HasRhoMove G (alphaC d + 1 / pConst d) c.s u) ∨
        (bnd G d m sinit c.phase ≤ privateCost G c.s u ∧ HasRhoMove G (pConst d) c.s u)) →
      IsBestResponse G c.s u t →
      AlgStep G d m sinit c ⟨c.phase, Function.update c.s u t, c.F⟩
  | endI (c : Config G) :
      1 ≤ c.phase → c.phase + 1 ≤ m →
      (∀ u : Fin n, u ∉ c.F →
        ¬ ((bnd G d m sinit (c.phase + 1) ≤ privateCost G c.s u ∧
            privateCost G c.s u < bnd G d m sinit c.phase ∧
            HasRhoMove G (alphaC d + 1 / pConst d) c.s u) ∨
          (bnd G d m sinit c.phase ≤ privateCost G c.s u ∧ HasRhoMove G (pConst d) c.s u))) →
      AlgStep G d m sinit c
        ⟨c.phase + 1, c.s,
          c.F ∪ Finset.univ.filter (fun u => u ∉ c.F ∧ bnd G d m sinit c.phase ≤ privateCost G c.s u)⟩

end WeightedCongestionBR


