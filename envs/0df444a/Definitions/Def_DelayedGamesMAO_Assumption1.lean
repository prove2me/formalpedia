-- Prove2me | Definitions.Def_DelayedGamesMAO_Assumption1
-- name    : DelayedGamesMAO_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:02.728232+00:00
-- url     : https://prove2.me/theorems/9158da75-bc7f-4190-921c-b0cc20f05a76
-- title:
--   Assumption 1 — $G$-Lipschitzness and $L$-smoothness
-- statement:
--   Let $X,Y$ be the players' action sets and $g^x,g^y$ their loss-gradient maps. **Assumption 1** holds with constants $G,L$ if $G>0$, $L>0$ and, for each player $p\in\{x,y\}$ and all $x,x'\in X$, $y,y'\in Y$,
--   $$
--   \|g^p(x,y)\|_*\le G,\qquad \|g^p(x,y)-g^p(x',y')\|_*\le L\bigl(\|x-x'\|+\|y-y'\|\bigr).
--   $$
--   Both gradient maps are bounded and Lipschitz in the joint profile, with the same constants for both players.
--
--   **Formalization Note** The dual norm $\|\cdot\|_*$ is the operator norm on continuous linear functionals.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §3, Assumption 1, p.4

import Mathlib

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Assumption 1** (`G`-Lipschitzness and `L`-smoothness).
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §3, Assumption 1, p.4: "There exist constants `G, L > 0` such that `‖g^p(x, y)‖_* ≤ G` and
`‖g^p(x, y) − g^p(x', y')‖_* ≤ L(‖x − x'‖ + ‖y − y'‖)` for each player `p ∈ {x, y}` and all
`x, x' ∈ X` and `y, y' ∈ Y`."

**Formalization Note.** `gx, gy` are the two loss-gradient maps (see `IsConvexConcaveGame`);
`‖·‖` on a space of continuous linear functionals is the operator norm, i.e. the dual norm. -/
def Assumption1 {EX EY : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] (X : Set EX) (Y : Set EY)
    (gx : EX → EY → EX →L[ℝ] ℝ) (gy : EX → EY → EY →L[ℝ] ℝ) (G L : ℝ) : Prop :=
  0 < G ∧ 0 < L ∧ ∀ x ∈ X, ∀ y ∈ Y,
    ‖gx x y‖ ≤ G ∧ ‖gy x y‖ ≤ G ∧ ∀ x' ∈ X, ∀ y' ∈ Y,
      ‖gx x y - gx x' y'‖ ≤ L * (‖x - x'‖ + ‖y - y'‖) ∧
      ‖gy x y - gy x' y'‖ ≤ L * (‖x - x'‖ + ‖y - y'‖)

end DelayedGamesMAO


