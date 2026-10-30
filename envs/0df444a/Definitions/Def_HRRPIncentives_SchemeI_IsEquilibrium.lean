-- Prove2me | Definitions.Def_HRRPIncentives_SchemeI_IsEquilibrium
-- name    : HRRPIncentives_SchemeI_IsEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:16:13.928011+00:00
-- url     : https://prove2.me/theorems/81aec9df-a6a1-4705-8667-0f58e7998156
-- title:
--   Pure-strategy Nash equilibrium of the HRRP-I game
-- statement:
--   A profile $\big((r_1,c_1),\dots,(r_N,c_N)\big)$ is an equilibrium of the one-round HRRP-I game if every action lies in the box $B$ and no hospital can increase its objective $\Pi_i$ by unilaterally changing its own pair:
--
--   $$\Pi_i\big((r_i,c_i),x_{-i}\big)\ \ge\ \Pi_i\big((r,c),x_{-i}\big)\qquad\text{for all } i \text{ and all } (r,c)\in B .$$
--
--   The deviation changes $r_i$ and $c_i$ jointly, anywhere in the box, while the other hospitals' actions, and hence hospital $i$'s yardsticks, stay fixed. A symmetric equilibrium is an equilibrium in which all hospitals choose the same pair; an asymmetric one has two hospitals choosing different pairs.
--
--   **Formalization Note** The equilibrium is the Nash equilibrium itself, not a solution of first-order conditions.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, unnumbered, p. 9 ("the (pure-strategy) Nash equilibrium in a one-round game"), with the box of p. 10 and the objective (1), (9)

import Mathlib
import Definitions.Def_HRRPIncentives_SchemeI_box
import Definitions.Def_HRRPIncentives_SchemeI_payoff

namespace HRRPIncentives.SchemeI

/-- A pure-strategy Nash equilibrium of the one-round HRRP-I game among `N` hospitals: every
hospital's action lies in the box, and no hospital can raise its HRRP-I payoff (1), (9) by
changing its own pair `(r_i, c_i)` to any other point of the box while the other hospitals'
actions (and hence its own yardsticks (6)) stay fixed.

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, unnumbered, p. 9 ("the (pure-strategy) Nash equilibrium in a one-round game"),
with the action box of p. 10 and the payoff (1), (9).

**Formalization Note.** A deviation is a joint change of `(r_i, c_i)` over the whole box,
written `Function.update x i y`; the equilibrium is not defined by first-order conditions.
A symmetric profile is a constant one, `fun _ => p`. -/
def IsEquilibrium (lam rmin rmax cmin cmax : ℝ) (R : ℝ × ℝ → ℝ) {N : ℕ}
    (x : Fin N → ℝ × ℝ) : Prop :=
  (∀ i, x i ∈ box rmin rmax cmin cmax) ∧
    ∀ i, ∀ y ∈ box rmin rmax cmin cmax,
      payoff lam R (Function.update x i y) i ≤ payoff lam R x i

end HRRPIncentives.SchemeI


