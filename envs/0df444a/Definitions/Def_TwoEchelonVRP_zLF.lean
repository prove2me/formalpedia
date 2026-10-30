-- Prove2me | Definitions.Def_TwoEchelonVRP_zLF
-- name    : TwoEchelonVRP_zLF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:29:46.005668+00:00
-- url     : https://prove2.me/theorems/a553d3e3-04b1-41d4-b7e7-b49d5383ff3c
-- title:
--   LP relaxation LF and its optimal cost $z(LF)$
-- statement:
--   **LF** is the LP relaxation of formulation F: the linear constraints (2)–(8) are kept and the integrality constraints (9)–(11) are replaced by
--
--   $$
--   0 \le x_{kl} \le 1, \qquad 0 \le y_r \le 1, \qquad q_{kr} \ge 0 .
--   $$
--
--   $z(LF)$ is the minimum of the objective (1) over the feasible solutions of LF. It is a lower bound on $z(F)$, and Theorem 2 compares it with the Lagrangean bound of relaxation RF.
--
--   **Formalization Note** The bound $x_{kl} \le 1$ is implied by (2) and $x \ge 0$; the bound $y_r \le 1$ is not implied and is part of LF. $z(LF)$ is the infimum in the extended reals of the objective values, $+\infty$ when LF is infeasible. The module declares `LFFeasible` and `zLF`.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §3, unnumbered, p. 301 ('Let LF be the LP-relaxation of formulation F, and let z(LF) be its optimal solution cost')

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_Route2
import Definitions.Def_TwoEchelonVRP_Route1
import Definitions.Def_TwoEchelonVRP_LinearConstraints
import Definitions.Def_TwoEchelonVRP_zF

namespace TwoEchelonVRP

/-- **Feasible solutions of LF, the LP relaxation of formulation F.**
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §3, unnumbered, p. 301: "Let LF be the LP-relaxation of
formulation F". The linear constraints (2)–(8) (`LinearConstraints`) are kept, and the integrality
constraints (9)–(11) are replaced by their continuous relaxations
`0 ≤ x_kl ≤ 1`, `0 ≤ y_r ≤ 1`, `q_kr ≥ 0`.

**Formalization Note.** This is the standard LP relaxation of binary and nonnegative-integer
variables. The bound `x_kl ≤ 1` is implied by (2) and `x ≥ 0`; the bound `y_r ≤ 1` is not implied
and is part of LF. -/
def LFFeasible {ns nc : ℕ} (I : Instance ns nc) (x : Fin ns → Route2 I → ℝ)
    (y : Route1 I → ℝ) (qd : Route1 I → Fin ns → ℝ) : Prop :=
  LinearConstraints I x y qd ∧
    (∀ k l, 0 ≤ x k l ∧ x k l ≤ 1) ∧
    (∀ r, 0 ≤ y r ∧ y r ≤ 1) ∧
    (∀ r k, 0 ≤ qd r k)

/-- **The LP-relaxation bound** `z(LF)`, "its optimal solution cost" (Baldacci et al., Operations
Research 61(2) (2013), §3, p. 301): the minimum of objective (1) over `LFFeasible`.

**Formalization Note.** `z(LF)` is the infimum in `EReal` of the objective values of the feasible
solutions; it is `⊤` (`+∞`) when LF is infeasible. -/
noncomputable def zLF {ns nc : ℕ} (I : Instance ns nc) : EReal :=
  sInf ((fun v : ℝ => (v : EReal)) ''
    {v | ∃ x y qd, LFFeasible I x y qd ∧ v = objF I x y})

end TwoEchelonVRP


