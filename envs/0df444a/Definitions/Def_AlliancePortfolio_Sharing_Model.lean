-- Prove2me | Definitions.Def_AlliancePortfolio_Sharing_Model
-- name    : AlliancePortfolio_Sharing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:14.466882+00:00
-- url     : https://prove2.me/theorems/217430d2-9473-4d26-a00f-e8cf824cd41d
-- title:
--   §2, §4.1, pp. 7–9, 21–23 — single-alliance Nash payoffs (1), the Table 1 coalition game, net Shapley payoffs, feasibility
-- statement:
--   This file sets up the two models of Arora, Belenzon and Patacconi: a single knowledge-sharing alliance between a focal firm $F$ and a partner $A$ (§2), and an alliance portfolio in which $F$ has two partners $A$ and $B$ (§4.1).
--
--   **Single alliance.** Each firm pays a private cost $\tfrac12 I$ to share knowledge, so $I > 0$ is the total cost. After knowledge sharing, implementing the project together creates value $V$, while premature termination gives $F$ and $A$ their ex post outside options $\pi_F$ and $\pi_A$, with $V \ge \pi_F + \pi_A$. Under equal-weight Nash bargaining, firm $i \in \{F, A\}$ obtains (eq. (1))
--
--   $$\Pi_i = \pi_i + \tfrac12\,[V - \pi_F - \pi_A] - \tfrac12 I .$$
--
--   Firm $i$'s **knowledge-sharing constraint** is $\Pi_i \ge 0$ (eq. (2)). Knowledge sharing in the single alliance is called *feasible* when both constraints hold: $\Pi_F \ge 0$ and $\Pi_A \ge 0$.
--
--   **Alliance portfolio.** The players are $N = \{F, A, B\}$. After knowledge sharing in both alliances, the value $v(S)$ of each coalition $S$ is given by Table 1 (p. 22):
--
--   $$v(FAB) = 2V + b,\quad v(FA) = v(FB) = V + \pi_F + s^{Imp},\quad v(AB) = 0,\quad v(F) = 2\pi_F - s^{RB},\quad v(A) = v(B) = 0,$$
--
--   together with $v(\emptyset) = 0$. Here $b$ is the synergy between $A$ and $B$ in implementation, $s^{Imp}$ measures substitutability in implementation and $s^{RB}$ substitutability in rival benefits. The gross payoffs $\varphi_F, \varphi_A, \varphi_B$ are the Shapley value of $v$,
--
--   $$\varphi_i = \sum_{S \subseteq N\setminus\{i\}} \frac{|S|!\,(|N|-|S|-1)!}{|N|!}\,\bigl(v(S\cup\{i\}) - v(S)\bigr).$$
--
--   $F$ pays $\tfrac12 I$ in each of its two alliances, so the net payoffs are $\Pi_F = \varphi_F - I$, $\Pi_A = \varphi_A - \tfrac12 I$ and $\Pi_B = \varphi_B - \tfrac12 I$, and knowledge sharing in the portfolio is *feasible* when $\Pi_i \ge 0$ for every $i \in \{F, A, B\}$.
--
--   Finally, the **standing assumptions** of the portfolio model are $I > 0$, $b \ge 0$, $s^{Imp} \in [0, V - \pi_F]$ and $s^{RB} \in [0, \pi_F]$; the partners' outside options are normalised to $\pi_A = \pi_B = 0$.
--
--   These objects are the common vocabulary of every statement of the mission: Proposition 1, equations (9)–(11) and Proposition 6.
--
--   **Formalization Note** Players are `Fin 3` with $F = 0$, $A = 1$, $B = 2$. The game is written as: a coalition without $F$ is worth $0$; a coalition containing $F$ is worth $2\pi_F - s^{RB}$, $V + \pi_F + s^{Imp}$ or $2V + b$ according as it has one, two or three members, which is exactly Table 1 with $v(\emptyset)=0$ (the convention footnote 22 uses). The Shapley value is the platform's published `Supermodularity.Cooperative.ShapleyValue`, not a closed form, and feasibility is defined from the payoffs, not from the inequalities (5) or (11). "Feasible" means that the knowledge-sharing constraints hold; the coordination issue of footnote 10 is ignored, as in the paper. The standing assumptions are bundled as `Standing V I b πF sImp sRB`; $\pi_A = \pi_B = 0$ is built into the game.
-- source:
--   Arora, Belenzon & Patacconi, Knowledge sharing in alliances and alliance portfolios, author manuscript of January 24, 2020 (Management Science 2021, doi:10.1287/mnsc.2020.3614), pp. 7–9, 21–23, §2 eq. (1)–(2), §4.1 Table 1

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue

namespace AlliancePortfolio.Sharing

/-! The models of Arora, Belenzon & Patacconi (author manuscript of January 24, 2020):
the single F–A alliance of §2 (pp. 7–9, eq. (1)–(2)) and the alliance portfolio of §4.1
(pp. 21–23, Table 1 and the Shapley value). -/

/-- The focal firm `F` (player `0` of `Fin 3`). -/
abbrev F : Fin 3 := 0
/-- The first non-focal partner `A` (player `1` of `Fin 3`). -/
abbrev A : Fin 3 := 1
/-- The second non-focal partner `B` (player `2` of `Fin 3`). -/
abbrev B : Fin 3 := 2

/-- Eq. (1), p. 9: in a single alliance with value `V`, ex post outside options `πF`, `πA` and
total knowledge-sharing cost `I`, the Nash-bargaining payoff of a firm with outside option `πi`
is `Π_i = π_i + ½[V − π_F − π_A] − ½I`. -/
noncomputable def singlePayoff (V I πF πA πi : ℝ) : ℝ :=
  πi + (1 / 2) * (V - πF - πA) - (1 / 2) * I

/-- Constraint (2), p. 9, for both firms of a single alliance: knowledge sharing is privately
profitable for `F` and for `A`, i.e. `Π_F ≥ 0` and `Π_A ≥ 0`. -/
def SingleFeasible (V I πF πA : ℝ) : Prop :=
  0 ≤ singlePayoff V I πF πA πF ∧ 0 ≤ singlePayoff V I πF πA πA

/-- Table 1, p. 22: the coalitional values after knowledge sharing in both alliances,
`v(FAB) = 2V + b`, `v(FA) = v(FB) = V + π_F + s^Imp`, `v(AB) = 0`, `v(F) = 2π_F − s^RB`,
`v(A) = v(B) = 0`, and the convention `v(∅) = 0` (footnote 22). Every coalition without `F`
is worth `0`; a coalition containing `F` is classified by its size. -/
noncomputable def game (V b πF sImp sRB : ℝ) : Finset (Fin 3) → ℝ :=
  fun S =>
    if F ∈ S then
      (if S.card = 1 then 2 * πF - sRB
       else if S.card = 2 then V + πF + sImp
       else 2 * V + b)
    else 0

/-- The (gross) payoffs `φ_F, φ_A, φ_B` (p. 22): the Shapley value of the Table 1 game. -/
noncomputable def φ (V b πF sImp sRB : ℝ) : Fin 3 → ℝ :=
  Supermodularity.Cooperative.ShapleyValue (game V b πF sImp sRB)

/-- Net payoffs in the portfolio (p. 23): `Π_F = φ_F − I`, `Π_A = φ_A − ½I`, `Π_B = φ_B − ½I`. -/
noncomputable def netPayoff (V I b πF sImp sRB : ℝ) (i : Fin 3) : ℝ :=
  if i = F then φ V b πF sImp sRB i - I else φ V b πF sImp sRB i - (1 / 2) * I

/-- Knowledge sharing in both alliances is privately profitable for all partners (p. 23):
`Π_i ≥ 0` for `i = F, A, B`. -/
def PortfolioFeasible (V I b πF sImp sRB : ℝ) : Prop :=
  ∀ i : Fin 3, 0 ≤ netPayoff V I b πF sImp sRB i

/-- The standing assumptions of §2 and §4.1: `½I > 0` (p. 7), `b ≥ 0` (p. 21),
`s^Imp ∈ [0, V − π_F]` (p. 21) and `s^RB ∈ [0, π_F]` (p. 22). -/
def Standing (V I b πF sImp sRB : ℝ) : Prop :=
  0 < I ∧ 0 ≤ b ∧ 0 ≤ sImp ∧ sImp ≤ V - πF ∧ 0 ≤ sRB ∧ sRB ≤ πF

end AlliancePortfolio.Sharing


