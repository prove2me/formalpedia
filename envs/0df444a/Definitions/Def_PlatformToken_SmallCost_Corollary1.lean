-- Prove2me | Definitions.Def_PlatformToken_SmallCost_Corollary1
-- name    : PlatformToken_SmallCost_Corollary1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:23.335262+00:00
-- url     : https://prove2.me/theorems/42785c33-61e6-4f11-a2ad-7f17a02883fb
-- title:
--   Corollary 1's programs, the effort factors $\beta^B,\beta^\$$, and the functions $h$, $g$, $e^*$ of the proof of Proposition 2
-- statement:
--   The reformulation of both payoffs in Corollary 1, and the auxiliary functions of the proof of Proposition 2.
--
--   **Effort-incentive factors** (40):
--   $$\beta^B=1-\frac{(1-\delta)C(Q)}{d(e,Q)Q},\qquad
--   \beta^\$=\begin{cases}1-\dfrac{(1-\delta)C(Q)}{\mathcal F(e,Q)-(1-\delta)cQ}&\text{if } c\le d(e,Q)-s(Q),\\[2mm]
--   1-\dfrac{(1-\delta)\bigl(C(Q)+cQ-\mathcal F(e,Q)\bigr)}{\delta\mathcal F(e,Q)}&\text{otherwise.}\end{cases}$$
--
--   **Corollary 1's programs.** For $i\in\{\$,B\}$ the feasible pairs $(Q,e)$ satisfy $Q>0$, $e>0$,
--   $$\beta^i\frac{\mathcal F_e(e,Q)}{1-\delta}=\gamma\qquad(38)$$
--   and, for $i=B$ only, $d(e,Q)Q\ge vC(Q)$ (39). The corresponding payoffs are $\max\{0,\sup[\mathcal F(e,Q)/(1-\delta)-cQ-C(Q)-\gamma e]\}$ over these sets (37). The **relaxed** blockchain problem (B.19)–(B.20) drops (39).
--
--   **Functions of the proof of Proposition 2.**
--   $$h(e,Q)=\Bigl(1-\frac{(1-\delta)C(Q)}{d(e,Q)Q}\Bigr)\frac{\mathcal F_e(e,Q)}{1-\delta}-\gamma\qquad(B.21)$$
--   $g(e,Q)$ is (B.26): the same expression with the factor $1-\frac{(1-\delta)C(Q)}{d(e,Q)Q-s(Q)Q-(1-\delta)cQ}$ if $c\le d(e,Q)-s(Q)$, and $1-\frac{(1-\delta)(C(Q)+cQ-d(e,Q)Q+s(Q)Q)}{\delta(d(e,Q)Q-s(Q)Q)}$ otherwise. Finally
--   $$e^*(Q)=\Bigl(\frac{aQ^{1-b}}{(1-\delta)\gamma}\Bigr)^{1/(1-a)},$$
--   the root of $\mathcal F_e(e,Q)/(1-\delta)-\gamma=0$.
--
--   These objects carry the milestones that bridge Lemmas 2–3 to Corollary 1 and assemble Proposition 2.
--
--   **Formalization Note** Decisions of Corollary 1 are pairs `(Q, e)`. The case split of (40) and (B.26) is evaluated at the same $(e,Q)$. A vanishing denominator gives the factor $1$ in Lean; this happens only where $\mathcal F(e,Q)=0$ or $d(e,Q)Q=0$, where the objective is negative. $e^*(Q)$ is defined by its closed form; that it is the argmax of the objective is the milestone `claim_ii_concave`.
-- source:
--   Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard, Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 10, Corollary 1, (37)–(40); p. 19, proof of Proposition 2, (B.19)–(B.21), (B.26); p. 20, (B.29)

import Mathlib
import Definitions.Def_PlatformToken_SmallCost_Setting

set_option autoImplicit false

/-!
# Corollary 1's programs and the functions of the proof of Proposition 2

Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard,
Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 10,
Corollary 1, (37)–(40); p. 19, proof of Proposition 2, (B.19)–(B.21), (B.26); p. 20, (B.29).

**Formalization Note.**
* A decision of Corollary 1 is a pair `(Q, e) : ℝ × ℝ`, in the order of `max_{Q>0, e>0}`.
* `betaTrad` keeps the case split of (40) on `c ≤ d(e,Q) - s(Q)` at the same `(e, Q)`.
* Lean's `x / 0 = 0` makes `β = 1` where a denominator of (40) vanishes; this can only happen
  where `F(e,Q) = 0` or `d(e,Q) Q = 0`, where the objective is negative.
* Payoffs are `max 0 (sSup …)`, as for `PiTrad`, `PiBlock`.
* `estar Q = (a Q^{1-b} / ((1 - δ) γ))^{1/(1-a)}` is the closed-form root of
  `F_e(e,Q)/(1 - δ) - γ = 0`; that it is the printed `argmax_e` of the objective is the
  milestone `claim_ii_concave`, not part of the definition.
-/

namespace PlatformToken.SmallCost

/-- `β^B = 1 - (1 - δ) C(Q) / (d(e,Q) Q)`, (40), p. 10. -/
noncomputable def betaB (p : Params) (e Q : ℝ) : ℝ :=
  1 - (1 - p.δ) * Ccap p Q / (d p e Q * Q)

/-- `β^$`, (40), p. 10: `1 - (1 - δ) C(Q) / (F(e,Q) - (1 - δ) c Q)` if `c ≤ d(e,Q) - s(Q)`,
and `1 - (1 - δ)(C(Q) + cQ - F(e,Q)) / (δ F(e,Q))` otherwise. -/
noncomputable def betaTrad (p : Params) (e Q : ℝ) : ℝ :=
  if p.c ≤ d p e Q - s p Q then
    1 - (1 - p.δ) * Ccap p Q / (F p e Q - (1 - p.δ) * p.c * Q)
  else
    1 - (1 - p.δ) * (Ccap p Q + p.c * Q - F p e Q) / (p.δ * F p e Q)

/-- Corollary 1's feasible set for `i = B`, (38)–(39), p. 10: `Q > 0`, `e > 0`,
`β^B F_e(e,Q)/(1 - δ) = γ`, and `d(e,Q) Q ≥ v C(Q)`. -/
def Cor1FeasibleB (p : Params) : Set (ℝ × ℝ) :=
  {y | 0 < y.1 ∧ 0 < y.2 ∧ betaB p y.2 y.1 * Fe p y.2 y.1 / (1 - p.δ) = p.γ ∧
      p.v * Ccap p y.1 ≤ d p y.2 y.1 * y.1}

/-- Corollary 1's feasible set for `i = $`, (38), p. 10: `Q > 0`, `e > 0`,
`β^$ F_e(e,Q)/(1 - δ) = γ`. -/
def Cor1FeasibleTrad (p : Params) : Set (ℝ × ℝ) :=
  {y | 0 < y.1 ∧ 0 < y.2 ∧ betaTrad p y.2 y.1 * Fe p y.2 y.1 / (1 - p.δ) = p.γ}

/-- The relaxed blockchain problem (B.19)–(B.20), p. 19: Corollary 1's `i = B` program without
(39), i.e. `Q > 0`, `e > 0`, `h(e,Q) = 0`. -/
def Cor1FeasibleBRelaxed (p : Params) : Set (ℝ × ℝ) :=
  {y | 0 < y.1 ∧ 0 < y.2 ∧ betaB p y.2 y.1 * Fe p y.2 y.1 / (1 - p.δ) = p.γ}

/-- `Π^B` written as in Corollary 1, (37)–(39), p. 10. -/
noncomputable def PiCor1B (p : Params) : ℝ :=
  max 0 (sSup ((fun y : ℝ × ℝ => obj p y.2 y.1) '' Cor1FeasibleB p))

/-- `Π^$` written as in Corollary 1, (37)–(38), p. 10. -/
noncomputable def PiCor1Trad (p : Params) : ℝ :=
  max 0 (sSup ((fun y : ℝ × ℝ => obj p y.2 y.1) '' Cor1FeasibleTrad p))

/-- The value of the relaxed blockchain problem (B.19)–(B.20), p. 19. -/
noncomputable def PiCor1BRelaxed (p : Params) : ℝ :=
  max 0 (sSup ((fun y : ℝ × ℝ => obj p y.2 y.1) '' Cor1FeasibleBRelaxed p))

/-- `h(e,Q) = (1 - (1 - δ) C(Q)/(d(e,Q) Q)) F_e(e,Q)/(1 - δ) - γ`, (B.21), p. 19. -/
noncomputable def h (p : Params) (e Q : ℝ) : ℝ :=
  (1 - (1 - p.δ) * Ccap p Q / (d p e Q * Q)) * Fe p e Q / (1 - p.δ) - p.γ

/-- `g(e,Q)`, (B.26), p. 19: `(1 - (1 - δ) C(Q)/(d(e,Q)Q - s(Q)Q - (1 - δ)cQ)) F_e(e,Q)/(1 - δ) - γ`
if `c ≤ d(e,Q) - s(Q)`, and
`(1 - (1 - δ)(C(Q) + cQ - d(e,Q)Q + s(Q)Q)/(δ(d(e,Q)Q - s(Q)Q))) F_e(e,Q)/(1 - δ) - γ`
otherwise. -/
noncomputable def g (p : Params) (e Q : ℝ) : ℝ :=
  if p.c ≤ d p e Q - s p Q then
    (1 - (1 - p.δ) * Ccap p Q / (d p e Q * Q - s p Q * Q - (1 - p.δ) * p.c * Q)) *
      Fe p e Q / (1 - p.δ) - p.γ
  else
    (1 - (1 - p.δ) * (Ccap p Q + p.c * Q - d p e Q * Q + s p Q * Q) /
        (p.δ * (d p e Q * Q - s p Q * Q))) * Fe p e Q / (1 - p.δ) - p.γ

/-- `e*(Q) = (a Q^{1-b} / ((1 - δ) γ))^{1/(1-a)}`, the closed-form root of
`F_e(e,Q)/(1 - δ) - γ = 0` (B.29), p. 20. -/
noncomputable def estar (p : Params) (Q : ℝ) : ℝ :=
  (p.a * Q ^ (1 - p.b) / ((1 - p.δ) * p.γ)) ^ (1 / (1 - p.a))

end PlatformToken.SmallCost


