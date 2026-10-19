-- Prove2me | Definitions.Def_PlatformToken_SmallCost_Programs
-- name    : PlatformToken_SmallCost_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:18.160829+00:00
-- url     : https://prove2.me/theorems/515d9625-6a08-4e78-b66a-2f2cf847d4b1
-- title:
--   The equilibrium payoffs $\Pi^\$$ (Lemma 2) and $\Pi^B$ (Lemma 3)
-- statement:
--   The entrepreneur's equilibrium payoffs in the two business models, defined by the programs of Lemma 2 (traditional, equity-financed model) and Lemma 3 (blockchain-based, token-financed model).
--
--   **Traditional model.** Let
--   $$\alpha(e,Q)=\frac{C(Q)-\min\{\pi(\bar x_1,\bar q_1),0\}}{\pi(\bar x_1,\bar q_1)+\frac{\delta}{1-\delta}\pi(\bar x_2,\bar q_2)-\min\{\pi(\bar x_1,\bar q_1),0\}}\qquad(19)$$
--   be the VC's equity share. The feasible set of Lemma 2 consists of the triples $(Q,\alpha,e)$ with
--   $$(1-\alpha)\frac{\mathcal F_e(e,Q)}{1-\delta}=\gamma\ (18),\qquad \alpha=\alpha(e,Q)\ (19),\qquad Q>0,\ e>0,\ 0<\alpha<1\ (20),$$
--   and
--   $$\Pi^\$=\max\Bigl\{0,\ \sup_{(Q,\alpha,e)\ \text{feasible}}\Bigl[\frac{\mathcal F(e,Q)}{1-\delta}-cQ-C(Q)-\gamma e\Bigr]\Bigr\}.\qquad(17)$$
--
--   **Blockchain-based model.** The feasible set of Lemma 3 consists of the triples $(Q,\alpha,e)$ with
--   $$\frac{\mathcal F_e(e,Q)}{1-\delta}-\alpha\frac1v d_e(e,Q)Q=\gamma\ (34),\qquad \alpha\, d(e,Q)Q=vC(Q)\ (35),\qquad Q\ge0,\ e\ge0,\ 0\le\alpha\le1\ (36),$$
--   and $\Pi^B$ is the supremum (33) of the same objective over this set, against the outside option $0$.
--
--   In the traditional model $\alpha$ is the share of equity sold to the venture capitalist; in the blockchain model it is the fraction of tokens sold in the ICO. The two payoffs are the objects compared by Proposition 2.
--
--   **Formalization Note** Lemmas 2 and 3 characterize the interior equilibrium payoffs of the paper's dynamic game; the mission takes their programs as the definitions of $\Pi^\$$ and $\Pi^B$ and does not model the game itself. The printed "max" is encoded as a supremum (`sSup`, whose junk value on an empty or unbounded set is $0$), and the outer $\max\{0,\cdot\}$ is the outside option of not starting the venture, $Q=e=0$, invoked in the last paragraph of the proof of Proposition 2. A vanishing denominator in (19) yields $\alpha=0$ in Lean, which (20) excludes. Decisions are triples `(Q, α, e)`.
-- source:
--   Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard, Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 7, Lemma 2, (17)–(20); p. 10, Lemma 3, (33)–(36)

import Mathlib
import Definitions.Def_PlatformToken_SmallCost_Setting

set_option autoImplicit false

/-!
# The entrepreneur's payoffs Π^$ and Π^B (Lemma 2, p. 7; Lemma 3, p. 10)

Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard,
Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, p. 7, Lemma 2,
(17)–(20), and p. 10, Lemma 3, (33)–(36).

**Formalization Note.**
* Lemmas 2 and 3 are the paper's characterization of the *interior* equilibrium payoffs
  ("Suppose Q̄ > 0 and ē > 0"). Here the two programs are taken as the *definitions* of Π^$ and
  Π^B; the dynamic game (3)–(7) and the bilevel problems (12)–(16), (25)–(31) are not modelled.
* A decision is a triple `(Q, α, e) : ℝ × ℝ × ℝ`, in the order of the printed `max_{Q, α, e}`.
* The printed "max" is never shown to be attained, so it is encoded as `sSup` of the image of
  the objective; the outside option of not starting the venture (`Q = e = 0`, payoff `0`, proof
  of Proposition 2, last paragraph, p. 20) is the outer `max 0`. Lean's `sSup` of a set that is
  empty or not bounded above is `0`; the goal theorem asserts boundedness separately.
* In (19), Lean's `x / 0 = 0` gives `α = 0` when the denominator vanishes, which (20) excludes.
* (36) is encoded as printed, with `Q ≥ 0, e ≥ 0`; with `γ > 0` and Lean's `0 ^ y = 0`,
  `Q = 0` or `e = 0` violates (34).
-/

namespace PlatformToken.SmallCost

/-- The VC's equity share (19), p. 7:
`α = (C(Q) - min{π(x̄₁,q̄₁), 0}) / (π(x̄₁,q̄₁) + δ/(1-δ) π(x̄₂,q̄₂) - min{π(x̄₁,q̄₁), 0})`. -/
noncomputable def alpha19 (p : Params) (e Q : ℝ) : ℝ :=
  (Ccap p Q - min (pi1 p e Q) 0) /
    (pi1 p e Q + p.δ / (1 - p.δ) * pi2 p e Q - min (pi1 p e Q) 0)

/-- The feasible set of Lemma 2's program (18)–(20), p. 7, over `(Q, α, e)`:
`(1 - α) F_e(e,Q)/(1 - δ) = γ`, `α` given by (19), `Q > 0`, `e > 0`, `0 < α < 1`. -/
def TradFeasible (p : Params) : Set (ℝ × ℝ × ℝ) :=
  {x | (1 - x.2.1) * Fe p x.2.2 x.1 / (1 - p.δ) = p.γ ∧
      x.2.1 = alpha19 p x.2.2 x.1 ∧
      0 < x.1 ∧ 0 < x.2.2 ∧ 0 < x.2.1 ∧ x.2.1 < 1}

/-- The entrepreneur's equilibrium payoff in the traditional model, `Π^$`, Lemma 2 (17), p. 7:
the supremum of `F(e,Q)/(1 - δ) - cQ - C(Q) - γe` over `TradFeasible`, against the outside
option `0`. -/
noncomputable def PiTrad (p : Params) : ℝ :=
  max 0 (sSup ((fun x : ℝ × ℝ × ℝ => obj p x.2.2 x.1) '' TradFeasible p))

/-- The feasible set of Lemma 3's program (34)–(36), p. 10, over `(Q, α, e)`:
`F_e(e,Q)/(1 - δ) - α (1/v) d_e(e,Q) Q = γ`, `α d(e,Q) Q = v C(Q)`, `Q ≥ 0`, `e ≥ 0`,
`0 ≤ α ≤ 1`. -/
def BlockFeasible (p : Params) : Set (ℝ × ℝ × ℝ) :=
  {x | Fe p x.2.2 x.1 / (1 - p.δ) - x.2.1 * (1 / p.v) * de p x.2.2 x.1 * x.1 = p.γ ∧
      x.2.1 * d p x.2.2 x.1 * x.1 = p.v * Ccap p x.1 ∧
      0 ≤ x.1 ∧ 0 ≤ x.2.2 ∧ 0 ≤ x.2.1 ∧ x.2.1 ≤ 1}

/-- The entrepreneur's equilibrium payoff in the blockchain-based model, `Π^B`, Lemma 3 (33),
p. 10: the supremum of the objective over `BlockFeasible`, against the outside option `0`. -/
noncomputable def PiBlock (p : Params) : ℝ :=
  max 0 (sSup ((fun x : ℝ × ℝ × ℝ => obj p x.2.2 x.1) '' BlockFeasible p))

end PlatformToken.SmallCost


