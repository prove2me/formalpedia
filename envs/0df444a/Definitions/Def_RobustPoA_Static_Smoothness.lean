-- Prove2me | Definitions.Def_RobustPoA_Static_Smoothness
-- name    : RobustPoA_Static_Smoothness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:43.709358+00:00
-- url     : https://prove2.me/theorems/1fa80630-8dd7-4221-ae02-9ef41958ef72
-- title:
--   Definitions 2.1–2.2, pp. 4–5 — (λ, µ)-smooth games and the robust price of anarchy
-- statement:
--   Let $G$ be a cost-minimization game with players $i$, player costs $C_i$ and joint cost $C(s) = \sum_i C_i(s)$.
--
--   **Definition 2.1 (smooth game).** For real numbers $\lambda, \mu$, the game is **$(\lambda,\mu)$-smooth** if for every two outcomes $s$ and $s^*$,
--
--   $$\sum_{i} C_i(s_i^*, s_{-i}) \le \lambda \cdot C(s^*) + \mu \cdot C(s). \tag{2}$$
--
--   **Definition 2.2 (robust POA).** The **robust price of anarchy** of the game is
--
--   $$\rho(G) = \inf\left\{ \frac{\lambda}{1-\mu} \;:\; (\lambda,\mu) \text{ such that the game is } (\lambda,\mu)\text{-smooth},\ \mu < 1 \right\}.$$
--
--   The robust POA is the best upper bound on the price of anarchy that a smoothness argument can prove; the extension theorems of the mission show that it bounds the cost of much more general equilibrium concepts than pure Nash equilibria.
--
--   **Formalization Note** No sign is imposed on $\lambda$ or $\mu$ in (2), as in the paper; only $\mu < 1$ is required in Definition 2.2. The infimum is taken in `EReal`, preserving $+\infty$ when no admissible pair exists and $-\infty$ when the admissible ratios are unbounded below. With a nonnegative objective and at least one positive-cost outcome, taking $s = s^* = s_0$ in (2) gives $\lambda \ge 1 - \mu$, so every candidate ratio is at least $1$. The zero-cost game is an exceptional case in which the literal infimum can be $-\infty$. Remark 2.3's relaxations are not built in.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), Definition 2.1 (2), p. 4; Definition 2.2, p. 5

import Mathlib
import Definitions.Def_RobustPoA_Static_Game

namespace RobustPoA.Static

/-- Definition 2.1, (2), p. 4: the game is `(λ, µ)`-smooth if for every two outcomes `s, s*`,
`∑ᵢ Cᵢ(s*ᵢ, s₋ᵢ) ≤ λ · C(s*) + µ · C(s)`. Here `s'` plays `s*`; no sign is imposed on `λ, µ`. -/
def IsSmooth {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ) : Prop :=
  ∀ s s' : ∀ i, S i,
    (∑ i, C i (Function.update s i (s' i))) ≤ lam * cost C s' + mu * cost C s

/-- Definition 2.2, p. 5: the extended-real infimum of `λ / (1 - µ)` over the
smoothness pairs `(λ, µ)` with `µ < 1`. The empty infimum is `+∞`, and an
unbounded-below set of admissible ratios has infimum `-∞`. -/
noncomputable def robustPoA {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) : EReal :=
  sInf {r : EReal | ∃ lam mu : ℝ, mu < 1 ∧ IsSmooth C lam mu ∧
    r = (lam / (1 - mu) : ℝ)}

end RobustPoA.Static


