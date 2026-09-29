-- Prove2me | Definitions.Def_GallegoOzerADI_PositiveSetup_MyopicLevels
-- name    : GallegoOzerADI_PositiveSetup_MyopicLevels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:44:59.485487+00:00
-- url     : https://prove2.me/theorems/fe3d1928-02ab-4600-a3b5-de7300e78d42
-- title:
--   Myopic levels $S^m$, $s^m$ and $\overline{S}$ of the stationary problem
-- statement:
--   Let $G : \mathbb{R} \to \mathbb{R}$ be the single-period cost of a stationary inventory problem, $K$ its set-up cost and $\alpha$ its discount factor. The paper defines
--
--   $$
--   S^m = \min\{y : G(y) \le G(x) \text{ for all } x\},\qquad
--   s^m = \max\{y \le S^m : G(y) \ge K + G(S^m)\},
--   $$
--   $$
--   \overline{S} = \inf\{y > S^m : G(y) > G(S^m) + \alpha K\}.
--   $$
--
--   $S^m$ is the least minimizer of $G$ (the myopic order-up-to level), $s^m$ is the largest level below $S^m$ at which paying the set-up cost to reach $S^m$ does not increase the single-period cost (the myopic reorder point), and $\overline{S}$ is the point beyond which $G$ exceeds its minimum by more than the discounted set-up cost. The pair $(s^m, S^m)$ is the myopic policy that ignores advance demand information; $s^m$ and $\overline{S}$ bound the optimal policy parameters from below and above.
--
--   **Formalization Note** The paper prints $\overline{S}$ as a minimum, $\min\{y > S^m : G(y) > G(S^m) + \alpha K\}$. For continuous $G$ this set is open and has no minimum, so it is read as the infimum (this is also what the paper's proof of Lemma 3 uses). The minimum and maximum defining $S^m$ and $s^m$ are written as `sInf` and `sSup`; for convex $G$ with $G(y)\to\infty$ as $|y|\to\infty$ both sets are nonempty, closed and bounded on the relevant side, so these are the paper's minimum and maximum. The theorems that use these levels carry exactly those hypotheses on $G$.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1350, definitions of S^m, s^m and S̄ (Section 4)

import Mathlib

namespace GallegoOzerADI.PositiveSetup

/-- The myopic order-up-to level of the stationary problem (p. 1350):
`S^m = min {y : G(y) ≤ G(x) for all x}`, the least global minimizer of the single-period cost
`G`. -/
noncomputable def myopicOrderUpTo (G : ℝ → ℝ) : ℝ :=
  sInf {y : ℝ | ∀ x, G y ≤ G x}

/-- The myopic reorder point of the stationary problem (p. 1350):
`s^m = max {y ≤ S^m : G(y) ≥ K + G(S^m)}`. -/
noncomputable def myopicReorderPoint (G : ℝ → ℝ) (K : ℝ) : ℝ :=
  sSup {y : ℝ | y ≤ myopicOrderUpTo G ∧ K + G (myopicOrderUpTo G) ≤ G y}

/-- The upper bound `S̄` of p. 1350, printed as `min {y > S^m : G(y) > G(S^m) + α K}`. That set
is open for continuous `G` and has no minimum, so it is read as the infimum. -/
noncomputable def myopicUpperLevel (G : ℝ → ℝ) (K α : ℝ) : ℝ :=
  sInf {y : ℝ | myopicOrderUpTo G < y ∧ G (myopicOrderUpTo G) + α * K < G y}

end GallegoOzerADI.PositiveSetup


