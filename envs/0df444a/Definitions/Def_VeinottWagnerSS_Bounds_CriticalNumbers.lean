-- Prove2me | Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers
-- name    : VeinottWagnerSS_Bounds_CriticalNumbers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T13:33:55.808227+00:00
-- url     : https://prove2.me/theorems/46793edd-b6b3-41a1-aaa3-6a8cd9d7b704
-- title:
--   The bounds $\underline{s}$, $\bar{s}$, $\underline{S}$, $\bar{S}$ of Veinott–Wagner, Eqs. (21)–(23)
-- statement:
--   Let $G_\alpha : \mathbb Z \to \mathbb R$ be the one-period cost function, $K \ge 0$ the set-up cost and $\alpha$ the discount factor. Veinott and Wagner (1965, p. 537) define four integers from $G_\alpha$ alone.
--
--   1. $\underline{S}$ is the smallest integer that minimizes $G_\alpha$.
--   2. $\bar{S}$ is the smallest integer $\bar S \ge \underline{S}$ with
--   $$G_\alpha(\bar{S} + 1) \ge G_\alpha(\underline{S}) + \alpha K. \tag{21}$$
--   3. $\underline{s}$ is the smallest integer with
--   $$G_\alpha(\underline{s}) \le G_\alpha(\underline{S}) + K. \tag{22}$$
--   4. $\bar{s}$ is the smallest integer with
--   $$G_\alpha(\bar{s}) \le G_\alpha(\underline{S}) + (1 - \alpha) K. \tag{23}$$
--
--   The paper shows that the first-period parameters $(s_n, S_n)$ of some optimal $(s, S)$ policy of the $n$-period model satisfy $\underline{s} \le s_n \le \bar{s} \le \underline{S} \le S_n \le \bar{S}$. The bounds depend only on the one-period data, so they cut the search for an optimal policy down to a finite box.
--
--   **Formalization Note** Each number is the infimum (`sInf` on `ℤ`) of the set of integers with the stated property: `SLow G` is $\underline{S}$, `SHigh G K α` is $\bar S$, `sLow G K` is $\underline{s}$ and `sHigh G K α` is $\bar s$. When $G_\alpha$ is convex with $G_\alpha(y) \to \infty$ as $|y| \to \infty$, $K \ge 0$ and $\alpha \le 1$, each set is nonempty and bounded below, so the infimum is its least element (this is stated as a separate theorem). On an empty or unbounded-below set, `sInf` on `ℤ` returns $0$; every statement that uses these numbers assumes the paper's standing assumptions.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 537, Section 4 'Bounds on s* and S*', Eqs. (21), (22), (23)

import Mathlib

namespace VeinottWagnerSS.Bounds

/-- `S̲` ("S underbar", `\underline{S}`), p. 537: the smallest integer that minimizes `G_α`.
Defined as the infimum of the set of global minimizers of `G`; when `G` is convex and
`G(y) → ∞` as `|y| → ∞` that set is nonempty and bounded below, so this is its least element.
(On a set that is empty or unbounded below, `sInf` on `ℤ` returns `0`; every theorem using
`SLow` assumes `G` coercive.) -/
noncomputable def SLow (G : ℤ → ℝ) : ℤ :=
  sInf {y : ℤ | ∀ z : ℤ, G y ≤ G z}

/-- `S̄` ("S bar", `\bar{S}`), Eq. (21), p. 537: the smallest integer `S̄ ≥ S̲` for which
`G_α(S̄ + 1) ≥ G_α(S̲) + αK`. -/
noncomputable def SHigh (G : ℤ → ℝ) (K α : ℝ) : ℤ :=
  sInf {y : ℤ | SLow G ≤ y ∧ G (SLow G) + α * K ≤ G (y + 1)}

/-- `s̲` ("s underbar", `\underline{s}`), Eq. (22), p. 537: the smallest integer for which
`G_α(s̲) ≤ G_α(S̲) + K`. -/
noncomputable def sLow (G : ℤ → ℝ) (K : ℝ) : ℤ :=
  sInf {y : ℤ | G y ≤ G (SLow G) + K}

/-- `s̄` ("s bar", `\bar{s}`), Eq. (23), p. 537: the smallest integer for which
`G_α(s̄) ≤ G_α(S̲) + (1 − α)K`. -/
noncomputable def sHigh (G : ℤ → ℝ) (K α : ℝ) : ℤ :=
  sInf {y : ℤ | G y ≤ G (SLow G) + (1 - α) * K}

end VeinottWagnerSS.Bounds


