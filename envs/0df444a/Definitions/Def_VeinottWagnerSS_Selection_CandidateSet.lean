-- Prove2me | Definitions.Def_VeinottWagnerSS_Selection_CandidateSet
-- name    : VeinottWagnerSS_Selection_CandidateSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T14:01:18.159497+00:00
-- url     : https://prove2.me/theorems/0a803d17-6757-4b66-97b4-813fe4fa7bce
-- title:
--   The bounds $\underline{s}, \bar{s}, \underline{S}, \bar{S}$ of (21)–(23), $\mathcal L_\alpha(S, D)$ and the candidate set $\mathcal S$ of Step ii
-- statement:
--   In the model of `VeinottWagnerSS.Selection.Model` (demand distribution $\varphi$, set-up cost $K \ge 0$, convex $G_\alpha$ with $G_\alpha(y) \to \infty$ as $|y| \to \infty$) and for a discount factor $\alpha$, Veinott and Wagner define four integers bounding an optimal $(s, S)$ policy:
--
--   1. $\underline{S}$ is the smallest integer that minimizes $G_\alpha$;
--   2. $\bar{S}$ is the smallest integer not less than $\underline{S}$ for which $$G_\alpha(\bar{S} + 1) \ge G_\alpha(\underline{S}) + \alpha K; \tag{21}$$
--   3. $\underline{s}$ is the smallest integer for which $$G_\alpha(\underline{s}) \le G_\alpha(\underline{S}) + K; \tag{22}$$
--   4. $\bar{s}$ is the smallest integer for which $$G_\alpha(\bar{s}) \le G_\alpha(\underline{S}) + (1 - \alpha)K. \tag{23}$$
--
--   For $x < s = S - D$ the average cost $a_\alpha(x \mid S - D, S)$ does not depend on $x$; its value is denoted $\mathcal L_\alpha(S, D)$. The **candidate set** $\mathcal S$ (Step ii) is the collection of all $(s, S)$ policies with
--   $$\underline{s} \le s \le \bar{s}, \qquad \underline{S} \le S \le \bar{S}, \qquad s \le S,$$
--   that minimize $\mathcal L_\alpha(S, S - s)$ over all policies satisfying the same bounds.
--
--   The paper shows that every policy in $\mathcal S$ is optimal for $x < \underline{s}$ and that at least one of them is optimal for all $x$; Step iii then selects an optimal policy from $\mathcal S$.
--
--   **Formalization Note** The four bounds are infima (`sInf`) of sets of integers. Under the standing assumptions of `Model` and for $\alpha < 1$ each set is nonempty and bounded below, so the infimum is its least element, as the paper's "smallest integer" requires (for sets that are empty or unbounded below Lean's `sInf` on $\mathbb Z$ returns $0$, which never happens in that range). $\mathcal L_\alpha(S, D)$ is defined as $a_\alpha(S - D - 1 \mid S - D, S)$, i.e. evaluated at the starting stock $x = s - 1$ just below $s$; that this equals $a_\alpha(x \mid s, S)$ for every $x < s$ is the milestone $f(x) = K + f(S)$, $x < s$. A policy is a pair `p : ℤ × ℤ` with `p.1 = s`, `p.2 = S`.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 536 (ℒ_α, Steps i-ii), p. 537 (S̲, (21), (22), (23))

import Mathlib
import Definitions.Def_VeinottWagnerSS_Selection_Model

namespace VeinottWagnerSS.Selection

/-- `S̲` ("S underbar", p. 537): the smallest integer that minimizes `G_α`. Under the standing
assumption `G_α(y) → ∞` as `|y| → ∞` the set of minimizers is nonempty and bounded below, so
the infimum is its least element. -/
noncomputable def SLow (M : Model) : ℤ :=
  sInf {y : ℤ | ∀ z : ℤ, M.G y ≤ M.G z}

/-- `S̄` ("S bar", (21), p. 537): the smallest integer not less than `S̲` for which
`G_α(S̄ + 1) ≥ G_α(S̲) + αK`. The set is bounded below by `S̲` and nonempty since
`G_α(y) → ∞` as `y → ∞`. -/
noncomputable def SHigh (M : Model) (α : ℝ) : ℤ :=
  sInf {y : ℤ | SLow M ≤ y ∧ M.G (SLow M) + α * M.K ≤ M.G (y + 1)}

/-- `s̲` ("s underbar", (22), p. 537): the smallest integer for which `G_α(s̲) ≤ G_α(S̲) + K`.
The set contains `S̲` (as `K ≥ 0`) and is bounded below since `G_α(y) → ∞` as `y → −∞`. -/
noncomputable def sLow (M : Model) : ℤ :=
  sInf {y : ℤ | M.G y ≤ M.G (SLow M) + M.K}

/-- `s̄` ("s bar", (23), p. 537): the smallest integer for which
`G_α(s̄) ≤ G_α(S̲) + (1 − α)K`. For `α ≤ 1` the set contains `S̲`, and it is bounded below since
`G_α(y) → ∞` as `y → −∞`. -/
noncomputable def sHigh (M : Model) (α : ℝ) : ℤ :=
  sInf {y : ℤ | M.G y ≤ M.G (SLow M) + (1 - α) * M.K}

/-- `ℒ_α(S, D)` (p. 536): for `x < s = S − D`, `a_α(x | S − D, S)` is a function of `S` and `D`
only; `ℒ_α(S, D)` is that value, taken here at `x = S − D − 1`. -/
noncomputable def calL (M : Model) (α : ℝ) (S D : ℤ) : ℝ :=
  aCost M α (S - D) S (S - D - 1)

/-- The `(s, S)` policies falling within the bounds of Step i (pp. 536–537):
`s̲ ≤ s ≤ s̄`, `S̲ ≤ S ≤ S̄`, and `s ≤ S`. A pair `p` stands for the policy `(s, S) = (p.1, p.2)`. -/
def Box (M : Model) (α : ℝ) : Set (ℤ × ℤ) :=
  {p | sLow M ≤ p.1 ∧ p.1 ≤ sHigh M α ∧ SLow M ≤ p.2 ∧ p.2 ≤ SHigh M α ∧ p.1 ≤ p.2}

/-- The candidate set `𝒮` of Step ii (p. 536): the collection of all `(s, S)` policies within the
bounds of Step i that minimize `ℒ_α(S, D)`, `D = S − s`, over the policies within those bounds. -/
def candSet (M : Model) (α : ℝ) : Set (ℤ × ℤ) :=
  {p | p ∈ Box M α ∧ ∀ q ∈ Box M α, calL M α p.2 (p.2 - p.1) ≤ calL M α q.2 (q.2 - q.1)}

end VeinottWagnerSS.Selection


