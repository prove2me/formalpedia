-- Prove2me | Definitions.Def_CardinalMatching_ModParams
-- name    : CardinalMatching_ModParams
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:47.360601+00:00
-- url     : https://prove2.me/theorems/0c52ab86-f283-4a06-aad9-21e009c1e9d8
-- title:
--   The modified instance $I'$ (corrected: $k\ge n^4/\varepsilon$, $k\ge n^4$)
-- statement:
--   From an instance $I$ with $n\ge 1$ agents and goods and utilities $u_{ij}\in[0,1]$, parameters $k\in\mathbb N^+$ and $\varepsilon>0$ with $n\mid k$, an arbitrary order of types and direction for every interpolating chain, and a dummy utility $d\ge 0$, the **modified instance** $I'=(A',G',u')$ is:
--
--   1. $k$ copies of every original good and $k$ copies of every original agent; a copy of $i$ values a copy of $j$ at $u_{ij}$;
--   2. $k/n$ **awesome goods**, valued at $2$ by every copy and every interpolating agent;
--   3. the **interpolating agents** (see `interpVectors`), valuing a copy of $j$ at their vector's $j$-th entry;
--   4. **dummy agents**, added until $|A'|=|G'|$, valuing every good of $G'$ at $d$.
--
--   Two goods (agents) of $I'$ are **of the same type** if all agents have identical utilities for them (all goods have identical utilities for them); see Definition 11.
--
--   **Admissible parameters (correction C1).** The paper requires $k\ge n^3/\varepsilon$. Then step 3 can add more interpolating agents than there are awesome goods, and no number of dummy agents balances the instance. For example, take $n=5$, $\varepsilon=1/15625$, $k=n^3/\varepsilon$, $u_1=u_2=(0,\dots,0)$, $u_3=u_4=(1,\dots,1)$ and $u_5=(1,0.99,0.98,0.97,0.96)$: there are $468\,748$ interpolating agents but only $390\,625$ awesome goods. The printed condition also fails for large $\varepsilon$: $n=3$, $\varepsilon=100$, $k=3$ gives 4 interpolating agents for one awesome good. This item requires instead
--   $$
--   k\ \ge\ \frac{n^4}{\varepsilon}\qquad\text{and}\qquad k\ge n^4,
--   $$
--   under which there are fewer than $n^3\max\{1,1/\varepsilon\}\le k/n$ interpolating agents.
--
--   **Formalization Note** Goods are $(\text{Fin } n\times\text{Fin } k)\sqcup\text{Fin}(k/n)$; agents are copies, interpolating agents and $k/n-\#\text{interp}$ dummies (truncated subtraction, never active under admissible parameters). Step 2 of the paper says "every agent has utility 2" for awesome goods, while step 4 says dummies "have identical utilities for all goods"; the latter is followed, so dummies value awesome goods at $d$.
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Step 1, p.8 (items 1–4), Definition 11, p.7; standing assumptions p.5 (|A| = |G| = n, non-negative utilities) and p.7 (utilities in [0,1])

import Mathlib
import Definitions.Def_CardinalMatching_interpVectors

namespace CardinalMatching

/-- **Data of the modified instance `I′`** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*,
arXiv:2402.08851v6, Step 1, p.8): the original instance `I` (`n` agents and goods `Fin n`,
utilities `u`), the parameters `k ∈ ℕ⁺` and `ε > 0`, the arbitrary order of the types and
direction of each interpolating chain (`ord`, `rev`), and the common utility `d` of the dummy
agents. -/
structure ModParams (n : ℕ) where
  /-- Utilities of the original instance `I`. -/
  u : Fin n → Fin n → ℝ
  /-- Number of copies of every original agent and good. -/
  k : ℕ
  /-- Interpolation step. -/
  ε : ℝ
  /-- The order of the types used by the chain of the pair `i < i'`. -/
  ord : Fin n → Fin n → Equiv.Perm (Fin n)
  /-- Whether the chain of the pair `i < i'` runs from `u_i'` to `u_i` instead. -/
  rev : Fin n → Fin n → Bool
  /-- The utility of every dummy agent for every good. -/
  d : ℝ

namespace ModParams

variable {n : ℕ} (P : ModParams n)

/-- **Admissible parameters** for the construction of `I′` (Tröbst–Vazirani, arXiv:2402.08851v6,
p.8: "Fix a positive integer k ∈ N+ and some ǫ > 0 such that k is divisible by n and
k ≥ n³/ǫ"), with the standing assumptions of §2.2: `n ≥ 1` and utilities in `[0, 1]` (p.7),
dummy utility `d ≥ 0` (utilities are non-negative, p.5).

**Formalization Note (correction C1)** As printed (`k ≥ n³/ε`) the construction can be
impossible: step 3 may add more interpolating agents than there are awesome goods, and then no
number of dummy agents makes `|A′| = |G′|` (counterexample: `n = 5`, `ε = 1/15625`,
`k = n³/ε = 1953125`, `u₁ = u₂ = (0,0,0,0,0)`, `u₃ = u₄ = (1,1,1,1,1)`,
`u₅ = (1, 0.99, 0.98, 0.97, 0.96)`: at least 465 595 interpolating agents but only 390 625
awesome goods; and for large `ε`: `n = 3`, `ε = 100`, `k = 3`, `u₁ = u₃ = 0`, `u₂ = (1,1,1)`:
4 interpolating agents but `k/n = 1` awesome good). The minimal correction used here is
`k ≥ n⁴/ε` and `k ≥ n⁴`, i.e. `k ≥ n⁴ · max {1, 1/ε}`; then the interpolating agents number fewer
than `n³ · max {1, 1/ε} ≤ k/n`. -/
def Admissible : Prop :=
  1 ≤ n ∧ (∀ i j, 0 ≤ P.u i j ∧ P.u i j ≤ 1) ∧ 0 < P.k ∧ n ∣ P.k ∧
    0 < P.ε ∧ (n : ℝ) ^ 4 / P.ε ≤ P.k ∧ (n : ℝ) ^ 4 ≤ P.k ∧ 0 ≤ P.d

/-- The utility vectors of the interpolating agents (Step 1 item 3, p.8). -/
noncomputable def interp : List (Fin n → ℝ) := interpVectors P.u P.ε P.ord P.rev

/-- **Goods of `I′`** (p.8, items 1–2): `k` copies `(j, c)` of every original good `j`, and
`k/n` awesome goods. -/
abbrev Good : Type := (Fin n × Fin P.k) ⊕ Fin (P.k / n)

/-- **Agents of `I′`** (p.8, items 1, 3, 4): `k` copies `(i, c)` of every original agent `i`, the
interpolating agents (one per entry of `interp`), and `k/n − #interp` dummy agents, which makes
`|A′| = |G′|` under `Admissible` (truncated subtraction is never active there). -/
abbrev Agent : Type := (Fin n × Fin P.k) ⊕ (Fin P.interp.length ⊕ Fin (P.k / n - P.interp.length))

/-- **Utilities `u′` of `I′`** (p.8): a copy of agent `i` values a copy of good `j` at `u_ij`; an
interpolating agent with vector `w` values a copy of good `j` at `w_j`; every copy and every
interpolating agent values every awesome good at `2`; a dummy agent values **every** good of `G′`
(awesome goods included) at `d`.

**Formalization Note** Item 2 says "every agent has utility 2" for awesome goods while item 4
says dummies "have identical utilities for all goods"; the second is followed for dummies. -/
noncomputable def util : P.Agent → P.Good → ℝ
  | Sum.inl (i, _), Sum.inl (j, _) => P.u i j
  | Sum.inl _, Sum.inr _ => 2
  | Sum.inr (Sum.inl m), Sum.inl (j, _) => P.interp.get m j
  | Sum.inr (Sum.inl _), Sum.inr _ => 2
  | Sum.inr (Sum.inr _), _ => P.d

/-- An agent of `I′` is a **dummy agent** (p.8, item 4). Copies and interpolating agents are the
non-dummy agents. -/
def IsDummy : P.Agent → Prop
  | Sum.inr (Sum.inr _) => True
  | _ => False

/-- Two goods of `I′` are **of the same type** (Definition 11, p.7) if all agents of `I′` have
identical utilities for them. -/
def SameGoodType (g g' : P.Good) : Prop := ∀ a, P.util a g = P.util a g'

/-- Two agents of `I′` are **of the same type** (Definition 11, p.7) if they have identical
utilities for all goods of `I′`. -/
def SameAgentType (a a' : P.Agent) : Prop := ∀ g, P.util a g = P.util a' g

end ModParams

end CardinalMatching


