-- Prove2me | Definitions.Def_FairRandomObject_Bads_BottomHeavy
-- name    : FairRandomObject_Bads_BottomHeavy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:45.8159+00:00
-- url     : https://prove2.me/theorems/46cd8854-a036-443a-af44-cd18153a4a28
-- title:
--   (9), p. 15; (10), p. 16; (13), p. 25 — the fairness bound (9) and the Bottom-Heavy rules ϕ^θ
-- statement:
--   Fix $n\ge2$ agents, a profile $x\in\mathbb R^N_+$ with mean $\bar x$, and a parameter $\theta\in[0,1]$.
--
--   1. **The bound (9).** For agent $i$,
--   $$b^\theta_i(x)=\min\Big\{\frac1n+\frac{\theta}{n-1}\Big(\frac{\bar x}{x_i}-1\Big),\,1\Big\},$$
--   with the convention $1/0=+\infty$: if $x_i=0$ the bound is $1$, for every $\theta$. A rule **satisfies (9) with parameter $\theta$** if $\varphi_i(x)\le b^\theta_i(x)$ for all $i\in N$ and $x\in\mathbb R^N_+$.
--   2. **The Bottom-Heavy rule $\varphi^\theta$** (13). Let $\psi^\theta_i(x)=\frac1n+\frac{\theta}{n-1}\big(\frac{\bar x}{x_i}-1\big)$. Order the disutilities $x^{(1)}\le\dots\le x^{(n)}$, set $x^{(0)}=-\infty$, $\sigma(x;t)=\{i: x_i=x^{(t)}\}$, and let $\tilde t$ be the largest $t\in\{0,\dots,n\}$ with $\sum_{i:x_i\le x^{(t)}}\psi^\theta_i(x)\le1$. Then
--   $$\varphi^\theta_i(x)=\begin{cases}\psi^\theta_i(x), & x_i\le x^{(\tilde t)},\\[2pt] \dfrac{1}{|\sigma(x;\tilde t+1)|}\Big(1-\sum_{j:x_j\le x^{(\tilde t)}}\psi^\theta_j(x)\Big), & i\in\sigma(x;\tilde t+1),\\[2pt] 0, & \text{otherwise.}\end{cases}$$
--   Agents with the lowest disutilities receive the full bound (9), the next class of tied agents splits what remains equally, and everyone else gets nothing. The canonical **Bottom-Heavy rule** of Definition 15 is $\varphi^1$; for $x_i>0$, $\psi^1_i(x)=x_{N\setminus\{i\}}/(n(n-1)x_i)$.
--
--   These objects carry the characterization of fair rules (Proposition 14) and the main result (Theorem 17).
--
--   **Formalization Note** $\tilde t$ is encoded without sorting. With $S(v)=\sum_{j:x_j\le v}\psi^\theta_j(x)$, the agents with $x_i\le x^{(\tilde t)}$ are those with $S(x_i)\le1$, and $\sigma(x;\tilde t+1)$ is the set of agents with $S(x_i)>1$ all of whose strictly lower agents have $S\le1$. For $\theta>0$ and a profile with some zero coordinate, the paper's $\bar x/0=+\infty$ gives $\tilde t=0$: the agents with $x_i=0$ split the bad equally (at $x=0$ this is $e^N/n$); this case is an explicit first branch. For $\theta=0$, $\psi^0\equiv1/n$ and $\varphi^0$ is Equal Split, as the paper says.
-- source:
--   Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 15, (9); p. 16, Definition 15, (10); p. 25, (13)

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting

namespace FairRandomObject.Bads

open Classical

/-! Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object,
arXiv:1903.10361v4, p. 15, (9); p. 16, Definition 15, (10); p. 25, (13): the bound (9) and
the family of Bottom-Heavy rules `ϕ^θ`. -/

/-- p. 15, (9): the upper bound `min{1/n + θ/(n−1) (x̄/x_i − 1), 1}` on the share of agent `i`
at profile `x`, with the paper's convention `1/0 = +∞`.

**Formalization Note.** The convention `1/0 = +∞` is made explicit: when `x_i = 0` the bound is
`1` (no constraint beyond `ϕ_i ≤ 1`) for every `θ`, including `θ = 0`. Lean's `x̄ / 0 = 0` is
never used. -/
noncomputable def bound9 (n : ℕ) (θ : ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  if x i = 0 then 1 else min (1 / n + θ / (n - 1) * (mean x / x i - 1)) 1

/-- p. 15, (9): the rule `ϕ` satisfies inequalities (9) with parameter `θ`:
`ϕ_i(x) ≤ min{1/n + θ/(n−1) (x̄/x_i − 1), 1}` for all `i ∈ N` and `x ∈ ℝ^N_+`. -/
def Satisfies9 {n : ℕ} (ϕ : Rule n) (θ : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, 0 ≤ x → ∀ i, ϕ x i ≤ bound9 n θ x i

/-- p. 25, (13): the uncapped bound `ψ^θ_i(x) = 1/n + θ/(n−1) (x̄/x_i − 1)`. It is only used at
profiles where it is meaningful (`x_i > 0`, or `θ = 0`). For `θ = 1` and `x_i > 0` it equals
`x_{N∖{i}} / (n(n−1) x_i)` (p. 15). -/
noncomputable def psi (n : ℕ) (θ : ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  1 / n + θ / (n - 1) * (mean x / x i - 1)

/-- p. 25: the prefix mass `S(v) = ∑_{j : x_j ≤ v} ψ^θ_j(x)`. At `v = x^{(t)}` it is the sum
`∑_{i : x_i ≤ x^{(t)}} (1/n + θ/(n−1)(x̄/x_i − 1))` that defines `t̃`. -/
noncomputable def prefixMass (n : ℕ) (θ : ℝ) (x : Fin n → ℝ) (v : ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => x j ≤ v), psi n θ x j

/-- p. 25, (13), and Definition 15, p. 16, (10): the Bottom-Heavy rule `ϕ^θ`.

Agents are weakly ordered by disutility. With order statistics `x^{(1)} ≤ … ≤ x^{(n)}`,
`x^{(0)} = −∞` and `σ(x; t) = {i : x_i = x^{(t)}}`, let `t̃` be the largest `t ∈ {0, …, n}`
with `∑_{i : x_i ≤ x^{(t)}} ψ^θ_i(x) ≤ 1`. Then agents with `x_i ≤ x^{(t̃)}` get `ψ^θ_i(x)`,
the agents of `σ(x; t̃+1)` split `1 − ∑_{i : x_i ≤ x^{(t̃)}} ψ^θ_i(x)` equally, and all other
agents get `0`. The canonical Bottom-Heavy rule of Definition 15 is `ϕ¹ = bottomHeavy n 1`.

**Formalization Note.** `t̃` is encoded at the level of values, without sorting: since
`ψ^θ ≥ 0`, `{i : x_i ≤ x^{(t̃)}} = {i : S(x_i) ≤ 1}` with `S = prefixMass n θ x`, and
`σ(x; t̃+1)` is the set of agents `i` with `S(x_i) > 1` such that every `j` with `x_j < x_i`
has `S(x_j) ≤ 1`. For `θ > 0` and a profile with a zero coordinate, the paper's `x̄/0 = +∞`
gives `t̃ = 0` and `σ(x; 1) = {i : x_i = 0}`: the zero-disutility agents split the bad equally
(at `x = 0` this is `e^N/n`, as symmetry forces). This case is an explicit first branch. For
`θ = 0`, `ψ^0 ≡ 1/n` and the rule is Equal Split, the paper's `ϕ^0`. -/
noncomputable def bottomHeavy (n : ℕ) (θ : ℝ) : Rule n := fun x i =>
  if 0 < θ ∧ ∃ j, x j = 0 then
    (if x i = 0 then 1 / ((Finset.univ.filter (fun j => x j = 0)).card : ℝ) else 0)
  else if prefixMass n θ x (x i) ≤ 1 then psi n θ x i
  else if ∀ j, x j < x i → prefixMass n θ x (x j) ≤ 1 then
    (1 - ∑ j ∈ Finset.univ.filter (fun j => prefixMass n θ x (x j) ≤ 1), psi n θ x j) /
      ((Finset.univ.filter (fun j => x j = x i)).card : ℝ)
  else 0

end FairRandomObject.Bads


