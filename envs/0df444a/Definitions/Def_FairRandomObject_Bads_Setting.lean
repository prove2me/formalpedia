-- Prove2me | Definitions.Def_FairRandomObject_Bads_Setting
-- name    : FairRandomObject_Bads_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:07:59.802416+00:00
-- url     : https://prove2.me/theorems/631db668-8653-4f06-b815-8707aaa153a3
-- title:
--   §2, pp. 8–10 — normalized problems, API rules, symmetry, Fair Share for a bad, social cost and domination
-- statement:
--   A single **bad** (a chore, a cost) is to be divided among the agents $N=\{1,\dots,n\}$. A **profile** is a vector $x\in\mathbb R^N_+$ of the agents' normalized disutilities for the whole bad; the orthant $\mathbb R^N_+$ includes profiles with zero coordinates. Write $x_N=\sum_{i\in N}x_i$, $\bar x = x_N/n$ for the arithmetic mean, and $e^N=(1,\dots,1)$.
--
--   1. **Normalized problem** (Definitions 2 and 7). A probability distribution $\mu$ on $\mathbb R^N$, carried by $\mathbb R^N_+$, under which every coordinate $X_i$ is integrable with $\mathbb E_\mu(X_i)=1$. The coordinates may be arbitrarily correlated.
--   2. **API rule** (Definitions 3–4). An almost prior-independent division rule is a single measurable map $\varphi$ that sends every profile $x\in\mathbb R^N_+$ to a lottery $\varphi(x)$ in the simplex $\Delta(N)$; $\varphi_i(x)$ is agent $i$'s share. It does not depend on $\mu$.
--   3. **Symmetry** (Definition 5). For every permutation $\pi$ of $N$, every $x\in\mathbb R^N_+$ and every $i$, $\varphi_i(x)=\varphi_{\pi(i)}(\pi(x))$, where $\pi(x)_{\pi(j)}=x_j$.
--   4. **Fair Share for a bad** (Definition 6, inequality reversed). For every normalized problem $\mu$ and every agent $i$,
--   $$\mathbb E_\mu\big(\varphi_i(X)\,X_i\big)\le \frac1n .$$
--   5. **Social cost and domination** (Definition 8, for a bad). The ex post social cost of $\varphi$ at $x$ is $\sum_{i\in N}\varphi_i(x)\,x_i$. A rule $\varphi$ **dominates** $\psi$ if its social cost is at most that of $\psi$ at every $x\in\mathbb R^N_+$ and strictly lower at some $x\in\mathbb R^N_+$.
--   6. **Equal Split**: $\varphi^{es}(x)=e^N/n$.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** Agents are `Fin n` (0-based). Rules are maps $\mathbb R^N\to\mathbb R^N$, measurable on all of $\mathbb R^N$ and simplex-valued on $\mathbb R^N_+$; their values off the orthant play no role. Fair Share is required for every normalized law, which for a prior-independent rule is the same as for every problem (the rule only sees the normalized profile).
-- source:
--   Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, pp. 8–10, Definitions 2–8

import Mathlib

namespace FairRandomObject.Bads

open MeasureTheory

/-! Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object,
arXiv:1903.10361v4, pp. 8–10, Definitions 2–8: the model of a random bad divided among the
agents `N = {1, …, n}`.

**Formalization Note.** Agents are `Fin n` (0-based: the paper's agent `1` is `⟨0, _⟩`). A
profile of (normalized) disutilities is a vector `x : Fin n → ℝ`; the paper's positive orthant
`ℝ^N_+` is `{x | 0 ≤ x}` and includes profiles with zero coordinates. -/

/-- p. 10: the arithmetic mean `x̄ = x_N / n` of a profile, where `x_N = ∑_{i ∈ N} x_i`. -/
noncomputable def mean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

/-- The vector `e^N = (1, …, 1)`. -/
def eN (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- Definitions 2 and 7, pp. 8–9: the law `μ` of a **normalized** division problem. `μ` is a
probability measure on `ℝ^N` carried by the orthant `ℝ^N_+`, each coordinate `x_i` is
`μ`-integrable and has expectation `E_μ(X_i) = 1`. The random object `X` is the identity map;
the coordinates may be arbitrarily correlated. -/
def IsNormalized {n : ℕ} (μ : Measure (Fin n → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧ μ {x | ¬ 0 ≤ x} = 0 ∧
    ∀ i, Integrable (fun x => x i) μ ∧ ∫ x, x i ∂μ = 1

/-- Definitions 3–4, p. 8: an almost prior-independent (API) division rule is a single map
from profiles to share vectors (it does not depend on the prior `μ`). -/
abbrev Rule (n : ℕ) := (Fin n → ℝ) → (Fin n → ℝ)

/-- Definitions 3–4, p. 8: `ϕ` is an API division rule: it is measurable and maps every
profile `x ∈ ℝ^N_+` to a lottery `ϕ(x)` in the simplex `Δ(N)`.

**Formalization Note.** The paper's rules are measurable maps on `ℝ^N_+`; here they are
measurable on all of `ℝ^N` (any measurable rule on the orthant extends), and their values off
the orthant play no role anywhere. -/
def IsAPIRule {n : ℕ} (ϕ : Rule n) : Prop :=
  Measurable ϕ ∧ ∀ x : Fin n → ℝ, 0 ≤ x → ϕ x ∈ stdSimplex ℝ (Fin n)

/-- Definition 5, p. 8: `ϕ` is symmetric: for every permutation `π` of `N`, every profile
`x ∈ ℝ^N_+` and every agent `i`, `ϕ_i(x) = ϕ_{π(i)}(π(x))`, where `π(x)_{π(j)} = x_j`, i.e.
`π(x) = x ∘ π⁻¹`. -/
def IsSymmetric {n : ℕ} (ϕ : Rule n) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (x : Fin n → ℝ), 0 ≤ x →
    ∀ i, ϕ (fun j => x (π.symm j)) (π i) = ϕ x i

/-- Definition 6, p. 9 (the case of a bad, inequality (1) reversed): `ϕ` guarantees Fair
Share: in every normalized problem `μ`, every agent's expected disutility from her share is
at most `1/n`, `E_μ(ϕ_i(X) · X_i) ≤ 1/n`.

**Formalization Note.** Fair Share is quantified over all normalized laws (Definition 7), not
over all problems; for an API rule the two are equivalent, since the rule only sees the
normalized profile `X*`. -/
def FairShareBad {n : ℕ} (ϕ : Rule n) : Prop :=
  ∀ μ : Measure (Fin n → ℝ), IsNormalized μ → ∀ i, ∫ x, ϕ x i * x i ∂μ ≤ 1 / n

/-- (2)–(3), p. 10: the ex post social cost `∑_{i ∈ N} ϕ_i(x) · x_i` of the rule `ϕ` at the
profile `x`. -/
def cost {n : ℕ} (ϕ : Rule n) (x : Fin n → ℝ) : ℝ := ∑ i, ϕ x i * x i

/-- Definition 8, p. 10, in the case of a bad (inequalities (3) reversed): `ϕ` dominates `ψ`
if its social cost is at most that of `ψ` at every profile `x ∈ ℝ^N_+`, and strictly lower at
some profile `x ∈ ℝ^N_+`. -/
def DominatesBad {n : ℕ} (ϕ ψ : Rule n) : Prop :=
  (∀ x : Fin n → ℝ, 0 ≤ x → cost ϕ x ≤ cost ψ x) ∧ ∃ x : Fin n → ℝ, 0 ≤ x ∧ cost ϕ x < cost ψ x

/-- p. 9: the Equal Split rule `ϕ^es(x) = e^N / n`. -/
noncomputable def equalSplit (n : ℕ) : Rule n := fun _ _ => 1 / n

end FairRandomObject.Bads


