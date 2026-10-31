-- Prove2me | Definitions.Def_FamilyGenTest_risk
-- name    : FamilyGenTest_risk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:32.158991+00:00
-- url     : https://prove2.me/theorems/444b7aea-e7f1-488d-93f9-89c56c5e810d
-- title:
--   Family states, posterior, marginals and the genetic risk $\mathbb P_i(\mathbf s)$
-- statement:
--   Let $\mathcal I$ be a finite family and consider one gene. The genetic status of person $i$ is the number $g_i\in\Gamma=\{0,1,2\}$ of pathogenic copies, and the **prior** is a probability mass function $\mathbb P(G=g)$ on $\{0,1,2\}^{\mathcal I}$.
--
--   A **state** $\mathbf s$ records the test results so far: each person is either untested or tested with a result $\gamma\in\Gamma$. The set of genotypes compatible with $\mathbf s$ is $\mathcal G(\mathbf s)$, and $\mathbf s$ is **feasible** when $\mathbb P(G\in\mathcal G(\mathbf s))>0$. The admissible actions are $\mathcal A_{\mathbf s}=(\mathcal I\setminus\mathbf s)\cup\{\varnothing\}$, and $\mathbf s_\gamma\cup\{i\}$ denotes $\mathbf s$ with $i$ tested with result $\gamma$.
--
--   The **posterior** and the **marginals** are
--   $$
--   \mu(g\mid\mathbf s)=\begin{cases}\dfrac{\mathbb P(G=g)}{\mathbb P(G\in\mathcal G(\mathbf s))}&g\in\mathcal G(\mathbf s)\\0&g\notin\mathcal G(\mathbf s)\end{cases},
--   \qquad
--   \mathbb P(G_i=\gamma\mid\mathbf s)=\sum_{g\in\mathcal G(\mathbf s):\,g_i=\gamma}\mu(g\mid\mathbf s),
--   $$
--   the **genetic risk** is $\mathbb P_i(\mathbf s)=\mathbb P(G_i\in\{1,2\}\mid\mathbf s)$, and
--   $$
--   \alpha_i(\mathbf s)=\frac{\mathbb P(G_i=1\mid\mathbf s)}{\mathbb P(G_i=1\mid\mathbf s)+\mathbb P(G_i=2\mid\mathbf s)}.
--   $$
--
--   These objects carry the Bayesian updating of the whole mission.
--
--   **Formalization Note** A state is a map `I → Option (Fin 3)`. The paper's sample space $\mathcal G$ is the support of the prior. At an infeasible state the posterior is $0$, and $\alpha_i(\mathbf s)=0$ when its denominator is $0$.
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), §2.2, p.7; Definition 1, p.8; (6), (7), p.12; Proof of Theorem 1, p.ec2

import Mathlib

namespace FamilyGenTest

/-- The prior of the genetic status of a family `I`, for one gene: the law `ℙ(G = g)` of
`G ∈ {0,1,2}^I` (Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023),
§2.2, p.7, and (5), p.11).

**Formalization Note** The prior is an arbitrary mass function on `{0,1,2}^I`; the Mendelian prior
of (5) is an instance (`eq_5_mendelian_prior`). The status `gᵢ ∈ Γ = {0,1,2}` is an element of
`Fin 3`. The paper's sample space `𝒢` is the support of the prior: the family `I` is a `Fintype`,
possibly empty, and a single gene is modelled (`|𝒥| = 1`), the setting of Assumption 4 and of §4.3,
p.15. -/
structure Prior (I : Type*) [Fintype I] [DecidableEq I] where
  /-- The probability `ℙ(G = g)`. -/
  prob : (I → Fin 3) → ℝ
  nonneg : ∀ g, 0 ≤ prob g
  sum_eq_one : ∑ g, prob g = 1

/-- A state records the test results so far (Adelman & Wang, SSRN 4624694, §2.2, "State", p.7):
`s i = some γ` when `i ∈ s_γ`, and `s i = none` when `i ∈ I \ s` is untested.

**Formalization Note** The map `I → Option (Fin 3)` is the paper's partition `{s₀, s₁, s₂}` of the
tested individuals. The paper's absorbing state `Δ` and its action `C` have no counterpart, because
the return of `Vstar` ends at the stopping action. -/
abbrev State (I : Type*) := I → Option (Fin 3)

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The state `s_γ ∪ {i}`: the state `s` with `i` tested with result `γ`
(Adelman & Wang, SSRN 4624694, "Transition", p.8, and notation before (EC.2), p.ec2). -/
def test (s : State I) (i : I) (γ : Fin 3) : State I := Function.update s i (some γ)

/-- The untested individuals `I \ s` (Adelman & Wang, SSRN 4624694, p.7). -/
def untested (s : State I) : Finset I := Finset.univ.filter fun i => s i = none

/-- The admissible actions `𝒜_s = (I \ s) ∪ {∅}` of a state (Adelman & Wang, SSRN 4624694, p.8):
`some i` tests the untested `i`, and `none` is the paper's `∅`, stop testing. -/
def actionSet (s : State I) : Finset (Option I) := insert none ((untested s).image some)

/-- The genotypes `𝒢(s)` compatible with the state `s` (Adelman & Wang, SSRN 4624694, p.7). -/
def compatible (s : State I) : Finset (I → Fin 3) :=
  Finset.univ.filter fun g => ∀ i γ, s i = some γ → g i = γ

/-- The probability `ℙ(G ∈ 𝒢(s))` (Adelman & Wang, SSRN 4624694, (7), p.12). -/
noncomputable def mass (μ : Prior I) (s : State I) : ℝ := ∑ g ∈ compatible s, μ.prob g

/-- A state is feasible when it has positive probability. This is the paper's state space
`𝒮 = {s : ∃ g ∈ 𝒢(s)}` (Adelman & Wang, SSRN 4624694, p.7) when `𝒢` is the support of the prior. -/
def Feasible (μ : Prior I) (s : State I) : Prop := 0 < mass μ s

/-- The posterior `μ(g | s)` of (7) (Adelman & Wang, SSRN 4624694, (7), p.12): `ℙ(G = g)/ℙ(G ∈ 𝒢(s))`
for `g ∈ 𝒢(s)`, and `0` otherwise.

**Formalization Note** At an infeasible state the division by `0` makes the posterior `0`. -/
noncomputable def posterior (μ : Prior I) (s : State I) (g : I → Fin 3) : ℝ :=
  if g ∈ compatible s then μ.prob g / mass μ s else 0

/-- The marginal `ℙ(Gᵢ = γ | s)` of (6) (Adelman & Wang, SSRN 4624694, (6), p.12). -/
noncomputable def marginal (μ : Prior I) (s : State I) (i : I) (γ : Fin 3) : ℝ :=
  ∑ g ∈ (compatible s).filter (fun g => g i = γ), posterior μ s g

/-- The genetic risk `ℙᵢ(s) = ℙ(Gᵢ ∈ {1,2} | S = s)` (Adelman & Wang, SSRN 4624694, Definition 1,
p.8), for one gene. -/
noncomputable def risk (μ : Prior I) (s : State I) (i : I) : ℝ :=
  marginal μ s i 1 + marginal μ s i 2

/-- `αᵢ(s) = ℙ(gᵢ = 1 | s)/(ℙ(gᵢ = 1 | s) + ℙ(gᵢ = 2 | s))` (Adelman & Wang, SSRN 4624694, Proof of
Theorem 1, p.ec2).

**Formalization Note** `αᵢ(s) = 0` when the denominator `ℙᵢ(s)` is `0`, which can happen at a
feasible state; every use of `α` is then multiplied by `ℙᵢ(s) = 0`. -/
noncomputable def alpha (μ : Prior I) (s : State I) (i : I) : ℝ :=
  marginal μ s i 1 / (marginal μ s i 1 + marginal μ s i 2)

end FamilyGenTest


