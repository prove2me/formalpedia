-- Prove2me | Definitions.Def_RobustObedientPersuasion_Saddle_Model
-- name    : RobustObedientPersuasion_Saddle_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:17.623928+00:00
-- url     : https://prove2.me/theorems/0e8f3ae7-8a9a-4302-a110-e3feb72fc48e
-- title:
--   §§2–3 — obedience regions, the identified set P(α), robustly obedient policies Π_RO(α), and the Sender payoff V(π | μ)
-- statement:
--   Let $\Omega$ (states) and $A$ (Receiver actions) be finite sets, $u,v:\Omega\times A\to\mathbb R$ the Receiver's and the Sender's utilities, and $\alpha\in\Delta(A)$ the observed population action distribution, with support $B=\operatorname{supp}(\alpha)=\{a:\alpha(a)>0\}$.
--
--   1. The **obedience region** of $a\in A$ is
--   $$M_a=\Big\{\nu\in\Delta(\Omega):\ \sum_{\omega\in\Omega}\nu(\omega)\big[u(a,\omega)-u(a',\omega)\big]\ge0\ \ \forall a'\in A\Big\},$$
--   the posteriors at which $a$ is a best response.
--   2. The maintained condition that **no action in $\operatorname{supp}(\alpha)$ is statewise strictly dominated** is taken in the meaning the paper gives it: $M_a\neq\emptyset$ for every $a\in B$.
--   3. The **identified set** is the weighted Minkowski sum
--   $$\mathcal P(\alpha)=\sum_{a\in B}\alpha(a)M_a=\Big\{\sum_{a\in B}\alpha(a)\mu_a:\ \mu_a\in M_a\ \forall a\in B\Big\}.$$
--   4. $\Pi_B$ is the set of direct signaling policies $\pi(\cdot\mid\omega)\in\Delta(A)$ with $\pi(a\mid\omega)=0$ for all $a\notin B$ and $\omega\in\Omega$.
--   5. The **robustly obedient policies** are
--   $$\Pi_{RO}(\alpha)=\Big\{\pi\in\Pi_B:\ \sum_{\omega\in\Omega}\pi(a\mid\omega)\mu(\omega)\big[u(a,\omega)-u(a',\omega)\big]\ge0\ \ \forall a\in B,\ a'\in A,\ \mu\in\mathcal P(\alpha)\Big\}.$$
--   6. The Sender's expected payoff under a robustly obedient policy $\pi$ and prior $\mu$ is
--   $$V(\pi\mid\mu)=\sum_{\omega\in\Omega}\sum_{a\in B}\mu(\omega)\pi(a\mid\omega)v(a,\omega).$$
--
--   These objects define the Sender's robust (max-min) persuasion problem over the priors consistent with the observed behaviour, which Lemma 2.1 and Theorem 3.1 study.
--
--   **Formalization Note** Utilities and policies are indexed state-first: `u ω a` is $u(a,\omega)$, `v ω a` is $v(a,\omega)$ and `π ω a` is $\pi(a\mid\omega)$. Probability vectors are elements of Mathlib's `stdSimplex` (the closed simplex, boundary points allowed). Posteriors $\nu_a$ are required only for $a\in B$; unsupported actions may have empty $M_a$ but still appear as deviations $a'$. Obedience is written in the unconditional form, so no division by $q^\pi_a(\mu)$ occurs.
-- source:
--   Shabab Neel, Robustly Obedient Data Driven Persuasion under State-dependent Sender Payoffs, STOC 2027 submission #51 (October 2026), PDF SHA-256 c8d16d8d566dd78eea1f7db42ce72f49000256f933311c4daac2de1df952b40d, §2 (pp. 2–3), Definition 2.2 (p. 3), footnotes 4–5 (p. 3), §3 definitions of M_a, P(α), Π_B, Π_RO(α) (pp. 3–4), payoff formula in Appendix D (p. 9)

import Mathlib

namespace RobustObedientPersuasion.Saddle

variable {Ω A : Type*} [Fintype Ω] [Fintype A]

/-! States `Ω` and actions `A` are finite. Utilities are real arrays indexed state-first:
`u ω a` is the Receiver's utility `u(a, ω)` and `v ω a` the Sender's `v(a, ω)`.
A signaling policy is `π : Ω → A → ℝ` with `π ω a = π(a | ω)`. -/

/-- The support `B = supp(α) = {a : α(a) > 0}` of the observed action distribution. -/
noncomputable def supp (α : A → ℝ) : Finset A := Finset.univ.filter (fun a => 0 < α a)

/-- The Receiver's obedience region
`M_a = {ν ∈ Δ(Ω) : ∑_ω ν(ω) [u(a, ω) - u(a', ω)] ≥ 0 for all a' ∈ A}`. -/
def obedienceRegion (u : Ω → A → ℝ) (a : A) : Set (Ω → ℝ) :=
  {ν | ν ∈ stdSimplex ℝ Ω ∧ ∀ a' : A, 0 ≤ ∑ ω, ν ω * (u ω a - u ω a')}

/-- The maintained condition: no action in `supp(α)` is statewise strictly dominated under `u`,
in the source's stated meaning that every supported action is optimal under some posterior,
i.e. `M_a ≠ ∅` for every `a ∈ supp(α)`. -/
def NoSupportedActionDominated (u : Ω → A → ℝ) (α : A → ℝ) : Prop :=
  ∀ a ∈ supp α, (obedienceRegion u a).Nonempty

/-- The data-driven identified set `P(α) = ∑_{a ∈ B} α(a) M_a`: priors `μ` of the form
`μ = ∑_{a ∈ B} α(a) ν_a` with `ν_a ∈ M_a` for every `a ∈ B`. Posteriors are required only
for supported actions. -/
def identifiedSet (u : Ω → A → ℝ) (α : A → ℝ) : Set (Ω → ℝ) :=
  {μ | ∃ ν : A → Ω → ℝ, (∀ a ∈ supp α, ν a ∈ obedienceRegion u a) ∧
    ∀ ω, μ ω = ∑ a ∈ supp α, α a * ν a ω}

/-- Direct signaling policies recommending only actions in `B`:
`Π_B = {π ∈ Π(A | Ω) : π(a | ω) = 0 for all a ∉ B, ω ∈ Ω}`. -/
def supportedPolicies (α : A → ℝ) : Set (Ω → A → ℝ) :=
  {π | (∀ ω a, 0 ≤ π ω a) ∧ (∀ ω, ∑ a, π ω a = 1) ∧ (∀ ω a, a ∉ supp α → π ω a = 0)}

/-- The robustly obedient policy set
`Π_RO(α) = {π ∈ Π_B : ∑_ω π(a|ω) μ(ω) [u(a,ω) - u(a',ω)] ≥ 0 ∀ a ∈ B, a' ∈ A, μ ∈ P(α)}`. -/
def robustlyObedientPolicies (u : Ω → A → ℝ) (α : A → ℝ) : Set (Ω → A → ℝ) :=
  {π | π ∈ supportedPolicies α ∧ ∀ μ ∈ identifiedSet u α, ∀ a ∈ supp α, ∀ a' : A,
    0 ≤ ∑ ω, π ω a * μ ω * (u ω a - u ω a')}

/-- The Sender's expected payoff under a robustly obedient policy,
`V(π | μ) = ∑_{ω ∈ Ω} ∑_{a ∈ B} μ(ω) π(a | ω) v(a, ω)`. -/
noncomputable def senderPayoff (v : Ω → A → ℝ) (α : A → ℝ) (π : Ω → A → ℝ) (μ : Ω → ℝ) : ℝ :=
  ∑ ω, ∑ a ∈ supp α, μ ω * π ω a * v ω a

end RobustObedientPersuasion.Saddle


