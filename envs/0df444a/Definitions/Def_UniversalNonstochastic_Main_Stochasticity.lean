-- Prove2me | Definitions.Def_UniversalNonstochastic_Main_Stochasticity
-- name    : UniversalNonstochastic_Main_Stochasticity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:06:11.089819+00:00
-- url     : https://prove2.me/theorems/f0769bdc-0690-4f57-b024-f68577a204bf
-- title:
--   $(\alpha,\beta)$-stochastic objects and the set $N_{\alpha,\beta}$
-- statement:
--   Let $K$ be prefix complexity, given by an optimal prefix decoder. For $\alpha\in\mathbb N_0$ and $\beta\in[0,\infty]$, an object $\omega\in\mathbb N$ is **$(\alpha,\beta)$-stochastic** if there is a finite set $\Omega\subseteq\mathbb N$ such that
--
--   1. $\omega\in\Omega$;
--   2. $K(\Omega)\le\alpha$;
--   3. $K(\omega\mid\Omega)\ge\log_2|\Omega|-\beta$.
--
--   Otherwise $\omega$ is **$(\alpha,\beta)$-nonstochastic**. $N_{\alpha,\beta}\subseteq\mathbb N$ denotes the set of all $(\alpha,\beta)$-nonstochastic objects. Kolmogorov's notion uses finite sets as models; $\Omega$ is nonempty because it contains $\omega$.
--
--   **Formalization Note** The predicate takes an extended-real parameter, so the source's case $\beta=\infty$ is included: its third condition is vacuous. Every theorem explicitly restricts $\beta$ to nonnegative finite real values. Membership guarantees $|\Omega|\ge1$, so the logarithm is finite; at $\beta=\infty$ its difference is $-\infty$. `IsStochasticOn` transports the same predicate to another object space by the fixed computable bijection; its finite models correspond bijectively to those on the positive integers.
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/11.pdf, Sect. 2 p.5 (definition of (α,β)-stochastic objects and N_{α,β})

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Complexity

namespace UniversalNonstochastic.Main

/-- `ω` is `(α, β)`-stochastic (Kolmogorov): some finite set `Ω ∋ ω` has `K(Ω) ≤ α` and
`K(ω | Ω) ≥ log₂ |Ω| - β`. Extended-real `β` includes the source's `β = +∞`;
all theorem parameters are nonnegative and finite. -/
def IsStochastic (U : OptimalPrefixDecoder) (α : ℕ) (β : EReal) (ω : ℕ+) : Prop :=
  ∃ Ω : Finset ℕ+, ω ∈ Ω ∧ Kset U Ω ≤ (α : ℕ∞) ∧
    ((Real.logb 2 (Ω.card : ℝ) : ℝ) : EReal) - β ≤ toEReal (KobjGivenSet U ω Ω)

/-- `N_{α,β}`: the set of `(α, β)`-nonstochastic objects. -/
def nonstochastic (U : OptimalPrefixDecoder) (α : ℕ) (β : EReal) : Set ℕ+ :=
  {ω | ¬ IsStochastic U α β ω}

/-- Stochasticity on another space is transported by the source's fixed bijection.
Its finite models correspond bijectively to the finite models on `ℕ+`. -/
def IsStochasticOn {X : Type*} [Primcodable X] (e : ObjectEncoding X)
    (U : OptimalPrefixDecoder) (α : ℕ) (β : EReal) (ω : X) : Prop :=
  IsStochastic U α β (e.equiv ω)

end UniversalNonstochastic.Main


