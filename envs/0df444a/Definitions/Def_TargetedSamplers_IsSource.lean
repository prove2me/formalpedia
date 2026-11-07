-- Prove2me | Definitions.Def_TargetedSamplers_IsSource
-- name    : TargetedSamplers_IsSource
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:20.5909+00:00
-- url     : https://prove2.me/theorems/37a9c033-5a55-48c6-8eb1-3450c7fd377c
-- title:
--   Min-entropy, $(n,b)$-sources and statistical distance (Definitions 4.3–4.4)
-- statement:
--   For distributions $P,Q$ on a finite set, the **statistical distance** is $\tfrac12\sum_a|P(a)-Q(a)|$ (the published `SamplingAC0.tvDist`), and $P,Q$ are **$\gamma$-close** if it is at most $\gamma$.
--
--   A distribution $X$ has **min-entropy at least $b$** if $b\le H_\infty(X)$, where $H_\infty(X)=-\log_2\max_a\Pr[X=a]$ is the published `SamplingAC0.minEntropy`. This is the same as $\Pr[X=a]\le 2^{-b}$ for every $a$ (Definition 4.3: $H_\infty(X)$ is the largest such $b$). An **$(n,b)$-source** is a distribution on $\{0,1\}^n$ with $H_\infty\ge b$ (Definition 4.4). Its min-entropy rate is $b/n$.
--
--   **Formalization Note** The paper measures distance "by their $L_1$ norm (i.e. statistical distance)"; the statistical distance $\tfrac12\|P-Q\|_1$ is used.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), §4.1.1 and Definitions 4.3–4.4, pp.20–21 (pdf pp.22–23)

import Mathlib
import Definitions.Def_SamplingAC0_tvDist
import Definitions.Def_SamplingAC0_minEntropy

namespace TargetedSamplers

/-- Two distributions on a finite set are `γ`-close if their statistical distance
`½ ∑ₐ |P(a) − Q(a)|` (the published `SamplingAC0.tvDist`) is at most `γ` (Chen, Doron, Ebtehaj, Tell,
Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, §4.1.1, p.20).

**Formalization Note** The paper says "L1 norm (i.e. statistical distance)"; the statistical
distance `½‖P − Q‖₁` is used. -/
def IsClose {α : Type} [Fintype α] (γ : ℝ) (P Q : PMF α) : Prop := SamplingAC0.tvDist P Q ≤ γ

/-- `H∞(X) ≥ b` (Definition 4.3, p.21: the min-entropy of `X` is the largest `b` with
`Pr[X = x] ≤ 2^{−b}` for every `x ∈ supp(X)`), with `H∞` the published
`SamplingAC0.minEntropy X = −log₂ maxₓ Pr[X = x]`. -/
def HasMinEntropy {α : Type} [Fintype α] (X : PMF α) (b : ℝ) : Prop :=
  b ≤ SamplingAC0.minEntropy X

/-- An `(n, b)`-source (Definition 4.4, p.21): a distribution on `{0,1}ⁿ` with min-entropy at least
`b`. Its min-entropy rate is `b/n`. -/
def IsSource (n : ℕ) (b : ℝ) (X : PMF (Fin n → Bool)) : Prop := HasMinEntropy X b

end TargetedSamplers


