-- Prove2me | Definitions.Def_RetailTheft_Model
-- name    : RetailTheft_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:37.148199+00:00
-- url     : https://prove2.me/theorems/93fc9914-da7a-4e4e-b5e6-1414074c8be1
-- title:
--   Retail-theft principal–agent model: demand, revenue, $\mathcal R$, $\Gamma$, agent utility (4), problems (5)–(7) and (8), $R_{\bar r}$ (9), $\bar F_p^{-1}$, $V(p)$ (13)–(14)
-- statement:
--   A firm (the principal) gives a store manager (the agent) capacity $q\ge 0$ at unit cost $c>0$ and sets the retail price $p>0$. Demand is multiplicative,
--   $$
--   D_p=a\,p^{-b}\,\varepsilon,\qquad a>0,\ b>1,
--   $$
--   where the shock $\varepsilon$ has law $\mu$. **Standing assumptions:** $\mu$ is a probability measure on $[0,\infty)$ whose cdf $F(x)=\mu(-\infty,x]$ is continuous and strictly increasing on $\{0<F<1\}$.
--
--   **Theft.** The agent may deploy only $q'\in[0,q]$ units (ex ante theft, earning $\theta c$ per diverted unit) and, after observing the revenue $r$, report $\gamma(r)\le r$ (ex post theft, earning $\lambda(r-\gamma(r))$). The realized revenue is $P_{p,q'}=p\,(D_p\wedge q')$ (1), and $\mathbb E$ is integration against $\mu$.
--
--   **Contracts.** A revenue-splitting rule $R\in\mathcal R$ is nondecreasing with $R(r)\le r$ for $r\ge 0$; a report $\gamma\in\Gamma$ satisfies $0\le\gamma(r)\le r$. The agent's utility (4) is
--   $$
--   U(q',\gamma\mid p,q)=\theta c(q-q')+\mathbb E\big[\lambda(P_{p,q'}-\gamma(P_{p,q'}))+\gamma(P_{p,q'})-R(\gamma(P_{p,q'}))\big].
--   $$
--   A tuple $(p,q,R,q',\gamma)$ is **feasible** for the principal's problem (5)–(7) if $p>0$, $q\ge0$, $R\in\mathcal R$ and $(q',\gamma)$ maximizes $U(\cdot,\cdot\mid p,q)$ over $[0,q]\times\Gamma$. Its objective is $\mathbb E[R(\gamma(P_{p,q'}))]-cq$. It is **optimal** if its objective is at least that of every feasible tuple, and **fixed-price optimal** if this holds among feasible tuples with the same price. A pair $(p,q)$ is an **optimal pair** if some optimal tuple has price $p$ and capacity $q$.
--
--   **Problem (8).** $(p,q,R)$ is feasible for (8) if $p>0$, $q\ge0$, $R$ is nondecreasing and
--   1. (LL) $R(r)\le r$ for $r\ge0$;
--   2. (Ex Ante IC) $\mathbb E[P_{p,q}-R(P_{p,q})]\ge\mathbb E[P_{p,q'}-R(P_{p,q'})]+\theta c(q-q')$ for all $q'\in[0,q]$;
--   3. (Ex Post IC) $r-R(r)\ge r'-R(r')+\lambda(r-r')$ for all $0\le r'\le r$.
--
--   Its objective is $\mathbb E[R(P_{p,q})]-cq$.
--
--   **Threshold commission (9):** $R_{\bar r}(r)=(1-\lambda)(r\wedge\bar r)$.
--
--   **Quantiles.** $\bar F_p(q)=\mathbb P(D_p>q)$, and $\bar F_p^{-1}(y)$ is the largest $q\ge0$ with $\bar F_p(q)\ge y$. The capacity $q^*$ of Proposition 1 is $\bar F_p^{-1}((1+\theta)c/p)$ in cases (1)–(2) ($\lambda p\le\theta c$ and $(1+\theta)c<p$, or $\theta c<\lambda p$ and $\lambda<\theta/(1+\theta)$), $\bar F_p^{-1}(c/((1-\lambda)p))$ in case (3) ($\lambda\ge\theta/(1+\theta)$ and $p\ge c/(1-\lambda)$), and $0$ otherwise.
--
--   **Value function (13)–(14)**, with $q^*=\bar F_p^{-1}((1+\theta)c/p)$ and $\tilde q=\bar F_p^{-1}(\theta c/(\lambda p))$ when $\lambda<\theta/(1+\theta)$:
--   $$
--   V(p)=\begin{cases}\mathbb E[P_{p,q^*}]-(1+\theta)cq^*, & (1+\theta)c<p\le\theta c/\lambda,\\ \mathbb E[P_{p,q^*}]-\lambda\mathbb E[P_{p,\tilde q}]-(1+\theta)cq^*+\theta c\tilde q, & p>\theta c/\lambda,\\ 0 & \text{otherwise;}\end{cases}
--   $$
--   and, when $\lambda\ge\theta/(1+\theta)$, with $q^*=\bar F_p^{-1}(c/((1-\lambda)p))$: $V(p)=(1-\lambda)\mathbb E[P_{p,q^*}]-cq^*$ if $p>c/(1-\lambda)$, and $0$ otherwise.
--
--   These are the primitives on which every result of the mission is stated.
--
--   **Formalization Note** $\theta$ and $\lambda$ (`lam`) are explicit arguments, not fields of the parameter structure. $R$ is `Monotone` on all of $\mathbb R$ (only its values on $[0,\infty)$ matter). Reports are measurable. Every branch condition is multiplied out ($\lambda p\le\theta c$ for $p\le\theta c/\lambda$, which at $\lambda=0$ is the paper's $\theta c/0=+\infty$). The second branch of (13) carries $+\theta c\tilde q$ where the paper prints $+\theta\tilde q$ (a slip: see the proof of Proposition EC.2, p. ec8). $\bar F_p^{-1}$ is a supremum; it is only used at $y\in(0,1]$.
-- source:
--   Chen–Tian–Zuo, Optimal Capacity and Price Designs Under Ex Ante and Ex Post Theft, MSOM (2025), doi:10.1287/msom.2025.0024, §3, (1)–(8), pp. 7–10; (9), p. 11; Proposition 1, p. 13 (F̄_p^{-1}, q*); Corollary 1, (13)–(14), pp. 14–15; corrected θcq̃ from the proof of Proposition EC.2, p. ec8

import Mathlib

open MeasureTheory

namespace RetailTheft

/-- The fixed data of the retail-theft model of Chen, Tian and Zuo, *Optimal Capacity and Price
Designs Under Ex Ante and Ex Post Theft*, Manufacturing & Service Operations Management (2025),
doi:10.1287/msom.2025.0024, §3, pp. 7–9 (PDF 7–9).

* `a`, `b` are the demand parameters of (2), `D_p = a p^{-b} ε`;
* `c` is the unit capacity cost;
* `μ` is the law of the demand shock `ε`.

**Formalization Note** The stealing efficiencies `θ` (ex ante) and `λ` (ex post, written `lam`)
are not fields: every definition below takes them as explicit arguments, because Theorem 2
varies `λ`. The standing assumptions are the separate predicate `Params.Standing`. -/
structure Params where
  a : ℝ
  b : ℝ
  c : ℝ
  μ : Measure ℝ

/-- The cdf `F(x) = P(ε ≤ x)` of the demand shock. -/
noncomputable def Params.cdf (M : Params) (x : ℝ) : ℝ := (M.μ (Set.Iic x)).toReal

/-- The standing assumptions of §3, p. 8 (PDF 8): `a > 0`, `b > 1`, `c > 0`, and `ε` is a
nonnegative random variable "with a known distribution and a well-defined inverse function".

**Formalization Note** The last phrase is read as: `μ` is a probability measure with
`μ(-∞, 0) = 0` whose cdf `F` is continuous and strictly increasing on `{x : 0 < F x < 1}`; then
`F` has a well-defined inverse on `(0, 1)`. The paper writes `a ∈ ℝ₊`; `a > 0` is the reading
(at `a = 0` demand vanishes and `F̄_p^{-1}` is degenerate) and `c > 0` is the reading of a unit
cost. -/
structure Params.Standing (M : Params) : Prop where
  a_pos : 0 < M.a
  b_gt_one : 1 < M.b
  c_pos : 0 < M.c
  isProb : IsProbabilityMeasure M.μ
  nonneg : M.μ (Set.Iio 0) = 0
  cdf_continuous : Continuous M.cdf
  cdf_strictMonoOn : StrictMonoOn M.cdf {x | 0 < M.cdf x ∧ M.cdf x < 1}

/-- Demand (2), p. 8: `D_p(ε) = a p^{-b} ε` (`Real.rpow`; prices are positive). -/
noncomputable def demand (M : Params) (p ε : ℝ) : ℝ := M.a * p ^ (-M.b) * ε

/-- Sales revenue (1), p. 8: `P_{p,q'}(ε) = p (D_p(ε) ∧ q')` at price `p` and deployed
capacity `q'`. -/
noncomputable def revenue (M : Params) (p q' ε : ℝ) : ℝ := p * min (demand M p ε) q'

/-- Expected revenue `E[P_{p,q}] = ∫ P_{p,q}(ε) dμ(ε)`. -/
noncomputable def expRevenue (M : Params) (p q : ℝ) : ℝ := ∫ ε, revenue M p q ε ∂M.μ

/-- The class `ℛ` of revenue-splitting functions, p. 8: `R` is nondecreasing and satisfies
limited liability `R(r) ≤ r` for `r ≥ 0`.

**Formalization Note** The paper asks `R(r') ≤ R(r)` for `r ≥ r' ≥ 0` only; here `R` is
`Monotone` on all of `ℝ`. Only values on `[0, ∞)` are ever evaluated (revenues and reports are
nonnegative), and every `R` nondecreasing on `[0, ∞)` agrees there with the monotone function
`r ↦ R (max r 0)`, so the class of objective values is unchanged. -/
def IsRepayment (R : ℝ → ℝ) : Prop :=
  Monotone R ∧ ∀ r, 0 ≤ r → R r ≤ r

/-- The class `Γ` of reporting functions (3), p. 8: `γ(r) ≤ r` for `r ≥ 0`.

**Formalization Note** Reports are also required to be measurable (the expectation in (4) is
taken of `γ(P_{p,q'})`) and nonnegative (`R` is only defined on reports `≥ 0`). -/
def IsReport (γ : ℝ → ℝ) : Prop :=
  Measurable γ ∧ ∀ r, 0 ≤ r → 0 ≤ γ r ∧ γ r ≤ r

/-- The agent's utility (4), p. 9, given capacity `q` and price `p`, when he deploys `q'` and
reports with `γ`:
`U(q', γ | p, q) = θc(q − q') + E[λ(P_{p,q'} − γ(P_{p,q'})) + (γ(P_{p,q'}) − R(γ(P_{p,q'})))]`. -/
noncomputable def agentUtility (M : Params) (θ lam : ℝ) (R : ℝ → ℝ) (p q q' : ℝ)
    (γ : ℝ → ℝ) : ℝ :=
  θ * M.c * (q - q') +
    ∫ ε, (lam * (revenue M p q' ε - γ (revenue M p q' ε)) +
      (γ (revenue M p q' ε) - R (γ (revenue M p q' ε)))) ∂M.μ

/-- Constraint (7), p. 9: `(q', γ)` is a best response of the agent, i.e. it lies in
`[0, q] × Γ` and maximizes `U(· , · | p, q)` over `[0, q] × Γ`. -/
def IsBestResponse (M : Params) (θ lam : ℝ) (R : ℝ → ℝ) (p q q' : ℝ) (γ : ℝ → ℝ) : Prop :=
  q' ∈ Set.Icc 0 q ∧ IsReport γ ∧
    ∀ q₁ ∈ Set.Icc 0 q, ∀ γ₁ : ℝ → ℝ, IsReport γ₁ →
      agentUtility M θ lam R p q q₁ γ₁ ≤ agentUtility M θ lam R p q q' γ

/-- Feasibility in the principal's problem (5)–(7), p. 9: the contract `(p, q, R)` lies in
`ℝ₊ × ℝ₊ × ℛ` (6) and `(q', γ)` is a best response of the agent (7).

**Formalization Note** Prices are positive (`p > 0`): demand `a p^{-b} ε` is undefined at
`p = 0`, and Proposition 1 fixes `p > 0`. Stealing is allowed: `q' < q` and `γ ≠ id` are
feasible. -/
def IsFeasible (M : Params) (θ lam : ℝ) (p q : ℝ) (R : ℝ → ℝ) (q' : ℝ) (γ : ℝ → ℝ) : Prop :=
  0 < p ∧ 0 ≤ q ∧ IsRepayment R ∧ IsBestResponse M θ lam R p q q' γ

/-- The principal's objective (5), p. 9: `E[R(γ(P_{p,q'}))] − cq`. -/
noncomputable def objective (M : Params) (p q : ℝ) (R : ℝ → ℝ) (q' : ℝ) (γ : ℝ → ℝ) : ℝ :=
  (∫ ε, R (γ (revenue M p q' ε)) ∂M.μ) - M.c * q

/-- An optimal tuple of the principal's problem (5)–(7), p. 9: feasible, with objective at
least that of every feasible tuple.

**Formalization Note** Footnote 1 (p. 9): among several best responses the agent picks the one
the principal prefers. This is encoded by maximizing jointly over `(p, q, R, q', γ)` subject to
`(q', γ)` being a best response. -/
def IsOptimal (M : Params) (θ lam : ℝ) (p q : ℝ) (R : ℝ → ℝ) (q' : ℝ) (γ : ℝ → ℝ) : Prop :=
  IsFeasible M θ lam p q R q' γ ∧
    ∀ (p₁ q₁ : ℝ) (R₁ : ℝ → ℝ) (q₁' : ℝ) (γ₁ : ℝ → ℝ), IsFeasible M θ lam p₁ q₁ R₁ q₁' γ₁ →
      objective M p₁ q₁ R₁ q₁' γ₁ ≤ objective M p q R q' γ

/-- An optimal tuple of problem (5)–(7) at the fixed price `p` (Proposition 1, "Fix price
`p > 0`"): feasible, with objective at least that of every feasible tuple with the same price. -/
def IsFixedPriceOptimal (M : Params) (θ lam : ℝ) (p q : ℝ) (R : ℝ → ℝ) (q' : ℝ)
    (γ : ℝ → ℝ) : Prop :=
  IsFeasible M θ lam p q R q' γ ∧
    ∀ (q₁ : ℝ) (R₁ : ℝ → ℝ) (q₁' : ℝ) (γ₁ : ℝ → ℝ), IsFeasible M θ lam p q₁ R₁ q₁' γ₁ →
      objective M p q₁ R₁ q₁' γ₁ ≤ objective M p q R q' γ

/-- `(p, q)` is an optimal price and capacity: some optimal tuple of problem (5)–(7) has price
`p` and capacity `q`. -/
def OptimalPair (M : Params) (θ lam : ℝ) (p q : ℝ) : Prop :=
  ∃ (R : ℝ → ℝ) (q' : ℝ) (γ : ℝ → ℝ), IsOptimal M θ lam p q R q' γ

/-- Feasibility in the reformulated problem (8) of Lemma 1, p. 10 (PDF 10): `p > 0`, `q ≥ 0`,
`R` nondecreasing, and
* (LL) `R(r) ≤ r` for all `r ≥ 0`;
* (Ex Ante IC) `E[P_{p,q} − R(P_{p,q})] ≥ E[P_{p,q'} − R(P_{p,q'})] + θc(q − q')` for all
  `q' ∈ [0, q]`;
* (Ex Post IC) `r − R(r) ≥ r' − R(r') + λ(r − r')` for all `0 ≤ r' ≤ r`.

**Formalization Note** The printed (8) has `p ≥ 0`; `p > 0` is kept as in (5). "`∀ q' ≤ q`" is
read with `q' ≥ 0` (a capacity). -/
def IsFeasible8 (M : Params) (θ lam : ℝ) (p q : ℝ) (R : ℝ → ℝ) : Prop :=
  0 < p ∧ 0 ≤ q ∧ Monotone R ∧ (∀ r, 0 ≤ r → R r ≤ r) ∧
    (∀ q' ∈ Set.Icc 0 q,
      (∫ ε, (revenue M p q' ε - R (revenue M p q' ε)) ∂M.μ) + θ * M.c * (q - q') ≤
        ∫ ε, (revenue M p q ε - R (revenue M p q ε)) ∂M.μ) ∧
    (∀ r r', 0 ≤ r' → r' ≤ r → r' - R r' + lam * (r - r') ≤ r - R r)

/-- The objective of problem (8), p. 10: `E[R(P_{p,q})] − cq`. -/
noncomputable def objective8 (M : Params) (p q : ℝ) (R : ℝ → ℝ) : ℝ :=
  (∫ ε, R (revenue M p q ε) ∂M.μ) - M.c * q

/-- The threshold commission (9), p. 11 (PDF 11): `R_r̄(r) = (1 − λ)(r ∧ r̄)`. -/
noncomputable def thresholdR (lam rbar : ℝ) (r : ℝ) : ℝ := (1 - lam) * min r rbar

/-- The survival function of demand, `F̄_p(q) = P(D_p > q)`. -/
noncomputable def survival (M : Params) (p q : ℝ) : ℝ :=
  (M.μ {ε | q < demand M p ε}).toReal

/-- The inverse `F̄_p^{-1}(y)` used in Proposition 1, p. 13: the largest `q ≥ 0` with
`F̄_p(q) ≥ y`.

**Formalization Note** For `y ∈ (0, 1)` and `M.Standing` this is the unique root of
`F̄_p(q) = y`; for `y = 1` it is the bottom of the support of `D_p`. It is only evaluated at
`y ∈ (0, 1]` in this development. On other inputs the `sSup` is a Lean default (`0` for an
empty or unbounded set). -/
noncomputable def survInv (M : Params) (p y : ℝ) : ℝ :=
  sSup {q : ℝ | 0 ≤ q ∧ y ≤ survival M p q}

/-- The optimal capacity `q*` of Proposition 1, p. 13, at price `p > 0`:
* cases (1)–(2) (`(1+θ)c < p` and `λp ≤ θc`, or `θc < λp` and `λ(1+θ) < θ`):
  `q* = F̄_p^{-1}((1+θ)c/p)`;
* case (3) (`λ(1+θ) ≥ θ` and `c ≤ (1−λ)p`): `q* = F̄_p^{-1}(c/((1−λ)p))`;
* case (4), otherwise: `q* = 0`.

**Formalization Note** The branch conditions are those of Proposition 1 multiplied out
(`λ ≤ θc/p` as `λp ≤ θc`, `λ < θ/(1+θ)` as `λ(1+θ) < θ`, `p ≥ c/(1−λ)` as `c ≤ (1−λ)p`), so
that no division by `λ` or `1 − λ` occurs. -/
noncomputable def capStar (M : Params) (θ lam p : ℝ) : ℝ :=
  if ((lam * p ≤ θ * M.c ∧ (1 + θ) * M.c < p) ∨ (θ * M.c < lam * p ∧ lam * (1 + θ) < θ)) then
    survInv M p ((1 + θ) * M.c / p)
  else if (θ ≤ lam * (1 + θ) ∧ M.c ≤ (1 - lam) * p) then
    survInv M p (M.c / ((1 - lam) * p))
  else 0

/-- The value function `V(p)` of Corollary 1, (13)–(14), pp. 14–15 (PDF 15), with
`q* = F̄_p^{-1}((1+θ)c/p)` in (13), `q* = F̄_p^{-1}(c/((1−λ)p))` in (14) and
`q̃ = F̄_p^{-1}(θc/(λp))`:
* when `λ < θ/(1+θ)`: `V(p) = E[P_{p,q*}] − (1+θ)cq*` if `(1+θ)c < p ≤ θc/λ`;
  `V(p) = E[P_{p,q*}] − λE[P_{p,q̃}] − (1+θ)cq* + θcq̃` if `p > θc/λ`; `0` otherwise;
* when `λ ≥ θ/(1+θ)`: `V(p) = (1−λ)E[P_{p,q*}] − cq*` if `p > c/(1−λ)`; `0` otherwise.

**Formalization Note** The printed second branch of (13) ends in `+ θq̃`; it is corrected to
`+ θcq̃`, the principal's utility derived in the proof of Proposition EC.2 (p. ec8, (EC.21)).
Branch conditions are multiplied out (`p ≤ θc/λ` as `λp ≤ θc`, which at `λ = 0` is the paper's
`θc/0 = +∞`; `p > θc/λ` as `θc < λp`; `p > c/(1−λ)` as `c < (1−λ)p`). -/
noncomputable def V (M : Params) (θ lam p : ℝ) : ℝ :=
  if lam * (1 + θ) < θ then
    if (1 + θ) * M.c < p ∧ lam * p ≤ θ * M.c then
      expRevenue M p (survInv M p ((1 + θ) * M.c / p)) -
        (1 + θ) * M.c * survInv M p ((1 + θ) * M.c / p)
    else if θ * M.c < lam * p then
      expRevenue M p (survInv M p ((1 + θ) * M.c / p)) -
        lam * expRevenue M p (survInv M p (θ * M.c / (lam * p))) -
        (1 + θ) * M.c * survInv M p ((1 + θ) * M.c / p) +
        θ * M.c * survInv M p (θ * M.c / (lam * p))
    else 0
  else if M.c < (1 - lam) * p then
    (1 - lam) * expRevenue M p (survInv M p (M.c / ((1 - lam) * p))) -
      M.c * survInv M p (M.c / ((1 - lam) * p))
  else 0

end RetailTheft


