-- Prove2me | Definitions.Def_SolomonRWRE_Recurrence_Model
-- name    : SolomonRWRE_Recurrence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:17.914996+00:00
-- url     : https://prove2.me/theorems/b4967277-8ac2-4cfc-9948-39b400694f4f
-- title:
--   §0–§1, pp. 1–5 — the chain M_α, the random walk in a random environment, σ_n, ρ_n, f_ij, the two series and E(ln σ)
-- statement:
--   This file sets up the random walk in a random environment of Solomon (1975) and the quantities in which its limit behaviour is expressed.
--
--   **Fixed environment.** An environment is a sequence $a=(a_n)_{n\in\mathbb Z}$ of numbers in $[0,1]$. The chain $M_a$ on $\mathbb Z$ moves one step at a time with transition probabilities
--   $$M_a(n,n+1)=a_n,\qquad M_a(n,n-1)=\beta_n=1-a_n .$$
--   A process $(X_n)_{n\ge0}$ on a probability space $(\Omega,\mathcal F,P)$ is this chain started at $i$ when, for every $n$ and all $x_0,\dots,x_n\in\mathbb Z$,
--   $$P(X_0=x_0,\dots,X_n=x_n)=\mathbf 1\{x_0=i\}\prod_{k=0}^{n-1}M_a(x_k,x_{k+1}).$$
--
--   **Random environment.** Let $\alpha=(\alpha_n)_{n\in\mathbb Z}$ be independent, identically distributed random variables with values in $[0,1]$, and $Q$ their joint law. The random walk in a random environment is a process $(X_n)_{n\ge0}$, defined together with $\alpha$, such that for every measurable set $A$ of environments and every path cylinder
--   $$P\big(\alpha\in A,\ X_0=x_0,\dots,X_n=x_n\big)=\int_{\{\alpha\in A\}}\mathbf 1\{x_0=0\}\prod_{k=0}^{n-1}M_\alpha(x_k,x_{k+1})\,dP .$$
--   This is the paper's $P(A\times\Omega')=\int_A M_\alpha(\Omega')\,dQ(\alpha)$ on cylinders: given the environment, $X$ is the chain $M_\alpha$ started at $0$.
--
--   **The ratios.** For an environment $a$ set
--   $$\sigma_n=\frac{\beta_n}{a_n}=\frac{1-a_n}{a_n}\in[0,\infty],\qquad \rho_n=\sigma_1\cdots\sigma_n\ (n>0),\qquad \rho_n=\sigma_{-1}\cdots\sigma_n\ (n<0),$$
--   so that $\rho_{-n}=\sigma_{-1}\cdots\sigma_{-n}$ for $n\ge1$; $\sigma_n=\infty$ when $a_n=0$ and $\sigma_n=0$ when $a_n=1$. For the random environment, $\sigma_n$ and $\rho_n$ are computed from $\alpha$.
--
--   **Hitting probabilities.** $f_{ij}=P(X_n=j \text{ for some } n>0\mid X_0=i)$ is the probability that the chain started at $i$ visits $j$ at some positive time.
--
--   **Recurrence.** A sequence $(x_n)$ *oscillates* when $-\infty=\liminf_n x_n<\limsup_n x_n=\infty$, i.e. it falls below every level and rises above every level infinitely often.
--
--   **The two series.** For the random environment,
--   $$\Sigma_>=\sum_{n=1}^\infty \frac1n P(\rho_n>1),\qquad \Sigma_<=\sum_{n=1}^\infty \frac1n P(\rho_n<1),$$
--   both in $[0,\infty]$.
--
--   **Logarithmic moment.** $\ln\sigma\in[-\infty,\infty]$ with $\ln0=-\infty$, $\ln\infty=+\infty$. Write $E(\ln\sigma)^+$ and $E(\ln\sigma)^-$ for the expectations of the positive and negative parts, both in $[0,\infty]$. $E(\ln\sigma)$ is *defined* when at least one of them is finite, and then $E(\ln\sigma)=E(\ln\sigma)^+-E(\ln\sigma)^-\in[-\infty,\infty]$. Finally $S_n=\ln\sigma_1+\dots+\ln\sigma_n$, and for a real sequence $Y_1,Y_2,\dots$ the partial sums are $S_n=Y_1+\dots+Y_n$.
--
--   These are the objects of Lemmas (1.1), (1.5), (1.6) and Theorems (0.1), (1.7).
--
--   **Formalization Note** The chain is specified by its cylinder probabilities, which determine its law; `IsRWRE` imposes $\alpha_n(\omega)\in[0,1]$ for every outcome. $\sigma_n$, $\rho_n$ and the series live in `ℝ≥0∞`; `rho a 0 = 1` (empty product) is a convention the paper never uses. Series over $n\ge1$ are `tsum`s over `ℕ` with index $n+1$. $E(\ln\sigma)$ is computed for $\sigma_0$ (the $\sigma_n$ are identically distributed) with lower Lebesgue integrals, never a Bochner integral. In `partialSum`, `Y j` is the paper's $Y_{j+1}$.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, pp. 1–5, §0 and §1 (transition matrix p. 1; P(A × Ω) p. 2; f_ij, σ_n, ρ_n p. 2; Theorem (1.7) p. 4; S_n p. 5)

import Mathlib

namespace SolomonRWRE.Recurrence

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Solomon, *Random Walks in a Random Environment*, Ann. Probab. 3(1) (1975), §0, p. 1:
the one-step transition probability `M_a(x, y)` of the nearest-neighbour chain on `ℤ` in the
fixed environment `a`: `M(x, x+1) = a_x`, `M(x, x-1) = β_x = 1 - a_x`, and `0` otherwise. -/
def step (a : ℤ → ℝ) (x y : ℤ) : ℝ :=
  if y = x + 1 then a x else if y = x - 1 then 1 - a x else 0

/-- Solomon (1975), §0, pp. 1–2: `X` is the Markov chain `M_a` with transition matrix `step a`,
    started at `i`, on the measure space `(Ω, P)`. The fixed environment has values in `[0, 1]`
    at every site, as stipulated in §0.

**Formalization Note.** The chain is specified by its finite-dimensional (cylinder) laws,
which determine the law of the path: for every `n` and every path `x`, the probability that
`X_0 = x_0, …, X_n = x_n` is `1{x_0 = i} · ∏_{k<n} M_a(x_k, x_{k+1})`. -/
def IsChainInEnv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (a : ℤ → ℝ) (i : ℤ)
    (X : ℕ → Ω → ℤ) : Prop :=
  (∀ j, a j ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ n, Measurable (X n)) ∧
  ∀ (n : ℕ) (x : ℕ → ℤ), P {ω | ∀ k ≤ n, X k ω = x k} =
    ENNReal.ofReal ((if x 0 = i then 1 else 0) *
      ∏ k ∈ Finset.range n, step a (x k) (x (k + 1)))

/-- Solomon (1975), §0, pp. 1–2: the **random walk in a random environment**. The environment
`α = {α_n}_{n ∈ ℤ}` is an i.i.d. family of `[0,1]`-valued random variables and, given the
environment, `X` is the chain `M_α` started at `0`.

**Formalization Note.** The paper builds the process on `[0,1]^ℤ × ℤ^ℕ` with
`P(A × Ω') = ∫_A M_α(Ω') dQ(α)`, `Q` the product law of the environment. Here the process lives
on an arbitrary probability space and `law` is that identity on cylinders: for every measurable
set `A` of environments and every path cylinder, `P(α ∈ A, X_0 = x_0, …, X_n = x_n)` is the
integral over `{α ∈ A}` of the quenched cylinder probability. This determines the joint law of
`(α, X)`. The condition `α_n ∈ [0,1]` is imposed for every outcome (the paper's
"0 ≤ α_n ≤ 1"). -/
structure IsRWRE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) : Prop where
  meas_α : ∀ n, Measurable (α n)
  meas_X : ∀ n, Measurable (X n)
  mem : ∀ n ω, α n ω ∈ Set.Icc (0 : ℝ) 1
  indep : iIndepFun α P
  ident : ∀ n, IdentDistrib (α n) (α 0) P P
  law : ∀ (n : ℕ) (x : ℕ → ℤ) (A : Set (ℤ → ℝ)), MeasurableSet A →
    P ({ω | (fun m => α m ω) ∈ A} ∩ {ω | ∀ k ≤ n, X k ω = x k}) =
      ∫⁻ ω in {ω | (fun m => α m ω) ∈ A},
        ENNReal.ofReal ((if x 0 = 0 then 1 else 0) *
          ∏ k ∈ Finset.range n, step (fun m => α m ω) (x k) (x (k + 1))) ∂P

/-- The environment of outcome `ω`, `n ↦ α_n(ω)`; its law `P.map (env α)` is the paper's `Q`. -/
def env {Ω : Type*} (α : ℤ → Ω → ℝ) (ω : Ω) : ℤ → ℝ := fun m => α m ω

/-- Solomon (1975), Lemma (1.1), p. 2: `σ_n = β_n / α_n = (1 - a_n) / a_n`, valued in `[0, ∞]`:
`σ_n = ∞` when `a_n = 0` and `σ_n = 0` when `a_n = 1`. -/
noncomputable def sigma (a : ℤ → ℝ) (n : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - a n) / ENNReal.ofReal (a n)

/-- Solomon (1975), Lemma (1.1), p. 2: `ρ_n = σ_1 ⋯ σ_n` for `n > 0` and `ρ_n = σ_{-1} ⋯ σ_n`
for `n < 0`, so `ρ_{-n} = σ_{-1} ⋯ σ_{-n}` for `n ≥ 1`.

**Formalization Note.** Products are taken in `[0, ∞]`. The paper does not define `ρ_0`; the
empty product gives `rho a 0 = 1`, which is never used. -/
noncomputable def rho (a : ℤ → ℝ) (n : ℤ) : ℝ≥0∞ :=
  if 0 ≤ n then ∏ k ∈ Finset.Icc (1 : ℤ) n, sigma a k
  else ∏ k ∈ Finset.Icc n (-1), sigma a k

/-- Solomon (1975), §1, p. 2: `f_ij = P(X_n = j, some n > 0 | X_0 = i)`. For a chain `X` with
`IsChainInEnv P a i X`, this is the probability that `X` visits `j` at some time `n > 0`. -/
def hitProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℤ) (j : ℤ) : ℝ≥0∞ :=
  P {ω | ∃ n, 0 < n ∧ X n ω = j}

/-- `−∞ = lim inf_{n→∞} x_n < lim sup_{n→∞} x_n = ∞`: the sequence goes below every level and
above every level infinitely often. This is the "in fact" form of recurrence in Solomon (1975),
Lemma (1.5)(iii) and Theorem (1.7)(iii), and of Lemma (1.6)(ii). -/
def Oscillates {β : Type*} [Preorder β] (x : ℕ → β) : Prop :=
  (∀ M : β, ∃ᶠ n in atTop, x n ≤ M) ∧ (∀ M : β, ∃ᶠ n in atTop, M ≤ x n)

/-- Solomon (1975), Theorem (1.7)(i), p. 4: `Σ_{n=1}^∞ n⁻¹ P(ρ_n > 1)` in `[0, ∞]`, for the
random environment `α` (the `ℕ`-index `n` stands for the paper's `n + 1`). -/
noncomputable def seriesGt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (α : ℤ → Ω → ℝ) :
    ℝ≥0∞ :=
  ∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 1 < rho (env α ω) ((n : ℤ) + 1)}

/-- Solomon (1975), Theorem (1.7)(ii), p. 4: `Σ_{n=1}^∞ n⁻¹ P(ρ_n < 1)` in `[0, ∞]` (the
`ℕ`-index `n` stands for the paper's `n + 1`). -/
noncomputable def seriesLt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (α : ℤ → Ω → ℝ) :
    ℝ≥0∞ :=
  ∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | rho (env α ω) ((n : ℤ) + 1) < 1}

/-- `ln σ_n` as an extended real: `ln 0 = −∞`, `ln ∞ = +∞`. -/
noncomputable def logSigma {Ω : Type*} (α : ℤ → Ω → ℝ) (n : ℤ) (ω : Ω) : EReal :=
  ENNReal.log (sigma (env α ω) n)

/-- `E[(ln σ)⁺] ∈ [0, ∞]`, computed for `σ = σ_0` (the `σ_n` are identically distributed). -/
noncomputable def logMomentPos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (α : ℤ → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (logSigma α 0 ω).toENNReal ∂P

/-- `E[(ln σ)⁻] ∈ [0, ∞]`, computed for `σ = σ_0`. -/
noncomputable def logMomentNeg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (α : ℤ → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (-logSigma α 0 ω).toENNReal ∂P

/-- Solomon (1975), Theorem (1.7), p. 4: "`E(ln σ)` is defined (possibly `±∞`)": at least one
of `E[(ln σ)⁺]`, `E[(ln σ)⁻]` is finite. -/
def LogMomentDefined {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (α : ℤ → Ω → ℝ) : Prop :=
  logMomentPos P α ≠ ∞ ∨ logMomentNeg P α ≠ ∞

/-- Solomon (1975), Theorem (1.7), p. 4: `E(ln σ) = E[(ln σ)⁺] − E[(ln σ)⁻] ∈ [−∞, ∞]`. It is
meaningful under `LogMomentDefined`, where it is never `∞ − ∞`. -/
noncomputable def logMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (α : ℤ → Ω → ℝ) : EReal :=
  (logMomentPos P α : EReal) - (logMomentNeg P α : EReal)

/-- Solomon (1975), Lemma (1.6), p. 3: the partial sums `S_n = Y_1 + ⋯ + Y_n` of a real sequence.

**Formalization Note.** The sequence is indexed from `0`: `Y j` is the paper's `Y_{j+1}`, so
`partialSum Y n = Y 0 + ⋯ + Y (n-1)` is the paper's `S_n`, and `partialSum Y 0 = 0`. -/
def partialSum {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, Y j ω

/-- Solomon (1975), proof of Theorem (1.7), p. 5: `S_n = ln σ_1 + ⋯ + ln σ_n ∈ [−∞, ∞]`. -/
noncomputable def logSum {Ω : Type*} (α : ℤ → Ω → ℝ) (n : ℕ) (ω : Ω) : EReal :=
  ∑ k ∈ Finset.Icc (1 : ℤ) n, logSigma α k ω

end SolomonRWRE.Recurrence


