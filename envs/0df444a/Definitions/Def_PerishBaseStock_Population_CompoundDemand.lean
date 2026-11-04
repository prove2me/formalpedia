-- Prove2me | Definitions.Def_PerishBaseStock_Population_CompoundDemand
-- name    : PerishBaseStock_Population_CompoundDemand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:58.158093+00:00
-- url     : https://prove2.me/theorems/bae7a6e5-a4be-4ce2-9e36-7098427d6181
-- title:
--   The demand-population form (7) $D(n)=\sum_{j=1}^{N(n)}\hat D_j$ (p. 11)
-- statement:
--   This file defines the demand-population form (7) of Bu, Gong & Chao (p. 11).
--
--   1. **Customer demands.** $\hat D_1,\hat D_2,\dots$ are i.i.d. non-negative random variables with finite mean and finite variance. Write $\mu=\mathbb E[\hat D_1]$ and $\sigma^2=\mathrm{Var}[\hat D_1]$.
--   2. **Inter-arrival times.** $X_1,X_2,\dots$ are i.i.d. non-negative random variables with $\mathbb E[X_1]=1$, finite variance $\sigma_X^2=\mathrm{Var}[X_1]$, and $\mathbb E[e^{sX_1}]<\infty$ for some $s>0$. The two families are independent.
--   3. **Population count.** For a positive integer $n$,
--   $$
--   N(n)=\sup\Big\{N\in\mathbb N:\ \sum_{k=1}^N X_k/n\le 1\Big\},
--   $$
--   the number of renewals in $[0,n]$ of the renewal process with inter-arrival times $X_k$ (so $N(n)=n$ when $X_k\equiv 1$).
--   4. **One-period demand.**
--   $$
--   D(n)=\sum_{j=1}^{N(n)}\hat D_j ,
--   $$
--   and its law is the image of the joint law of $((\hat D_j)_j,(X_k)_k)$.
--   5. **Population family.** A sequence $(P_n)$ of demand laws (non-negative, finite positive mean) is a population family when $P_n$ is the law of $D(n)$ for every $n\ge 1$. The $n$-th inventory system is the system of §2 with generic demand $D(n)$.
--
--   The parameter $n$ is the demand population size: the mean demand grows like $n\mu$.
--
--   **Formalization Note** Both families live on the product of two infinite product spaces; Lean index $j$ is the paper's $j+1$. $N(n)$ is the counting variable $N_t$ of the published `SmithRenewal.Elementary` definition at $t=n$, the number of $k\ge 1$ with $X_1+\dots+X_k\le n$, an element of $\mathbb N\cup\{\infty\}$; for non-negative $X_k$ and $n\ge 1$ it equals the supremum above. On the null event $N(n)=\infty$ the sum is read as $0$. Finite variance is a finite second moment. The population family is given as a sequence of `CappedBaseStock.DemandLaw` with the law fixed by (7) for $n\ge 1$; its value at $n=0$ is unconstrained and never used.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 11, (7); notation p. ec3

import Definitions.Def_CappedBaseStock_Model
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Population

/-!
# The demand-population form (7) (Bu, Gong & Chao, p. 11)

For a positive integer `n`, the one-period demand is `D(n) = Σ_{j=1}^{N(n)} D̂_j` with
`N(n) = sup{N ∈ ℕ : Σ_{k=1}^N X_k / n ≤ 1}`, where `(D̂_j)` and `(X_k)` are two independent i.i.d.
families of non-negative random variables.

Both families live on one canonical product space: `ω.1 j` is the paper's `D̂_{j+1}` and
`ω.2 k` is the paper's `X_{k+1}` (zero-based indices).
-/

/-- The law of a customer's demand `D̂_1` (p. 11): a probability law on `[0, ∞)` with finite mean
and finite variance (finite second moment). -/
structure CustomerLaw where
  law : Measure ℝ≥0
  probability : IsProbabilityMeasure law
  memLp_two : MemLp (fun x : ℝ≥0 => (x : ℝ)) 2 law

attribute [instance] CustomerLaw.probability

/-- The law of the scaled inter-arrival time `X_1` (p. 11): a probability law on `[0, ∞)` with
mean one, finite variance, and a finite exponential moment `E[e^{s X_1}] < ∞` for some `s > 0`. -/
structure InterarrivalLaw where
  law : Measure ℝ≥0
  probability : IsProbabilityMeasure law
  memLp_two : MemLp (fun x : ℝ≥0 => (x : ℝ)) 2 law
  mean_eq_one : ∫ x : ℝ≥0, (x : ℝ) ∂law = 1
  exp_moment : ∃ s : ℝ, 0 < s ∧ Integrable (fun x : ℝ≥0 => Real.exp (s * (x : ℝ))) law

attribute [instance] InterarrivalLaw.probability

/-- `μ = E[D̂_1]` (p. ec3). -/
def customerMean (Dh : CustomerLaw) : ℝ := ∫ x : ℝ≥0, (x : ℝ) ∂Dh.law

/-- `σ² = Var[D̂_1]` (p. ec3). -/
def customerVariance (Dh : CustomerLaw) : ℝ := variance (fun x : ℝ≥0 => (x : ℝ)) Dh.law

/-- `σ_X² = Var[X_1]` (p. ec3). -/
def interarrivalVariance (X : InterarrivalLaw) : ℝ := variance (fun x : ℝ≥0 => (x : ℝ)) X.law

/-- The sample space of the two families: customer demands `(D̂_j)` and inter-arrival times
`(X_k)`. -/
abbrev PopSample := (ℕ → ℝ≥0) × (ℕ → ℝ≥0)

/-- The i.i.d. law of the inter-arrival sequence `(X_k)`. -/
def interarrivalSeqLaw (X : InterarrivalLaw) : Measure (ℕ → ℝ≥0) :=
  Measure.infinitePi (fun _ : ℕ => X.law)

/-- The joint law: `(D̂_j)` i.i.d. with law `Dh.law`, `(X_k)` i.i.d. with law `X.law`, and the two
families independent. -/
def popSampleLaw (Dh : CustomerLaw) (X : InterarrivalLaw) : Measure PopSample :=
  (Measure.infinitePi (fun _ : ℕ => Dh.law)).prod (interarrivalSeqLaw X)

/-- The inter-arrival times as real random variables on the sequence space, `X_{k+1} = x k`. -/
def interarrivals : ℕ → (ℕ → ℝ≥0) → ℝ := fun k x => (x k : ℝ)

/-- `N(n) = sup{N ∈ ℕ : Σ_{k=1}^N X_k / n ≤ 1}` (p. 11): the number of renewals in `[0, n]` of the
renewal process with inter-arrival times `X_k`, i.e. the counting variable `N_t` at `t = n` of
`SmithRenewal.Elementary`. It takes values in `ℕ∞`; the value `⊤` occurs only on a null event. -/
def arrivalCount (n : ℕ) (x : ℕ → ℝ≥0) : ℕ∞ :=
  SmithRenewal.Elementary.N interarrivals (n : ℝ) x

/-- The one-period demand `D(n) = Σ_{j=1}^{N(n)} D̂_j` of (7). On the null event `N(n) = ⊤` the
count is read through `ENat.toNat`, which gives the empty sum `0`. -/
def compoundDemand (n : ℕ) (ω : PopSample) : ℝ≥0 :=
  ∑ j ∈ Finset.range (arrivalCount n ω.2).toNat, ω.1 j

/-- The law of `D(n)`. -/
def compoundLaw (Dh : CustomerLaw) (X : InterarrivalLaw) (n : ℕ) : Measure ℝ≥0 :=
  Measure.map (compoundDemand n) (popSampleLaw Dh X)

/-- `P` is the population family of demand laws of form (7): for every positive integer `n`, the
generic one-period demand of the `n`-th system has the law of `D(n)`. -/
def IsPopulationFamily (Dh : CustomerLaw) (X : InterarrivalLaw)
    (P : ℕ → CappedBaseStock.DemandLaw) : Prop :=
  ∀ n : ℕ, 1 ≤ n → (P n).law = compoundLaw Dh X n

end PerishBaseStock.Population


