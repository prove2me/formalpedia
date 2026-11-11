-- Prove2me | Definitions.Def_CorrKClust_BalancedPivot_Orders
-- name    : CorrKClust_BalancedPivot_Orders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:19.607912+00:00
-- url     : https://prove2.me/theorems/5232772c-f362-40f2-b315-9f9232cb961d
-- title:
--   Uniform arrival orders, probabilities and finite expectations
-- statement:
--   Let $n=|V|$. An arrival order $\sigma$ is a bijection from $\{0,\ldots,n-1\}$ to $V$. The paper's arrival time is $t_v=\sigma^{-1}(v)+1$. For any real-valued function on a finite sample space $\Omega$, define
--   $$\mathbb E[f]=\frac{\sum_{\omega\in\Omega}f(\omega)}{|\Omega|},\qquad\Pr(E)=\mathbb E[\mathbf 1_E].$$
--   All arrival-order applications use the $n!$ bijections with equal weight. Conditional probability is $\Pr(E\cap A)/\Pr(A)$, used with positive-probability conditioning events; an event contribution is $\mathbb E[f\mathbf 1_E]$. For a fixed marked set $A\subseteq V$, the prefix count is the number of its elements arriving by time $t$.
--
--   This finite interface avoids measure-theoretic integrability conventions. The empty graph has one arrival order. The average on an empty auxiliary sample space is totalized to zero, but that case is never used for arrival orders.
--
--   The module also provides, for Facts 2.1–2.2, expectations and probabilities under explicit probability weights $p$ on a finite sample space ($\mathbb E_p[f]=\sum_\omega p(\omega)f(\omega)$, with $p\ge0$ and $\sum_\omega p(\omega)=1$), mutual independence of a family of random variables (the joint probability of every product event factorises), negative association in the sense of Joag-Dev and Proschan (for disjoint index sets $I,J$ and coordinatewise nondecreasing $f$, $g$ depending only on the $I$- and the $J$-coordinates respectively, $\mathbb E[f(X)g(X)]\le\mathbb E[f(X)]\,\mathbb E[g(X)]$), and the predicate that a random variable $X$ with mean $\mu$ satisfies the four tail bounds of Fact 2.1: $\Pr[X\ge(1+\delta)\mu]\le e^{-\delta^2\mu/(2+\delta)}$ for $\delta>0$, $\Pr[X\le(1-\delta)\mu]\le e^{-\delta^2\mu/2}$ for $0<\delta<1$, $\Pr[X\ge a]\le2^{-a}$ for $a\ge2e\mu$, and $\Pr[X\ge(1+\delta)\mu]\le e^{-\delta\mu/3}$ for $\delta\ge1$.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), §2; Facts 2.1–2.2, pp. 6–11, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Mathlib

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- §2: all n! bijections from zero-based time indices to vertices. -/
abbrev ArrivalOrder (V : Type*) [Fintype V] := Fin (Fintype.card V) ≃ V

/-- Uniform finite average. Its denominator for ArrivalOrder V is n!. -/
def average {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / (Fintype.card Ω : ℝ)

def probability {Ω : Type*} [Fintype Ω] (E : Ω → Prop) : ℝ :=
  average (fun ω => if E ω then (1 : ℝ) else 0)

/-- Conditional probability as a ratio; zero only for a zero-mass condition. -/
def conditional {Ω : Type*} [Fintype Ω] (E A : Ω → Prop) : ℝ :=
  probability (fun ω => E ω ∧ A ω) / probability A

def contribution {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  average (fun ω => if E ω then f ω else 0)

/-- Paper time is one-based: first arrival has time 1. -/
def arrivalTime {V : Type*} [Fintype V] (σ : ArrivalOrder V) (v : V) : ℕ :=
  (σ.symm v).val + 1

def arrivalList {V : Type*} [Fintype V] (σ : ArrivalOrder V) : List V := List.ofFn σ

/-- Hypergeometric count from a uniform permutation, sample size t ≤ n. -/
def prefixCount {V : Type*} [Fintype V] (A : Finset V) (t : ℕ) (σ : ArrivalOrder V) : ℕ :=
  (A.filter (fun v => arrivalTime σ v ≤ t)).card

/-- Expectation under explicit probability weights `p` on a finite sample space. -/
def wExp {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, p ω * f ω

def wProb {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  wExp p (fun ω => if E ω then (1 : ℝ) else 0)

/-- Nonnegative weights summing to one. -/
def IsProbWeights {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) : Prop :=
  (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1

/-- Mutual independence of the family `X` under the weights `p`. -/
def MutuallyIndependent {Ω ι : Type*} [Fintype Ω] [Fintype ι] (p : Ω → ℝ)
    (X : ι → Ω → ℝ) : Prop :=
  ∀ s : ι → Set ℝ, wProb p (fun ω => ∀ i, X i ω ∈ s i) = ∏ i, wProb p (fun ω => X i ω ∈ s i)

/-- Negative association (Joag-Dev--Proschan): for disjoint index sets `I`, `J` and
coordinatewise nondecreasing `f` depending only on the `I`-coordinates and `g` depending only
on the `J`-coordinates, `E[f(X) g(X)] ≤ E[f(X)] E[g(X)]`, i.e. the covariance is `≤ 0`. -/
def NegativelyAssociated {Ω ι : Type*} [Fintype Ω] (p : Ω → ℝ) (X : ι → Ω → ℝ) : Prop :=
  ∀ (I J : Set ι), Disjoint I J → ∀ f g : (ι → ℝ) → ℝ, Monotone f → Monotone g →
    (∀ x y : ι → ℝ, (∀ i ∈ I, x i = y i) → f x = f y) →
    (∀ x y : ι → ℝ, (∀ i ∈ J, x i = y i) → g x = g y) →
    wExp p (fun ω => f (fun i => X i ω) * g (fun i => X i ω)) ≤
      wExp p (fun ω => f (fun i => X i ω)) * wExp p (fun ω => g (fun i => X i ω))

/-- The four tail bounds of Fact 2.1 for `X` with mean `μ = E[X]` under the weights `p`:
(1), (2), the clause `a ≥ 2eμ`, and the `δ ≥ 1` form of (1). -/
def ChernoffTails {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → ℝ) : Prop :=
  (∀ δ : ℝ, 0 < δ →
    wProb p (fun ω => (1 + δ) * wExp p X ≤ X ω) ≤ Real.exp (-(δ ^ 2 * wExp p X / (2 + δ)))) ∧
  (∀ δ : ℝ, 0 < δ → δ < 1 →
    wProb p (fun ω => X ω ≤ (1 - δ) * wExp p X) ≤ Real.exp (-(δ ^ 2 * wExp p X / 2))) ∧
  (∀ a : ℝ, 2 * Real.exp 1 * wExp p X ≤ a → wProb p (fun ω => a ≤ X ω) ≤ (2 : ℝ) ^ (-a)) ∧
  (∀ δ : ℝ, 1 ≤ δ →
    wProb p (fun ω => (1 + δ) * wExp p X ≤ X ω) ≤ Real.exp (-(δ * wExp p X / 3)))

end CorrKClust.BalancedPivot


