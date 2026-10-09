-- Prove2me | Definitions.Def_ChenFarias_SimplePolicy_Model
-- name    : ChenFarias_SimplePolicy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:01:55.461039+00:00
-- url     : https://prove2.me/theorems/6c270440-a81c-4b83-9101-706c9b873b93
-- title:
--   pp. 1123–1125 — valuation law, Bellman value, root policy and myopic sales process
-- statement:
--   Customer valuations have a density $f$ on $\mathbb R$: $f\ge0$, $f=0$ on $(-\infty,0)$, $f$ is integrable with $\int f=1$, and $f(p)>0$ for every $p\ge0$. Write $\bar F(p)=\int_p^\infty f(v)\,dv$ for the tail and $\psi(p)=p-\bar F(p)/f(p)$ for the virtual value. **Assumption 1** asks that $\psi$ be nondecreasing on $[0,\infty)$ and have a nonnegative root $v^*$. For customer-arrival rate $\lambda>0$ and discount rate $\beta>0$, the value $V(x)$ solves
--
--   $$
--   V(0)=0,\qquad \beta V(x)=\sup_{p\ge0}\lambda\bar F(p)\bigl(p+V(x-1)-V(x)\bigr)\quad(x\ge1).
--   $$
--
--   At positive inventory $x$, the policy price $\pi(x)$ is the unique nonnegative root of $\psi(\pi(x))=V(x)-V(x-1)$. Sales use independent unit-rate exponential clocks: while the inventory is $x$, the next sale occurs at rate $\lambda\bar F(\pi(x))$ and is paid $\pi(x)$. The finite-horizon revenue $J(x_0,T)$ is the expected sum of prices paid at sales by time $T$; the model also records the discounted sum and the posted price path.
--
--   **Formalization Note** The printed Bellman recursion has its marginal-value sign reversed; the displayed formula is the corrected reading consistent with its root equation and equation (4). Assumption 1 includes the disclosed addition $f(p)>0$ for all $p\ge0$ to avoid division by zero, so it excludes bounded-support densities. Unique-root existence is an explicit policy predicate because monotonicity of $\psi$ alone does not imply it. The Bellman predicate uses a real least-upper-bound assertion, so $V$ is specified by the recursion rather than by policy revenue; the recursion determines it uniquely, because the right side minus the left is strictly monotone in $V(x)$, and the uniqueness clause of the root predicate determines $\pi$. Quantifying over every such $V$ and $\pi$ is therefore quantifying over the paper's single $V^*_\beta$ and $\pi^*_\beta$. Sales are numbered $1,\ldots,x_0$, clocks from $0$, and payment at sale $k$ is $\pi(x_0-k+1)$. The posted price after sell-out is $+\infty$; the revenue rate there is zero, implementing $\infty\cdot0=0$. Expectations are lower integrals in $[0,\infty]$; all prices and sums are nonnegative under the policy predicate. Independent exponential horizons are represented by an iterated lower integral. The pure-death clock construction represents the thinning of Poisson arrivals by the myopic purchase probability. The strategic-customer equilibrium is outside this model.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1123, Assumption 1; p. 1124, (2); p. 1125, (3)–(4); p. 1141, endnotes 2, 6, 7

import Mathlib

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ChenFarias.SimplePolicy

/-- The upper tail of the valuation density: `F̄(p) = P(v > p)`. -/
noncomputable def Fbar (f : ℝ → ℝ) (p : ℝ) : ℝ :=
  ∫ v in Set.Ioi p, f v

/-- The virtual valuation `ψ(v) = v - F̄(v)/f(v)`. -/
noncomputable def psi (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  v - Fbar f v / f v

/-- Assumption 1 together with the valuation-law conventions of Section 2 and the
disclosed full-support condition needed to make `F̄(v)/f(v)` meaningful at every
nonnegative price. -/
structure Assumption1 (f : ℝ → ℝ) : Prop where
  nonnegative : ∀ v, 0 ≤ f v
  zero_of_negative : ∀ v, v < 0 → f v = 0
  integrable : Integrable f
  total_mass : (∫ v, f v) = 1
  virtual_monotone : MonotoneOn (psi f) (Set.Ici 0)
  virtual_root : ∃ vstar, 0 ≤ vstar ∧ psi f vstar = 0
  positive_of_nonnegative : ∀ v, 0 ≤ v → 0 < f v

/-- The sign-corrected discounted Bellman recursion from Section 3.1. `IsLUB`
represents the real supremum without the default value of `sSup` on an unbounded set. -/
def IsValueFn (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ) : Prop :=
  V 0 = 0 ∧
    ∀ x : ℕ, 1 ≤ x →
      IsLUB {y : ℝ | ∃ p : ℝ, 0 ≤ p ∧
        y = lam * Fbar f p * (p + V (x - 1) - V x)} (β * V x)

/-- The stationary price is the unique nonnegative root of the paper's equation
at each positive inventory level. Its value at zero is unused. -/
def IsRootPolicy (f : ℝ → ℝ) (V : ℕ → ℝ) (π : ℕ → ℝ) : Prop :=
  ∀ x : ℕ, 1 ≤ x →
    0 ≤ π x ∧
      psi f (π x) = V x - V (x - 1) ∧
      (∀ p : ℝ, 0 ≤ p → psi f p = V x - V (x - 1) → p = π x)

/-- Independent standard exponential clocks, one per potential sale. -/
noncomputable def clockLaw (x0 : ℕ) : Measure (Fin x0 → ℝ) :=
  Measure.pi (fun _ : Fin x0 => expMeasure 1)

/-- The time of sale `k`, summing the first `k` inventory-dependent holding
times. The first clock has index zero and is used at inventory `x0`. -/
noncomputable def saleTime (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ)
    (x0 k : ℕ) (e : Fin x0 → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin x0 => i.val < k),
    e i / (lam * Fbar f (π (x0 - i.val)))

/-- Inventory immediately before `t`; a sale exactly at `t` has not yet
reduced the inventory. -/
noncomputable def Xminus (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ)
    (x0 : ℕ) (e : Fin x0 → ℝ) (t : ℝ) : ℕ :=
  x0 - ((Finset.Icc 1 x0).filter (fun k => saleTime lam f π x0 k e < t)).card

/-- The posted price, with the paper's infinite price after sell-out. -/
noncomputable def priceAt (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ)
    (x0 : ℕ) (e : Fin x0 → ℝ) (t : ℝ) : WithTop ℝ :=
  if Xminus lam f π x0 e t = 0 then ⊤ else π (Xminus lam f π x0 e t)

/-- Revenue rate without the arrival-rate factor. At sell-out it is zero,
implementing the paper's convention `∞ · 0 = 0`. -/
noncomputable def rateRev (f : ℝ → ℝ) (π : ℕ → ℝ) (x : ℕ) : ℝ :=
  if x = 0 then 0 else π x * Fbar f (π x)

/-- Revenue from sales made by the finite horizon `T`. Sale `k` is paid the
price posted just before that sale, at inventory `x0 - k + 1`. -/
noncomputable def revenueBy (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ)
    (x0 : ℕ) (T : ℝ) (e : Fin x0 → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 x0,
    if saleTime lam f π x0 k e ≤ T then π (x0 - k + 1) else 0

/-- Infinite-horizon discounted sales revenue. -/
noncomputable def discRevenue (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ)
    (x0 : ℕ) (β : ℝ) (e : Fin x0 → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 x0,
    π (x0 - k + 1) * Real.exp (-(β * saleTime lam f π x0 k e))

/-- Expected finite-horizon revenue of the myopic sales process. -/
noncomputable def J (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ)
    (x0 : ℕ) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ e, ENNReal.ofReal (revenueBy lam f π x0 T e) ∂clockLaw x0

end ChenFarias.SimplePolicy


