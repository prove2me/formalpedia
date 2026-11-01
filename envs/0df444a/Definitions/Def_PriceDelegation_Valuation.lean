-- Prove2me | Definitions.Def_PriceDelegation_Valuation
-- name    : PriceDelegation_Valuation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:01.074981+00:00
-- url     : https://prove2.me/theorems/e09c3795-fce9-4d1b-8a6a-88024a6f7f71
-- title:
--   Valuation law: density $f$, survival function $\bar F$, expectation, Assumptions 1 and 2
-- statement:
--   A customer's willingness-to-pay $V$ is a continuous random variable with density $f$ and support $(0,\infty)$. Concretely, $f:\mathbb R\to\mathbb R$ is measurable, nonnegative, zero on $(-\infty,0]$, integrable with $\int f=1$; every interval $[a,b]$ with $0\le a<b$ has positive mass; and the mean is finite, $\int_0^\infty v f(v)\,dv<\infty$.
--
--   From the density one defines the survival function and the distribution function
--   $$
--   \bar F(p)=\int_p^\infty f(t)\,dt,\qquad F(p)=1-\bar F(p),
--   $$
--   and, for a function $g$, the expectation $E[g(V)]=\int_0^\infty g(v)f(v)\,dv$.
--
--   Two standing assumptions of the paper are recorded as predicates.
--
--   1. **Assumption 1** (for a learning cost $\psi$): learning is worth inducing in the single-customer first best, $J^{FB}=E[V]-\psi\ge\max_\varphi \varphi\,\bar F(\varphi)$.
--   2. **Assumption 2**: the failure rate $f(p)/\bar F(p)$ is non-decreasing in $p>0$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** "Support $(0,\infty)$" is encoded as positive mass on every interval of $[0,\infty)$, which makes $\bar F$ strictly decreasing there. Finiteness of $E[V]$ is not printed in the paper but is part of the model (Assumption 1 compares finite numbers). Assumption 1 is stated as $\varphi\bar F(\varphi)\le E[V]-\psi$ for every real $\varphi$. The expectation is a Bochner integral, which is $0$ for a non-integrable integrand; every use in the mission is of an integrand bounded by an integrable one or carries an integrability hypothesis.
-- source:
--   Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), §2.1, p.8; §2.3 and Assumption 1, p.11; Assumption 2, p.20

import Mathlib

open MeasureTheory Set

namespace PriceDelegation

/-- The law of a customer's willingness-to-pay `V` (Atasu–Ciocan–Désir, Price Delegation with
Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), §2.1, p.8): "a continuous random
variable with density `f(v)` and cumulative distribution function `F(v)`, with support `(0,∞)`".

**Formalization Note** The density is a measurable `f : ℝ → ℝ`, nonnegative, zero on `(-∞, 0]`,
integrable with total mass `1`. "Support `(0,∞)`" is encoded as positive mass on every interval
`[a, b]` with `0 ≤ a < b`, which makes the survival function strictly decreasing on `[0, ∞)`.
`E[V] < ∞` (integrability of `v ↦ v f(v)`) is part of the model: the paper compares
`J^FB = E[V] − ψ` with finite quantities (Assumption 1, p.11) and every maximum of §4.3 needs it. -/
structure Valuation where
  /-- The density `f`. -/
  f : ℝ → ℝ
  measurable_f : Measurable f
  nonneg : ∀ v, 0 ≤ f v
  eq_zero_of_nonpos : ∀ v, v ≤ 0 → f v = 0
  integrable_f : Integrable f
  integral_f : ∫ v, f v = 1
  /-- `E[V] < ∞`. -/
  integrable_mul : Integrable (fun v => v * f v)
  /-- Support `(0, ∞)`: every interval `[a, b] ⊆ [0, ∞)` with `a < b` has positive mass. -/
  pos_mass : ∀ a b : ℝ, 0 ≤ a → a < b → 0 < ∫ t in a..b, f t

/-- The survival function `F̄(p) = ℙ(V > p) = ∫_p^∞ f` (SSRN 3931055, p.9). -/
noncomputable def Fbar (V : Valuation) (p : ℝ) : ℝ := ∫ t in Ioi p, V.f t

/-- The distribution function `F(p) = 1 − F̄(p)` (SSRN 3931055, p.8). -/
noncomputable def Fcdf (V : Valuation) (p : ℝ) : ℝ := 1 - Fbar V p

/-- The expectation `E[g(V)] = ∫_{(0,∞)} g(v) f(v) dv` (SSRN 3931055, p.9).

**Formalization Note** The integral is over `(0, ∞)`, the support; `f` vanishes elsewhere. It is
a Bochner integral, so it is `0` when `v ↦ g(v) f(v)` is not integrable on `(0,∞)`; every use in
this mission is of a function bounded by an integrable one, or carries the integrability
hypothesis explicitly. -/
noncomputable def expect (V : Valuation) (g : ℝ → ℝ) : ℝ := ∫ v in Ioi 0, g v * V.f v

/-- The mean `E[V]` (SSRN 3931055, p.11). -/
noncomputable def meanV (V : Valuation) : ℝ := expect V id

/-- Assumption 1 (SSRN 3931055, p.11): `J^FB ≥ max_φ {φ · F̄(φ)}`, where `J^FB = E[V] − ψ` is the
first-best payoff of the single-customer problem (p.11).

**Formalization Note** The maximum over `φ` is stated as a bound at every real `φ`. -/
def Assumption1 (V : Valuation) (ψ : ℝ) : Prop :=
  ∀ φ : ℝ, φ * Fbar V φ ≤ meanV V - ψ

/-- Assumption 2 (SSRN 3931055, p.20): the valuation has an increasing failure rate, i.e.
`f(p)/F̄(p)` is non-decreasing in `p` (on the support `(0, ∞)`). -/
def Assumption2 (V : Valuation) : Prop :=
  MonotoneOn (fun p => V.f p / Fbar V p) (Ioi 0)

end PriceDelegation


