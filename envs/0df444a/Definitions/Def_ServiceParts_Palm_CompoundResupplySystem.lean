-- Prove2me | Definitions.Def_ServiceParts_Palm_CompoundResupplySystem
-- name    : ServiceParts_Palm_CompoundResupplySystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T22:09:00.997987+00:00
-- url     : https://prove2.me/theorems/2fbbf914-db6c-4c33-a825-b508f34e29c6
-- title:
--   Compound Poisson (s–1, s) system: i.i.d. order sizes sharing one resupply time per order
-- statement:
--   The compound Poisson version of the $(s-1,s)$ backorder system. On top of the order stream $T_0 < T_1 < \cdots$ with rate $\lambda$ and the resupply times $L_0, L_1, \dots$ of the basic model, the $k$-th customer order asks for $X_k \ge 1$ units. The order sizes are identically distributed with
--   $$u_j = P[X_k = j], \qquad j \ge 1,$$
--   and all interarrival times, resupply times and order sizes are mutually independent. All units of one order share the resupply time of that order.
--
--   Derived quantities:
--
--   1. the number of units in resupply at time $t$, $\;Y(t) = \sum_{k : T_k \le t < T_k + L_k} X_k$;
--   2. for $T \ge 0$, the number of units in resupply at time $t$ that have been in the resupply system for at least $T$ time units, $\;Y_T(t) = \sum_{k : T_k + T \le t < T_k + L_k} X_k$;
--   3. the $j$-fold convolution $u^{(j)}_n$, the probability that $j$ customers ask for $n$ units in total ($u^{(0)}_n = [n = 0]$, $u^{(j+1)}_n = \sum_{m=0}^{n} u^{(j)}_m u_{n-m}$);
--   4. the compound Poisson probabilities with Poisson parameter $\mu$,
--   $$p(n \mid \mu) = \sum_{y=0}^{n} \frac{\mu^y e^{-\mu}}{y!}\, u^{(y)}_n .$$
--
--   This is the model of Theorems 7 and 9.
--
--   **Formalization Note** Order sizes are natural numbers; their independence from the real-valued interarrival and resupply times is stated through their casts to $\mathbb R$, which generate the same $\sigma$-algebras. Because $u_0 = 0$, $u^{(y)}_n = 0$ for $y > n$, so the finite sum above equals the book's series $\sum_{j \ge 1} u^{(j)}_n e^{-\mu}\mu^j/j!$ of (3.22) for $n \ge 1$ and gives $e^{-\mu}$ at $n = 0$, as in (3.23). A total over infinitely many orders (a probability-zero event) is $0$ by convention.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 41-47, Section 3.1, Eqs. (3.14)-(3.18), (3.22)-(3.23), hypotheses of Theorems 7 and 9

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.Palm

/-- The compound Poisson (s–1, s) backorder system of Muckstadt (2005), Section 3.1, pp. 41–47:
the system of `ResupplySystem`, where in addition the `k`-th customer order asks for
`size k ≥ 1` units, order sizes are i.i.d., and all interarrival times, resupply times and order
sizes are mutually independent. All units of one order share the order's resupply time
`resupply k`. -/
structure CompoundResupplySystem (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    extends ResupplySystem Ω P where
  /-- number of units asked for by the `k`-th customer order -/
  size : ℕ → Ω → ℕ
  size_measurable : ∀ k, Measurable (size k)
  /-- every order asks for at least one unit -/
  size_pos : ∀ k ω, 1 ≤ size k ω
  /-- order sizes are identically distributed -/
  size_law : ∀ k, P.map (size k) = P.map (size 0)
  /-- interarrival times, resupply times and order sizes are all mutually independent -/
  indep_all : iIndepFun (Sum.elim gap (Sum.elim resupply (fun k ω => (size k ω : ℝ)))) P

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The order-size probabilities `u_j = P[X_k = j]`. -/
noncomputable def CompoundResupplySystem.sizePMF (S : CompoundResupplySystem Ω P) (j : ℕ) : ℝ :=
  (P {ω | S.size 0 ω = j}).toReal

/-- The number of units in resupply at time `t`: the total size of the orders placed by time `t`
whose (common) resupply is not complete at time `t` (`0` on the null event where infinitely many
orders qualify). -/
noncomputable def CompoundResupplySystem.unitsInResupply (S : CompoundResupplySystem Ω P)
    (t : ℝ) (ω : Ω) : ℕ :=
  ∑ᶠ k ∈ {k : ℕ | S.arrival k ω ≤ t ∧ t < S.arrival k ω + S.resupply k ω}, S.size k ω

/-- The number of units in resupply at time `t` that have been in the resupply system for at
least `T` time units: the total size of the orders placed by time `t - T` whose resupply is not
complete at time `t`. -/
noncomputable def CompoundResupplySystem.agedUnitsInResupply (S : CompoundResupplySystem Ω P)
    (T t : ℝ) (ω : Ω) : ℕ :=
  ∑ᶠ k ∈ {k : ℕ | S.arrival k ω + T ≤ t ∧ t < S.arrival k ω + S.resupply k ω}, S.size k ω

/-- The `j`-fold convolution `u^{(j)}_n` of a probability vector `u` on `ℕ`: the probability that
`j` independent orders with size law `u` ask for `n` units in total. -/
noncomputable def convPow (u : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => if n = 0 then 1 else 0
  | j + 1, n => ∑ m ∈ Finset.range (n + 1), convPow u j m * u (n - m)

/-- The compound Poisson probabilities with Poisson parameter `μ` and compounding law `u`
(with `u 0 = 0`): `p(n | μ) = ∑_{y=0}^{n} e^{-μ} μ^y / y! · u^{(y)}_n`. -/
noncomputable def compoundPoissonPMF (μ : ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ y ∈ Finset.range (n + 1), Real.exp (-μ) * μ ^ y / (Nat.factorial y : ℝ) * convPow u y n

end ServiceParts.Palm


