-- Prove2me | Definitions.Def_BauerleRiederMDP_Contracting_ConvergenceAssumptionC
-- name    : BauerleRiederMDP_Contracting_ConvergenceAssumptionC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:48.73239+00:00
-- url     : https://prove2.me/theorems/efbcdcfc-2e5e-4dc1-9a4a-55237819de59
-- title:
--   The Convergence Assumption (C) of an infinite-horizon Markov Decision Model
-- statement:
--   Let $(E,A,D,Q,r,\beta)$ be a stationary Markov Decision Model with infinite horizon and no terminal reward, and let $F^\infty$ be the set of Markov policies $\pi=(f_0,f_1,\dots)$, sequences of measurable decision rules $f_k:E\to A$ with $f_k(x)\in D(x)$. Write $r^+=\max(r,0)$ and let $(X_k)$ be the state process under $\pi$ started in $x$.
--
--   The model satisfies the **Convergence Assumption (C)** if for every state $x\in E$
--
--   $$\lim_{n\to\infty}\ \sup_{\pi\in F^\infty}\ \mathbb E^\pi_x\Big[\sum_{k=n}^\infty \beta^k r^+\big(X_k,f_k(X_k)\big)\Big]=0 .$$
--
--   Together with the Integrability Assumption (A), $\delta(x)=\sup_\pi \mathbb E^\pi_x[\sum_{k\ge0}\beta^k r^+(X_k,f_k(X_k))]<\infty$, it is the standing assumption of Chapter 7: it makes the infinite-horizon problem the limit of the finite-horizon ones.
--
--   **Formalization Note** The model and the value functionals are the published `MDPFinance.Contracting` bundles. For each policy the tail expectation is written as the full-horizon expectation of the discounted positive rewards minus the $n$-stage one, both computed in `EReal`; under (A) both are finite and the difference is exactly the tail.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Springer Universitext, DOI 10.1007/978-3-642-18324-9, §7.1, Convergence Assumption (C), p.195 (PDF p.206)

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value

open MeasureTheory ProbabilityTheory Filter Topology

namespace BauerleRiederMDP.Contracting

open MDPFinance.Contracting

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- The **Convergence Assumption (C)** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), §7.1, p.195, PDF p.206), a standing assumption of Chapter 7:
for every state `x`,
`lim_{n→∞} sup_π 𝔼^π_x [∑_{k=n}^∞ β^k r^+(X_k, f_k(X_k))] = 0`,
the supremum taken over all Markov policies `π = (f_0, f_1, …) ∈ F^∞`.

**Formalization Note.** The model and its value functionals are the published
`MDPFinance.Contracting` bundles. For a policy `π`, the tail expectation
`𝔼^π_x [∑_{k≥n} β^k r^+(X_k, f_k(X_k))]` is written as the full-horizon expectation
`Jinfpi M r⁺ π x = 𝔼^π_x [∑_{k≥0} β^k r^+]` minus the `n`-stage expectation
`Jnpi M r⁺ π n x = 𝔼^π_x [∑_{k<n} β^k r^+]` (both `[0, ∞]`-valued, computed in `EReal`).
Under the Integrability Assumption (A), with which the book always pairs (C), both terms are
finite and the difference is exactly the tail expectation; the convergence is in `EReal`. -/
def ConvergenceAssumptionC (M : MarkovDecisionModel E A) : Prop :=
  ∀ x : E, Tendsto
    (fun n : ℕ => ⨆ π ∈ {π : ℕ → E → A | IsPolicyOf M π},
      Jinfpi M (fun p => max (M.r p) 0) π x - Jnpi M (fun p => max (M.r p) 0) π n x)
    atTop (𝓝 0)

end BauerleRiederMDP.Contracting


