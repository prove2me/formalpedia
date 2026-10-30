-- Prove2me | Definitions.Def_RoughgardenPOA_IsCCE
-- name    : RoughgardenPOA_IsCCE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:36:42.371986+00:00
-- url     : https://prove2.me/theorems/743ab35c-3eb4-4356-977f-900e905fbc26
-- title:
--   Coarse correlated equilibrium (eq. (15))
-- statement:
--   A **coarse correlated equilibrium** of a cost-minimization game is a probability distribution $\sigma$ over outcomes such that, for every player $i$ and every strategy $s_i' \in S_i$,
--
--   $$\mathbf E_{\mathbf s \sim \sigma}[C_i(\mathbf s)] \le \mathbf E_{\mathbf s \sim \sigma}[C_i(s_i', \mathbf s_{-i})].$$
--
--   Here both expectations are taken under the joint distribution $\sigma$: an outcome $\mathbf s$ is drawn from $\sigma$, and on the right player $i$ replaces its own component by the fixed strategy $s_i'$. No player gains in expectation by committing in advance to a fixed deviation. The set of these distributions (the Hannan set) contains every correlated, mixed Nash and pure Nash equilibrium.
--
--   **Formalization Note** $\sigma$ is a probability measure on the product of arbitrary measurable strategy spaces (no finiteness is assumed). The definition also requires every expectation in the inequality to exist as a finite number, i.e. each $C_i$ and each deviation cost $\mathbf s \mapsto C_i(s_i', \mathbf s_{-i})$ is $\sigma$-integrable; for a finite game with discrete $\sigma$-algebras this holds for every probability measure.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), doi:10.1145/2806883, §3.1, eq. (15), p. 12

import Mathlib

namespace RoughgardenPOA

/-- **Coarse correlated equilibrium ((15)).**
Roughgarden, *Intrinsic Robustness of the Price of Anarchy*, J. ACM 62(5) (2015),
doi:10.1145/2806883, §3.1, (15), p. 12: "Finally, a coarse correlated equilibrium [86] of a
cost-minimization game is a probability distribution σ over outcomes that satisfies
E_{s∼σ}[Ci(s)] ≤ E_{s∼σ}[Ci(s′i, s−i)] (15) for every i and s′i ∈ Si."

`IsCCE C σ` says that `σ` is a probability measure on the outcomes `∀ i, S i`, that every
expectation in (15) exists (is finite), and that for every player `i` and every strategy
`t : S i`, `∫ s, C i s ∂σ ≤ ∫ s, C i (Function.update s i t) ∂σ`.

**Formalization Note.** Outcomes carry Mathlib's product σ-algebra; the strategy sets are
arbitrary measurable spaces (no finiteness), so the paper's continuous strategy spaces are
included. The deviation expectation `E_{s∼σ}[Ci(s′i, s−i)]` integrates the map
`s ↦ C i (Function.update s i t)` against the joint distribution `σ` itself (not a product or
marginal measure). The integrability conjuncts read the paper's expectations as finite: the
Bochner integral of a non-integrable function would be `0`. -/
def IsCCE {ι : Type*} [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (C : ι → (∀ i, S i) → ℝ) (σ : MeasureTheory.Measure (∀ i, S i)) : Prop :=
  MeasureTheory.IsProbabilityMeasure σ ∧
    (∀ i, MeasureTheory.Integrable (C i) σ) ∧
    (∀ i (t : S i), MeasureTheory.Integrable (fun s => C i (Function.update s i t)) σ) ∧
    (∀ i (t : S i), ∫ s, C i s ∂σ ≤ ∫ s, C i (Function.update s i t) ∂σ)

end RoughgardenPOA


