-- Prove2me | Definitions.Def_SampleMechDesign_Supplement_SamplesSuffice
-- name    : SampleMechDesign_Supplement_SamplesSuffice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:47:18.436625+00:00
-- url     : https://prove2.me/theorems/2c2769a9-13ad-502f-b96f-4c935b225ec2
-- title:
--   Theorem A.16 — $N$ samples suffice for $\epsilon$-uniform convergence with confidence $1-\delta$
-- statement:
--   Theorem A.16 speaks of $N_{\mathcal M}(\epsilon,\delta)$, "the number of samples required to ensure that for any distribution $\mathcal D$, with probability at least $1-\delta$ over the draw of a set of samples of size $N_{\mathcal M}(\epsilon,\delta)$ from $\mathcal D$, for all auctions $M\in\mathcal M$, average profit is $\epsilon$-close to expected profit."
--
--   For a class $F$ of real functions on $X$, **$N$ samples suffice** if for every finitely supported probability distribution $\mathcal D$ on $X$,
--   $$
--   \Pr_{S\sim\mathcal D^N}\Big[\forall f\in F:\ \Big|\frac1N\sum_{i=1}^Nf(S_i)-\mathbb E_{\mathcal D}[f]\Big|\le\epsilon\Big]\ \ge\ 1-\delta .
--   $$
--   A lower bound "$N_{\mathcal M}(\epsilon,\delta)\ge B$" then says that every $N$ for which $N$ samples suffice has $N\ge B$.
--
--   **Formalization Note** Only finitely supported distributions are required, which weakens the hypothesis and so strengthens a lower bound; for such distributions every expectation is a finite weighted sum. The probability of the event is its product measure (its outer measure if it is not measurable).
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Theorem A.16, p.34 (PDF p.34)

import Mathlib

open MeasureTheory

namespace SampleMechDesign.Supplement

/-- **`N` samples suffice for `ε`-uniform convergence with confidence `1 − δ`.** Balcan,
Sandholm, Vitercik, arXiv:1705.00243v6, Theorem A.16, p.34: `N_M(ε, δ)` is "the number of samples
required to ensure that for any distribution D, with probability at least 1 − δ over the draw of
a set of samples of size N_M(ε, δ) from D, for all auctions M ∈ M, average profit is ϵ-close to
expected profit."

`SamplesSuffice F ε δ N` says: for every finitely supported probability distribution `D` on `X`,
with probability at least `1 − δ` over `S ∼ D^N`, every `f ∈ F` has
`|(1/N) ∑_i f(S_i) − E_D[f]| ≤ ε`. Theorem A.16 is then "`SamplesSuffice F ε δ N` implies
`N ≥` the bound".

**Formalization Note.**
* Only finitely supported distributions are required: that is a weaker hypothesis than "for any
  distribution", so a lower bound on `N` proved from it is the stronger statement. For a finitely
  supported `D` every `f` is integrable, so `E_D[f]` is the finite weighted sum.
* A sample is a tuple `S : Fin N → X` drawn from `Measure.pi`; the probability of the event is its
  product measure (its outer measure if it is not measurable). -/
def SamplesSuffice {X : Type*} [MeasurableSpace X] (F : Set (X → ℝ)) (ε δ : ℝ) (N : ℕ) : Prop :=
  ∀ (D : Measure X) [IsProbabilityMeasure D], (∃ s : Finset X, D (↑s)ᶜ = 0) →
    ENNReal.ofReal (1 - δ) ≤ Measure.pi (fun _ : Fin N => D)
      {S : Fin N → X | ∀ f ∈ F, |(1 / (N : ℝ)) * ∑ i, f (S i) - ∫ x, f x ∂D| ≤ ε}

end SampleMechDesign.Supplement


