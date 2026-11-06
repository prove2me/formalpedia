-- Prove2me | Definitions.Def_BlockBochner_linkLaw
-- name    : BlockBochner_linkLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:27.372418+00:00
-- url     : https://prove2.me/theorems/a64af9ee-850d-46b4-942d-28a27b527223
-- title:
--   The link $\mu^\tau$ (pinning of $V\setminus R$ at $\tau$)
-- statement:
--   A pinning fixes the spins outside $R$ to a configuration $\tau$; the pinned spin system lives on the sites of $R$ with law $\mu^\tau$, a regular conditional distribution of $X_R$ given $X_{V\setminus R}=\tau$.
--
--   **Formalization Note** Mathlib's `condDistrib`, which exists because the spin spaces are standard Borel. It is determined up to a null set of $\tau$ for the law of the pinned spins, and every statement about pinnings is made for almost every $\tau$. The spin spaces are assumed nonempty, which is implied by the existence of a probability measure on their product.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 1.1, p.3; Sec. 2.2, p.15

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BlockBochner

/-- **The link `µ^τ`: `µ` pinned at `τ` outside `R`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.1, p.3 ("a pinning is a spin
system on the unpinned vertices, with distribution µ conditioned on the pinned spins") and Sec. 2.2,
p.15 ("let µ^τ be a regular conditional distribution of `X_R` given `X_{V∖R} = τ`").

**Formalization Note** Mathlib's regular conditional distribution `condDistrib` of the spins on `R`
given the spins outside `R`, evaluated at `τ`. It is unique up to a `pinLaw µ R`-null set of `τ`, and
every statement about pinnings is made for `pinLaw µ R`-a.e. `τ`. Standard Borel spin spaces (the
paper's setting) make `condDistrib` available; nonemptiness of the spin spaces is implied by the
existence of a probability measure on the product. -/
noncomputable def linkLaw {V : Type*} {S : V → Type*} [∀ v, MeasurableSpace (S v)]
    [∀ v, StandardBorelSpace (S v)] [∀ v, Nonempty (S v)]
    (μ : Measure (∀ v, S v)) [IsFiniteMeasure μ] (R : Finset V)
    (τ : ∀ v : {v // v ∉ R}, S v) : Measure (∀ v : R, S v) :=
  condDistrib (fun x (v : R) => x v) (fun x (v : {v // v ∉ R}) => x v) μ τ

end BlockBochner


