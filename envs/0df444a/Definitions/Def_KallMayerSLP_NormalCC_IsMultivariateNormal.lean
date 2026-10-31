-- Prove2me | Definitions.Def_KallMayerSLP_NormalCC_IsMultivariateNormal
-- name    : KallMayerSLP_NormalCC_IsMultivariateNormal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:05.140996+00:00
-- url     : https://prove2.me/theorems/59eff472-cbbf-43ce-a48f-87ec0007b5c4
-- title:
--   Multivariate normal random vector $\zeta=B\tilde\zeta+\mu$ (Definition 2.1)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space. An $r$-dimensional random vector $\zeta$ has a **multivariate normal distribution** if there exist an integer $s\ge 0$, an $r\times s$ matrix $B$, a vector $\mu\in\mathbb R^r$ and an $s$-dimensional random vector $\tilde\zeta$ whose components $\tilde\zeta_1,\dots,\tilde\zeta_s$ are stochastically independent and standard normal, such that
--   $$\zeta=B\tilde\zeta+\mu .$$
--
--   The definition allows degenerate distributions: $B$ is arbitrary, so components of $\zeta$ may be deterministic (a zero row of $B$ gives $\zeta_i\equiv\mu_i$). It is the class of distributions for which the separate chance constraints of §2.3.2 are studied.
--
--   **Formalization Note** $\tilde\zeta$ lives on the same probability space as $\zeta$ and is a standard Gaussian vector in the sense of the platform definition `HighDimProb.RandomVectors.IsStandardGaussianVector`; the identity $\zeta=B\tilde\zeta+\mu$ is required $\mathbb P$-almost surely.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Definition 2.1, eq. (2.25), p.103 (PDF p.113)

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector

open MeasureTheory ProbabilityTheory

namespace KallMayerSLP.NormalCC

/-- **Multivariate normal distribution** (Kall & Mayer 2005, Chapter 2, Definition 2.1, (2.25),
p.103, PDF p.113): "The `r`-dimensional random vector `ζ` has a multivariate normal distribution,
if there exist an `(r × s)` matrix `B` and `μ ∈ ℝ^r`, such that `ζ = B ζ̃ + μ` holds, where `ζ̃` is
an `s`-dimensional random vector with `ζ̃_i` being stochastically independent and having a standard
normal distribution, `∀ i`."

The definition allows degenerate distributions (any matrix `B`, any `s`), as the book stresses on
p.104 ("this definition allows for deterministic components of `ζ`").

**Formalization Note.** The random vector `ζ̃` lives on the same probability space as `ζ` and is
a standard Gaussian vector in the sense of the platform definition
`HighDimProb.RandomVectors.IsStandardGaussianVector` (measurable, jointly independent coordinates,
each with law `gaussianReal 0 1`). The identity `ζ = B ζ̃ + μ` is an identity of random vectors,
read as `P`-almost sure equality. -/
def IsMultivariateNormal {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {r : ℕ}
    (ζ : Ω → Fin r → ℝ) : Prop :=
  ∃ (s : ℕ) (B : Matrix (Fin r) (Fin s) ℝ) (μ : Fin r → ℝ) (ζt : Fin s → Ω → ℝ),
    HighDimProb.RandomVectors.IsStandardGaussianVector P ζt ∧
      ∀ᵐ ω ∂P, ζ ω = B.mulVec (fun j => ζt j ω) + μ

end KallMayerSLP.NormalCC


