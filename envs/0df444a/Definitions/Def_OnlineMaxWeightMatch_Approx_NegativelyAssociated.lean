-- Prove2me | Definitions.Def_OnlineMaxWeightMatch_Approx_NegativelyAssociated
-- name    : OnlineMaxWeightMatch_Approx_NegativelyAssociated
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:04.025491+00:00
-- url     : https://prove2.me/theorems/1c9c0c89-d465-420e-bf25-1fe57972d342
-- title:
--   Negatively associated random variables (Definition 2.5)
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a measure space and let $(X_k)_{k\in\kappa}$ be a family of real random variables on it. The family is **negatively associated (NA)** if every two monotone non-decreasing functions of the family that depend on disjoint sets of variables are negatively correlated: for all disjoint finite index sets $A,B\subseteq\kappa$ and all non-decreasing $f:\mathbb R^{A}\to\mathbb R$, $g:\mathbb R^{B}\to\mathbb R$,
--
--   $$
--   \mathbb E\big[f(X_A)\cdot g(X_B)\big]\;\le\;\mathbb E\big[f(X_A)\big]\cdot\mathbb E\big[g(X_B)\big], \tag{1}
--   $$
--
--   where $X_A=(X_a)_{a\in A}$ and "non-decreasing" refers to the coordinatewise order on $\mathbb R^A$.
--
--   Independent random variables are trivially NA. The notion is the negative-dependence tool of the analysis of Algorithm 1: it yields the pairwise negative correlation of the early-occupancy indicators of different bins (Lemma 4.9, Corollary 4.10).
--
--   **Formalization Note** The test functions $f,g$ range over Borel measurable functions that are bounded, so that all three expectations in (1) exist; the paper writes no integrability condition. For the $\{0,1\}$-valued variables used in the paper this is no restriction. The index set $\kappa$ is an arbitrary type and $A,B$ are finite subsets of it.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 5, Definition 2.5, eq. (1)

import Mathlib

open MeasureTheory

namespace OnlineMaxWeightMatch.Approx

/-- **Negative association** (Papadimitriou–Pollner–Saberi–Wajc, Definition 2.5, after
Joag-Dev–Proschan and Khursheed–Lai Saxena). A family `X : κ → Ω → ℝ` of real random variables on
`(Ω, μ)` is negatively associated if for every two disjoint finite sets of indices `A`, `B` and
every two monotone non-decreasing functions `f` of the coordinates in `A` and `g` of the
coordinates in `B`,
`E[f(X_A) · g(X_B)] ≤ E[f(X_A)] · E[g(X_B)]` (equation (1)).
The test functions are taken Borel measurable and bounded, so that every expectation in (1)
exists; monotonicity is for the coordinatewise order on `A → ℝ`. -/
def NegativelyAssociated {Ω κ : Type*} [MeasurableSpace Ω] (X : κ → Ω → ℝ) (μ : Measure Ω) :
    Prop :=
  ∀ (A B : Finset κ), Disjoint A B →
    ∀ (f : (A → ℝ) → ℝ) (g : (B → ℝ) → ℝ),
      Monotone f → Monotone g → Measurable f → Measurable g →
      (∃ C : ℝ, ∀ y, |f y| ≤ C) → (∃ C : ℝ, ∀ y, |g y| ≤ C) →
      ∫ ω, f (fun a => X a ω) * g (fun b => X b ω) ∂μ ≤
        (∫ ω, f (fun a => X a ω) ∂μ) * ∫ ω, g (fun b => X b ω) ∂μ

end OnlineMaxWeightMatch.Approx


