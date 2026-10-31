-- Prove2me | Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveMeasure
-- name    : KallMayerSLP_GenConcave_IsGammaConcaveMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:37.634089+00:00
-- url     : https://prove2.me/theorems/bc3fe9fe-2796-4641-9482-d2d8e6492111
-- title:
--   $\gamma$-concave probability measures (Definition 2.4)
-- statement:
--   A probability measure $\mathbb P$ on the Borel sets $\mathcal B^r$ of $\mathbb R^r$ is **$\gamma$-concave**, for $\gamma\in[-\infty,\infty]$, if for any convex Borel sets $A$ and $B$ and any $\lambda\in[0,1]$ for which $\lambda A+(1-\lambda)B$ is Borel measurable,
--
--   $$
--   \mathbb P\bigl(\lambda A+(1-\lambda)B\bigr)\ \ge\ \mathcal M_\gamma^\lambda\bigl(\mathbb P(A),\mathbb P(B)\bigr).
--   $$
--
--   Here $A+B=\{y+z\mid y\in A,\ z\in B\}$ and $\lambda A=\{\lambda y\mid y\in A\}$ (eq. (2.64)). For $\gamma=-\infty$ the measure is called quasi-concave, $\mathbb P(\lambda A+(1-\lambda)B)\ge\min\{\mathbb P(A),\mathbb P(B)\}$; for $\gamma=0$ log-concave, $\mathbb P(\lambda A+(1-\lambda)B)\ge\mathbb P(A)^\lambda\mathbb P(B)^{1-\lambda}$.
--
--   $\gamma$-concavity of the law of a random vector $\xi$ makes its distribution function $\gamma$-concave and hence the joint probability constraint $\mathbb P(Tx\ge\xi)\ge\alpha$ convex.
--
--   **Formalization Note** $\mathbb R^r$ is `Fin r → ℝ`, whose product σ-algebra is the Borel σ-algebra. The sums and scalings of sets are Mathlib's pointwise operations, which coincide with (2.64). The measurability side condition on $\lambda A+(1-\lambda)B$ is kept as printed. Probabilities enter $\mathcal M_\gamma^\lambda$ as real numbers.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Definition 2.4, pp.125–126 (PDF 135–136), with (2.64), p.124 (PDF 134)

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_genMean

open MeasureTheory
open scoped Pointwise

namespace KallMayerSLP.GenConcave

/-- A **`γ`-concave probability measure** (Kall & Mayer, *Stochastic Linear Programming*
(2005), Chapter 2, Definition 2.4, pp. 125–126, PDF pp. 135–136): a probability measure
`ℙ` on the Borel sets of `ℝ^r` such that for any convex Borel sets `A`, `B` and any
`λ ∈ [0, 1]` for which `λA + (1 − λ)B` is Borel measurable,
`ℙ(λA + (1 − λ)B) ≥ M_γ^λ(ℙ(A), ℙ(B))`.

`γ = −∞` gives a quasi-concave measure, `γ = 0` a log-concave measure (p. 126).

**Formalization Note.** `ℝ^r` is `Fin r → ℝ`, whose product σ-algebra is its Borel
σ-algebra. `λA` and `A + B` are Mathlib's pointwise set operations, which are the book's
(2.64) (p. 124): `A + B = {y + z | y ∈ A, z ∈ B}`, `λA = {λy | y ∈ A}`. The measurability
side condition on `λA + (1 − λ)B` is kept exactly as printed. Probabilities are real numbers
(`toReal` of the measure, finite since `ℙ` is a probability measure). -/
def IsGammaConcaveMeasure {r : ℕ} (γ : EReal) (P : Measure (Fin r → ℝ)) : Prop :=
  IsProbabilityMeasure P ∧
    ∀ A B : Set (Fin r → ℝ), Convex ℝ A → Convex ℝ B → MeasurableSet A → MeasurableSet B →
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, MeasurableSet (lam • A + (1 - lam) • B) →
        genMean γ lam (P A).toReal (P B).toReal ≤ (P (lam • A + (1 - lam) • B)).toReal

end KallMayerSLP.GenConcave


