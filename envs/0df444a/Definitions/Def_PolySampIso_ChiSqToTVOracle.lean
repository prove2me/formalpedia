-- Prove2me | Definitions.Def_PolySampIso_ChiSqToTVOracle
-- name    : PolySampIso_ChiSqToTVOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:12.166551+00:00
-- url     : https://prove2.me/theorems/a2b71d6a-1a71-4ee4-96a8-1fe60ef7c09f
-- title:
--   Definition 8: a $(\beta,\delta)$-χ²-to-TV oracle
-- statement:
--   Let $\mu$ be a probability measure on $X$ and let $O$ be a randomized map $X\to X$, given by its Markov kernel $x\mapsto\mathrm{Law}(O(x))$. Then $O$ is a **$(\beta,\delta)$-$\chi^2$-to-TV oracle for $\mu$** if, whenever its input $x_0$ has a law $\nu$ with $\chi^2(\nu\|\mu)\le\beta$, its output has law $\nu O$ with
--
--   $$\mathrm{TV}(\nu O,\mu)\le\delta .$$
--
--   This is the interface between the cooling framework (Algorithm 5, Lemma 29) and the samplers for the cooled measures (Algorithm 7, Proposition 8): each stage turns a $\chi^2$-warm start into a TV-accurate sample.
--
--   **Formalization Note** The definition records three clauses: $O$ is a Markov kernel, it maps $X$ into $X$, and the TV bound holds for every probability measure $\nu$ with $\chi^2(\nu\|\mu)\le\beta$ (which forces $\nu\ll\mu$, so $x_0\in X$ almost surely).
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Definition 8, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_PolySampIso_Divergences

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolySampIso

/-- **Definition 8** (χ²-to-TV oracle).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Definition 8, p.31 (PDF p.33): "Let µ ∈ P(X) and
let O : X → X be randomized. We call O a (β, δ)-χ2-to-TV oracle for µ if, given x0 ∈ X with
χ2(Law(x0)∥µ) ≤ β, it outputs x ∈ X with TV(Law(x), µ) ≤ δ."

**Formalization Note.** The randomized map `O` is its Markov kernel `x ↦ Law(O(x))` (as in the
paper's proof of Lemma 29, p.39, "Pt(x, ·) := Law(Ot(x))"). The clauses are: `O` is a Markov kernel;
it maps `X` to `X` (`O(x, Xᶜ) = 0` for `x ∈ X`); and for every probability measure `ν` (the law of
`x₀`) with `χ²(ν∥µ) ≤ β`, the output law `νO = O ∘ₘ ν` satisfies `TV(νO, µ) ≤ δ`. When `µ` lives on
`X`, `χ²(ν∥µ) ≤ β < ∞` forces `ν ≪ µ`, so `x₀ ∈ X` almost surely. -/
def IsChiSqToTVOracle {α : Type*} [MeasurableSpace α] (X : Set α) (O : Kernel α α)
    (μ : Measure α) (β δ : ℝ) : Prop :=
  IsMarkovKernel O ∧ (∀ x ∈ X, O x Xᶜ = 0) ∧
    ∀ ν : Measure α, IsProbabilityMeasure ν → chiSq ν μ ≤ ENNReal.ofReal β →
      tvDist (O ∘ₘ ν) μ ≤ δ

end PolySampIso


