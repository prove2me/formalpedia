-- Prove2me | Definitions.Def_KnownFidelity_Rank_mse
-- name    : KnownFidelity_Rank_mse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:48.78418+00:00
-- url     : https://prove2.me/theorems/7d197ef8-7c75-4e36-945c-e58a49aacad9
-- title:
--   Mean-square error $\mathbb E|\widehat F-v|^2$ of a real-valued measurement on $n$ copies
-- statement:
--   For a POVM $E$ on $n$ copies with real outcomes, a state $\rho$ and a target value $v\in\mathbb R$, the **mean-square error** is
--
--   $$\mathbb E\,|\widehat F-v|^2=\int_{\mathbb R}(x-v)^2\,d\mathbb P_{E,\rho}(x),$$
--
--   where $\widehat F$ is the outcome of measuring $E$ on $\rho^{\otimes n}$. This is the risk in Theorem 1.1, Lemma 3.1 and Proposition 3.2.
--
--   **Formalization Note** The integral is a lower Lebesgue integral with values in $[0,\infty]$, so a non-integrable square gives $+\infty$ rather than a junk value.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Theorem 1.1, p. 1 (PDF p. 3); Lemma 3.1, p. 5 (PDF p. 7); Proposition 3.2, p. 7 (PDF p. 9)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_copyLaw

open MeasureTheory

namespace KnownFidelity.Rank

/-- **Mean-square error** `E|F̂ − v|²` of a real-valued collective measurement.
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Theorem 1.1, printed p. 1 (PDF p. 3), Lemma 3.1, printed p. 5 (PDF p. 7), and
Proposition 3.2, printed p. 7 (PDF p. 9): the risk `E|F̂ − F(ρ, σ)|²` of an estimator `F̂`.

For a POVM `E` on `n` copies with real outcomes, a state `ρ` and a target value `v`,
`mse n E ρ hρ v = ∫ (x − v)² d P(x)`, where `P = copyLaw n E ρ hρ` is the law of the outcome
`F̂ = x` on `ρ^{⊗n}`.

**Formalization Note.** The expectation is the lower Lebesgue integral of `ofReal((x − v)²)` in
`ℝ≥0∞`, so a non-integrable square gives `∞`, never the junk value `0` of a Bochner integral. The
estimator's real output is the POVM's outcome itself (post-processing is part of the POVM). -/
noncomputable def mse {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (E : QAlgorithms.Measurements.OperatorPOVM (Fin n → ι) ℝ)
    (ρ : Matrix ι ι ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) (v : ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal ((x - v) ^ 2) ∂(copyLaw n E ρ hρ)

end KnownFidelity.Rank


