-- Prove2me | Definitions.Def_KnownFidelity_Rank_IsGoodEstimator
-- name    : KnownFidelity_Rank_IsGoodEstimator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:40.877722+00:00
-- url     : https://prove2.me/theorems/e8eeff49-6e58-4a40-a4e5-3bcf76ec5256
-- title:
--   A measurement estimating $F(\rho,\sigma)$ within $\varepsilon$ with probability $2/3$ on every state of rank $\le s$
-- statement:
--   Let $\sigma$ be a known state on $\mathbb C^d$, $s\in\mathbb N$, $\varepsilon\in\mathbb R$ and $n\in\mathbb N$. A POVM $E$ on $(\mathbb C^d)^{\otimes n}$ with real outcomes is a **good estimator** if, for every state $\rho$ on $\mathbb C^d$ with $\operatorname{rank}\rho\le s$,
--
--   $$\mathbb P_{E,\rho}\big(|\widehat F-F(\rho,\sigma)|\le\varepsilon\big)\ \ge\ \tfrac23 .$$
--
--   The measurement may depend on the known reference $\sigma$, the rank bound $s$ and the accuracy, but not on $\rho$.
--
--   **Formalization Note** The success event is closed in the outcome, hence measurable.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §1 (unnumbered), p. 1 (PDF p. 3)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_copyLaw
import Definitions.Def_KnownFidelity_Rank_fid

open MeasureTheory

namespace KnownFidelity.Rank

/-- **A measurement estimates the fidelity within `ε` with probability `2/3` on every state of
rank at most `s`.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §1 (unnumbered), printed p. 1 (PDF p. 3): "Let S^(≤s)_σ(ε) be the least number
of copies needed to estimate F(ρ, σ) within additive error ε, with probability at least 2/3, for
every ρ of rank at most a supplied bound s. … The measurements may depend on the known reference
and rank bound."

`IsGoodEstimator σ s ε n E` says that the POVM `E` on `n` copies of `ℂ^d`, with real outcomes,
satisfies `P(|F̂ − F(ρ, σ)| ≤ ε) ≥ 2/3` for **every** state `ρ` on `ℂ^d` with `rank ρ ≤ s`.

**Formalization Note.** The POVM is fixed before `ρ` (it may depend on `σ`, `s`, `ε`, `n`, `d`
only). The success event `{x | |x − F(ρ, σ)| ≤ ε}` is closed, hence measurable, so its Born
probability is `tr(E(B) ρ^{⊗n})`. `F(ρ, σ)` is `fid ρ σ`. -/
def IsGoodEstimator {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ) (s : ℕ) (ε : ℝ) (n : ℕ)
    (E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) ℝ) : Prop :=
  ∀ (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ), ρ.rank ≤ s →
    ENNReal.ofReal (2 / 3) ≤ copyLaw n E ρ hρ {x : ℝ | |x - fid ρ σ| ≤ ε}

end KnownFidelity.Rank


