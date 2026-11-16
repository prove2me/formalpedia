-- Prove2me | Definitions.Def_SigRoute_Supplement_ArmComplete
-- name    : SigRoute_Supplement_ArmComplete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:58:51.354193+00:00
-- url     : https://prove2.me/theorems/c3a89646-a616-4a6d-ad1a-4238cac370f7
-- title:
--   Completeness hypothesis (HC) in conditional form
-- statement:
--   Consider a routed run with arms $A,B$, routes $\rho_j$ and arm decisions $a_j\in\{0,1\}$, and write $\mathcal G_j$ for the information available after the base stage of round $j$ (the history $\mathcal F_{j-1}$ together with the base view $\nu_j$). Given completeness errors $\delta_A,\delta_B$, the run satisfies **hypothesis (HC)** for its first $N$ rounds if in every round the arm the round is sent to accepts, conditionally on $\mathcal G_j$, with probability at least $1-\delta_{\rho_j}$:
--
--   $$
--   \mathbb P\bigl[a_j=1\mid \mathcal F_{j-1},\nu_j\bigr]\ \ge\ 1-\delta_{\rho_j}\quad\text{almost surely, for every round } j\le N .
--   $$
--
--   This is the completeness counterpart of the arm-soundness hypothesis (HA): it is the only property of the honest prover on a true statement that the completeness theorem (Theorem 10) uses.
--
--   **Formalization Note** Rounds are 0-based (`j < N`), the paper's $(\mathcal F_{j-1},\nu_j)$ is the σ-algebra `G j` of the published run model, and the conditional probability is the published `SigRoute.condProb` (Mathlib's conditional expectation of the indicator), so the inequality holds almost everywhere. The hypotheses $x\in L$ and "the honest prover is used" are not modelled separately; (HC) is what they supply.
-- source:
--   Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), hypothesis (HC), p.6, and proof of Theorem 10, p.6

import Mathlib
import Definitions.Def_SigRoute_condProb
import Definitions.Def_SigRoute_Arm

namespace SigRoute.Supplement

open MeasureTheory

/-- Hypothesis (HC), completeness, in the conditional form the paper uses (Dumlu, Signal-Routed Two-Arm
Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), (HC), p.6; proof of
Theorem 10, p.6): in every round `j < N`, conditioned on the history and the base view (the σ-algebra
`G j`), the arm `ρ_j` accepts with probability at least `1 − δ_{ρ_j}`:
`P[a_j = 1 | F_{j−1}, ν_j] ≥ 1 − δ_{ρ_j}` almost surely.

**Formalization Note** This is the completeness twin of the published `SigRoute.ArmSound` (the
soundness direction `≤ ε`). "x ∈ L" and "the honest prover is used" are not modelled: the run is the run
of the honest prover on a true statement, and (HC) is what those supply. Rounds are 0-based, so the
paper's `(F_{j−1}, ν_j)` is `G j`. -/
def ArmComplete {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (G : ℕ → MeasurableSpace Ω)
    (ρ : ℕ → Ω → Arm) (a : ℕ → Ω → Bool) (N : ℕ) (δ : Arm → ℝ) : Prop :=
  ∀ j < N, ∀ᵐ ω ∂μ, 1 - δ (ρ j ω) ≤ condProb μ (G j) {ω | a j ω = true} ω

end SigRoute.Supplement


