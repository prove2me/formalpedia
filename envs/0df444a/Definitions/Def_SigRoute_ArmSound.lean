-- Prove2me | Definitions.Def_SigRoute_ArmSound
-- name    : SigRoute_ArmSound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:19.796895+00:00
-- url     : https://prove2.me/theorems/5602005f-3d3f-4da2-a388-6fc0d8d442d2
-- title:
--   Arm soundness (HA) and the forgery bound $\gamma$
-- statement:
--   Fix a run with post-base-stage σ-algebras $\mathcal G_j$.
--
--   1. **Arm soundness (HA).** For soundness errors $\varepsilon_A,\varepsilon_B$, in every round $j\le N$, given the history and the base view, the arm $\rho_j$ accepts with probability at most $\varepsilon_{\rho_j}$:
--   $$
--   \mathbb P[a_j=1\mid\mathcal F_{j-1},\nu_j]\le\varepsilon_{\rho_j}\quad\text{almost surely.}
--   $$
--   2. **Forgery bound.** A number $\gamma$ bounds the A-forgery rate of the run if in every round $j\le N$
--   $$
--   \mathbb P[\rho_j=A\mid\mathcal F_{j-1}]\le\gamma\quad\text{almost surely.}
--   $$
--
--   (HA) is where the statistical soundness of the arm protocols enters, and $\gamma$ is how much probability a cheating prover can push into arm $A$.
--
--   **Formalization Note** The paper states (HA) for interactive machines (every view, every prover strategy) and notes that, because the arm stage uses fresh verifier coins, it holds for every history; the proof of Lemma 13 uses exactly the conditional form above, with $\mathcal G_j$ (`G j`) playing the role of $(\mathcal F_{j-1},\nu_j)$. The paper defines $\gamma$ as the supremum of $\mathbb P[\rho_j=A\mid\mathcal F_{j-1}]$ over provers, rounds and histories; the theorems take any bound on it, which the paper's $\gamma$ is.
-- source:
--   Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), (HA), p.6; §4.2 "Forgery rate", p.7

import Mathlib
import Definitions.Def_SigRoute_condProb
import Definitions.Def_SigRoute_Arm

namespace SigRoute

open MeasureTheory

/-- Hypothesis (HA), arm soundness, in the conditional form the paper uses (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), (HA) and the
paragraph after it, p.6; proof of Lemma 13, p.7): in every round `j < N`, given the history and the base
view (the σ-algebra `G j`), the arm `ρ_j` accepts with probability at most `ε_{ρ_j}`:
`P[a_j = 1 | F_{j−1}, ν_j] ≤ ε_{ρ_j}` almost surely.

**Formalization Note** (HA) is printed for interactive machines ("for every view ν and every prover
strategy, V_X accepts Π_X on input (x, ν) with probability at most ε_X"); the paper states that, because
the arm stage uses fresh verifier coins, it holds "for every history", and the proof of Lemma 13 uses it
exactly in this conditional form. No machine model is formalized; "x ∉ L" is not modelled, the run being
the run on a false statement. -/
def ArmSound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (G : ℕ → MeasurableSpace Ω)
    (ρ : ℕ → Ω → Arm) (a : ℕ → Ω → Bool) (N : ℕ) (ε : Arm → ℝ) : Prop :=
  ∀ j < N, ∀ᵐ ω ∂μ, condProb μ (G j) {ω | a j ω = true} ω ≤ ε (ρ j ω)

/-- `γ` bounds the A-forgery rate of a run (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), §4.2 "Forgery rate", p.7): in every round `j < N`,
`P[ρ_j = A | F_{j−1}] ≤ γ` almost surely.

**Formalization Note** The paper defines `γ` as the supremum of `P[ρ_j = A | F_{j−1}]` over provers,
rounds and histories; a single run cannot see that supremum, so the theorems take any `γ` that bounds the
conditional routing probability of the run. The paper's `γ` is such a bound for every prover's run. -/
def ForgeryBound {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) (F : Filtration ℕ m)
    (ρ : ℕ → Ω → Arm) (N : ℕ) (γ : ℝ) : Prop :=
  ∀ j < N, ∀ᵐ ω ∂μ, condProb μ (F j) {ω | ρ j ω = Arm.A} ω ≤ γ

end SigRoute


