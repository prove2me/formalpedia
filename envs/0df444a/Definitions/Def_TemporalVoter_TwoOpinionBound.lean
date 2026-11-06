-- Prove2me | Definitions.Def_TemporalVoter_TwoOpinionBound
-- name    : TemporalVoter_TwoOpinionBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:09.23456+00:00
-- url     : https://prove2.me/theorems/90b4cd1d-2b89-4425-bdb6-4d2b850db7a8
-- title:
--   The two-opinion consensus bound of Theorem 3.1 for a given constant $b$
-- statement:
--   For a real number $b$, **TwoOpinionBound$(b)$** is the statement: for every temporal graph $\mathcal G$ with fixed degrees and minimum degree $d_{\min}$, every initial two-opinion state with initial minority set $s_0$, all integers $\Delta_0,\Delta_1,\ldots\ge1$ and reals $\phi_0,\phi_1,\ldots\in[0,1]$ with $\phi^{I_j}(\mathcal G)\ge\phi_j$ for all $j$, where $I_j=[I^-_j,I^+_j]$: if
--   $$J=\min\Bigl\{j:\ \sum_{\ell=0}^{j}\phi_\ell\ \ge\ b\Bigl(\frac{\mathrm{Vol}(s_0)}{d_{\min}}+\log\bigl(1+\mathrm{Vol}(s_0)\bigr)\Bigr)\Bigr\}<\infty,$$
--   then with probability at least $1/2$ the consensus time of the standard two-opinion voter model is at most $\Delta_0+\dots+\Delta_J$.
--
--   Theorem 3.1 asserts that TwoOpinionBound$(b)$ holds for some $b>0$. The proof of Theorem 1.3 uses that conclusion for a fixed such $b$ (the Claim on p.25), which is why it is named here.
--
--   **Formalization Note** $J$ is the least index given by the finiteness hypothesis (`Nat.find`). The initial state is any $\sigma_0:V\to\{0,1\}$ and $s_0$ is its minority set.
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Theorem 3.1, p.15 (restated p.22)

import Mathlib
import Definitions.Def_TemporalVoter_minoritySet

open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory

namespace TemporalVoter

/-- The conclusion of **Theorem 3.1** (arXiv:2606.13374, version of 2 Nov 2026, p.15, restated
p.22) for a given constant `b`: for every temporal graph with fixed degrees, every initial
two-opinion state `σ₀` (initial minority set `s₀`), all integers `Δ_0, Δ_1, … ≥ 1` and reals
`φ_0, φ_1, … ∈ [0, 1]` with `φ^{I_j}(G) ≥ φ_j` for all `j`, if
`J = min{j : ∑_{ℓ=0}^{j} φ_ℓ ≥ b(Vol(s₀)/d_min + log(1 + Vol(s₀)))}` is finite, then with probability
at least `1/2` the consensus time is at most `Δ_0 + ⋯ + Δ_J`.

**Formalization Note** Theorem 3.1 is `∃ b > 0, TwoOpinionBound b`; the Claim in the proof of
Theorem 1.3 (p.25) is stated for every `b` with `TwoOpinionBound b`. `J` is `Nat.find` of the
finiteness hypothesis. -/
def TwoOpinionBound (b : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] (T : TemporalGraph V) (σ₀ : V → Fin 2) (Δ : ℕ → ℕ) (φ : ℕ → ℝ),
    (∀ j, 1 ≤ Δ j) → (∀ j, 0 ≤ φ j ∧ φ j ≤ 1) →
    (∀ j, φ j ≤ intervalCond T (Iminus Δ j) (Iplus Δ j)) →
    ∀ hJ : ∃ j, b * (T.vol (minoritySet T σ₀) / T.dmin + Real.log (1 + T.vol (minoritySet T σ₀)))
        ≤ ∑ ℓ ∈ Finset.range (j + 1), φ ℓ,
    (1 / 2 : ℝ≥0∞) ≤ voterLaw T 2 σ₀
      {ω | ∃ t, t ≤ ∑ ℓ ∈ Finset.range (Nat.find hJ + 1), Δ ℓ ∧ IsConsensus (ω t)}

end TemporalVoter


