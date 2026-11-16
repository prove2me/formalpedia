-- Prove2me | Definitions.Def_FewExperts_Supplement_IsOnlineDP
-- name    : FewExperts_Supplement_IsOnlineDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:53:29.742254+00:00
-- url     : https://prove2.me/theorems/143f0dda-ee33-4048-ace6-39d42f2e7b9e
-- title:
--   Adjacent gain arrays and $\varepsilon$-differential privacy of an online algorithm
-- statement:
--   Two gain arrays $g,g'\in[0,1]^{T\times N}$ are **adjacent** if they differ in a single round. That is, there is a round $t_0\in\{1,\dots,T\}$ such that $g_u=g'_u$ for every other round $u\in\{1,\dots,T\}$. At round $t_0$ the gains of all experts may change.
--
--   A randomized online algorithm $\mathcal A$, with randomness $\omega\sim\mu$, plays an expert $a_t(\omega,g)$ at each round $t$ against the gains $g$. Its output is the sequence of predictions $(a_1,\dots,a_T)$. The algorithm is **$\varepsilon$-differentially private** if, for all adjacent $g,g'$ and every set $V$ of play sequences,
--
--   $$\mu\{\omega:(a_1,\dots,a_T)(\omega,g)\in V\}\le e^{\varepsilon}\,\mu\{\omega:(a_1,\dots,a_T)(\omega,g')\in V\}.$$
--
--   This is pure differential privacy ($\delta=0$). It is the privacy notion of Theorem 5.
--
--   **Formalization Note** The output space `Fin T → Fin N` is finite, so every set of outputs is measurable. The measures are outer measures, so the condition is meaningful for every algorithm. For a measurable algorithm they are probabilities. The published `PrivLearn.Generic.IsDP` (database form, law via a map) was not reused: it would need a pushforward measure, which is zero for a non-measurable map.
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §1, p.2 (PDF p.3) and §3.3, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting
import Definitions.Def_FewExperts_gainRegret

namespace FewExperts.Supplement

open MeasureTheory

/-- Two gain arrays are **adjacent** over the horizon `T` (§1, p.2, and §3.3, p.14): they differ in
a single round, i.e. there is a round `t₀ ∈ {1, …, T}` such that `g u = g′ u` for every other round
`u ∈ {1, …, T}` (the gains of all experts at round `t₀` may change). -/
def IsAdjacentGain {N : ℕ} (T : ℕ) (g g' : ℕ → Fin N → ℝ) : Prop :=
  ∃ t₀, 1 ≤ t₀ ∧ t₀ ≤ T ∧ ∀ u, 1 ≤ u → u ≤ T → u ≠ t₀ → g u = g' u

/-- **ε-differential privacy of an online algorithm** (§3.3, p.14, and §1, p.2).
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), §3.3, p.14 (PDF 15): "A mechanism M is ε-differentially private if, for adjacent inputs
x, x′ and every measurable event V, its output distributions satisfy Pr[M(x) ∈ V] ≤
e^ε Pr[M(x′) ∈ V]."

The randomized online algorithm `A` with randomness `ω ∼ μ` is ε-DP over the horizon `T` if, for
all gain arrays `g, g′ ∈ [0, 1]^{T × N}` that are adjacent, and every set `V` of sequences of plays
`(a_1, …, a_T)`,
`μ{ω | (a_1, …, a_T)(ω, g) ∈ V} ≤ e^ε · μ{ω | (a_1, …, a_T)(ω, g′) ∈ V}`,
where `a_t(ω, g)` is the expert `A` plays at round `t` against `g`. The output is the whole
sequence of predictions (pure DP, `δ = 0`).

**Formalization Note** The output space `Fin T → Fin N` is finite, so every set of outputs is
measurable. Measures of sets are outer measures, so the inequality is meaningful for every `A`;
for a measurable algorithm they are the probabilities of the paper. -/
def IsOnlineDP {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ}
    (A : LimitedSwitching.HighProb.OnlineAlg Ω N) (T : ℕ) (ε : ℝ) : Prop :=
  ∀ g g' : ℕ → Fin N → ℝ, IsGainSeq T g → IsGainSeq T g' → IsAdjacentGain T g g' →
    ∀ V : Set (Fin T → Fin N),
      μ {ω | (fun s : Fin T => LimitedSwitching.HighProb.play A ω g (s.val + 1)) ∈ V} ≤
        ENNReal.ofReal (Real.exp ε) *
          μ {ω | (fun s : Fin T => LimitedSwitching.HighProb.play A ω g' (s.val + 1)) ∈ V}

end FewExperts.Supplement


