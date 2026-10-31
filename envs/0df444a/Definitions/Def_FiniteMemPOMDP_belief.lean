-- Prove2me | Definitions.Def_FiniteMemPOMDP_belief
-- name    : FiniteMemPOMDP_belief
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:02.283982+00:00
-- url     : https://prove2.me/theorems/ec17abcd-2726-4f2a-b668-22a903a412ec
-- title:
--   Belief $P_m(k)=\mathbb P^{p_1}_\sigma(K_m=k\mid H_m)$ after a history
-- statement:
--   Given $\sigma$ and $p_1$, the **belief** at stage $m$ is the conditional law of the current state given the history:
--
--   $$P_m(k)=\mathbb P^{p_1}_\sigma(K_m=k\mid H_m),\qquad k\in\mathcal K .$$
--
--   For a history $h$ of positive probability, `belief Γ p σ h` is $k\mapsto\mathbb P(H=h,K=k)/\mathbb P(H=h)$, where $H$ and $K$ are the history of length $|h|$ and the state that follows it. The support of a belief $p$ is $\{k: p(k)>0\}$. The module also defines $\mathbb P(H=h)$ and $\mathbb P(H=h,K=k)$.
--
--   **Formalization Note** The denominator is written $\sum_{k'}\mathbb P(H=h,K=k')$, which equals $\mathbb P(H=h)$. On histories of probability zero the conditional probability is undefined and the definition returns the initial belief; all statements about beliefs are almost-sure statements.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Definitions 5.1–5.2, p.13

import Mathlib
import Definitions.Def_FiniteMemPOMDP_lawOfPlays
import Definitions.Def_FiniteMemPOMDP_avgReward

open MeasureTheory

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [Fintype A] [Fintype S] [Nonempty A] [Nonempty S]

/-- The probability `P^p_σ(H_{n+1} = h)` that the history before stage `n + 1 = |h| + 1` is `h`. -/
noncomputable def historyProb (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A)
    (h : List (A × S)) : ℝ :=
  (lawOfPlays Γ p σ).real {ω | historyAt h.length ω = h}

/-- The probability `P^p_σ(H_{n+1} = h, K_{n+1} = k)`, with `n = |h|`. -/
noncomputable def jointProb (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A)
    (h : List (A × S)) (k : K) : ℝ :=
  (lawOfPlays Γ p σ).real {ω | historyAt h.length ω = h ∧ stateAt h.length ω = k}

/-- **The belief `P_m` after a history.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Definition 5.2, p.13: "Given a strategy σ ∈ Σ
and an initial belief p1, denote the belief at stage m by Pm, which is given by, for all k ∈ K,
Pm(k) := P^{p1}_σ(Km = k | Hm)." Definition 5.1: "Hm := ((A1, S1), (A2, S2), . . . ,
(Am−1, Sm−1))". "For p ∈ ∆(K), denote the support of p by supp(p), which is the set of k ∈ K
such that p(k) > 0."

`belief Γ p σ h` is the conditional law of the state `K_{|h|+1}` given the history `h`:
`k ↦ P(H = h, K = k) / ∑_{k'} P(H = h, K = k')`. The random belief of the paper is
`P_{n+1}(ω) = belief Γ p σ (historyAt n ω)`.

**Formalization Note** The denominator `∑_{k'} P(H = h, K = k')` equals `P(H = h)` (the events
`{K = k'}` partition the play space), so on every history of positive probability this is
exactly the paper's conditional probability. On a history of probability zero the conditional
probability is undefined; the definition then returns the initial belief `p` (a fixed element of
`∆(K)`); every statement about beliefs is an almost-sure statement, so this value never
matters. -/
noncomputable def belief (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A)
    (h : List (A × S)) : stdSimplex ℝ K :=
  if hpos : 0 < ∑ k, jointProb Γ p σ h k then
    ⟨fun k => jointProb Γ p σ h k / ∑ k', jointProb Γ p σ h k',
      fun k => div_nonneg measureReal_nonneg hpos.le,
      by rw [← Finset.sum_div, div_self hpos.ne']⟩
  else p

end FiniteMemPOMDP


