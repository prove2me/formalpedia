-- Prove2me | Definitions.Def_LoadBalMatch_Main_Sampling
-- name    : LoadBalMatch_Main_Sampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:31:47.073454+00:00
-- url     : https://prove2.me/theorems/cbdb25be-a806-4298-8f50-3b4440867e40
-- title:
--   Independent sampling of edges: the law of $R\subseteq E$ (Lemma 8.1, Algorithm 4 line (2c))
-- statement:
--   Let $G$ be a graph with edge set $E$ and let $q_e\in[0,1]$ for $e\in E$. A random set $R\subseteq E$ **includes each edge $e$ independently with probability $q_e$** when
--   $$\Pr[R=S]=\prod_{e\in S}q_e\prod_{e\in E\setminus S}(1-q_e)\qquad(S\subseteq E),$$
--   and the probability of an event $\mathcal A$ is $\sum_{S\subseteq E,\,S\in\mathcal A}\Pr[R=S]$.
--
--   This is the sampling of Lemma 8.1 and of line (2c) of Algorithm 4 (with $q_e=\min\{1,p_e\}$).
--
--   **Formalization Note.** `sampleProb G q R` is the product above for `R ⊆ E` and `0` for any other finite set of pairs; `sampleEventProb G q A` sums it over the finite sets `R` satisfying `A`.
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 44, Lemma 8.1; p. 46, Algorithm 4 line (2c)

import Mathlib

/-!
# Independent edge sampling: the law of `R ⊆ E`

Assadi, Bernstein, Wrzos-Kaminska, STOC 2027 submission (sha256 7cd28a8b…), Lemma 8.1, p. 44:
"For each e ∈ E, let p_e ∈ [0, 1]. Let R ⊆ E be obtained by including each edge e independently
with probability p_e." Algorithm 4 line (2c), p. 46: "Sample each edge e ∈ E independently with
probability min{1, p_e}."

`sampleProb G q R` is the probability that the sample equals `R`:
`Π_{e∈E} (q_e if e ∈ R, 1 − q_e otherwise)` for `R ⊆ E`, and `0` otherwise.
`sampleEventProb G q A` is the probability of the event `A` (a finite sum).
-/

namespace LoadBalMatch.Main

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The probability that independent sampling of the edges of `G` with probabilities `q` returns
exactly `R`. -/
noncomputable def sampleProb (G : SimpleGraph V) (q : Sym2 V → ℝ) (R : Finset (Sym2 V)) : ℝ := by
  classical
  exact if ∀ e ∈ R, e ∈ G.edgeSet then
    ∏ e ∈ (Finset.univ : Finset (Sym2 V)).filter (· ∈ G.edgeSet),
      (if e ∈ R then q e else 1 - q e)
  else 0

/-- The probability of the event `A` under independent sampling of the edges of `G` with
probabilities `q`. -/
noncomputable def sampleEventProb (G : SimpleGraph V) (q : Sym2 V → ℝ)
    (A : Finset (Sym2 V) → Prop) : ℝ := by
  classical
  exact ∑ R, if A R then sampleProb G q R else 0

end LoadBalMatch.Main


