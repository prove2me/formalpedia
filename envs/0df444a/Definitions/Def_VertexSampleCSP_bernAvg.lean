-- Prove2me | Definitions.Def_VertexSampleCSP_bernAvg
-- name    : VertexSampleCSP_bernAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:27.066428+00:00
-- url     : https://prove2.me/theorems/01ba8df1-fcac-40f0-bad7-935457c2e0f5
-- title:
--   Expectation over a Bernoulli($\rho$) random subset
-- statement:
--   If $S\subseteq V$ contains every element independently with probability $\rho$, the expectation of $X(S)$ is
--
--   $$\sum_{S\subseteq V}\rho^{|S|}(1-\rho)^{|V|-|S|}X(S).$$
--
--   For $\rho\in[0,1]$ the weights form a probability distribution on the subsets of $V$.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma C.1(a), p.16 (PDF p.18); Proposition C.2(a), p.16; Lemma C.3 and Theorem C.4(b), p.17 (PDF p.19)

import Mathlib

namespace VertexSampleCSP

/-- **Expectation over a Bernoulli(`ρ`) subset.** Chang, *Optimal Vertex Sampling for Constraint
Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma C.1(a),
Proposition C.2(a), Lemma C.3 and Theorem C.4(b), pp.16–17: "S contains every variable independently
with probability ρ".

`bernAvg ρ X = Σ_{S ⊆ V} ρ^{|S|} (1 − ρ)^{|V| − |S|} X(S)`, the expectation of `X(S)` for that random
subset `S`. For `ρ ∈ [0, 1]` the weights are a probability distribution on the subsets of `V`. -/
noncomputable def bernAvg {V : Type*} [Fintype V] (ρ : ℝ) (X : Finset V → ℝ) : ℝ :=
  ∑ S : Finset V, ρ ^ S.card * (1 - ρ) ^ (Fintype.card V - S.card) * X S

end VertexSampleCSP


