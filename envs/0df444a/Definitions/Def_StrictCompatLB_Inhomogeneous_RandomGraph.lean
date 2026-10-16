-- Prove2me | Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph
-- name    : StrictCompatLB_Inhomogeneous_RandomGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:19.118981+00:00
-- url     : https://prove2.me/theorems/7f6dc893-a0e9-434b-bd83-1587ccd04066
-- title:
--   Inhomogeneous random bipartite graphs: Bernoulli($p_w(N)$) edges, $\bar p(N)$ and $\|p(N)^{-1}\|_2^{-2}$
-- statement:
--   Fix the number $M(N)$ of dispatchers and edge probabilities $p_w(N) \in (0, 1]$ for $w \in W_N$. The **inhomogeneous random bipartite graph** $G_N$ on $V_N \times W_N$ ($|V_N| = N$, $|W_N| = M(N)$) contains each pair $(v, w)$ as an edge independently with probability $p_w(N)$, which depends only on the dispatcher. Its adjacency matrix $x \in \{0, 1\}^{V_N \times W_N}$ therefore has the product law
--   $$\mathbb P_N = \bigotimes_{(v, w) \in V_N \times W_N} \mathrm{Bernoulli}\bigl(p_w(N)\bigr),$$
--   and $E_N = \{(v, w) : x_{vw} = 1\}$.
--
--   Two summaries of the edge probabilities appear in the hypotheses:
--   $$\bar p(N) = \min_{w \in W_N} p_w(N), \qquad \|p(N)^{-1}\|_2^{-2} = \Bigl( \sum_{w \in W_N} \frac{1}{p_w(N)^2} \Bigr)^{-1}.$$
--
--   In expectation a dispatcher $w$ is compatible with $N p_w(N)$ servers, so $p_w(N)$ sets the level of flexibility of task type $w$; the two summaries control the least flexible dispatcher and the spread of flexibilities.
--
--   **Formalization Note** The Bernoulli law is Mathlib's `bernoulliMeasure true false q` on `Bool` (`true` = edge present). Its argument is projected onto $[0, 1]$ so the definition is total; it is only applied with $0 < p_w(N) \le 1$, where it is exactly Bernoulli$(p_w(N))$. The minimum $\bar p(N)$ is written as an infimum over the finite set `Fin (M N)`; it is the minimum when $M(N) \ge 1$, which every theorem assumes.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 14, Theorem 3.6 (construction of G_N), p. 35 (definition of p̄(N)), p. 37, Lemma B.2 (∥p(N)^{−1}∥_2^{−2})

import Mathlib

namespace StrictCompatLB.Inhomogeneous

open MeasureTheory Finset

/-- The Bernoulli law on `Bool` with success probability `q` (`true` = "edge present"): mass `q`
on `true` and `1 - q` on `false` (Mathlib's `ProbabilityTheory.bernoulliMeasure`). The argument is
projected onto `[0, 1]` so that the definition is total; it is only used with `0 < q ≤ 1`, where
it is exactly Bernoulli(`q`). -/
noncomputable def bernoulliEdge (q : ℝ) : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false (Set.projIcc (0 : ℝ) 1 zero_le_one q)

/-- The law of the adjacency matrix of the `N`-th inhomogeneous random bipartite graph of
Theorem 3.6: each pair `(v, w) ∈ V_N × W_N`, with `V_N = Fin N` and `W_N = Fin (M N)`, is an edge
independently with probability `p N w = p_w(N)`. It is the product over all pairs of the Bernoulli
laws `Bernoulli(p_w(N))`. -/
noncomputable def edgeLaw (M : ℕ → ℕ) (p : (N : ℕ) → Fin (M N) → ℝ) (N : ℕ) :
    Measure (Fin N × Fin (M N) → Bool) :=
  Measure.pi fun e : Fin N × Fin (M N) => bernoulliEdge (p N e.2)

/-- The edge set `E_N = {(v, w) | x (v, w) = true}` of the bipartite graph with adjacency
matrix `x`. -/
def graphOf {N m : ℕ} (x : Fin N × Fin m → Bool) : Finset (Fin N × Fin m) :=
  univ.filter fun e => x e = true

/-- `p̄(N) = min_{w ∈ W_N} p_w(N)` (Appendix B, p. 35). Written as an infimum over the finite type
`Fin (M N)`; it is the minimum whenever `M N > 0` (on the empty type it would be the junk value
`0`, which the theorems exclude by assuming `0 < M N`). -/
noncomputable def minEdgeProb (M : ℕ → ℕ) (p : (N : ℕ) → Fin (M N) → ℝ) (N : ℕ) : ℝ :=
  ⨅ w : Fin (M N), p N w

/-- `‖p(N)⁻¹‖₂⁻² = (Σ_{w ∈ W_N} p_w(N)⁻²)⁻¹` (Lemma B.2, p. 37), the inverse squared Euclidean norm
of the vector of reciprocal edge probabilities. -/
noncomputable def invNormSq (M : ℕ → ℕ) (p : (N : ℕ) → Fin (M N) → ℝ) (N : ℕ) : ℝ :=
  (∑ w : Fin (M N), (p N w)⁻¹ ^ 2)⁻¹

end StrictCompatLB.Inhomogeneous


