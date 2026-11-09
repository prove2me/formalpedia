-- Prove2me | Definitions.Def_MaxCutSample2027_Coreset_model
-- name    : MaxCutSample2027_Coreset_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:38:43.204213+00:00
-- url     : https://prove2.me/theorems/1688affc-5b99-4795-a8e3-82fe3f12ff79
-- title:
--   Reweighted sampled graph, normalized kernel, and exact H
-- statement:
--   Let $V$ be finite, $n=|V|$, $A:V\times V\to\mathbb R$, and $p:V\to\mathbb R$. For a sample $x:\operatorname{Fin}(k)\to V$, define
--   $$\widehat A_{ij}(x)=\frac{A_{x_i x_j}}{k^2p_{x_i}p_{x_j}},\qquad
--   K_{uv}=\frac{A_{uv}}{n^2p_up_v},\qquad
--   H=\sum_{v\in V}p_v\sqrt{\sum_{u\in V}p_uK_{uv}^2}.$$
--   The weighted degree is $d(v)=\sum_u A_{vu}$ and the total weighted degree is $D=\sum_v d(v)$. The sampled graph is indexed by $\operatorname{Fin}(k)$, so repeated draws remain distinct vertices. In every use below, $A$ is admissible, $p$ is a positive probability vector, $V$ is nonempty, and $k\ge1$. These conditions make every displayed denominator positive and every square-root input nonnegative.
--
--   This model records the exact reweighting and error parameter of Theorem 2.1. No bound $A_{uv}\le1$, degree lower bound on $p$, or assumption $d(v)>0$ is built into it. Values outside the stated domain use Lean's total division and square root; none is used to assert a source theorem.
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), §2, equation (2.1), definition of H and weighted degrees, p. 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Definitions.Def_MaxCutSample2027_Coreset_cuts
import Definitions.Def_MaxCutSample2027_Coreset_averages
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset

/-- Weighted degree; strict positivity is deliberately not required. -/
def weightedDegree {V : Type*} [Fintype V] (A : V → V → ℝ) (v : V) : ℝ :=
  ∑ u, A v u

/-- Total weighted degree, D = ∑ v, d(v), in the section setup. -/
def totalDegree {V : Type*} [Fintype V] (A : V → V → ℝ) : ℝ :=
  ∑ v, weightedDegree A v

/-- Equation (2.1): repeated samples remain distinct vertices of Fin k. -/
def Ahat {V : Type*} {k : ℕ} (A : V → V → ℝ) (p : V → ℝ)
    (x : Fin k → V) (i j : Fin k) : ℝ :=
  A (x i) (x j) / ((k : ℝ) ^ 2 * p (x i) * p (x j))

/-- Equation (2.1): the kernel normalized by n² and the sampling weights. -/
def K {V : Type*} [Fintype V] (A : V → V → ℝ) (p : V → ℝ) (u v : V) : ℝ :=
  A u v / ((Fintype.card V : ℝ) ^ 2 * p u * p v)

/-- The exact column second-moment quantity on source p.6. -/
def H {V : Type*} [Fintype V] (A : V → V → ℝ) (p : V → ℝ) : ℝ :=
  ∑ v, p v * Real.sqrt (∑ u, p u * (K A p u v) ^ 2)

end MaxCutSample2027.Coreset


