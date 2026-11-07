-- Prove2me | Definitions.Def_VertexSampleCSP_DeltaS
-- name    : VertexSampleCSP_DeltaS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:44.364314+00:00
-- url     : https://prove2.me/theorems/a905d213-aaf2-4fca-b417-2de9ba1fe451
-- title:
--   The product of simplices $\Delta_S\subseteq\mathbb R^{V\times[q]}$
-- statement:
--   Index the coordinates of $\mathbb R^{V\times[q]}$ by pairs $(i,a)$, and let $x_i\in\mathbb R^q$ be the $i$th block of $x$. With $\Delta_q=\mathrm{conv}\{e_a:a\in[q]\}$, for $S\subseteq V$,
--
--   $$\Delta_S=\{x\in\mathbb R^{V\times[q]}:x_i\in\Delta_q\text{ for }i\in S,\ x_i=0\text{ for }i\notin S\},\qquad\Delta=\Delta_V.$$
--
--   This is the feasible region of the relaxation of the instance restricted to $S$.
--
--   **Formalization Note** $\Delta_q$ is written by its coordinates: nonnegative entries summing to $1$.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "The encoding", p.13 (PDF p.15)

import Mathlib

namespace VertexSampleCSP

/-- **The product of simplices `Δ_S`.** Chang, *Optimal Vertex Sampling for Constraint Satisfaction
Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "The encoding", p.13
(PDF p.15): "Index the coordinates of ℝ^{V×[q]} by pairs (i, a) ∈ V × [q] … for x ∈ ℝ^{V×[q]} let
xi ∈ ℝ^q be its ith block. Let ∆q = conv{ea : a ∈ [q]} ⊆ ℝ^q, and for S ⊆ V let
∆S = {x ∈ ℝ^{V×[q]} : xi ∈ ∆q for i ∈ S, xi = 0 for i ∉ S}, ∆ = ∆V."

`DeltaS V q S` is the set of vectors `x` of the Euclidean space `ℝ^{V × [q]}` whose block
`x_i = (x(i, a))_{a ∈ [q]}` is a probability vector for `i ∈ S` and is zero for `i ∉ S`. The set
`Δ = Δ_V` is `DeltaS V q Finset.univ`.

**Formalization Note.** The simplex `Δ_q = conv{e_a}` is written by its coordinates: nonnegative
entries summing to `1`. These are the same set. -/
def DeltaS (V : Type*) [Fintype V] (q : ℕ) (S : Finset V) : Set (EuclideanSpace ℝ (V × Fin q)) :=
  {x | (∀ i ∈ S, (∀ a, 0 ≤ x (i, a)) ∧ ∑ a, x (i, a) = 1) ∧ ∀ i ∉ S, ∀ a, x (i, a) = 0}

end VertexSampleCSP


