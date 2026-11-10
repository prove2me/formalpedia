-- Prove2me | Definitions.Def_TightCoreset2027_Euclidean_projectionModel
-- name    : TightCoreset2027_Euclidean_projectionModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:06:00.3102+00:00
-- url     : https://prove2.me/theorems/9188369e-9d80-45f3-9282-65c3de78df46
-- title:
--   Projection levels and the joint discrepancy specification
-- statement:
--   For positive integers $L,q$, a projection family comprises vectors $x_s\in\mathbb R^{2L}$, a finite set $V\subseteq\mathbb R^{2L}$, and level indices $\ell(s;v)\in\{0,\ldots,L\}$. The grid is $t_\ell=1-2\ell/L$. Its geometric specification requires distinct unit vectors $x_s$, nonempty $V$, squared norm $\|v\|^2=2$ for every $v\in V$, and
--
--   $$\langle x_s,v\rangle=t_{\ell(s;v)}\quad(s\in[q],\ v\in V).$$
--
--   The discrepancy specification says that for every positive integer $t$ and every family $A^{(1)},\ldots,A^{(t)}\in\mathbb R^q$, one direction $v\in V$ satisfies
--
--   $$\sum_{r=1}^t\left|\sum_{s=1}^q A_s^{(r)}(-1)^{\ell(s;v)}\right|\ge\frac1{\sqrt3}\sum_{r=1}^t\|A^{(r)}\|_2.$$
--
--   The raw family structure carries no proofs; its specification is the conjunction of these two predicates. Lemma 2.1 must produce a family satisfying it, before coefficients are chosen. This separates the existence problem from its subsequent uses.
--
--   **Formalization Note** Zero-based finite indices represent the source's finite index sets. The level is stored for all vectors, but constrained only on $V$; for $L\ge1$ the grid values are distinct, so this is exactly the source's determined index. A witnessing direction states the finite maximum lower bound equivalently, since $V$ is nonempty and finite.
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), Lemma 2.1 and Eq. (3)–(4), printed p. 10 / PDF p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Mathlib
open scoped BigOperators
set_option autoImplicit false

namespace TightCoreset2027.Euclidean

abbrev ProjectionSpace (L : ℕ) := EuclideanSpace ℝ (Fin (2 * L))

/-- Raw geometric data; none of the desired properties is built into its carrier. -/
structure ProjectionFamily (L q : ℕ) where
  x : Fin q → ProjectionSpace L
  directions : Finset (ProjectionSpace L)
  level : Fin q → ProjectionSpace L → Fin (L + 1)

noncomputable def gridValue (L : ℕ) (ℓ : Fin (L + 1)) : ℝ :=
  1 - 2 * (ℓ.val : ℝ) / (L : ℝ)

/-- The geometric clauses of Lemma 2.1. -/
def ProjectionGeometry {L q : ℕ} (G : ProjectionFamily L q) : Prop :=
  Function.Injective G.x ∧
  (∀ s, ‖G.x s‖ = 1) ∧
  G.directions.Nonempty ∧
  (∀ v ∈ G.directions, ‖v‖ ^ 2 = 2) ∧
  ∀ s v, v ∈ G.directions →
    inner ℝ (G.x s) v = gridValue L (G.level s v)

/-- An attained finite maximum, expressed by its witnessing direction. -/
def ProjectionDiscrepancy {L q : ℕ} (G : ProjectionFamily L q) : Prop :=
  ∀ t : ℕ, 1 ≤ t → ∀ A : Fin t → EuclideanSpace ℝ (Fin q),
    ∃ v ∈ G.directions,
      (1 / Real.sqrt 3) * (∑ r, ‖A r‖) ≤
        ∑ r, |∑ s, A r s * (-1 : ℝ) ^ (G.level s v).val|

/-- All output clauses of Lemma 2.1, used only after its existence assertion. -/
def ProjectionSpecification {L q : ℕ} (G : ProjectionFamily L q) : Prop :=
  ProjectionGeometry G ∧ ProjectionDiscrepancy G

end TightCoreset2027.Euclidean


