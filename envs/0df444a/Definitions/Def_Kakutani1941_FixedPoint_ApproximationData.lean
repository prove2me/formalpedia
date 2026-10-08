-- Prove2me | Definitions.Def_Kakutani1941_FixedPoint_ApproximationData
-- name    : Kakutani1941_FixedPoint_ApproximationData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:02:58.635293+00:00
-- url     : https://prove2.me/theorems/e704405e-93dc-40c2-a0f7-3ba120b58eaa
-- title:
--   Proof of Theorem 1 — finite barycentric approximation data
-- statement:
--   For a set $S$, a point-to-set mapping $\Phi$, an integer $r\ge0$, and an error $\varepsilon$, approximation data consist of a point $x\in S$, points $x_0,\ldots,x_r\in S$ within $\varepsilon$ of $x$, selections $y_i\in\Phi(x_i)$, and nonnegative weights $\lambda_i$ with sum one such that
--
--   $$x=\sum_{i=0}^{r}\lambda_i x_i=\sum_{i=0}^{r}\lambda_i y_i,\qquad \|x_i-x\|\le\varepsilon.$$
--
--   These are the finite data extracted from a cell of the barycentric subdivision in Kakutani's proof. They isolate the part of the approximation that the subsequent limit argument uses.
--
--   **Formalization Note** The weights form Mathlib's standard simplex on $r+1$ indices. The definition can hold or fail for any real $\varepsilon$; the theorem that produces the data assumes $\varepsilon>0$.
-- source:
--   Kakutani, A generalization of Brouwer's fixed point theorem, Duke Math. J. 8 (1941), pp. 457–458, proof of Theorem 1, https://doi.org/10.1215/s0012-7094-41-00838-4

import Mathlib

namespace Kakutani1941.FixedPoint

/-- Finite barycentric data extracted from one small cell of a subdivision. -/
def ApproximationData {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (Φ : E → Set E) (r : ℕ) (ε : ℝ) : Prop :=
  ∃ (x : E) (xs ys : Fin (r + 1) → E) (w : Fin (r + 1) → ℝ),
    x ∈ S ∧ (∀ i, xs i ∈ S ∧ dist (xs i) x ≤ ε) ∧
    (∀ i, ys i ∈ Φ (xs i)) ∧ w ∈ stdSimplex ℝ (Fin (r + 1)) ∧
    x = ∑ i, (w i) • xs i ∧ x = ∑ i, (w i) • ys i

end Kakutani1941.FixedPoint


