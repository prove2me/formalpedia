-- Prove2me | Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
-- name    : ThreeOpSplitting_Convergence_WeakConvergence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:46:40.382732+00:00
-- url     : https://prove2.me/theorems/2a782905-f28b-4b25-94f0-3ad72bd6e00e
-- title:
--   Weak convergence of a sequence in a real Hilbert space
-- statement:
--   Let $H$ be a real inner product space. A sequence $(u_k)_{k \ge 0}$ in $H$ **converges weakly** to $x \in H$, written $u_k \rightharpoonup x$, if
--   $$\lim_{k \to \infty} \langle u_k, y\rangle = \langle x, y\rangle \quad \text{for every } y \in H.$$
--
--   Weak convergence is the mode in which the iterates of the three-operator splitting converge in general (Corollary 2.1 and Theorem 2.1, Part 1); strong (norm) convergence requires the extra hypotheses of Theorem 2.1, Part 2.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, pp. 834-835, Corollary 2.1 and Theorem 2.1 (notation ⇀)

import Mathlib

open InnerProductSpace Filter Topology

namespace ThreeOpSplitting.Convergence

/-- Weak convergence `u k ⇀ x` in a real inner product space:
`⟪u k, y⟫ → ⟪x, y⟫` for every `y`. -/
def WeakTendsto {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℕ → H) (x : H) : Prop :=
  ∀ y : H, Tendsto (fun k => ⟪u k, y⟫_ℝ) atTop (𝓝 ⟪x, y⟫_ℝ)

end ThreeOpSplitting.Convergence


