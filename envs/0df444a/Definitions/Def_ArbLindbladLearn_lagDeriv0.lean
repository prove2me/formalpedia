-- Prove2me | Definitions.Def_ArbLindbladLearn_lagDeriv0
-- name    : ArbLindbladLearn_lagDeriv0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:20:58.632605+00:00
-- url     : https://prove2.me/theorems/66b11b94-e016-44c7-a245-223e1f5b1f47
-- title:
--   Chebyshev–Lobatto nodes and endpoint-derivative weights $\ell_j'(0)$
-- statement:
--   For $q\in\mathbb N_{>0}$ and $T>0$, the Chebyshev–Lobatto nodes on $[0,T]$ are $t_j=\frac T2\big(1-\cos\frac{j\pi}{q}\big)$, $j=0,\dots,q$, so $t_0=0$ and $t_q=T$. The endpoint derivative of the degree-$q$ interpolant $p_q$ of $f$ is
--   $$p_q'(0)=\sum_{j=0}^q\ell_j'(0)f(t_j),\qquad \ell_j(t)=\prod_{0\le i\le q,\ i\ne j}\frac{t-t_i}{t_j-t_i}.$$
--   The module also defines the rule for complex $f$ and $W=\sum_{j=1}^q|\ell_j'(0)|$ (eq. (11)).
--
--   **Formalization Note** $\ell_j'(0)$ is defined as the derivative at $0$ of the product above.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Definition 2.10, p.15; §2.5, p.16; Lemma 2.5, eq. (11), p.17

import Mathlib

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

/-- The Chebyshev–Lobatto nodes mapped to `[0, T]` (Definition 2.10, p.15, and the display after it,
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.16): `t_j = (T/2)(1 − cos(jπ/q))`, `j = 0, …, q`, so `t₀ = 0` and
`t_q = T`. -/
def chebNode (q : ℕ) (T : ℝ) (j : ℕ) : ℝ := T / 2 * (1 - Real.cos (j * Real.pi / q))

/-- The endpoint weight `ℓ′_j(0)`, the derivative at `0` of the `j`th Lagrange basis polynomial
`ℓ_j(t) = Π_{0≤i≤q, i≠j} (t − t_i)/(t_j − t_i)` on the nodes `chebNode q T` (§2.5, p.16). -/
def lagDeriv0 (q : ℕ) (T : ℝ) (j : ℕ) : ℝ :=
  deriv (fun t : ℝ => ∏ i ∈ (Finset.range (q + 1)).erase j,
    (t - chebNode q T i) / (chebNode q T j - chebNode q T i)) 0

/-- The endpoint-derivative rule `p′_q(0) = Σ_{j=0}^q ℓ′_j(0) f(t_j)` of the degree-`q` interpolant
of a real function `f` at the nodes `chebNode q T` (§2.5, p.16). -/
def endpointRule (q : ℕ) (T : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (q + 1), lagDeriv0 q T j * f (chebNode q T j)

/-- The same rule for a complex-valued function (Lemma 2.4, second sentence, p.16). -/
def endpointRuleC (q : ℕ) (T : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (q + 1), (lagDeriv0 q T j : ℂ) * f (chebNode q T j)

/-- The endpoint weight sum `W = Σ_{j=1}^q |ℓ′_j(0)|` (Lemma 2.5, eq. (11), p.17). -/
def chebW (q : ℕ) (T : ℝ) : ℝ := ∑ j ∈ Finset.Icc 1 q, |lagDeriv0 q T j|

end ArbLindbladLearn


