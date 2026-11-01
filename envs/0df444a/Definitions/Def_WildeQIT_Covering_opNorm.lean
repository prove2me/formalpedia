-- Prove2me | Definitions.Def_WildeQIT_Covering_opNorm
-- name    : WildeQIT_Covering_opNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:50.846995+00:00
-- url     : https://prove2.me/theorems/22896168-c7ca-48a5-9e97-44174cefefb8
-- title:
--   Operator norm $\|M\|_\infty$ (largest singular value)
-- statement:
--   For a matrix $M$ acting from $\mathbb C^n$ to $\mathbb C^m$ with their Euclidean norms, the **operator norm** (Schatten $\infty$-norm)
--
--   $$\|M\|_\infty=\sup_{\|v\|_2\le1}\|Mv\|_2$$
--
--   is the largest singular value of $M$. It appears on the right side of the Bernstein trick (17.23).
--
--   **Formalization Note** Mathlib's $\ell^2$-operator norm on matrices, wrapped in a definition so that no global norm instance on matrices is introduced.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 17.3.3, eq. (17.23), p. 509

import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Lemma 17.3.3, eq. (17.23),
p. 509 (the operator norm `‖·‖_∞`).
-/

open scoped Matrix.Norms.L2Operator

namespace WildeQIT.Covering

/-- **Operator norm** `‖M‖_∞` (Wilde, arXiv:1106.1445v8, eq. (17.23), p. 509): the largest
singular value of `M`, that is, the norm of `M` as an operator between the Euclidean spaces
`ℂⁿ → ℂᵐ`.

**Formalization Note.** Mathlib's `ℓ²`-operator norm on matrices (`Matrix.Norms.L2Operator`),
used here through a definition so that no norm instance on matrices is introduced globally. -/
noncomputable def opNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) : ℝ :=
  ‖M‖

end WildeQIT.Covering


