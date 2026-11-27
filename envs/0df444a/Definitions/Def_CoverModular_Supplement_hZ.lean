-- Prove2me | Definitions.Def_CoverModular_Supplement_hZ
-- name    : CoverModular_Supplement_hZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:15:23.149325+00:00
-- url     : https://prove2.me/theorems/37f1f965-101c-418b-b6b2-2ed9b5011c15
-- title:
--   Integer version $h_{\mathbb Z}(\mathcal A)$ of the LP-based set function
-- statement:
--   With the data of the LP-based set function $h$ of (17), the **integer version** adds the integrality constraint $x\in\mathbb Z^n_+$:
--
--   $$
--   h_{\mathbb Z}(\mathcal A)=\max_x\ \sum_{1\le j\le n}p_jx_j\quad\text{s.t.}\quad\sum_{1\le j\le n}a_{ij}x_j\le b_i\ (1\le i\le m),\qquad x_j=0\ (j\notin J(\mathcal A)),\qquad x_j\ge0,\qquad x\in\mathbb Z^n_+.
--   $$
--
--   The right-hand side $b$ is real and need not be integral. Theorem 2 extends the cover modularity of $h$ to $h_{\mathbb Z}$ when $A$ is totally unimodular.
--
--   **Formalization Note** A feasible point is a real vector, feasible for (17), whose coordinates are all integers. With $x\ge0$ this is $x\in\mathbb Z^n_+$. The maximum is the supremum of the objective values. The feasible set contains $x=0$ when $b\ge0$, and the set of values is bounded above whenever the LP (17) for the same $\mathcal A$ is bounded.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), Appendix A.3, proof of Theorem 2, p.43

import Mathlib
import Definitions.Def_CoverModular_Supplement_h

namespace CoverModular.Supplement

/-- The **integer version** `h_Z` of the LP-based set function (DeValve, Pekeč, Wei,
*Approximate submodularity in network design problems*, SSRN 3844987, Appendix A.3, proof of
Theorem 2, p.43): the program (17) with the additional constraint `x ∈ ℤⁿ₊`,
`h_Z(A) = max_x ∑_j p_j x_j` s.t. `∑_j a_ij x_j ≤ b_i`, `x_j = 0` (`j ∉ J(A)`), `x_j ≥ 0`,
`x ∈ ℤⁿ₊`.

**Formalization Note** Integrality is `∀ j, x_j ∈ range (ℤ → ℝ)`; together with `x ≥ 0` from
`Feasible` this is `x ∈ ℤⁿ₊`. The right-hand side `b` is real and need not be integral. The `max`
is `sSup` of the objective values; the feasible set contains `x = 0` when `b ≥ 0`, and the set is
bounded above whenever the LP (17) for the same `A` is. -/
noncomputable def hZ {U : Type*} [DecidableEq U] {m n : ℕ} (a : Fin m → Fin n → ℕ)
    (p : Fin n → ℝ) (b : Fin m → ℝ) (J : U → Finset (Fin n)) (A : Finset U) : ℝ :=
  sSup (objective p '' {x | Feasible a b J A x ∧ ∀ j, x j ∈ Set.range (Int.cast : ℤ → ℝ)})

end CoverModular.Supplement


