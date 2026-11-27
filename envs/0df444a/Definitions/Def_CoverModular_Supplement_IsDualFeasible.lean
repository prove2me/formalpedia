-- Prove2me | Definitions.Def_CoverModular_Supplement_IsDualFeasible
-- name    : CoverModular_Supplement_IsDualFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:16:32.311687+00:00
-- url     : https://prove2.me/theorems/3bc5a0ad-84fe-4120-9fc6-3ea5633a6cbb
-- title:
--   Feasible solution of the dual (28) of the LP (17)
-- statement:
--   The dual of the LP (17) for the set $\mathcal A$ is
--
--   $$
--   \min_\alpha\ \sum_ib_i\alpha_i\quad\text{s.t.}\quad\sum_ia_{ij}\alpha_i\ge p_j\ (j\in J(\mathcal A)),\qquad\alpha_i\ge0\ \ \forall i.\tag{28}
--   $$
--
--   A vector $\alpha\in\mathbb R^m$ is a **feasible dual solution** if it satisfies these constraints. By weak duality, $\sum_ib_i\alpha_i$ then bounds $h(\mathcal A)$ from above. Lemma 3 builds such a solution for $\mathcal A=\mathcal S\cup\mathcal T$.
--
--   **Formalization Note** Feasibility does not involve $b$, so the definition does not take $b$ as an argument.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), Appendix A.3, display (28), p.40

import Mathlib
import Definitions.Def_CoverModular_Supplement_h

namespace CoverModular.Supplement

/-- `α` is a **feasible solution of the dual (28)** of the LP (17) for the set `A` (DeValve,
Pekeč, Wei, SSRN 3844987, Appendix A.3, display (28), p.40):
`min_α ∑_i b_i α_i` s.t. `∑_i a_ij α_i ≥ p_j` for `j ∈ J(A)`, `α_i ≥ 0` for all `i`.
Feasibility does not involve `b`. -/
def IsDualFeasible {U : Type*} [DecidableEq U] {m n : ℕ} (a : Fin m → Fin n → ℕ)
    (p : Fin n → ℝ) (J : U → Finset (Fin n)) (A : Finset U) (α : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ α i) ∧ ∀ j ∈ jUnion J A, p j ≤ ∑ i, (a i j : ℝ) * α i

end CoverModular.Supplement


