-- Prove2me | Definitions.Def_VecBalPoly_IsClean
-- name    : VecBalPoly_IsClean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:11:58.766213+00:00
-- url     : https://prove2.me/theorems/7f13403e-fc9f-4d2b-b526-c766d30e1d10
-- title:
--   States after cleanup
-- statement:
--   A state is **clean** when
--   1. $x\in[-1,1]^n$ and $V=\{j:|x_j|<1\}$;
--   2. $T_i\subseteq V$ for every row $i$;
--   3. the spreading condition (2.2) holds: $a_{ij}^2\le q_i/K$ for all $j\in T_i$;
--   4. the scale condition (2.3) holds on every medium row: $q_i\le r_i^2<4q_i$ and $r_i\le K$;
--   5. every column of $A$ has Euclidean norm at most $1$.
--
--   These are the properties of the states after cleanup in Algorithm 2.2 that the analysis of Section 4 and Appendices C and D uses.
--
--   **Formalization Note** Statements over clean states are more general than statements over states reached by the algorithm.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), §2.1, (2.2), p.4 (PDF p.5); (2.3), p.4; §2.4, p.5

import Mathlib
import Definitions.Def_VecBalPoly_q

namespace VecBalPoly

variable {m n : ℕ}

/-- **A state after cleanup.** The structural conditions that hold after every cleanup of
Algorithm 2.2 and that the analysis of Sections 4 and Appendices C–D uses:
1. `x ∈ [−1, 1]ⁿ` and `V = {j : |xⱼ| < 1}`;
2. `Tᵢ ⊆ V` for every row;
3. the spreading condition (2.2): `a²ᵢⱼ ≤ qᵢ/K` for all `j ∈ Tᵢ`;
4. the scale condition (2.3) on every medium row: `qᵢ ≤ rᵢ² < 4qᵢ`, `rᵢ ≤ K`;
5. every column of `A` has Euclidean norm at most `1`.

Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), §2.1, pp.3–4 (PDF pp.4–5), (2.2); §2.2, (2.3), p.4; §2.4, p.5; Theorem 1.1, p.1.

**Formalization Note** The paper's "state after cleanup" (Lemmas 2.1, 4.1, 4.2, C.1, D.1,
Proposition 4.5) is a state reached by the algorithm. This predicate is the list of properties
of such states that those proofs use, so statements over it are more general. Column norms are
written `∑ᵢ A i j ² ≤ 1`. -/
def IsClean (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) : Prop :=
  (∀ j, |st.x j| ≤ 1) ∧
  st.V = Finset.univ.filter (fun j => |st.x j| < 1) ∧
  (∀ i, st.T i ⊆ st.V) ∧
  (∀ i, ∀ j ∈ st.T i, A i j ^ 2 ≤ q A st i / K) ∧
  (∀ i, IsMedium A st i →
    q A st i ≤ st.r i ^ 2 ∧ st.r i ^ 2 < 4 * q A st i ∧ st.r i ≤ K) ∧
  (∀ j, ∑ i, A i j ^ 2 ≤ 1)

end VecBalPoly


