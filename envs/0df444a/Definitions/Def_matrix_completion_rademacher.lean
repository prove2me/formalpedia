-- Prove2me | Definitions.Def_matrix_completion_rademacher
-- name    : matrix_completion_rademacher
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-13T22:56:51.185434+00:00
-- url     : https://prove2.me/theorems/281b1608-5653-426a-857b-84716c07be53
-- statement:
--   This definition module provides Rademacher symmetrization objects and conditional Khintchine-style moment predicates.
--
--   $$
--   \sum_{(i,j)\in\Omega}\varepsilon_{ij}A_{ij}
--   \quad\text{with independent Rademacher signs }\varepsilon_{ij}.
--   $$
--
--   Module overview: Rademacher signs used in the symmetrization step of Section 6.1. The paper introduces an independent sign sequence $\varepsilon_{ab}$ after symmetrizing $p^{-1}(P_\Omega - pI)X$. We encode a sign realization by the finset of coordinates where the sign is +1; all other coordinates have sign -1.
--
--   Documented declarations:
--   1. Uniform probability weight on all Rademacher sign assignments.
--   2. Expectation over independent Rademacher signs on matrix coordinates.
--   3. The sign $\varepsilon_{ij}$, encoded by membership in a sign-realization finset.
--   4. The symmetrized sampled matrix $p^{-1} \sum \varepsilon_{ij} \delta_{ij} X_{ij} e_{i} e_{j}^\,$ from Section 6.1.
--   5. Conditional Khintchine variance scale for the coordinate Rademacher series: $p^{-1}$ times the square root of the larger sampled row/column energy.
--
--   Role in the mission. Key declarations include rademacherObservationWeight, rademacherExpectation, rademacherSign, rademacherSampledMatrix, rademacherSampledVarianceScale. These definitions provide shared vocabulary for the Exact Matrix Completion decomposition, so theorem statements can refer to sampling models, recovery events, tangent-space geometry, and concentration estimates without restating the infrastructure each time.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_schatten

/-!
Rademacher signs used in the symmetrization step of Section 6.1.

The paper introduces an independent sign sequence `ε_ab` after symmetrizing
`p^{-1}(P_Omega - pI)X`.  We encode a sign realization by the finset of
coordinates where the sign is `+1`; all other coordinates have sign `-1`.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Uniform probability weight on all Rademacher sign assignments. -/
noncomputable def rademacherObservationWeight {n1 n2 : Nat}
    (_eps : Finset (Fin n1 × Fin n2)) : Real :=
  ((1 : Real) / 2) ^ Fintype.card (Fin n1 × Fin n2)

/-- Expectation over independent Rademacher signs on matrix coordinates. -/
noncomputable def rademacherExpectation {n1 n2 : Nat}
    (F : Finset (Fin n1 × Fin n2) → Real) : Real :=
  ∑ eps : Finset (Fin n1 × Fin n2),
    rademacherObservationWeight eps * F eps

/-- The sign `ε_ij`, encoded by membership in a sign-realization finset. -/
def rademacherSign {n1 n2 : Nat}
    (eps : Finset (Fin n1 × Fin n2)) (i : Fin n1) (j : Fin n2) :
    Real :=
  if (i, j) ∈ eps then 1 else -1

/-- The symmetrized sampled matrix
`p^{-1} ∑ ε_ij δ_ij X_ij e_i e_j^*` from Section 6.1. -/
noncomputable def rademacherSampledMatrix {n1 n2 : Nat}
    (Omega eps : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  fun i j =>
    p⁻¹ * if (i, j) ∈ Omega then rademacherSign eps i j * X i j else 0

/-- Conditional Khintchine variance scale for the coordinate Rademacher series:
`p^{-1}` times the square root of the larger sampled row/column energy. -/
noncomputable def rademacherSampledVarianceScale {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) : Real :=
  p⁻¹ * Real.sqrt
    (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X))

end MatrixCompletion


