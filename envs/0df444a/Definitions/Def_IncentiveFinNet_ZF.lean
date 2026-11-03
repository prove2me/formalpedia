-- Prove2me | Definitions.Def_IncentiveFinNet_ZF
-- name    : IncentiveFinNet_ZF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:02.427532+00:00
-- url     : https://prove2.me/theorems/dc0e2d8d-8389-402b-88e1-5d0e30727181
-- title:
--   The permitted pairs $F$, the vectors $\mathrm{uvec}(X)_F$, the matrix $A$, and the matrix $Z_F$ of Theorem 1
-- statement:
--   Fix a network setting with permitted sets $J_i$, expected-return matrix $M$ and matrices $Q_i$.
--
--   1. **Permitted pairs.** $F = \{(i,j) : 1 \le i < j \le n,\ \Psi_i e_j \neq 0\}$ is the set of pairs $i < j$ with $j \in J_i$, i.e. the entries $P_{ij}$ above the diagonal that may be nonzero.
--   2. **Restricted vectorization.** For an $n\times n$ matrix $X$, $\mathrm{uvec}(X)_F \in \mathbb R^{|F|}$ is the vector of the entries $X_{ij}$, $(i,j) \in F$.
--   3. **The matrix $A$.** $A_{ij} = e_i^{\top} Q_j M e_j$.
--   4. **The matrix $Z_F$.** $Z_F$ is the $|F| \times |F|$ matrix whose row indexed by $(i,j) \in F$ is $\mathrm{uvec}(C_{(i,j)})_F$, where $C_{(i,j)}$ is built from the $Q_i$ as in Theorem 1.
--
--   Theorem 1 states that stable points exist exactly when the linear system $Z_F\,p = \mathrm{uvec}(A - A^{\top})_F$ is solvable, and that the prices of a stable point solve it.
--
--   **Formalization Note** $F$ is the subtype of pairs $(i,j) \in$ `Fin n × Fin n` with $i < j$ and $j \in J_i$ (the condition $\Psi_ie_j \ne 0$). Vectors in $\mathbb R^{|F|}$ are functions on $F$, and $Z_F$ is a matrix indexed by $F \times F$, so the paper's order on $F$ plays no role. The module defines `PermittedPairs`, `uvecF`, `matA` and `ZF`.
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, §2.1, F and uvec(X)_F p.11, Theorem 1 (A, Z_F) pp.11–12; repeated in A.1, p.33

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_matC
import Definitions.Def_IncentiveFinNet_Q

open Matrix

namespace IncentiveFinNet

variable {n : ℕ}

/-- `F = {(i, j) : 1 ≤ i < j ≤ n, Ψ_i e_j ≠ 0}`, the ordered pairs `i < j` where `P_ij` is allowed
to be non-zero, arXiv:2212.06808v3, p.11.

**Formalization Note** `Ψ_i e_j ≠ 0` is `j ∈ J_i`. `F` is a subtype of `Fin n × Fin n`; vectors
indexed by `F` replace the paper's vectors in `ℝ^{|F|}` listed in the order of `F`. -/
abbrev PermittedPairs (S : NetworkSetting n) : Type :=
  {p : Fin n × Fin n // p.1 < p.2 ∧ p.2 ∈ S.J p.1}

/-- `uvec(X)_F ∈ ℝ^{|F|}`, the vector of entries `{X_ij | (i, j) ∈ F}`, arXiv:2212.06808v3, p.11. -/
def uvecF (S : NetworkSetting n) (X : Matrix (Fin n) (Fin n) ℝ) : PermittedPairs S → ℝ :=
  fun p => X p.1.1 p.1.2

/-- The matrix `A` of Theorem 1, `A_ij = e_iᵀ Q_j M e_j`, arXiv:2212.06808v3, p.11. -/
noncomputable def matA (S : NetworkSetting n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Pi.single i (1 : ℝ) ⬝ᵥ ((Q S j * S.M) *ᵥ Pi.single j 1)

/-- The `|F| × |F|` matrix `Z_F` of Theorem 1, arXiv:2212.06808v3, p.12: its rows are
`uvec(C_{(i,j)})_F` for `(i, j) ∈ F`, with `C_{(i,j)}` built from the setting's `Q_i`.

**Formalization Note** The row index `r = (i, j)` names the pair, so `Z_F r c = C_{(i,j)}` at the
pair `c`. -/
noncomputable def ZF (S : NetworkSetting n) : Matrix (PermittedPairs S) (PermittedPairs S) ℝ :=
  Matrix.of fun r c => uvecF S (matC (Q S) r.1.1 r.1.2) c

end IncentiveFinNet


