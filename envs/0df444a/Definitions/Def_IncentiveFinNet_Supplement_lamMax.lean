-- Prove2me | Definitions.Def_IncentiveFinNet_Supplement_lamMax
-- name    : IncentiveFinNet_Supplement_lamMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:30:24.497505+00:00
-- url     : https://prove2.me/theorems/b7f70f04-c01c-4fc9-be06-58373c0b4608
-- title:
--   $(L^{\dagger}K)|_R$, its extreme eigenvalues $\lambda_{\max},\lambda_{\min}$, the rate $\alpha$ and the $L$-weighted norm
-- statement:
--   Let $K$, $L^{\dagger}$ be as in Theorem 4.
--
--   1. $(L^{\dagger}K)|_R$ is the principal submatrix of $L^{\dagger}K$ on the rows and columns $(i,j)$ such that the edge $(i,j)$ is not prohibited, i.e. $j\in J_i$ (both orders of an edge, and $(i,i)$ when $i\in J_i$).
--   2. $\lambda_{\max}$ and $\lambda_{\min}$ are its largest and smallest eigenvalues.
--   3. For a dampening factor $\eta$, $\alpha = \max\{|1-\eta\lambda_{\min}|,\ |1-\eta\lambda_{\max}|\}$.
--   4. The **$L$-weighted norm** of an $n\times n$ matrix $X$ is
--   $$
--   \|X\|_L = \Bigl(\sum_{(i,j):\ j\in J_i}\bigl(Q_{i;j,j}+Q_{j;i,i}\bigr)X_{ij}^2\Bigr)^{1/2}.
--   $$
--
--   Items 1–3 are the quantities of Theorem 4. Item 4 is not in the paper: it is the norm in which the rate bound of Theorem 4, part 2, holds (the printed Frobenius version is false; see Theorem 4).
--
--   **Formalization Note** The eigenvalues are the real spectrum of $(L^{\dagger}K)|_R$, and $\lambda_{\max}$, $\lambda_{\min}$ are its supremum and infimum. Since $(L^{\dagger}K)|_R = (L|_R)^{-1}K|_R$ is similar to the symmetric matrix $(L|_R)^{-1/2}K|_R(L|_R)^{-1/2}$ (proof of Proposition 5, p.41), all its eigenvalues are real, so nothing is lost. The spectrum is finite, and nonempty when some pair is permitted; for the empty index set it is empty and the supremum is $0$, a case the statements exclude. The weights of $\|\cdot\|_L$ are positive on permitted pairs (proof of Proposition 4, p.38).
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Theorem 4, pp.15–16 ((L†K)|_R, λ_max, λ_min, α); proof of Proposition 5, A.8, p.41

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Q
import Definitions.Def_IncentiveFinNet_Supplement_matK

open Matrix

namespace IncentiveFinNet.Supplement

variable {n : ℕ}

/-- The positions `(i − 1)n + j` "such that the edge `(i, j)` is not prohibited"
(arXiv:2212.06808v3, Theorem 4, p.15), i.e. the pairs `(i, j)` with `j ∈ J_i`; both orders of an
edge and the diagonal `(i, i)` when `i ∈ J_i` are included. They are the nonzero rows of `R`. -/
abbrev PermIdx (S : NetworkSetting n) : Type :=
  {p : Fin n × Fin n // p.2 ∈ S.J p.1}

/-- `(L†K)|_R`, "the principal submatrix of `L†K` containing the rows/columns `(i − 1)n + j` such
that the edge `(i, j)` is not prohibited" (Theorem 4, p.15). -/
noncomputable def LKR (S : NetworkSetting n) : Matrix (PermIdx S) (PermIdx S) ℝ :=
  (matLpinv S * matK S).submatrix Subtype.val Subtype.val

/-- `λ_max`, the largest eigenvalue of `(L†K)|_R` (Theorem 4, p.15).

**Formalization Note** The eigenvalues are the real spectrum `spectrum ℝ (LKR S)`, and `λ_max` is
its `sSup`. `(L†K)|_R = (L|_R)⁻¹ K|_R` is similar to the symmetric matrix
`(L|_R)^{−1/2} K|_R (L|_R)^{−1/2}` (proof of Proposition 5, p.41), so all its eigenvalues are real
and the real spectrum is the whole spectrum. It is a finite set; it is nonempty when some pair is
permitted, which the statements using `lamMax` assume (for the empty index set the spectrum is
empty and `sSup ∅ = 0`). -/
noncomputable def lamMax (S : NetworkSetting n) : ℝ :=
  sSup (spectrum ℝ (LKR S))

/-- `λ_min`, the smallest eigenvalue of `(L†K)|_R` (Theorem 4, p.15); the `sInf` of its real
spectrum (see `lamMax`). -/
noncomputable def lamMin (S : NetworkSetting n) : ℝ :=
  sInf (spectrum ℝ (LKR S))

/-- The contraction factor `α = max{|1 − ηλ_min|, |1 − ηλ_max|}` of Theorem 4, part 2 (p.16). -/
noncomputable def convRate (S : NetworkSetting n) (η : ℝ) : ℝ :=
  max |1 - η * lamMin S| |1 - η * lamMax S|

/-- The `L`-weighted norm `‖X‖_L = √(Σ_{(i, j) : j ∈ J_i} (Q_{i;j,j} + Q_{j;i,i}) X_ij²)`, the norm in
which the rate bound of Theorem 4, part 2, holds (`‖vec X‖` weighted by the diagonal of `L` on the
permitted positions).

**Formalization Note** This norm is not in the paper. It replaces the Frobenius norm of the printed
part 2, which is false (see `IncentiveFinNet.Supplement.theorem_4`). The weights
`Q_{i;j,j} + Q_{j;i,i}` are positive for `j ∈ J_i` (proof of Proposition 4, p.38), so `‖·‖_L` is a
norm on the matrices that vanish off the permitted pairs, and it is equivalent to `‖·‖_F` there. -/
noncomputable def normL (S : NetworkSetting n) (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, if j ∈ S.J i then ((Q S i) j j + (Q S j) i i) * X i j ^ 2 else 0)

end IncentiveFinNet.Supplement


