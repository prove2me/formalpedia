-- Prove2me | Definitions.Def_VecBalPoly_M
-- name    : VecBalPoly_M
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:12:43.13864+00:00
-- url     : https://prove2.me/theorems/587134f7-079c-4a30-8b2e-670cee9af3d8
-- title:
--   The Gram matrix $M=W+\mathcal B+\eta\mathbf 1\mathbf 1^{\mathsf T}$ (2.5)–(2.6)
-- statement:
--   For a medium row $i$ and a sign $\sigma$ the barrier weight is
--   $$w_{i\sigma}=\frac{K^2}{2r_i^4}\,e^{u_{i\sigma}/(2K)},$$
--   and
--   $$W=\sum_{i\text{ medium},\,\sigma=\pm1}w_{i\sigma}\,p_ip_i^{\mathsf T},\qquad \mathcal B=\frac1K\sum_{i\text{ large}}\operatorname{diag}(p_i),\qquad M=W+\mathcal B+\eta\mathbf 1\mathbf 1^{\mathsf T},$$
--   with $\mathbf 1$ the all-ones vector of $\mathbb R^V$ and $\eta=1/(Kn)$. The largest eigenvalue of $M$ controls the number of nearly tight barriers.
--
--   **Formalization Note** $M$ is an $n\times n$ matrix with $\mathbf 1$ the indicator of $V$; the paper's matrix on $\mathbb R^V$ is its $V\times V$ block, also provided (indexed by the subtype $V$).
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), (2.5)–(2.6), p.5 (PDF p.6)

import Mathlib
import Definitions.Def_VecBalPoly_u

namespace VecBalPoly

open Classical

variable {m n : ℕ}

/-- **The barrier weight (2.5)** `w_{iσ} = K²/(2rᵢ⁴) · e^{u_{iσ}/(2K)}`.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), §2.3, (2.5), p.5 (PDF p.6). -/
noncomputable def w (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (i : Fin m) (σ : Bool) : ℝ :=
  K ^ 2 / (2 * st.r i ^ 4) * Real.exp (u A st i σ / (2 * K))

/-- **The weighted Gram matrix (2.5)** `W = ∑_{i medium, σ=±1} w_{iσ} pᵢpᵢᵀ`.
Source: ibid., (2.5), p.5 (PDF p.6). -/
noncomputable def W (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => IsMedium A st i), ∑ σ : Bool,
    w A st i σ • Matrix.vecMulVec (p A st i) (p A st i)

/-- **The large-row diagonal term (2.6)** `ℬ = (1/K) ∑_{i large} diag(pᵢ)`.
Source: ibid., (2.6), p.5 (PDF p.6). -/
noncomputable def B (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / K) • ∑ i ∈ Finset.univ.filter (fun i => IsLarge A st i), Matrix.diagonal (p A st i)

/-- The all-ones vector `1` of `ℝ^V`, as the indicator of `V` in `ℝⁿ`. -/
def oneV (st : St m n) : Fin n → ℝ :=
  fun j => if j ∈ st.V then 1 else 0

/-- **The matrix (2.6)** `M = W + ℬ + η11ᵀ`, with `η = 1/(Kn)` and `1` the all-ones vector of
`ℝ^V`.
Source: ibid., (2.6), p.5 (PDF p.6).

**Formalization Note** `M` is an `n × n` matrix; the paper's `M` on `ℝ^V` is its `V × V` block.
Off `V` the rank-one term vanishes (`1` is the indicator of `V`), and `pᵢ` vanishes off
`Tᵢ ⊆ V`. -/
noncomputable def M (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) : Matrix (Fin n) (Fin n) ℝ :=
  W A st + B A st + eta n • Matrix.vecMulVec (oneV st) (oneV st)

/-- The `V × V` block of `M`, the paper's `M` as a matrix on `ℝ^V`. -/
noncomputable def MV (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) : Matrix st.V st.V ℝ :=
  (M A st).submatrix Subtype.val Subtype.val

end VecBalPoly


