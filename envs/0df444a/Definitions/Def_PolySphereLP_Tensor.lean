-- Prove2me | Definitions.Def_PolySphereLP_Tensor
-- name    : PolySphereLP_Tensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:20.335983+00:00
-- url     : https://prove2.me/theorems/3dde7fd6-13bc-4860-95e3-6879edd63599
-- title:
--   Complex tensors and the Frobenius inner product
-- statement:
--   An order-$k$ complex tensor on $\mathbb C^n$ is an array $T=(T_{i_1\dots i_k})$ indexed by $i_1,\dots,i_k\in[n]$. The **Frobenius inner product**, linear in the first argument, is
--   $$\langle S,T\rangle_F=\sum_{i_1,\dots,i_k=1}^n S_{i_1\dots i_k}\,\overline{T_{i_1\dots i_k}},$$
--   and $\|T\|_F^2=\sum|T_{i_1\dots i_k}|^2$.
--
--   **Formalization Note** Indices are maps $\{0,\dots,k-1\}\to\{0,\dots,n-1\}$; $\|T\|_F^2$ is real-valued.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), §2.3, p.12

import Mathlib

namespace PolySphereLP

/-- **Complex order-`k` tensors on `ℂⁿ`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), §2.3, p.12. A tensor is its array of entries
`T_{i₁…i_k}`, indexed by `i : Fin k → Fin n` (0-based). -/
abbrev Tensor (n k : ℕ) : Type := (Fin k → Fin n) → ℂ

/-- **The Frobenius inner product.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), §2.3, p.12: `⟨S, T⟩_F =def ∑ S_{i₁…i_k} T̄_{i₁…i_k}`,
linear in the first argument. -/
noncomputable def frob {n k : ℕ} (S T : Tensor n k) : ℂ :=
  ∑ i, S i * starRingEnd ℂ (T i)

/-- **The squared Frobenius norm** `‖T‖²_F = ∑ |T_{i₁…i_k}|²` (real-valued). -/
noncomputable def frobNormSq {n k : ℕ} (T : Tensor n k) : ℝ :=
  ∑ i, Complex.normSq (T i)

end PolySphereLP


