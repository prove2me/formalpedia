-- Prove2me | Definitions.Def_PolySphereLP_tensorAct
-- name    : PolySphereLP_tensorAct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:24.11504+00:00
-- url     : https://prove2.me/theorems/d540b8ca-6f8f-4885-a649-ad91fcd383a8
-- title:
--   The tensor-power action $O^{\otimes k}$
-- statement:
--   For a real $n\times n$ matrix $O$ and an order-$k$ tensor $T$,
--   $$(O^{\otimes k}T)_{i_1\dots i_k}=\sum_{j_1,\dots,j_k}O_{i_1j_1}\cdots O_{i_kj_k}\,T_{j_1\dots j_k}.$$
--   For orthogonal $O$ it preserves $E_{n,k}$, and $U_{n,k}(O)=O^{\otimes k}|_{E_{n,k}}$ is the rotation action on harmonic tensors.
--
--   **Formalization Note** Defined as a complex-linear map on all order-$k$ tensors; its Frobenius adjoint is $(O^\top)^{\otimes k}$.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), p.13

import Mathlib
import Definitions.Def_PolySphereLP_Tensor

namespace PolySphereLP

/-- **The tensor-power action `O^{⊗k}`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), p.13: "the action becomes `U_{n,k}(O) =def
O^{⊗k}|_{E_{n,k}}`".

`(O^{⊗k} T)_{i₁…i_k} = ∑_{j} O_{i₁j₁}⋯O_{i_kj_k} T_{j₁…j_k}` for a real `n × n` matrix `O`, as a
complex-linear map on all order-`k` tensors.

**Formalization Note.** `U_{n,k}(O)` is this map restricted to `E_{n,k}`, which it preserves for
orthogonal `O`; the items apply it to elements of `E_{n,k}` only. Its Frobenius adjoint is
`Oᵀ^{⊗k}`. -/
noncomputable def tensorAct {n : ℕ} (k : ℕ) (O : Matrix (Fin n) (Fin n) ℝ) :
    Tensor n k →ₗ[ℂ] Tensor n k where
  toFun T i := ∑ j : Fin k → Fin n, (∏ s, ((O (i s) (j s) : ℝ) : ℂ)) * T j
  map_add' S T := by
    funext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c T := by
    funext i
    simp [Finset.mul_sum, mul_left_comm]

end PolySphereLP


