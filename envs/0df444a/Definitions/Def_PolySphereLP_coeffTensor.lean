-- Prove2me | Definitions.Def_PolySphereLP_coeffTensor
-- name    : PolySphereLP_coeffTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:19.827917+00:00
-- url     : https://prove2.me/theorems/5186b4e5-7cd4-438c-b3e7-46a5ecd16861
-- title:
--   The symmetric coefficient tensor $T_G$
-- statement:
--   A homogeneous polynomial $G$ of degree $k$ has a unique symmetric coefficient tensor $T_G$ with
--   $$G(x)=\sum_{i_1,\dots,i_k=1}^n (T_G)_{i_1\dots i_k}\,x_{i_1}\cdots x_{i_k},\qquad (T_G)_{i_1\dots i_k}=\frac1{k!}\,\partial_{i_1}\cdots\partial_{i_k}G.$$
--   For example the tensor of $x_1x_2$ has entries $\tfrac12$ at $(1,2)$ and $(2,1)$.
--
--   **Formalization Note** Computed by the derivative formula: the $k$-fold derivative of a homogeneous degree-$k$ polynomial is a constant, read off as its constant coefficient. Coefficients are complex.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), §2.3, p.12

import Mathlib
import Definitions.Def_PolySphereLP_Tensor

namespace PolySphereLP

/-- **The symmetric coefficient tensor `T_G`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), §2.3, p.12: "A homogeneous polynomial `G` of
degree `k` has a unique symmetric coefficient tensor `T_G` characterized by
`G(x) = ∑ (T_G)_{i₁…i_k} x_{i₁}⋯x_{i_k}`, `(T_G)_{i₁…i_k} = (1/k!) ∂_{i₁}⋯∂_{i_k} G`."

`coeffTensor k G i = (1/k!) · (∂_{i₁}⋯∂_{i_k} G)(0)`.

**Formalization Note.** For `G` homogeneous of degree `k` the iterated derivative is a constant, and
the constant coefficient reads it off. Partial derivatives commute, so the order is immaterial.
Complex coefficients; a real polynomial enters through its complex image. -/
noncomputable def coeffTensor {n : ℕ} (k : ℕ) (G : MvPolynomial (Fin n) ℂ) : Tensor n k :=
  fun i => (1 / (k.factorial : ℂ)) *
    MvPolynomial.constantCoeff ((List.ofFn i).foldr (fun j p => MvPolynomial.pderiv j p) G)

end PolySphereLP


