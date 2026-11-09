-- Prove2me | Definitions.Def_ResultantVNP_symTensorDet
-- name    : ResultantVNP_symTensorDet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:37:16.217191+00:00
-- url     : https://prove2.me/theorems/a2598be8-4148-43ce-be04-729f380e7a75
-- title:
--   Tensor determinant on symmetric tensors
-- statement:
--   A cubic tensor is **symmetric** if $a_{ijk}=a_{i'j'k'}$ whenever $(i',j',k')$ is a permutation of $(i,j,k)$. The tensor determinant restricted to symmetric tensors, with one independent variable $a_T$ for each unordered triple $T=\{i,j,k\}$ of indices, is the polynomial obtained from $\mathrm{Det}_n$ by substituting $a_{ijk}\mapsto a_{\{i,j,k\}}$.
--
--   On a symmetric tensor the coefficient of $x_jx_k$ ($j\ne k$) in $(Ax^2)_i$ is $2a_{\{i,j,k\}}$ and that of $x_j^2$ is $a_{\{i,j,j\}}$.
--
--   **Formalization Note** Unordered triples are multisets of size three (`Sym (Fin n) 3`), so $\{i,i,j\}\ne\{i,j,j\}$.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 2.3, p.13; Theorem 3.2, p.14; Theorem 1.4, p.6

import Mathlib
import Definitions.Def_ResultantVNP_tensorDet

namespace ResultantVNP

/-- The **tensor determinant on symmetric cubic tensors**, "with one independent variable for each
unordered triple of indices": `Det_n(A)` for the symmetric tensor whose entry `a_{ijk}` is the variable
`a_{{i,j,k}}` of the unordered triple (multiset) `{i, j, k}`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 2.3, p.13 ("The tensor A is symmetric if its entries are unchanged by permuting the index
positions") and Theorem 3.2, p.14 ("on symmetric cubic tensors, with one independent variable for each
unordered triple of indices"); Theorem 1.4, p.6 ("tensor determinants {Det_n(A)}_{n≥1} restricted to
symmetric tensors A of order three").

**Formalization Note** Unordered triples are `Sym (Fin n) 3` (multisets of size three, so
`{i,i,j} ≠ {i,j,j}`). Obtained from `tensorDet` by renaming `a_{ijk} ↦ a_{{i,j,k}}`; so the coefficient of
`x_j x_k` (`j ≠ k`) in `(Ax²)_i` becomes `2a_{{i,j,k}}`, as on p.16. -/
noncomputable def symTensorDet (𝓡 : ResultantSystem) (n : ℕ) : MvPolynomial (Sym (Fin n) 3) ℤ :=
  MvPolynomial.rename (fun t : Fin n × Fin n × Fin n => t.1 ::ₛ t.2.1 ::ₛ t.2.2 ::ₛ Sym.nil)
    (tensorDet 𝓡 n)

end ResultantVNP


