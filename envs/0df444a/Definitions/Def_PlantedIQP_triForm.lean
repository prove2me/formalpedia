-- Prove2me | Definitions.Def_PlantedIQP_triForm
-- name    : PlantedIQP_triForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:12.900205+00:00
-- url     : https://prove2.me/theorems/aa0aabf6-6de4-4f1e-9a12-94398cb649f4
-- title:
--   The alternating trilinear form $T_f$ and its slices $T^f_u$
-- statement:
--   For a cubic polynomial $f$ with cubic coefficients $F_{ijk}$, the **alternating trilinear form** $T_f:\mathbb F_2^n\times\mathbb F_2^n\times\mathbb F_2^n\to\mathbb F_2$ is fixed on standard basis vectors by $T_f(e_{\pi(i)},e_{\pi(j)},e_{\pi(k)})=F_{ijk}$ for distinct $i<j<k$ and every permutation $\pi$, and $T_f=0$ on basis triples with a repeated index, then extended by trilinearity:
--
--   $$
--   T_f(u,v,w)=\sum_{i,j,k}u_iv_jw_k\,T_f(e_i,e_j,e_k).
--   $$
--
--   The **slice** $T^f_u(v,w)=T_f(u,v,w)$ is a bilinear form, recorded by its matrix $\big(T_f(u,e_i,e_j)\big)_{i,j}$.
--
--   $T_f$ captures exactly the cubic coefficients of $f$; independent spaces are the subspaces on which it vanishes (Proposition 20).
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Definition 15, p.14 and Theorem 17, p.15

import Mathlib
import Definitions.Def_PlantedIQP_CubicPoly

set_option autoImplicit false

namespace PlantedIQP

/-!
# The alternating trilinear form `T_f` and its slices

Bläser et al., arXiv:2609.39918 (sha256 6e261694…), Definition 15, p.14: "Let f : 𝔽₂ⁿ → 𝔽₂ be a
cubic polynomial as in Eq. (11). The alternating trilinear form T_f : 𝔽₂ⁿ × 𝔽₂ⁿ × 𝔽₂ⁿ → 𝔽₂
associated with the cubic part of f is obtained by specifying its evaluations on the standard basis
vectors {e_i} and extending by linearity as follows: 1. For distinct indices i < j < k and any
permutation π ∈ S₃, we set T_f(e_π(i), e_π(j), e_π(k)) = F_ijk. 2. If any indices coincide, T_f
evaluates to 0." Theorem 17, p.15: `T^f_u(v, w) = T_f(u, v, w)`.

**Formalization Note.**
* Extension by trilinearity: `T_f(u, v, w) = Σ_{i,j,k} u_i v_j w_k T_f(e_i, e_j, e_k)` with
  `T_f(e_i, e_j, e_k) = coeff3 f i j k` (`F_{ijk}` in any order, `0` on coinciding indices).
* `sliceMatrix f u` is the matrix of the bilinear form `T^f_u = T_f(u, ·, ·)` in the standard basis,
  `(i, j) ↦ T_f(u, e_i, e_j)`. The form is named `triForm` to keep `T` free for time bounds.
-/

/-- `T_f(u, v, w)`, the alternating trilinear form of the cubic part of `f` (Definition 15). -/
def triForm {n : ℕ} (f : CubicPoly n) (u v w : Vec n) : ZMod 2 :=
  ∑ i, ∑ j, ∑ k, u i * v j * w k * f.coeff3 i j k

/-- The matrix of the bilinear form `T^f_u(v, w) = T_f(u, v, w)` (Theorem 17): entry `(i, j)` is
`T_f(u, e_i, e_j)`. -/
def sliceMatrix {n : ℕ} (f : CubicPoly n) (u : Vec n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => triForm f u (stdBasis i) (stdBasis j)

end PlantedIQP


