-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_ansatzF
-- name    : TwoFoldOPI_Supplement_ansatzF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:56:29.391571+00:00
-- url     : https://prove2.me/theorems/22ce3ac7-1410-4f89-a92b-38b5ac58235b
-- title:
--   Step 2 of Algorithm 8.1: the quadratic map $f(z)$
-- statement:
--   Given $\xi$, $A\in\mathbb F_q^{\ell\times m}$ and $h,w\in\mathbb F_q^m$, step 2 of Algorithm 8.1 defines $f:\mathbb F_q^\ell\to\mathbb F_q^m$ by
--   $$f(z)=\tfrac14\,h\odot\Big(\big(A^{\top}z+w\odot h^{-1}\big)^{\odot2}-\xi\mathbf 1\Big).$$
--   Step 4 returns $f(z)$ for the solution $z$ of step 3.
--
--   **Formalization Note** $\tfrac14$ is the field inverse of $4$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §8.1, Algorithm 8.1, step 2, p. 45

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **Step 2 of Algorithm 8.1: the quadratic map `f(z) = ¼ h ⊙ ((Aᵀz + w ⊙ h^{−1})^{⊙2} − ξ 1)`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §8.1, Algorithm 8.1, step 2, p.45: "Define f : F_q^ℓ → F_q^m by
f(z) = (1/4) h ⊙ [(A^⊤ z + w ⊙ h^{−1})^{⊙2} − ξ1]."

For `A ∈ K^{ℓ×m}` and `z ∈ K^ℓ`, coordinate `j` of `f(z)` is
`¼ h_j ((Σ_i A_{ij} z_i + w_j / h_j)² − ξ)`.

**Formalization Note.** `¼` is the field inverse of `4` (odd-order fields). Step 4 of the
algorithm returns `f(z)` for the `z` found in step 3. -/
def ansatzF {K : Type*} [Field K] {m ℓ : ℕ} (ξ : K) (A : Matrix (Fin ℓ) (Fin m) K)
    (h w : Fin m → K) (z : Fin ℓ → K) : Fin m → K :=
  fun j => (4 : K)⁻¹ * h j * (((A.transpose).mulVec z j + w j * (h j)⁻¹) ^ 2 - ξ)

end Supplement

end TwoFoldOPI


