-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_ansatzY0
-- name    : TwoFoldOPI_Supplement_ansatzY0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:56:12.474959+00:00
-- url     : https://prove2.me/theorems/febd087f-ebfb-4a32-9bea-4bb381e0088b
-- title:
--   Step 1 of Algorithm 8.1: $y_0=\tfrac14(h^{-1}\odot w^{\odot2}-\xi h)$
-- statement:
--   Given $\xi\in\mathbb F_q$ and $h,w\in\mathbb F_q^m$ with every $h_j\ne0$, step 1 of Algorithm 8.1 computes
--   $$y_0=\tfrac14\big(h^{-1}\odot w^{\odot2}-\xi h\big),\qquad (y_0)_j=\tfrac14\Big(\frac{w_j^2}{h_j}-\xi h_j\Big).$$
--
--   **Formalization Note** $\tfrac14$ is the field inverse of $4$, nonzero in the odd-order fields of the algorithm.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §8.1, Algorithm 8.1, step 1, p. 45

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **Step 1 of Algorithm 8.1: `y_0 = ¼ (h^{−1} ⊙ w^{⊙2} − ξ h)`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §8.1, Algorithm 8.1, step 1, p.45: "Compute y_0 = (1/4)(h^{−1} ⊙ w^{⊙2} − ξh)."

Coordinate-wise, `y_0(j) = ¼ (w_j² / h_j − ξ h_j)`.

**Formalization Note.** `¼` is the inverse of `4` in the field; the algorithm's fields have odd
order, where `4 ≠ 0`. `h` has nonzero entries on every input of the algorithm. -/
def ansatzY0 {K : Type*} [Field K] {m : ℕ} (ξ : K) (h w : Fin m → K) : Fin m → K :=
  fun j => (4 : K)⁻¹ * ((h j)⁻¹ * w j ^ 2 - ξ * h j)

end Supplement

end TwoFoldOPI


