-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_kronFamily
-- name    : OptimalSpectrum_Entangled_kronFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:07.32192+00:00
-- url     : https://prove2.me/theorems/38b4d00e-2017-4fdb-8315-659c0a688f9d
-- title:
--   Tensor product $H_1\otimes\cdots\otimes H_r$
-- statement:
--   For matrices $H_1,\dots,H_r$ on $\mathbb C^\iota$, the operator $H_1\otimes\cdots\otimes H_r$ on $(\mathbb C^\iota)^{\otimes r}$ has entries
--
--   $$(H_1\otimes\cdots\otimes H_r)_{x,y}=\prod_{j=1}^r (H_j)_{x_j,y_j},\qquad x,y\in\iota^r .$$
--
--   It is the test operator in Eq. (40) and Eq. (47), which define the derivative operators $\Theta^{(r)}_p$ and $K_r$ through their traces against product operators.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.2, Eq. (40), p. 22 (PDF p. 24)

import Mathlib

namespace OptimalSpectrum.Entangled

/-- **Tensor product `H₁ ⊗ ⋯ ⊗ H_r` of a family of matrices.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.2, printed pp. 21–22 (PDF pp. 23–24), Eq. (40): the operator `H₁ ⊗ ⋯ ⊗ H_r` on
`(C^d)^⊗r`.

For matrices `H₁, …, H_r` on `ℂ^ι`, the matrix on `(ℂ^ι)^{⊗r}` (basis indexed by `Fin r → ι`) with
entries `∏ⱼ (H_j)_(x_j, y_j)`.

**Formalization Note.** With all `H_j` equal to `M` this is the platform's `QAlgorithms.piKron r M`. -/
def kronFamily {ι : Type*} {r : ℕ} (H : Fin r → Matrix ι ι ℂ) :
    Matrix (Fin r → ι) (Fin r → ι) ℂ :=
  Matrix.of fun x y => ∏ j, H j (x j) (y j)

end OptimalSpectrum.Entangled


