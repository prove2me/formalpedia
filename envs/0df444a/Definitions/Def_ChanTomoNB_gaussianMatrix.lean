-- Prove2me | Definitions.Def_ChanTomoNB_gaussianMatrix
-- name    : ChanTomoNB_gaussianMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:34.639639+00:00
-- url     : https://prove2.me/theorems/8d04a4d7-078d-4abc-86be-fc6f0cb6d10e
-- title:
--   Standard complex Gaussian vectors and circular Gaussian matrices $\mathrm{vec}\,G=C^{1/2}z$
-- statement:
--   A **standard complex Gaussian** $\mathcal{CN}(0,1)$ has independent real and imaginary parts of variance $1/2$. For a finite index set $\iota$, $z\sim\mathcal{CN}(0,I_\iota)$ has independent standard complex Gaussian coordinates.
--
--   For a positive semidefinite $C$ on $\mathbb C^{ab}$, the **centered circular complex Gaussian matrix with vectorized covariance $C$** is
--   $$
--   G\in\mathbb C^{a\times b},\qquad \mathrm{vec}\,G=C^{1/2}z,\qquad z\sim\mathcal{CN}(0,I_{ab}).
--   $$
--   A matrix $G_0\in\mathbb C^{m\times k}$ with independent $\mathcal{CN}(0,1)$ entries is the case $C=I$, read off entrywise from $z$.
--
--   These laws appear in the proof that a Haar-random signal range is balanced.
--
--   **Formalization Note** Each coordinate law is the published `BraneBrauer.Orthogonal.complexGaussian`. The vectorization is indexed by (row, column); since $C$ ranges over all PSD matrices, the order does not matter.
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Lemma 5.5 and its proof, pp.27–28

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_ComplexGaussian

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace ChanTomoNB

/-- The law of a vector `z ∈ ℂ^ι` with independent standard complex Gaussian `CN(0, 1)`
coordinates: independent real and imaginary parts of variance `1/2`. Chen, Oufkir,
*Quantum channel tomography: optimal bounds in the near-boundary regime*, arXiv:2611.03639v1,
Lemma 5.5, p.27 ("Here a standard complex Gaussian has independent real and imaginary parts of
variance 1/2"). Each coordinate is the published `BraneBrauer.Orthogonal.complexGaussian`. -/
noncomputable def stdComplexGaussianVec (ι : Type) [Fintype ι] : Measure (ι → ℂ) :=
  Measure.pi fun _ : ι => BraneBrauer.Orthogonal.complexGaussian

/-- The centered circular complex Gaussian matrix `G ∈ ℂ^{a×b}` with vectorized covariance `C`,
as a function of a standard vector `z ∼ CN(0, I_{ab})`: `vec G = C^{1/2} z`
(arXiv:2611.03639v1, proof of Lemma 5.5, p.28: "represent vec G = C^{1/2}(x + iy)/√2 with
independent standard real Gaussian vectors x, y"). For `C ⪰ 0` every centered circular complex
Gaussian matrix with vectorized covariance `C` has the law of `gaussCovMatrix C z`,
`z ∼ stdComplexGaussianVec`.

**Formalization Note.** `vec G` is indexed by `Fin a × Fin b` (row index first); any fixed
vectorization order gives the same statements, since `C` ranges over all PSD matrices with
`C ⪯ I`. `C^{1/2}` is `CFC.sqrt C`. -/
noncomputable def gaussCovMatrix {a b : ℕ} (C : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (z : Fin a × Fin b → ℂ) : Matrix (Fin a) (Fin b) ℂ :=
  Matrix.of fun i j => (CFC.sqrt C *ᵥ z) (i, j)

/-- The `m × k` matrix `G₀` whose entries are the coordinates of `z ∈ ℂ^{m×k}`; with
`z ∼ stdComplexGaussianVec`, `G₀` has independent `CN(0, 1)` entries (arXiv:2611.03639v1,
Lemma 5.5, p.27). -/
def toMat {m k : ℕ} (z : Fin m × Fin k → ℂ) : Matrix (Fin m) (Fin k) ℂ :=
  Matrix.of fun i j => z (i, j)

end ChanTomoNB


