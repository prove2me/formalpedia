-- Prove2me | Definitions.Def_EulerSparsify_sqrtPinv
-- name    : EulerSparsify_sqrtPinv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:32.313195+00:00
-- url     : https://prove2.me/theorems/0ee3d28a-2fdc-4fa4-b1b2-6ad6cdf1d512
-- title:
--   The matrix $M^{\dagger/2}$
-- statement:
--   For a square real matrix $M$, $M^\dagger$ denotes its **Moore–Penrose pseudoinverse** and $M^{\dagger/2}$ the positive semidefinite square root of $M^\dagger$. For a Laplacian $L_G$ (symmetric positive semidefinite) the pseudoinverse is again positive semidefinite, so $L_G^{\dagger/2}$ is well defined; it is the normalisation in Definition 1.1 and in all spectral statements of the mission.
--
--   **Formalization Note** The pseudoinverse is the published `HarmonicGames.Decomposition.pinv` (taken in the Euclidean inner product) and the square root is the published `WassersteinDRO.Shrinkage.psdSqrt`; neither adds a condition. The junk value $0$ of `psdSqrt` (no PSD square root) is never reached on a pseudoinverse of a Laplacian.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §1, Definition 1.1, p.1 (PDF p.3); §3, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_WassersteinDRO_Shrinkage_psdSqrt

namespace EulerSparsify

/-- The Moore–Penrose pseudoinverse `M†` of a square real matrix, computed by the published
`HarmonicGames.Decomposition.pinv` on the Euclidean linear map of `M`. -/
noncomputable def pinvMat {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    Matrix n n ℝ :=
  Matrix.toEuclideanLin.symm (HarmonicGames.Decomposition.pinv (Matrix.toEuclideanLin M))

/-- **The matrix `M^{†/2}`** (§1, Definition 1.1, p.1, PDF p.3; §3, p.8, PDF p.10).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), §3, p.8: "We let ker(M),
im(M), and M† denote the kernel, image and pseudoinverse of M"; Definition 1.1 uses `L_G^{†/2}`.

`sqrtPinv M` is the positive semidefinite square root of the pseudoinverse `M†`.

**Formalization Note.** The pseudoinverse is the published `HarmonicGames.Decomposition.pinv`
(taken with respect to the Euclidean inner product) and the square root is the published
`WassersteinDRO.Shrinkage.psdSqrt`. For a Laplacian `L` (symmetric positive semidefinite), `L†` is
positive semidefinite, so its PSD square root exists and is unique; the junk value `0` of
`psdSqrt` is never reached on Laplacians. -/
noncomputable def sqrtPinv {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    Matrix n n ℝ :=
  WassersteinDRO.Shrinkage.psdSqrt (pinvMat M)

end EulerSparsify


