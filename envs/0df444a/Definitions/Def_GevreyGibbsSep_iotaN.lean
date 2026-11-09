-- Prove2me | Definitions.Def_GevreyGibbsSep_iotaN
-- name    : GevreyGibbsSep_iotaN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:37:26.563624+00:00
-- url     : https://prove2.me/theorems/7a3d51a0-c35a-4e90-a94f-8252bd3b0ae1
-- title:
--   Isometry $\iota_N=I_{2N}^*I_N$
-- statement:
--   The isometry $\iota_N=I_{2N}^*I_N$ from the $N$-grid to the $2N$-grid (Fourier transform, zero-padding, inverse Fourier transform). As a matrix, its entry at $(y,k)$ is the $L^2(\mathbb T^d)$ inner product
--   $$\big\langle I_{2N}e_y,\ I_Ne_k\big\rangle=\int_{[0,2\pi)^d}\overline{(I_{2N}e_y)(x)}\,(I_Ne_k)(x)\,dx .$$
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Section A 3, p.25 (before Eq. (A41))

import Mathlib
import Definitions.Def_GevreyGibbsSep_periodCube
import Definitions.Def_GevreyGibbsSep_Grid
import Definitions.Def_GevreyGibbsSep_interpBasis

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The isometry `ι_N = I_{2N}^* I_N` from the `N`-grid to the `2N`-grid (arXiv:2608.24527
(sha256 d4fd40eb…), p.25, before (A41)), as a matrix: its `(y, k)` entry is the `L²(T^d)` inner
product `⟨I_{2N} e_y, I_N e_k⟩ = ∫_{[0,2π)^d} conj(I_{2N} e_y) · I_N e_k`. -/
noncomputable def iotaN (d N : ℕ) : Matrix (Grid d (2 * N)) (Grid d N) ℂ :=
  Matrix.of fun y k =>
    ∫ x in periodCube d, star (interpBasis d (2 * N) y x) * interpBasis d N k x

end GevreyGibbsSep


