-- Prove2me | Definitions.Def_AronszajnRK_Limits_KernelLE
-- name    : AronszajnRK_Limits_KernelLE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:07:40.291439+00:00
-- url     : https://prove2.me/theorems/b956f3c8-716f-4300-ae4f-78eef4089c92
-- title:
--   The order $K_1 \ll K$ between kernels
-- statement:
--   A function $M : Y\times Y\to\mathbb C$ on a set $Y$ is a **positive matrix** (in the sense of E. H. Moore) if for every finite family of points $y_1,\dots,y_n\in Y$ and every $\xi_1,\dots,\xi_n\in\mathbb C$
--
--   $$\sum_{i,j=1}^n M(y_i,y_j)\,\bar\xi_i\,\xi_j \ \ge\ 0 .$$
--
--   For two functions $K_1, K : Y\times Y\to\mathbb C$ one writes
--
--   $$K_1 \ll K \quad\Longleftrightarrow\quad K - K_1 \text{ is a positive matrix.}$$
--
--   This is the order in which the kernels of a decreasing sequence of classes decrease.
--
--   **Formalization Note** Positive matrices are Mathlib's `Matrix.PosSemidef` over the arbitrary index type $Y$: it requires hermitian symmetry and nonnegativity of $\sum_{i,j}\overline{\xi_i}\,M(y_i,y_j)\,\xi_j$ for every finitely supported $\xi$, which is the form above (hermitian symmetry follows from nonnegativity of the form over $\mathbb C$). No finiteness of $Y$ is assumed.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 354, §7 (definition of ≪), extended to arbitrary kernels in §11, p. 373, with §2 (3), p. 344 (positive matrix)

import Mathlib

namespace AronszajnRK.Limits

open scoped ComplexOrder

/-- The order `K₁ ≪ K` between kernels on a set `Y` (Aronszajn, *Theory of Reproducing Kernels*,
Trans. Amer. Math. Soc. 68 (1950), §7, p. 354, PDF p. 18): `K₁ ≪ K` iff `K − K₁` is a positive
matrix in the sense of §2 (3), p. 344, i.e. `Σ (K(yᵢ, yⱼ) − K₁(yᵢ, yⱼ)) ξ̄ᵢ ξⱼ ≥ 0` for every
finite family of points `yᵢ ∈ Y` and complex numbers `ξᵢ`. Mathlib's `Matrix.PosSemidef` over an
arbitrary index type uses finitely supported vectors and the quadratic form
`Σ star ξᵢ * M yᵢ yⱼ * ξⱼ`, which is exactly that form (and it includes hermitian symmetry). -/
def KernelLE {Y : Type*} (K₁ K : Y → Y → ℂ) : Prop :=
  (Matrix.of K - Matrix.of K₁).PosSemidef

end AronszajnRK.Limits


