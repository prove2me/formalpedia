-- Prove2me | Definitions.Def_FourierEntropyApprox_Supplement_cubeSet
-- name    : FourierEntropyApprox_Supplement_cubeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:03:38.481913+00:00
-- url     : https://prove2.me/theorems/3dfa3050-371c-4254-9306-2c5cc42c735b
-- title:
--   Affine subspaces of the Boolean cube and their codimension
-- statement:
--   Identify the cube $\{-1,1\}^n$ with the vector space $\mathbb F_2^n$ coordinatewise, sending $-1\mapsto 1$ and $1\mapsto 0$. Under this identification the character is $\chi_S(x)=(-1)^{\sum_{i\in S}x_i}$, so a parity constraint $\chi_S(x)=c$ cuts out an affine hyperplane. An **affine subspace** of the cube is the set of points of the cube lying in an affine subspace $H$ of $\mathbb F_2^n$; equivalently, a nonempty solution set of finitely many parity constraints. Its **codimension** is
--
--   $$\operatorname{co-dim}(H)=n-\dim(\text{direction of }H),$$
--
--   the number of linearly independent parity constraints needed to cut it out. A subcube that fixes $k$ coordinates is an affine subspace of codimension $k$, and an affine subspace of codimension $k$ has $2^{n-k}$ points.
--
--   These sets are the cells of parity certificates and the terms of conical juntas over affine subspaces (Theorems 4.3 and 4.5).
--
--   **Formalization Note** `toF2` is the coordinate identification, `cubeSet A` the points of the cube in a Mathlib affine subspace `A` of `Fin n → ZMod 2`, and `codim A` is $n$ minus the dimension of its direction. The paper's affine subspaces are the nonempty ones; the definitions that use them require nonemptiness explicitly.
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), §2, p.11 (parity-certificate complexity, co-dim(H)), p.12 (unambiguous ⊕-certificates), p.13 (conical juntas over affine subspaces)

import Mathlib
import Definitions.Def_FourierEntropyApprox_Cube

set_option autoImplicit false

namespace FourierEntropyApprox

/-!
# Affine subspaces of the Boolean cube and their codimension

M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), §2, p.11 ("Parity-certificate complexity … co-dim(H) is the co-dimension of the affine
subspace H"), p.12 ("It is easily seen that a subcube is also an affine subspace") and p.13 (conical juntas
"over affine subspaces").

**Formalization Note.**
* The cube `{−1, 1}ⁿ` is identified with the vector space `𝔽₂ⁿ` coordinatewise, `−1 ↦ 1` and `1 ↦ 0`
  (in the base encoding `true ↦ 1`, `false ↦ 0`); under this identification the character is
  `χ_S(x) = (−1)^{∑_{i∈S} xᵢ}`, so a parity constraint `χ_S(x) = c` is an affine hyperplane of `𝔽₂ⁿ`.
* An affine subspace of the cube is the preimage `cubeSet A` of a Mathlib affine subspace `A` of `𝔽₂ⁿ`;
  the paper's affine subspaces are the nonempty ones, and every statement using them requires
  `(A : Set _).Nonempty`.
* `codim A = n − dim(direction A)` is the true codimension (not the number of listed constraints). A subcube
  fixing `k` coordinates has codimension `k`.
-/

namespace Supplement

/-- The coordinatewise identification `{−1, 1}ⁿ → 𝔽₂ⁿ` (`true` (= −1) ↦ 1, `false` (= 1) ↦ 0). -/
def toF2 {n : ℕ} (x : Cube n) : Fin n → ZMod 2 := fun i => if x i then 1 else 0

/-- The points of the cube lying in the affine subspace `A` of `𝔽₂ⁿ` (pp.11–13). -/
def cubeSet {n : ℕ} (A : AffineSubspace (ZMod 2) (Fin n → ZMod 2)) : Set (Cube n) :=
  {x | toF2 x ∈ A}

/-- The codimension `co-dim(A) = n − dim(direction A)` of an affine subspace of `𝔽₂ⁿ` (p.11). -/
noncomputable def codim {n : ℕ} (A : AffineSubspace (ZMod 2) (Fin n → ZMod 2)) : ℕ :=
  n - Module.finrank (ZMod 2) A.direction

end Supplement

end FourierEntropyApprox


