-- Prove2me | Definitions.Def_DerandSq_perpCompress
-- name    : DerandSq_perpCompress
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:47.214821+00:00
-- url     : https://prove2.me/theorems/84276f74-8fdf-4c6e-9f54-e02fb9b820fb
-- title:
--   Compression to $\mathbf 1^\perp$: $Y|_{\perp 1}$
-- statement:
--   For an operator $Y$ on $\mathbb C^D \otimes \mathbb C^N$ let
--   $$
--   Y|_{\perp 1} = \bigl(I_D \otimes (I - J)\bigr)\, Y\, \bigl(I_D \otimes (I - J)\bigr), \qquad J = \mathbf 1\mathbf 1^\top / N .
--   $$
--   This removes the trivial subspace spanned by the constant vector (in each of the $D$ copies), on which every polynomial in permutation matrices acts trivially; for $D = 1$ it is the paper's $A^N|_{\perp 1} = (I - J^N) A^N (I - J^N)$.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), §2.5, p.12

import Mathlib
import Definitions.Def_AccessibleMaps_tensorOp

namespace DerandSq

/-- `Y|_{⊥1} = (I_D ⊗ (I − J)) Y (I_D ⊗ (I − J))` with `J = 11ᵀ/N`, for an operator `Y` on `D`
copies of `ℂ^N` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), §2.5, p.12: "A^N|_{⊥1} = (I − J^N) A^N (I − J^N)"; with matrix
coefficients the projection acts on the `ℂ^N` factor). -/
noncomputable def perpCompress (D N : ℕ)
    (Y : PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →L[ℂ]
      PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) :
    PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →L[ℂ]
      PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) :=
  let Q : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
    Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - (N : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℂ)))
  (AccessibleMaps.tensorOp (1 : Matrix (Fin D) (Fin D) ℂ) Q).comp (Y.comp (AccessibleMaps.tensorOp (1 : Matrix (Fin D) (Fin D) ℂ) Q))

end DerandSq


