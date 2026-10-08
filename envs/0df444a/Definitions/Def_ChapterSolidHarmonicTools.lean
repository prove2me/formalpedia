-- Prove2me | Definitions.Def_ChapterSolidHarmonicTools
-- name    : ChapterSolidHarmonicTools
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T01:55:36.79889+00:00
-- url     : https://prove2.me/theorems/991dce9f-03f1-450a-9626-279dc3102ade
-- title:
--   Chapter SolidHarmonicTools
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSolidHarmonicTools.lean`): generated def bundle for ChapterSolidHarmonicTools. See BookProof/ChapterSolidHarmonicTools.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSolidHarmonicTools.lean

import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterRadialLaplacian
import Mathlib

/-!
# Tools for solid harmonics: Laplacians of powers of linear forms and of `‖x‖²`

This module supplies the differential-calculus toolkit needed to exhibit the
solid harmonics `rˡ Y_{lμ}(θ,φ)` of `book.tex` §A.5 as *bona fide* harmonic
functions, homogeneous of degree `l`, on a three-dimensional Euclidean space.
It continues `BookProof.ChapterRadialLaplacian` and
`BookProof.ChapterLaplacianProduct`.

## Contents

* `laplacian_clmPow` / `laplacian_rclmPow` — the Laplacian of the `k`-th power
  of a (complex- resp. real-valued) continuous linear functional:
  `Δ(ψ ^ k) = k(k−1) ψ^{k−2} ∑ᵢ ψ(bᵢ)²`.  In particular a functional whose
  coordinate squares sum to zero (a *null* functional, such as `x¹ + i x²`)
  has harmonic powers — these are the top spherical harmonics;
* `laplacian_normSqPow`, `fderiv_normSqPow` — the Laplacian and the derivative
  of `x ↦ (‖x‖²)ᵐ`;
* `laplacian_sum` — the Laplacian of a finite sum;
* `laplacian_angular_mul_term` — the key computation: for an *angular* factor
  `A` (harmonic, homogeneous of degree `μ` in the sense of Euler's identity,
  and constant along the axis `e`) and the cylindrical monomial
  `⟪e,x⟫ʲ (‖x‖²)ᵐ`,
  `Δ(A · ⟪e,·⟫ʲ‖·‖^{2m}) = A · [ j(j−1)⟪e,x⟫^{j−2}(‖x‖²)ᵐ
      + (4m(m−1) + 2nm + 4jm + 4μm) ⟪e,x⟫ʲ(‖x‖²)^{m−1} ]`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/
namespace BookProof.ChapterSolidHarmonicTools

end BookProof.ChapterSolidHarmonicTools


