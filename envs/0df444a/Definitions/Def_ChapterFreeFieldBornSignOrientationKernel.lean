-- Prove2me | Definitions.Def_ChapterFreeFieldBornSignOrientationKernel
-- name    : ChapterFreeFieldBornSignOrientationKernel
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T14:12:57.707984+00:00
-- url     : https://prove2.me/theorems/144fed60-6d8a-4612-968a-cef19771d825
-- title:
--   Chapter FreeFieldBornSignOrientationKernel
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFreeFieldBornSignOrientationKernel.lean`): generated def bundle for ChapterFreeFieldBornSignOrientationKernel. See BookProof/ChapterFreeFieldBornSignOrientationKernel.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFreeFieldBornSignOrientationKernel.lean

import Definitions.Def_ChapterFreeFieldBornSignOrientationCard
import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Definitions.Def_ChapterFreeFieldBornSignOrientation
import Mathlib

/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the orientation-preserving sign gauge as an index-two kernel

The preceding files represent the diagonal Born sign gauge by orthogonal
matrices, identify orientation preservation with even Hamming weight, and count
the orientation-preserving choices. This file records the corresponding
algebraic structure: the orientation-preserving choices contain the identity,
are closed under the boolean `xor` group law, and the parity of an `xor` is even
exactly when its two inputs have the same parity. Thus the even choices form the
kernel of the determinant/sign character, while the odd choices form its other
coset.

## Main results

* `orientationPreserving_false` — the identity sign choice preserves orientation.
* `orientationPreserving_xor` — orientation-preserving choices are closed under
  coordinate-wise `xor`.
* `even_flipCount_xor_iff` — an `xor` has even weight exactly when its inputs
  have the same parity.
* `orientationPreserving_xor_iff` — matrix form of the index-two kernel/coset law.
-/
namespace BookProof.ChapterFreeFieldBornSignOrientationKernel

end BookProof.ChapterFreeFieldBornSignOrientationKernel


