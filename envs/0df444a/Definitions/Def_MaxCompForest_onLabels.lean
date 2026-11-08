-- Prove2me | Definitions.Def_MaxCompForest_onLabels
-- name    : MaxCompForest_onLabels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:08.212202+00:00
-- url     : https://prove2.me/theorems/28a96fb2-ba78-4ba0-9d06-9933759521d7
-- title:
--   Principal block $A_F$ on a label set
-- statement:
--   For a matrix $A$ indexed by a set $E$ and $F\subseteq E$, the matrix $A_F$ keeping the rows and columns indexed by $F$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.1

import Mathlib

namespace MaxCompForest

variable {E : Type*}

/-- **The principal block `A_F`** of an edge-indexed matrix: rows and columns in `F`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.1: "where `K_F` keeps the rows and columns indexed by `F`". -/
def onLabels (A : Matrix E E ℝ) (F : Finset E) : Matrix F F ℝ :=
  A.submatrix Subtype.val Subtype.val

end MaxCompForest


