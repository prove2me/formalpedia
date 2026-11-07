-- Prove2me | Definitions.Def_CompNonlocal_decDir
-- name    : CompNonlocal_decDir
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:02.224924+00:00
-- url     : https://prove2.me/theorems/8a01a1f4-af5c-49d2-85b7-d1be850cc7e3
-- title:
--   Decoding a unit direction
-- statement:
--   A bit string read as a direction $n\in S^2$: the decoded vector $v$ normalized to $v/\|v\|_2$, and the fixed unit vector $e_3$ if $v=0$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 15, p.41

import Mathlib
import Definitions.Def_CompNonlocal_decVec

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The unit direction encoded by a bit string: the decoded vector `v = decVec s`, normalized to
`v / ‖v‖`, and the fixed unit vector `e₃` when `v = 0`. This reads a circuit's output as a
direction "n ∈ S²", as in Lemma 15 of Głuch, Morimae, *From Computational Nonlocality to Public-Key
Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), p.41 ("returns
n ∈ S²"). Every point of `S²` is a limit of decodable directions. -/
noncomputable def decDir (s : Str) : EuclideanSpace ℝ (Fin 3) :=
  if decVec s = 0 then EuclideanSpace.single 2 1 else ‖decVec s‖⁻¹ • decVec s

end CompNonlocal


