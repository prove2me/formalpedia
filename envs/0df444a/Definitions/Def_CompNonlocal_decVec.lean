-- Prove2me | Definitions.Def_CompNonlocal_decVec
-- name    : CompNonlocal_decVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:41:09.856853+00:00
-- url     : https://prove2.me/theorems/fd60dd99-0c12-480c-978a-b2f55ed50503
-- title:
--   Decoding a vector of $\mathbb R^3$
-- statement:
--   A bit string read as a vector $\hat r\in\mathbb R^3$: three consecutive self-delimiting dyadic rationals. Used for the outputs of the ASP decoder and of receiver-side estimators.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 14, p.33

import Mathlib
import Definitions.Def_CompNonlocal_decDyadic

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The vector of `ℝ³` encoded by a bit string: three consecutive self-delimiting dyadic rationals
(`decDyadic`). This is how a circuit's classical output is read as the vector `r̂ ∈ ℝ³` of
Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*,
manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 14, p.33 (Eqs. (23), (24)). -/
noncomputable def decVec (s : Str) : EuclideanSpace ℝ (Fin 3) :=
  let p₁ := decDyadic s
  let p₂ := decDyadic p₁.2
  let p₃ := decDyadic p₂.2
  WithLp.toLp 2 ![p₁.1, p₂.1, p₃.1]

end CompNonlocal


