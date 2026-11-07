-- Prove2me | Definitions.Def_CompNonlocal_fit
-- name    : CompNonlocal_fit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:09.671277+00:00
-- url     : https://prove2.me/theorems/bee6d78c-a3f1-490a-86ad-0c634f8271bf
-- title:
--   Reading a string as an element of $\{0,1\}^n$
-- statement:
--   The first $n$ bits of a string, padded with $0$ if it is shorter. Outputs that the paper requires to lie in $\{0,1\}^n$ (answers of fixed length, keys in $\{0,1\}^\kappa$, messages in $\{0,1\}^\kappa$) are read through this fixed local post-processing.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §5.2, p.24; Definitions 4, 5, p.21

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- A string read as an element of `{0,1}^n`: its first `n` bits, padded with `0` when shorter.
Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*,
manuscript (STOC 2027 submission, sha256 e245edd7…), uses fixed-length strings throughout (answers of
"polynomial length", §5.2, p.24; keys in `{0,1}^κ`, Definition 4, p.21; messages in `{0,1}^κ`,
Definition 5, p.21).

**Formalization Note** Every output that the paper requires to lie in `{0,1}^n` is read through
`fit n`, a fixed local post-processing by its owner. -/
def fit (n : ℕ) (s : Str) : Str := List.ofFn fun i : Fin n => s.getD i false

end CompNonlocal


